use crate::arithmetic::{best_multiexp, g_to_lagrange, parallelize};
use crate::helpers::SerdeCurveAffine;
use crate::poly::commitment::{Blind, CommitmentScheme, Params, ParamsProver, ParamsVerifier};
use crate::poly::{Coeff, LagrangeCoeff, Polynomial};
use crate::SerdeFormat;

use ff::{Field, PrimeField};
use group::{prime::PrimeCurveAffine, Curve, Group};
use halo2curves::pairing::Engine;
use rand_core::{OsRng, RngCore};
use std::fmt::Debug;
use std::marker::PhantomData;

use std::io;

use super::msm::MSMKZG;

/// These are the public parameters for the polynomial commitment scheme.
#[derive(Debug, Clone)]
pub struct ParamsKZG<E: Engine> {
    pub(crate) k: u32,
    pub(crate) n: u64,
    pub(crate) g: Vec<E::G1Affine>,
    pub(crate) g_lagrange: Vec<E::G1Affine>,
    pub(crate) g2: E::G2Affine,
    pub(crate) s_g2: E::G2Affine,
}

/// KZG multi-open verification parameters.
/// These parameters need to support the veification of a KZG PLONK proof.
/// As a consequence, they need to support the computation of the PI commitment.
#[derive(Debug, Clone)]
pub struct ParamsVerifierKZG<E: Engine> {
    // Log-size of the domain.
    pub(crate) k: u32,
    // Domain size.
    pub(crate) n: u64,
    // This is the maximum size of PI supported.
    pub(crate) trimed_size: u32,

    pub(crate) g_lagrange: Vec<E::G1Affine>,
    pub(crate) s_g2: E::G2Affine,
}

/// Umbrella commitment scheme construction for all KZG variants
#[derive(Debug)]
pub struct KZGCommitmentScheme<E: Engine> {
    _marker: PhantomData<E>,
}

impl<E: Engine + Debug> CommitmentScheme for KZGCommitmentScheme<E>
where
    E::Scalar: PrimeField,
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    type Scalar = E::Scalar;
    type Curve = E::G1Affine;

    type ParamsProver = ParamsKZG<E>;
    type ParamsVerifier = ParamsVerifierKZG<E>;

    fn new_params(k: u32) -> Self::ParamsProver {
        ParamsKZG::new(k)
    }

    fn read_params<R: io::Read>(reader: &mut R) -> io::Result<Self::ParamsProver> {
        ParamsKZG::read(reader)
    }
}

impl<E: Engine + Debug> ParamsKZG<E>
where
    E::Scalar: PrimeField,
{
    /// Initializes parameters for the curve, draws toxic secret from given rng.
    /// MUST NOT be used in production.
    pub fn setup<R: RngCore>(k: u32, rng: R) -> Self {
        // Largest root of unity exponent of the Engine is `2^E::Scalar::S`, so we can
        // only support FFTs of polynomials below degree `2^E::Scalar::S`.
        assert!(k <= E::Scalar::S);
        let n: u64 = 1 << k;

        // Calculate g = [G1, [s] G1, [s^2] G1, ..., [s^(n-1)] G1] in parallel.
        let g1 = E::G1Affine::generator();
        let s = <E::Scalar>::random(rng);

        let mut g_projective = vec![E::G1::identity(); n as usize];
        parallelize(&mut g_projective, |g, start| {
            let mut current_g: E::G1 = g1.into();
            current_g *= s.pow_vartime([start as u64]);
            for g in g.iter_mut() {
                *g = current_g;
                current_g *= s;
            }
        });

        let g = {
            let mut g = vec![E::G1Affine::identity(); n as usize];
            parallelize(&mut g, |g, starts| {
                E::G1::batch_normalize(&g_projective[starts..(starts + g.len())], g);
            });
            g
        };

        let mut g_lagrange_projective = vec![E::G1::identity(); n as usize];
        let mut root = E::Scalar::ROOT_OF_UNITY;
        for _ in k..E::Scalar::S {
            root = root.square();
        }
        let n_inv = E::Scalar::from(n)
            .invert()
            .expect("inversion should be ok for n = 1<<k");
        let multiplier = (s.pow_vartime([n]) - E::Scalar::ONE) * n_inv;
        parallelize(&mut g_lagrange_projective, |g, start| {
            for (idx, g) in g.iter_mut().enumerate() {
                let offset = start + idx;
                let root_pow = root.pow_vartime([offset as u64]);
                let scalar = multiplier * root_pow * (s - root_pow).invert().unwrap();
                *g = g1 * scalar;
            }
        });

        let g_lagrange = {
            let mut g_lagrange = vec![E::G1Affine::identity(); n as usize];
            parallelize(&mut g_lagrange, |g_lagrange, start| {
                let end = start + g_lagrange.len();
                E::G1::batch_normalize(&g_lagrange_projective[start..end], g_lagrange);
            });
            drop(g_lagrange_projective);
            g_lagrange
        };

        let g2 = <E::G2Affine as PrimeCurveAffine>::generator();
        let s_g2 = (g2 * s).into();

        Self {
            k,
            n,
            g,
            g_lagrange,
            g2,
            s_g2,
        }
    }

    /// Initializes parameters for the curve through existing parameters
    /// k, g, g_lagrange (optional), g2, s_g2
    pub fn from_parts(
        &self,
        k: u32,
        g: Vec<E::G1Affine>,
        g_lagrange: Option<Vec<E::G1Affine>>,
        g2: E::G2Affine,
        s_g2: E::G2Affine,
    ) -> Self {
        Self {
            k,
            n: 1 << k,
            g_lagrange: match g_lagrange {
                Some(g_l) => g_l,
                None => g_to_lagrange(g.iter().map(PrimeCurveAffine::to_curve).collect(), k),
            },
            g,
            g2,
            s_g2,
        }
    }

    /// Returns gernerator on G2
    pub fn g2(&self) -> E::G2Affine {
        self.g2
    }

    /// Returns first power of secret on G2
    pub fn s_g2(&self) -> E::G2Affine {
        self.s_g2
    }

    /// Writes parameters to buffer
    pub fn write_custom<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>
    where
        E::G1Affine: SerdeCurveAffine,
        E::G2Affine: SerdeCurveAffine,
    {
        writer.write_all(&self.k.to_le_bytes())?;
        for el in self.g.iter() {
            el.write(writer, format)?;
        }
        for el in self.g_lagrange.iter() {
            el.write(writer, format)?;
        }
        self.g2.write(writer, format)?;
        self.s_g2.write(writer, format)?;
        Ok(())
    }

    /// Reads params from a buffer.
    pub fn read_custom<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self>
    where
        E::G1Affine: SerdeCurveAffine,
        E::G2Affine: SerdeCurveAffine,
    {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);
        let n = 1 << k;

        let (g, g_lagrange) = match format {
            SerdeFormat::Processed => {
                use group::GroupEncoding;
                let load_points_from_file_parallelly =
                    |reader: &mut R| -> io::Result<Vec<Option<E::G1Affine>>> {
                        let mut points_compressed =
                            vec![<<E as Engine>::G1Affine as GroupEncoding>::Repr::default(); n];
                        for points_compressed in points_compressed.iter_mut() {
                            reader.read_exact((*points_compressed).as_mut())?;
                        }

                        let mut points = vec![Option::<E::G1Affine>::None; n];
                        parallelize(&mut points, |points, chunks| {
                            for (i, point) in points.iter_mut().enumerate() {
                                *point = Option::from(E::G1Affine::from_bytes(
                                    &points_compressed[chunks + i],
                                ));
                            }
                        });
                        Ok(points)
                    };

                let g = load_points_from_file_parallelly(reader)?;
                let g: Vec<<E as Engine>::G1Affine> = g
                    .iter()
                    .map(|point| {
                        point.ok_or_else(|| {
                            io::Error::new(io::ErrorKind::Other, "invalid point encoding")
                        })
                    })
                    .collect::<Result<_, _>>()?;
                let g_lagrange = load_points_from_file_parallelly(reader)?;
                let g_lagrange: Vec<<E as Engine>::G1Affine> = g_lagrange
                    .iter()
                    .map(|point| {
                        point.ok_or_else(|| {
                            io::Error::new(io::ErrorKind::Other, "invalid point encoding")
                        })
                    })
                    .collect::<Result<_, _>>()?;
                (g, g_lagrange)
            }
            SerdeFormat::RawBytes => {
                let g = (0..n)
                    .map(|_| <E::G1Affine as SerdeCurveAffine>::read(reader, format))
                    .collect::<Result<Vec<_>, _>>()?;
                let g_lagrange = (0..n)
                    .map(|_| <E::G1Affine as SerdeCurveAffine>::read(reader, format))
                    .collect::<Result<Vec<_>, _>>()?;
                (g, g_lagrange)
            }
            SerdeFormat::RawBytesUnchecked => {
                // avoid try branching for performance
                let g = (0..n)
                    .map(|_| <E::G1Affine as SerdeCurveAffine>::read(reader, format).unwrap())
                    .collect::<Vec<_>>();
                let g_lagrange = (0..n)
                    .map(|_| <E::G1Affine as SerdeCurveAffine>::read(reader, format).unwrap())
                    .collect::<Vec<_>>();
                (g, g_lagrange)
            }
        };

        let g2 = E::G2Affine::read(reader, format)?;
        let s_g2 = E::G2Affine::read(reader, format)?;

        Ok(Self {
            k,
            n: n as u64,
            g,
            g_lagrange,
            g2,
            s_g2,
        })
    }
}

impl<E: Engine + Debug> ParamsVerifierKZG<E>
where
    E::Scalar: PrimeField,
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    /// Reduce the size of the verifier parameters by eliminating elements of `g_lagrange`.
    /// The resulting parameters are only able to compute commitments up to the inputed `size`.
    /// As a result, this will be the maximum size of PI supported.
    pub fn trim(mut self, size: usize) -> Self {
        assert!(size as u64 <= self.n);
        self.trimed_size = size as u32;
        self.g_lagrange.truncate(size);
        self
    }

    /// Writes verifier parameters to buffer.
    pub fn write_custom<W: io::Write>(&self, writer: &mut W, format: SerdeFormat) -> io::Result<()>
    where
        E::G2Affine: SerdeCurveAffine,
    {
        writer.write_all(&self.k.to_le_bytes())?;
        writer.write_all(&self.trimed_size.to_le_bytes())?;
        for el in self.g_lagrange.iter() {
            el.write(writer, format)?;
        }
        self.s_g2.write(writer, format)?;
        Ok(())
    }

    /// Reads verifier parameters from a buffer.
    pub fn read_custom<R: io::Read>(reader: &mut R, format: SerdeFormat) -> io::Result<Self>
    where
        E::G2Affine: SerdeCurveAffine,
    {
        let mut k = [0u8; 4];
        reader.read_exact(&mut k[..])?;
        let k = u32::from_le_bytes(k);
        let n = 1 << k;
        // This is a generous bound on the size of the domain.
        debug_assert!(k < 32);

        let mut trimed_size = [0u8; 4];
        reader.read_exact(&mut trimed_size[..])?;
        let trimed_size = u32::from_le_bytes(trimed_size);

        let g_lagrange = match format {
            SerdeFormat::Processed => {
                use group::GroupEncoding;
                let load_points_from_file_parallelly =
                    |reader: &mut R| -> io::Result<Vec<Option<E::G1Affine>>> {
                        let mut points_compressed = vec![
                                <<E as Engine>::G1Affine as GroupEncoding>::Repr::default();
                                trimed_size as usize
                            ];
                        for points_compressed in points_compressed.iter_mut() {
                            reader.read_exact((*points_compressed).as_mut())?;
                        }

                        let mut points = vec![Option::<E::G1Affine>::None; trimed_size as usize];
                        parallelize(&mut points, |points, chunks| {
                            for (i, point) in points.iter_mut().enumerate() {
                                *point = Option::from(E::G1Affine::from_bytes(
                                    &points_compressed[chunks + i],
                                ));
                            }
                        });
                        Ok(points)
                    };

                let g_lagrange = load_points_from_file_parallelly(reader)?;
                g_lagrange
                    .iter()
                    .map(|point| {
                        point.ok_or_else(|| {
                            io::Error::new(io::ErrorKind::Other, "invalid point encoding")
                        })
                    })
                    .collect::<Result<_, _>>()?
            }
            SerdeFormat::RawBytes => (0..trimed_size)
                .map(|_| <E::G1Affine as SerdeCurveAffine>::read(reader, format))
                .collect::<Result<Vec<_>, _>>()?,
            SerdeFormat::RawBytesUnchecked => (0..trimed_size)
                .map(|_| <E::G1Affine as SerdeCurveAffine>::read(reader, format).unwrap())
                .collect::<Vec<_>>(),
        };
        let s_g2 = E::G2Affine::read(reader, format)?;

        Ok(Self {
            k,
            n,
            trimed_size,
            g_lagrange,
            s_g2,
        })
    }
}

impl<E: Engine + Debug> From<ParamsKZG<E>> for ParamsVerifierKZG<E> {
    fn from(value: ParamsKZG<E>) -> Self {
        Self {
            k: value.k,
            n: value.n,
            trimed_size: value.n as u32,
            g_lagrange: value.g_lagrange.clone(),
            s_g2: value.s_g2,
        }
    }
}

impl<E: Engine + Debug> From<&ParamsKZG<E>> for ParamsVerifierKZG<E> {
    fn from(value: &ParamsKZG<E>) -> Self {
        Self {
            k: value.k,
            n: value.n,
            trimed_size: value.n as u32,
            g_lagrange: value.g_lagrange.clone(),
            s_g2: value.s_g2,
        }
    }
}

impl<'params, E: Engine + Debug> Params<'params, E::G1Affine> for ParamsKZG<E>
where
    E::Scalar: PrimeField,
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    type MSM = MSMKZG<E>;

    fn k(&self) -> u32 {
        self.k
    }

    fn n(&self) -> u64 {
        self.n
    }

    fn downsize(&mut self, k: u32) {
        assert!(k <= self.k);

        self.k = k;
        self.n = 1 << k;

        self.g.truncate(self.n as usize);
        self.g_lagrange = g_to_lagrange(self.g.iter().map(|g| g.to_curve()).collect(), k);
    }

    fn empty_msm(&'params self) -> MSMKZG<E> {
        MSMKZG::new()
    }

    fn commit_lagrange(
        &self,
        poly: &Polynomial<E::Scalar, LagrangeCoeff>,
        _: Blind<E::Scalar>,
    ) -> E::G1 {
        let mut scalars = Vec::with_capacity(poly.len());
        scalars.extend(poly.iter());
        let bases = &self.g_lagrange;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size])
    }

    /// Writes params to a buffer.
    fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.write_custom(writer, SerdeFormat::RawBytes)
    }

    /// Reads params from a buffer.
    fn read<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        Self::read_custom(reader, SerdeFormat::RawBytes)
    }
}

impl<'params, E: Engine + Debug> Params<'params, E::G1Affine> for ParamsVerifierKZG<E>
where
    E::Scalar: PrimeField,
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    type MSM = MSMKZG<E>;

    fn k(&self) -> u32 {
        self.k
    }

    fn n(&self) -> u64 {
        self.n
    }

    fn downsize(&mut self, _k: u32) {
        // Verifier parameters cannot be downsized since they do not contain the original powers of g.
        panic!("Verifier parameters cannot be downsized. You may want to use `trim` instead.")
    }

    fn empty_msm(&'params self) -> MSMKZG<E> {
        MSMKZG::new()
    }

    fn commit_lagrange(
        &self,
        poly: &Polynomial<E::Scalar, LagrangeCoeff>,
        _: Blind<E::Scalar>,
    ) -> E::G1 {
        let mut scalars = Vec::with_capacity(poly.len());
        scalars.extend(poly.iter());
        let bases = &self.g_lagrange;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size])
    }

    /// Writes params to a buffer.
    fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
        self.write_custom(writer, SerdeFormat::RawBytes)
    }

    /// Reads params from a buffer.
    fn read<R: io::Read>(reader: &mut R) -> io::Result<Self> {
        Self::read_custom(reader, SerdeFormat::RawBytes)
    }
}

impl<'params, E: Engine + Debug> ParamsVerifier<'params, E::G1Affine> for ParamsVerifierKZG<E>
where
    E::Scalar: PrimeField,
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    fn trimed_size(&self) -> u64 {
        self.trimed_size as u64
    }
}

impl<'params, E: Engine + Debug> ParamsProver<'params, E::G1Affine> for ParamsKZG<E>
where
    E::Scalar: PrimeField,
    E::G1Affine: SerdeCurveAffine,
    E::G2Affine: SerdeCurveAffine,
{
    type ParamsVerifier = ParamsVerifierKZG<E>;

    fn into_verifier_params(self) -> Self::ParamsVerifier {
        self.into()
    }

    fn new(k: u32) -> Self {
        Self::setup(k, OsRng)
    }

    fn commit(&self, poly: &Polynomial<E::Scalar, Coeff>, _: Blind<E::Scalar>) -> E::G1 {
        let mut scalars = Vec::with_capacity(poly.len());
        scalars.extend(poly.iter());
        let bases = &self.g;
        let size = scalars.len();
        assert!(bases.len() >= size);
        best_multiexp(&scalars, &bases[0..size])
    }
}

#[cfg(test)]
mod test {
    use crate::poly::commitment::ParamsProver;
    use crate::poly::commitment::{Blind, Params};
    use crate::poly::kzg::commitment::ParamsKZG;
    use ff::Field;

    #[test]
    fn test_commit_lagrange() {
        const K: u32 = 6;

        use rand_core::OsRng;

        use crate::poly::EvaluationDomain;
        use halo2curves::bn256::{Bn256, Fr};

        let params = ParamsKZG::<Bn256>::new(K);
        let domain = EvaluationDomain::new(1, K);

        let mut a = domain.empty_lagrange();

        for (i, a) in a.iter_mut().enumerate() {
            *a = Fr::from(i as u64);
        }

        let b = domain.lagrange_to_coeff(a.clone());

        let alpha = Blind(Fr::random(OsRng));

        assert_eq!(params.commit(&b, alpha), params.commit_lagrange(&a, alpha));
    }

    #[test]
    fn test_parameter_serialisation_roundtrip() {
        const K: u32 = 4;

        use super::super::commitment::Params;
        use crate::halo2curves::bn256::Bn256;

        let params0 = ParamsKZG::<Bn256>::new(K);
        let mut data = vec![];
        <ParamsKZG<_> as Params<_>>::write(&params0, &mut data).unwrap();
        let params1: ParamsKZG<Bn256> = Params::read::<_>(&mut &data[..]).unwrap();

        assert_eq!(params0.k, params1.k);
        assert_eq!(params0.n, params1.n);
        assert_eq!(params0.g.len(), params1.g.len());
        assert_eq!(params0.g_lagrange.len(), params1.g_lagrange.len());

        assert_eq!(params0.g, params1.g);
        assert_eq!(params0.g_lagrange, params1.g_lagrange);
        assert_eq!(params0.g2, params1.g2);
        assert_eq!(params0.s_g2, params1.s_g2);
    }
}
