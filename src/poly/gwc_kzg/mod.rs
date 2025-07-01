//! An implementation of the multi-open technique described in GWC19 (https://eprint.iacr.org/2019/953.pdf).
//! See section `3 A batched version of the [KZG10] scheme` in GWC19
//! The implementation is ported from `https://github.com/input-output-hk/halo2/tree/main`

use halo2curves::pairing::Engine;
use std::marker::PhantomData;

/// Multiscalar multiplication engines
/// KZG commitment scheme
mod utils;

use std::fmt::Debug;

use crate::poly::kzg::msm::{DualMSM, MSMKZG};
use crate::poly::kzg::params::{ParamsKZG, ParamsVerifierKZG};
use crate::poly::query::{Query, VerifierQuery};
use crate::poly::{Coeff, Error, LagrangeCoeff, Polynomial, ProverQuery};
use crate::utils::arithmetic::{
    kate_division
    , powers, CurveExt, MSM,
};

use crate::poly::commitment::{Guard, PolynomialCommitmentScheme};
use crate::poly::gwc_kzg::utils::construct_intermediate_sets;
use crate::transcript::{Hashable, Sampleable, Transcript};
use crate::utils::helpers::ProcessedSerdeObject;
use ff::Field;
use group::prime::PrimeCurveAffine;
use group::{Curve, Group};
use halo2curves::msm::msm_best;
use halo2curves::pairing::MultiMillerLoop;
use halo2curves::CurveAffine;
use rand_core::OsRng;

#[derive(Clone, Debug)]
/// KZG verifier
pub struct GwcKZGCommitmentScheme<E: Engine> {
    _marker: PhantomData<E>,
}

impl<E: MultiMillerLoop> Guard<E::Fr, GwcKZGCommitmentScheme<E>> for DualMSM<E, GwcKZGCommitmentScheme<E>>
where
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    fn verify(
        self,
        params: &<crate::poly::kzg::KZGCommitmentScheme<E> as PolynomialCommitmentScheme<E::Fr>>::VerifierParameters,
    ) -> Result<(), Error> {
        self.check(params).then_some(()).ok_or(Error::OpeningError)
    }
}

impl<E: MultiMillerLoop> PolynomialCommitmentScheme<E::Fr> for GwcKZGCommitmentScheme<E>
where
    E::G1: Default + CurveExt<ScalarExt = E::Fr> + ProcessedSerdeObject,
    E::G1Affine: Default + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
{
    type Parameters = ParamsKZG<E>;
    type VerifierParameters = ParamsVerifierKZG<E>;
    type Commitment = E::G1;
    type VerificationGuard = DualMSM<E, GwcKZGCommitmentScheme<E>>;

    fn gen_params(k: u32) -> Self::Parameters {
        ParamsKZG::unsafe_setup(k, OsRng)
    }

    fn get_verifier_params(params: &Self::Parameters) -> Self::VerifierParameters {
        params.verifier_params()
    }

    fn commit(
        params: &Self::Parameters,
        polynomial: &Polynomial<E::Fr, Coeff>,
    ) -> Self::Commitment {
        let mut scalars = Vec::with_capacity(polynomial.len());
        scalars.extend(polynomial.iter());
        let mut bases = vec![<E::G1 as Curve>::AffineRepr::identity(); params.g.len()];
        <E::G1 as Curve>::batch_normalize(&params.g, bases.as_mut_slice());
        let size = scalars.len();
        assert!(bases.len() >= size);
        msm_best(&scalars, &bases[0..size])
    }

    fn commit_lagrange(
        params: &Self::Parameters,
        poly: &Polynomial<E::Fr, LagrangeCoeff>,
    ) -> E::G1 {
        let mut scalars = Vec::with_capacity(poly.len());
        scalars.extend(poly.iter());
        let size = scalars.len();

        let mut bases = vec![<E::G1 as Curve>::AffineRepr::identity(); params.g.len()];
        <E::G1 as Curve>::batch_normalize(&params.g_lagrange, bases.as_mut_slice());
        assert!(bases.len() >= size);

        msm_best(&scalars, &bases[0..size])
    }

    fn multi_open<'com, T: Transcript>(
        params: &Self::Parameters,
        prover_query: impl IntoIterator<Item = ProverQuery<'com, E::Fr>> + Clone,
        transcript: &mut T,
    ) -> Result<(), Error>
    where
        E::Fr: Sampleable<T::Hash> + Ord + Hashable<T::Hash>,
        E::G1: Hashable<T::Hash>,
    {
        let v: E::Fr = transcript.squeeze_challenge();
        let commitment_data = construct_intermediate_sets(prover_query);

        for commitment_at_a_point in commitment_data.iter() {
            let z = commitment_at_a_point.point;
            let (poly_batch, eval_batch) = commitment_at_a_point
                .queries
                .iter()
                .zip(powers(v))
                .map(|(query, power_of_v)| {
                    assert_eq!(query.get_point(), z);

                    let poly = query.get_commitment().poly;
                    let eval = query.get_eval();

                    (poly.clone() * power_of_v, eval * power_of_v)
                })
                .reduce(|(poly_acc, eval_acc), (poly, eval)| (poly_acc + &poly, eval_acc + eval))
                .unwrap();

            let poly_batch = &poly_batch - eval_batch;
            let witness_poly = Polynomial {
                values: kate_division(&poly_batch.values, z),
                _marker: PhantomData,
            };

            let w = Self::commit(params, &witness_poly);
            transcript.write(&w).map_err(|_| Error::OpeningError)?;
        }

        Ok(())
    }

    fn multi_prepare<'com, T: Transcript>(
        verifier_query: impl IntoIterator<Item = VerifierQuery<'com, E::Fr, GwcKZGCommitmentScheme<E>>>
            + Clone,
        transcript: &mut T,
    ) -> Result<DualMSM<E, GwcKZGCommitmentScheme<E>>, Error>
    where
        E::Fr: Sampleable<T::Hash> + Ord + Hashable<T::Hash>,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr>,
    {
        let v: E::Fr = transcript.squeeze_challenge();
        let commitment_data = construct_intermediate_sets(verifier_query);

        let w: Vec<E::G1> = (0..commitment_data.len())
            .map(|_| transcript.read().map_err(|_| Error::SamplingError))
            .collect::<Result<Vec<E::G1>, Error>>()?;

        let u: E::Fr = transcript.squeeze_challenge();

        let mut commitment_multi = MSMKZG::<E>::new();
        let mut eval_multi = E::Fr::ZERO;

        let mut witness = MSMKZG::<E>::new();
        let mut witness_with_aux = MSMKZG::<E>::new();

        for ((commitment_at_a_point, wi), power_of_u) in
            commitment_data.iter().zip(w.into_iter()).zip(powers(u))
        {
            assert!(!commitment_at_a_point.queries.is_empty());
            let z = commitment_at_a_point.point;

            let (mut commitment_batch, eval_batch) = commitment_at_a_point
                .queries
                .iter()
                .zip(powers(v))
                .map(|(query, power_of_v)| {
                    assert_eq!(query.get_point(), z);

                    let commitment = query.get_commitment();
                    let mut msm = MSMKZG::<E>::new();
                    msm.append_term(power_of_v, *commitment);

                    let eval = power_of_v * query.get_eval();

                    (msm, eval)
                })
                .reduce(|(mut commitment_acc, eval_acc), (commitment, eval)| {
                    commitment_acc.add_msm(&commitment);
                    (commitment_acc, eval_acc + eval)
                })
                .unwrap();

            commitment_batch.scale(power_of_u);
            commitment_multi.add_msm(&commitment_batch);
            eval_multi += power_of_u * eval_batch;

            witness_with_aux.append_term(power_of_u * z, wi);
            witness.append_term(power_of_u, wi);
        }

        let mut msm_accumulator = DualMSM::new();
        msm_accumulator.left.add_msm(&witness);

        msm_accumulator.right.add_msm(&witness_with_aux);
        msm_accumulator.right.add_msm(&commitment_multi);
        let g0: E::G1 = E::G1::generator();
        msm_accumulator.right.append_term(eval_multi, -g0);

        transcript.assert_empty().map_err(|_| Error::OpeningError)?;
        Ok(msm_accumulator)
    }
}

#[cfg(test)]
mod tests {
    use crate::poly::commitment::{Guard, PolynomialCommitmentScheme};
    use crate::poly::gwc_kzg::GwcKZGCommitmentScheme;
    use crate::poly::kzg::params::{ParamsKZG, ParamsVerifierKZG};
    use crate::poly::{
        query::{ProverQuery, VerifierQuery},
        EvaluationDomain,
    };
    use crate::transcript::{CircuitTranscript, Hashable, Sampleable, Transcript};
    use crate::utils::arithmetic::eval_polynomial;
    use blake2b_simd::State as Blake2bState;
    use ff::WithSmallOrderMulGroup;
    use halo2curves::pairing::{Engine, MultiMillerLoop};
    use halo2curves::serde::SerdeObject;
    use halo2curves::{CurveAffine, CurveExt};
    use rand_core::OsRng;

    #[test]
    fn test_roundtrip_gwc() {
        use halo2curves::bn256::Bn256;

        const K: u32 = 4;

        let params: ParamsKZG<Bn256> = ParamsKZG::unsafe_setup(K, OsRng);

        let proof = create_proof::<_, CircuitTranscript<Blake2bState>>(&params);

        let verifier_params = params.verifier_params();
        verify::<Bn256, CircuitTranscript<Blake2bState>>(&verifier_params, &proof[..], false);

        verify::<Bn256, CircuitTranscript<Blake2bState>>(&verifier_params, &proof[..], true);
    }

    fn verify<E, T>(verifier_params: &ParamsVerifierKZG<E>, proof: &[u8], should_fail: bool)
    where
        E: MultiMillerLoop,
        T: Transcript,
        E::Fr: Hashable<T::Hash> + Sampleable<T::Hash> + Ord,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
        E::G1Affine: CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1> + SerdeObject,
    {
        let mut transcript = T::init_from_bytes(proof);

        let a: E::G1 = transcript.read().unwrap();
        let b: E::G1 = transcript.read().unwrap();
        let c: E::G1 = transcript.read().unwrap();

        let x: E::Fr = transcript.squeeze_challenge();
        let y: E::Fr = transcript.squeeze_challenge();

        let avx: E::Fr = transcript.read().unwrap();
        let bvx: E::Fr = transcript.read().unwrap();
        let cvy: E::Fr = transcript.read().unwrap();

        let valid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::<<E as Engine>::Fr, GwcKZGCommitmentScheme<E>>::new(x, &a, avx)))
            .chain(Some(VerifierQuery::new(x, &b, bvx)))
            .chain(Some(VerifierQuery::new(y, &c, cvy)));

        let invalid_queries = std::iter::empty()
            .chain(Some(VerifierQuery::new(x, &a, avx)))
            .chain(Some(VerifierQuery::new(x, &b, avx)))
            .chain(Some(VerifierQuery::new(y, &c, cvy)));

        let queries = if should_fail {
            invalid_queries
        } else {
            valid_queries
        };

        let result = GwcKZGCommitmentScheme::multi_prepare(queries, &mut transcript).unwrap();

        if should_fail {
            assert!(result.verify(verifier_params).is_err());
        } else {
            assert!(result.verify(verifier_params).is_ok());
        }
    }

    fn create_proof<E, T>(kzg_params: &ParamsKZG<E>) -> Vec<u8>
    where
        E: MultiMillerLoop,
        T: Transcript,
        E::Fr: WithSmallOrderMulGroup<3> + Hashable<T::Hash> + Sampleable<T::Hash> + Ord,
        E::G1: Hashable<T::Hash> + CurveExt<ScalarExt = E::Fr, AffineExt = E::G1Affine>,
        E::G1Affine: SerdeObject + CurveAffine<ScalarExt = E::Fr, CurveExt = E::G1>,
    {
        let k = (kzg_params.g.len() - 1).ilog2() + 1;
        let domain = EvaluationDomain::new(1, k);

        let mut ax = domain.empty_coeff();
        for (i, a) in ax.iter_mut().enumerate() {
            *a = <E::Fr>::from(10 + i as u64);
        }

        let mut bx = domain.empty_coeff();
        for (i, a) in bx.iter_mut().enumerate() {
            *a = <E::Fr>::from(100 + i as u64);
        }

        let mut cx = domain.empty_coeff();
        for (i, a) in cx.iter_mut().enumerate() {
            *a = <E::Fr>::from(100 + i as u64);
        }

        let mut transcript = T::init();

        let a = GwcKZGCommitmentScheme::commit(kzg_params, &ax);
        let b = GwcKZGCommitmentScheme::commit(kzg_params, &bx);
        let c = GwcKZGCommitmentScheme::commit(kzg_params, &cx);

        transcript.write(&a).unwrap();
        transcript.write(&b).unwrap();
        transcript.write(&c).unwrap();

        let x: E::Fr = transcript.squeeze_challenge();
        let y = transcript.squeeze_challenge();

        let avx = eval_polynomial(&ax, x);
        let bvx = eval_polynomial(&bx, x);
        let cvy = eval_polynomial(&cx, y);

        transcript.write(&avx).unwrap();
        transcript.write(&bvx).unwrap();
        transcript.write(&cvy).unwrap();

        let queries = [
            ProverQuery {
                point: x,
                poly: &ax,
            },
            ProverQuery {
                point: x,
                poly: &bx,
            },
            ProverQuery {
                point: y,
                poly: &cx,
            },
        ]
        .into_iter();

        GwcKZGCommitmentScheme::multi_open(kzg_params, queries, &mut transcript).unwrap();

        transcript.finalize()
    }
}
