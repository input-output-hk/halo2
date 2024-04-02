#[macro_use]
extern crate criterion;

use crate::arithmetic::{parallelize, small_multiexp, CurveAffine, CurveExt};
use crate::halo2curves::pasta::{EqAffine, Fp};
use group::cofactor::CofactorCurveAffine;
use group::ff::Field;
use group::{Curve, Group};
use halo2_proofs::*;

use criterion::{black_box, Criterion};
use rand_core::OsRng;

fn criterion_benchmark(c: &mut Criterion) {
    let rng = OsRng;

    // small multiexp
    {
        let k = 5u32;
        let n: u64 = 1 << k;
        let id = <EqAffine as CofactorCurveAffine>::Curve::identity();

        let g_projective = {
            let mut g = Vec::with_capacity(n as usize);
            g.resize(n as usize, id);

            parallelize(&mut g, move |g, start| {
                let hasher = <EqAffine as CurveAffine>::CurveExt::hash_to_curve("Halo2-Parameters");

                for (i, g) in g.iter_mut().enumerate() {
                    let i = (i + start) as u32;

                    let mut message = [0u8; 5];
                    message[1..5].copy_from_slice(&i.to_le_bytes());

                    *g = hasher(&message);
                }
            });

            g
        };

        let mut g = {
            let mut g: Vec<EqAffine> = vec![id.into(); n as usize];
            parallelize(&mut g, |g, starts| {
                <EqAffine as CofactorCurveAffine>::Curve::batch_normalize(
                    &g_projective[starts..(starts + g.len())],
                    g,
                );
            });
            g
        };
        let len = g.len() / 2;
        let (g_lo, g_hi) = g.split_at_mut(len);

        let coeff_1 = Fp::random(rng);
        let coeff_2 = Fp::random(rng);

        c.bench_function("double-and-add", |b| {
            b.iter(|| {
                for (g_lo, g_hi) in g_lo.iter().zip(g_hi.iter()) {
                    small_multiexp(&[black_box(coeff_1), black_box(coeff_2)], &[*g_lo, *g_hi]);
                }
            })
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
