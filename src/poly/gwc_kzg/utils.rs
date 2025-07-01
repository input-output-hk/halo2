use crate::poly::query::Query;
use ff::Field;
use std::fmt::Debug;
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub(super) struct CommitmentData<F: Field, Q: Query<F>> {
    pub(super) queries: Vec<Q>,
    pub(super) point: F,
    _marker: PhantomData<F>,
}

pub fn construct_intermediate_sets<F: Field, I, Q: Query<F>>(queries: I) -> Vec<CommitmentData<F, Q>>
where
    I: IntoIterator<Item = Q> + Clone,
{
    let mut point_query_map: Vec<(F, Vec<Q>)> = Vec::new();
    for query in queries {
        if let Some(pos) = point_query_map
            .iter()
            .position(|(point, _)| *point == query.get_point())
        {
            let (_, queries) = &mut point_query_map[pos];
            queries.push(query);
        } else {
            point_query_map.push((query.get_point(), vec![query]));
        }
    }

    point_query_map
        .into_iter()
        .map(|(point, queries)| CommitmentData {
            queries,
            point,
            _marker: PhantomData,
        })
        .collect()
}