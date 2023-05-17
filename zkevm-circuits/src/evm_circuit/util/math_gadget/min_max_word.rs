use std::marker::PhantomData;

use crate::{
    evm_circuit::util::{constraint_builder::EVMConstraintBuilder, math_gadget::*, CachedRegion},
    util::word::{Word, WordExpr},
};
use eth_types::Field;
use halo2_proofs::plonk::{Error, Expression};
/// Returns `rhs` when `lhs < rhs`, and returns `lhs` otherwise.
/// lhs and rhs `< 256**N_BYTES`
/// `N_BYTES` is required to be `<= MAX_N_BYTES_INTEGER`.
#[derive(Clone, Debug)]
pub struct MinMaxWordGadget<F, T> {
    lt: LtWordGadget<F, T, T>,
    min: Word<Expression<F>>,
    max: Word<Expression<F>>,
    _marker: PhantomData<T>,
}

impl<F: Field, T: WordExpr<F> + Clone> MinMaxWordGadget<F, T> {
    pub(crate) fn construct(cb: &mut EVMConstraintBuilder<F>, lhs: T, rhs: T) -> Self {
        let lt = LtWordGadget::construct(cb, lhs.clone(), rhs.clone());
        let max = Word::select(lt.expr(), rhs.clone(), lhs.clone());
        let min = Word::select(lt.expr(), lhs, rhs);

        Self {
            lt,
            min,
            max,
            _marker: Default::default(),
        }
    }

    pub(crate) fn min(&self) -> Word<Expression<F>> {
        self.min.clone()
    }

    pub(crate) fn max(&self) -> Word<Expression<F>> {
        self.max.clone()
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        lhs: eth_types::Word,
        rhs: eth_types::Word,
    ) -> Result<(), Error> {
        self.lt.assign(region, offset, lhs, rhs)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{test_util::*, *};
    use crate::evm_circuit::util::{constraint_builder::ConstrainBuilderCommon, Cell};
    use eth_types::{ToScalar, Word};
    use halo2_proofs::{halo2curves::bn256::Fr, plonk::Error};

    #[derive(Clone)]
    /// MinMaxTestContainer: require(min(a, b) == (a if MIN_IS_A else b))
    struct MinMaxTestContainer<F, const N_BYTES: usize, const MIN_IS_A: bool> {
        minmax_gadget: MinMaxGadget<F, N_BYTES>,
        a: Cell<F>,
        b: Cell<F>,
    }

    impl<F: Field, const N_BYTES: usize, const MIN_IS_A: bool> MathGadgetContainer<F>
        for MinMaxTestContainer<F, N_BYTES, MIN_IS_A>
    {
        fn configure_gadget_container(cb: &mut EVMConstraintBuilder<F>) -> Self {
            let a = cb.query_cell();
            let b = cb.query_cell();
            let minmax_gadget = MinMaxGadget::<F, N_BYTES>::construct(cb, a.expr(), b.expr());

            if MIN_IS_A {
                cb.require_equal("min == a", minmax_gadget.min(), a.expr());
                cb.require_equal("max == b", minmax_gadget.max(), b.expr());
            } else {
                cb.require_equal("min == b", minmax_gadget.min(), b.expr());
                cb.require_equal("max == a", minmax_gadget.max(), a.expr());
            }

            MinMaxTestContainer {
                minmax_gadget,
                a,
                b,
            }
        }

        fn assign_gadget_container(
            &self,
            witnesses: &[Word],
            region: &mut CachedRegion<'_, '_, F>,
        ) -> Result<(), Error> {
            let a = witnesses[0].to_scalar().unwrap();
            let b = witnesses[1].to_scalar().unwrap();
            let offset = 0;

            self.a.assign(region, offset, Value::known(a))?;
            self.b.assign(region, offset, Value::known(b))?;
            self.minmax_gadget.assign(region, offset, a, b)?;

            Ok(())
        }
    }

    #[test]
    fn test_minmax_eq() {
        // a == b
        try_test!(
            MinMaxTestContainer<Fr, 4, true>,
            vec![Word::from(0), Word::from(0)],
            true,
        );
        try_test!(
            MinMaxTestContainer<Fr, 4, true>,
            vec![Word::from(5), Word::from(5)],
            true,
        );
        try_test!(
            MinMaxTestContainer<Fr, 16, true>,
            vec![WORD_LOW_MAX, WORD_LOW_MAX],
            true,
        );
    }

    #[test]
    fn test_minmax_expect_min_a() {
        // min == a, max == b
        try_test!(
            MinMaxTestContainer<Fr, 1, true>,
            vec![Word::from(0), Word::from(1)],
            true,
        );
        try_test!(
            MinMaxTestContainer<Fr, 1, true>,
            vec![Word::from(3), Word::from(5)],
            true,
        );
        try_test!(
            MinMaxTestContainer<Fr, 31, true>,
            vec![WORD_LOW_MAX, WORD_LOW_MAX],
            true,
        );
    }

    #[test]
    fn test_minmax_unexpect_min_a() {
        // min == b, max == a
        try_test!(
            MinMaxTestContainer<Fr, 1, true>,
            vec![Word::from(1), Word::from(0)],
            false,
        );
        try_test!(
            MinMaxTestContainer<Fr, 1, true>,
            vec![Word::from(256), Word::from(3)],
            false,
        );
        try_test!(
            MinMaxTestContainer<Fr, 31, true>,
            vec![WORD_LOW_MAX, Word::from(123456)],
            false,
        );
    }

    #[test]
    fn test_minmax_expect_min_b() {
        // min == a, max == b
        try_test!(
            MinMaxTestContainer<Fr, 1, false>,
            vec![Word::from(1), Word::from(0)],
            true,
        );

        try_test!(
            MinMaxTestContainer<Fr, 4, false>,
            vec![Word::from(777), Word::from(44)],
            true,
        );

        try_test!(
            MinMaxTestContainer<Fr, 17, false>,
            vec![WORD_LOW_MAX+1, WORD_LOW_MAX],
            true,
        );
    }
}
