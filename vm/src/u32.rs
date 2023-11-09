use std::{marker::PhantomData, vec};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};

/// A lookup table of values up to RANGE
/// e.g. RANGE = 256, values = [0..255]
/// This table is tagged by an index `k`, where `k` is the number of bits of the element in the `value` column.
#[derive(Debug, Clone)]
pub(super) struct RangeTableConfig<F: FieldExt, const NUM_BITS: usize, const RANGE: usize> {
    pub(super) value: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const NUM_BITS: usize, const RANGE: usize> RangeTableConfig<F, NUM_BITS, RANGE> {
    pub(super) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        assert_eq!(1 << NUM_BITS, RANGE);

        let value = meta.lookup_table_column();

        Self {
            value,
            _marker: PhantomData,
        }
    }

    pub(super) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "load range-check table",
            |mut table| {
                let mut offset = 0;

                for value in 0..RANGE {
                    table.assign_cell(
                        || "assign value",
                        self.value,
                        offset,
                        || Value::known(F::from(value as u64)),
                    )?;
                    offset += 1;
                }

                Ok(())
            },
        )
    }
}

#[derive(Debug, Clone)]
/// A range-constrained value in the circuit produced by the RangeCheckConfig.
pub(crate) struct U32Constrained<F: FieldExt> {
    assigned_value: AssignedCell<Assigned<F>, F>,
    assigned_limbs: Vec<AssignedCell<Assigned<F>, F>>,
}

#[derive(Debug, Clone)]
pub(crate) struct U32CheckConfig<F: FieldExt, const NUM_LIMBS: usize> {
    q_lookup: Selector,
    value: Column<Advice>,
    limbs: Vec<Column<Advice>>,
    tables: Vec<RangeTableConfig<F, 8, 256>>,
}

impl<F: FieldExt, const NUM_LIMBS: usize> U32CheckConfig<F, NUM_LIMBS> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_lookup: Selector,
        value: Column<Advice>,
        limbs: Vec<Column<Advice>>,
    ) -> Self {
        // let q_lookup: Selector = meta.complex_selector();
        let tables: Vec<RangeTableConfig<F, 8, 256>> = (0..limbs.len())
            .into_iter()
            .map(|_| RangeTableConfig::configure(meta))
            .collect();

        for (limb, table) in limbs.iter().zip(tables.iter()) {
            meta.lookup("", |meta| {
                let q_lookup = meta.query_selector(q_lookup);
                let limb = meta.query_advice(*limb, Rotation::cur());

                vec![(q_lookup * limb, table.value)]
            });
        }

        meta.create_gate("value", |meta| {
            let q_lookup = meta.query_selector(q_lookup);
            let value = meta.query_advice(value, Rotation::cur());
            let limbs: Vec<Expression<F>> = limbs
                .iter()
                .map(|x| meta.query_advice(*x, Rotation::cur()))
                .collect();
            let rhs = limbs
                .iter()
                .enumerate()
                .fold(Expression::Constant(F::zero()), |x, (i, y)| {
                    x + (*y).clone() * F::from_u128((256 as u128).pow(i as u32))
                });
            vec![q_lookup * (rhs - value)]
        });

        Self {
            q_lookup,
            value,
            limbs,
            tables,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
        limbs: Vec<Value<Assigned<F>>>,
    ) -> Result<U32Constrained<F>, Error> {
        layouter.assign_region(
            || "Assign value",
            |mut region| self.assign_region(&mut region, value, limbs.clone()),
        )
    }

    pub fn assign_region_x(
        &self,
        region: &mut Region<'_, F>,
        value: Value<Assigned<F>>,
        limbs: Vec<Value<Assigned<F>>>,
        offset: usize,
    ) -> Result<U32Constrained<F>, Error> {
        // Enable q_lookup
        self.q_lookup.enable(region, offset)?;

        // Assign value
        let assigned_value = region.assign_advice(|| "value", self.value, offset, || value)?;

        let mut assigned_limbs: Vec<AssignedCell<Assigned<F>, F>> = vec![];
        for i in 0..limbs.len() {
            let assigend_limb =
                region.assign_advice(|| "value", self.limbs[i], offset, || limbs[i])?;
            assigned_limbs.push(assigend_limb);
        }

        Ok(U32Constrained {
            assigned_value,
            assigned_limbs,
        })
    }

    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        value: Value<Assigned<F>>,
        limbs: Vec<Value<Assigned<F>>>,
    ) -> Result<U32Constrained<F>, Error> {
        self.assign_region_x(region, value, limbs, 0)
    }

    pub fn load_tables(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        for table in self.tables.iter() {
            table.load(layouter)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::floor_planner::V1,
        dev::{FailureLocation, MockProver, VerifyFailure},
        halo2curves::bn256::Fr as Fp,
        plonk::{Any, Circuit},
    };

    use super::*;

    #[derive(Default)]
    struct MyCircuit<F: FieldExt, const NUM_LIMBS: usize> {
        value: Value<Assigned<F>>,
        limbs: Vec<Value<Assigned<F>>>,
    }

    impl<F: FieldExt, const NUM_LIMBS: usize> Circuit<F> for MyCircuit<F, NUM_LIMBS> {
        type Config = U32CheckConfig<F, NUM_LIMBS>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let q_lookup = meta.complex_selector();
            let value = meta.advice_column();
            let limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
            U32CheckConfig::configure(meta, q_lookup, value, limbs)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.load_tables(&mut layouter)?;

            config.assign(
                layouter.namespace(|| "Assign value"),
                self.value,
                self.limbs.clone(),
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_u8() {
        let k = 9;

        // Successful cases
        {
            let circuit = MyCircuit::<Fp, 1> {
                value: Value::known(Fp::from(222 as u64).into()),
                limbs: vec![Value::known(Fp::from(222 as u64).into())],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            let circuit = MyCircuit::<Fp, 1> {
                value: Value::known(Fp::from(0 as u64).into()),
                limbs: vec![Value::known(Fp::from(0 as u64).into())],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            let circuit = MyCircuit::<Fp, 1> {
                value: Value::known(Fp::from(255 as u64).into()),
                limbs: vec![Value::known(Fp::from(255 as u64).into())],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        // Failure cases
        {
            let circuit = MyCircuit::<Fp, 1> {
                value: Value::known(Fp::from(256 as u64).into()),
                limbs: vec![Value::known(Fp::from(256 as u64).into())],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err());
        }

        {
            let circuit = MyCircuit::<Fp, 1> {
                value: Value::known(Fp::from(123 as u64).into()),
                limbs: vec![Value::known(Fp::from(122 as u64).into())],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err())
        }
    }

    #[test]
    fn test_u16() {
        let k = 9;

        {
            let circuit = MyCircuit::<Fp, 2> {
                value: Value::known(Fp::from(222 as u64).into()),
                limbs: vec![
                    Value::known(Fp::from(222 as u64).into()),
                    Value::known(Fp::from(0 as u64).into()),
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            let circuit = MyCircuit::<Fp, 2> {
                value: Value::known(Fp::from(42134 as u64).into()),
                limbs: vec![
                    Value::known(Fp::from(150 as u64).into()),
                    Value::known(Fp::from(164 as u64).into()),
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            let circuit = MyCircuit::<Fp, 2> {
                value: Value::known(Fp::from(256 as u64).into()),
                limbs: vec![
                    Value::known(Fp::from(0 as u64).into()),
                    Value::known(Fp::from(1 as u64).into()),
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        // Failure cases
        {
            let circuit = MyCircuit::<Fp, 2> {
                value: Value::known(Fp::from(256 as u64).into()),
                limbs: vec![
                    Value::known(Fp::from(256 as u64).into()),
                    Value::known(Fp::from(0 as u64).into()),
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err())
        }

        {
            let circuit = MyCircuit::<Fp, 2> {
                value: Value::known(Fp::from(256 as u64).into()),
                limbs: vec![
                    Value::known(Fp::from(1 as u64).into()),
                    Value::known(Fp::from(1 as u64).into()),
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err())
        }
    }

    #[test]
    fn test_u32() {
        let k = 9;

        {
            let circuit = MyCircuit::<Fp, 4> {
                value: Value::known(Fp::from(222 as u64).into()),
                limbs: vec![
                    Value::known(Fp::from(222 as u64).into()),
                    Value::known(Fp::from(0 as u64).into()),
                    Value::known(Fp::from(0 as u64).into()),
                    Value::known(Fp::from(0 as u64).into()),
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            let circuit = MyCircuit::<Fp, 4> {
                value: Value::known(Fp::from(1493953875 as u64).into()),
                limbs: vec![
                    Value::known(Fp::from(83 as u64).into()),
                    Value::known(Fp::from(237 as u64).into()),
                    Value::known(Fp::from(11 as u64).into()),
                    Value::known(Fp::from(89 as u64).into()),
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }
    }
}
