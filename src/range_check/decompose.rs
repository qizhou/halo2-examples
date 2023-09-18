use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};

/// This helper checks that the value witnessed in a given cell is within a given range.
///
///        value_in value_low value_high    |    selector
///       ------------------------------
///          v         h            l          |         1
///

// #[derive(Debug, Clone)]
/// A range-constrained value in the circuit produced by the RangeCheckConfig.
// struct RangeConstrained<F: FieldExt, const RANGE: usize>(AssignedCell<Assigned<F>, F>);

#[derive(Debug, Clone)]
struct DecomposeConfig<F: FieldExt> {
    value_in: Column<Advice>,
    value_low: Column<Advice>,
    value_high: Column<Advice>,
    selector: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> DecomposeConfig<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        value_in: Column<Advice>,
        value_low: Column<Advice>,
        value_high: Column<Advice>,
    ) -> Self {
        let selector = meta.selector();

        meta.create_gate("decompose check", |meta| {
            //        value     |    q_range_check
            //       ------------------------------
            //          v       |         1

            let q = meta.query_selector(selector);
            let value_in = meta.query_advice(value_in, Rotation::cur());
            let value_low = meta.query_advice(value_low, Rotation::cur());
            let value_high = meta.query_advice(value_high, Rotation::cur());

            let range_check = |value: Expression<F>| {
                (0..2).fold(value.clone(), |expr, i| {
                    expr * (Expression::Constant(F::from(i as u64)) - value.clone())
                })
            };

            Constraints::with_selector(
                q,
                [
                    (
                        "equal check",
                        value_in - value_low.clone() - value_high.clone() * F::from(2),
                    ),
                    ("low check", range_check(value_low.clone())),
                    ("high check", range_check(value_high.clone())),
                ],
            )
        });

        Self {
            selector,
            value_in,
            value_low,
            value_high,
            _marker: PhantomData,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        value_in: Value<Assigned<F>>,
        value_low: Value<Assigned<F>>,
        value_high: Value<Assigned<F>>,
    ) -> Result<(AssignedCell<Assigned<F>, F>, AssignedCell<Assigned<F>, F>), Error> {
        layouter.assign_region(
            || "Assign value",
            |mut region| {
                let offset = 0;

                // Enable q_range_check
                self.selector.enable(&mut region, offset)?;

                // Assign value
                region.assign_advice(|| "value", self.value_in, offset, || value_in)?;

                let value_low =
                    region.assign_advice(|| "value", self.value_low, offset, || value_low)?;

                let value_high =
                    region.assign_advice(|| "value", self.value_high, offset, || value_high)?;

                Ok((value_low, value_high))
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::floor_planner::V1,
        dev::{FailureLocation, MockProver, VerifyFailure},
        pasta::Fp,
        plonk::{Any, Circuit},
    };

    use super::*;

    #[derive(Default)]
    struct MyCircuit<F: FieldExt> {
        value_in: Value<Assigned<F>>,
        value_low: Value<Assigned<F>>,
        value_high: Value<Assigned<F>>,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        type Config = DecomposeConfig<F>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value_in = meta.advice_column();
            let value_low = meta.advice_column();
            let value_high = meta.advice_column();
            DecomposeConfig::configure(meta, value_in, value_low, value_high)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let (value_low, value_high) = config.assign(
                layouter.namespace(|| "Assign value"),
                self.value_in,
                self.value_low,
                self.value_high,
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_range_check_1() {
        let k = 4;

        // Successful cases
        for i in 0..4 {
            let circuit: MyCircuit<Fp> = MyCircuit::<Fp> {
                value_in: Value::known(Fp::from(i as u64).into()),
                value_low: Value::known(Fp::from(i % 2 as u64).into()),
                value_high: Value::known(Fp::from(i / 2 as u64).into()),
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        // `low check`
        {
            let circuit = MyCircuit::<Fp> {
                value_in: Value::known(Fp::from(3 as u64).into()),
                value_low: Value::known(Fp::from(3 as u64).into()),
                value_high: Value::known(Fp::from(0 as u64).into()),
            };
            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert_eq!(
                prover.verify(),
                Err(vec![VerifyFailure::ConstraintNotSatisfied {
                    constraint: ((0, "decompose check").into(), 1, "low check").into(),
                    location: FailureLocation::InRegion {
                        region: (0, "Assign value").into(),
                        offset: 0
                    },
                    cell_values: vec![(((Any::Advice, 1).into(), 0).into(), "0x3".to_string())]
                }])
            );
        }

        // `high check`
        {
            let circuit = MyCircuit::<Fp> {
                value_in: Value::known(Fp::from(4 as u64).into()),
                value_low: Value::known(Fp::from(0 as u64).into()),
                value_high: Value::known(Fp::from(2 as u64).into()),
            };
            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert_eq!(
                prover.verify(),
                Err(vec![VerifyFailure::ConstraintNotSatisfied {
                    constraint: ((0, "decompose check").into(), 2, "high check").into(),
                    location: FailureLocation::InRegion {
                        region: (0, "Assign value").into(),
                        offset: 0
                    },
                    cell_values: vec![(((Any::Advice, 2).into(), 0).into(), "0x2".to_string())]
                }])
            );
        }

        // `equal check`
        {
            let circuit = MyCircuit::<Fp> {
                value_in: Value::known(Fp::from(4 as u64).into()),
                value_low: Value::known(Fp::from(1 as u64).into()),
                value_high: Value::known(Fp::from(1 as u64).into()),
            };
            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert_eq!(
                prover.verify(),
                Err(vec![VerifyFailure::ConstraintNotSatisfied {
                    constraint: ((0, "decompose check").into(), 0, "equal check").into(),
                    location: FailureLocation::InRegion {
                        region: (0, "Assign value").into(),
                        offset: 0
                    },
                    cell_values: vec![
                        (((Any::Advice, 0).into(), 0).into(), "0x4".to_string()),
                        (((Any::Advice, 1).into(), 0).into(), "1".to_string()),
                        (((Any::Advice, 2).into(), 0).into(), "1".to_string())
                    ]
                }])
            );
        }
    }
}
