use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

#[macro_export]
macro_rules! constant_from_u64 {
    ($x: expr) => {
        halo2_proofs::plonk::Expression::Constant(F::from($x as u64))
    };
}

#[macro_export]
macro_rules! value_from_u64 {
    ($x: expr) => {
        Value::known(Fp::from($x as u64).into())
    };
}

use super::u32::{U32CheckConfig, U32Constrained};

// Unique set, given a list of addr's (can be repeated), find the unique addr's, e.g.,
// addr | addr_u
//  2   |   2
//  2   |   3
//  3   |  PAD
// PAD  |  PAD
const PAD: u64 = 256;
#[derive(Debug, Clone)]
pub(crate) struct MemOutputConstrained<F: FieldExt> {
    addr: AssignedCell<Assigned<F>, F>,
    addr_u: AssignedCell<Assigned<F>, F>,
    addr_u_diff: U32Constrained<F>,
    addr_u_diff_inv: AssignedCell<Assigned<F>, F>,
}

#[derive(Debug, Clone)]
struct MemOutputCheckConfig<F: FieldExt, const NUM_LIMBS: usize> {
    q_sel: Selector,
    q_active: Selector,
    addr: Column<Advice>, // unsigned interger
    addr_u: Column<Advice>,
    addr_u_diff: U32CheckConfig<F, NUM_LIMBS>,
    addr_u_diff_inv: Column<Advice>,
}

impl<F: FieldExt, const NUM_LIMBS: usize> MemOutputCheckConfig<F, NUM_LIMBS> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        addr: Column<Advice>,
        addr_u: Column<Advice>,
        addr_u_diff: Column<Advice>,
    ) -> Self {
        let q_sel = meta.complex_selector();
        let q_active = meta.selector();

        let addr_u_diff_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let addr_u_diff_chip =
            U32CheckConfig::configure(meta, q_sel, addr_u_diff, addr_u_diff_limbs);

        let addr_u_diff_inv = meta.advice_column();

        meta.lookup_any("forward lookup check", |meta| {
            let q_sel = meta.query_selector(q_sel);

            let addr = meta.query_advice(addr, Rotation::cur());

            let addr_u = meta.query_advice(addr_u, Rotation::cur());

            vec![(q_sel.clone() * addr.clone(), addr_u.clone())]
            // vec![(q_sel * addr_u, addr)]
            // vec![(q_sel.clone() * addr.clone(), addr_u.clone()), (q_sel * addr_u, addr)]
        });

        meta.lookup_any("backward lookup check", |meta| {
            let q_sel = meta.query_selector(q_sel);

            let addr = meta.query_advice(addr, Rotation::cur());

            let addr_u = meta.query_advice(addr_u, Rotation::cur());

            // vec![(q_sel.clone() * addr.clone(), addr_u.clone())]
            vec![(q_sel * addr_u, addr)]
            // vec![(q_sel.clone() * addr.clone(), addr_u.clone()), (q_sel * addr_u, addr)]
        });

        meta.create_gate("unique check", |meta| {
            let q_active = meta.query_selector(q_active);

            let addr_u_prev = meta.query_advice(addr_u, Rotation::prev());
            let addr_u = meta.query_advice(addr_u, Rotation::cur());
            let addr_u_diff = meta.query_advice(addr_u_diff, Rotation::cur());
            let pad = constant_from_u64!(PAD);

            let addr_u_diff_inv = meta.query_advice(addr_u_diff_inv, Rotation::cur());

            let is_addr_u_diff_zero_expr =
                Expression::Constant(F::one()) - addr_u_diff.clone() * addr_u_diff_inv;

            vec![
                q_active.clone() * (addr_u.clone() - addr_u_prev.clone() - addr_u_diff.clone()), // addr_u >= addr_u_prev
                q_active.clone() * is_addr_u_diff_zero_expr.clone() * (addr_u_prev - pad.clone()), // if addr_u == addr_u_prev, then addr_u_prev = PAD
                q_active.clone() * is_addr_u_diff_zero_expr.clone() * (addr_u - pad), // if addr_u == addr_u_prev, then addr_u = PAD
                q_active * addr_u_diff * is_addr_u_diff_zero_expr, // addr_u_diff zero check
            ]
        });

        Self {
            q_sel,
            q_active,
            addr,
            addr_u,
            addr_u_diff: addr_u_diff_chip,
            addr_u_diff_inv,
        }
    }

    pub fn assign_row_x(
        &self,
        region: &mut Region<'_, F>,
        addr_value: Value<Assigned<F>>,
        addr_u_value: Value<Assigned<F>>,
        addr_u_diff_value: Value<Assigned<F>>,
        addr_u_diff_limbs: Vec<Value<Assigned<F>>>,
        offset: usize,
    ) -> Result<MemOutputConstrained<F>, Error> {
        self.q_sel.enable(region, offset)?;
        if offset != 0 {
            self.q_active.enable(region, offset)?;
        }

        Ok(MemOutputConstrained {
            addr: region.assign_advice(|| "addr", self.addr, offset, || addr_value)?,
            addr_u: region.assign_advice(|| "addr_u", self.addr_u, offset, || addr_u_value)?,
            addr_u_diff: self.addr_u_diff.assign_region_x(
                region,
                addr_u_diff_value,
                addr_u_diff_limbs,
                offset,
            )?,
            addr_u_diff_inv: region.assign_advice(
                || "addr_u_diff_inv",
                self.addr_u_diff_inv,
                offset,
                || addr_u_diff_value.invert(),
            )?,
        })
    }

    pub fn load_tables(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.addr_u_diff.load_tables(layouter)?;
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
    struct MyCircuitRow<F: FieldExt, const NUM_LIMBS: usize> {
        addr: Value<Assigned<F>>,
        addr_u: Value<Assigned<F>>,
        addr_u_diff: Value<Assigned<F>>,
        addr_u_diff_limbs: Vec<Value<Assigned<F>>>,
    }

    struct MyCircuit<F: FieldExt, const NUM_LIMBS: usize, const NUM_ROWS: usize> {
        rows: [MyCircuitRow<F, NUM_LIMBS>; NUM_ROWS],
    }

    impl<F: FieldExt, const NUM_LIMBS: usize, const NUM_ROWS: usize> Default
        for MyCircuit<F, NUM_LIMBS, NUM_ROWS>
    {
        fn default() -> Self {
            MyCircuit {
                rows: std::array::from_fn(|_| MyCircuitRow::default()),
            }
        }
    }

    impl<F: FieldExt, const NUM_LIMBS: usize, const NUM_ROWS: usize> Circuit<F>
        for MyCircuit<F, NUM_LIMBS, NUM_ROWS>
    {
        type Config = MemOutputCheckConfig<F, NUM_LIMBS>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let addr_value = meta.advice_column();
            let addr_u = meta.advice_column();
            let addr_u_diff = meta.advice_column();

            MemOutputCheckConfig::configure(meta, addr_value, addr_u, addr_u_diff)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.load_tables(&mut layouter)?;

            layouter.namespace(|| "first row").assign_region(
                || "first row",
                |mut region| {
                    for offset in 0..NUM_ROWS {
                        config.assign_row_x(
                            &mut region,
                            self.rows[offset].addr,
                            self.rows[offset].addr_u,
                            self.rows[offset].addr_u_diff,
                            self.rows[offset].addr_u_diff_limbs.clone(),
                            offset,
                        )?;
                    }

                    // TODO: add padding row

                    Ok(())
                },
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_u8() {
        let k = 9;

        {
            let circuit = MyCircuit::<Fp, 1, 4> {
                rows: [
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(2),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(3),
                        addr_u_diff: value_from_u64!(1),
                        addr_u_diff_limbs: vec![value_from_u64!(1)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(3),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(PAD - 3),
                        addr_u_diff_limbs: vec![value_from_u64!(PAD - 3)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(PAD),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            let circuit = MyCircuit::<Fp, 1, 4> {
                rows: [
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(2),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(PAD-2),
                        addr_u_diff_limbs: vec![value_from_u64!(PAD-2)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(PAD),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            // fail if unique set has extra
            let circuit = MyCircuit::<Fp, 1, 4> {
                rows: [
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(2),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(3),
                        addr_u_diff: value_from_u64!(1),
                        addr_u_diff_limbs: vec![value_from_u64!(1)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(PAD - 3),
                        addr_u_diff_limbs: vec![value_from_u64!(PAD - 3)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(PAD),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err());
        }

        {
            // fail if the element in unique set is not unique
            let circuit = MyCircuit::<Fp, 1, 4> {
                rows: [
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(2),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(2),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(3),
                        addr_u: value_from_u64!(3),
                        addr_u_diff: value_from_u64!(1),
                        addr_u_diff_limbs: vec![value_from_u64!(1)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(PAD),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(PAD-3),
                        addr_u_diff_limbs: vec![value_from_u64!(PAD-3)],
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err());
        }

        {
            // fail if unique set is not complete
            let circuit = MyCircuit::<Fp, 1, 4> {
                rows: [
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(2),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(2),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(PAD-2),
                        addr_u_diff_limbs: vec![value_from_u64!(PAD-2)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(3),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                    MyCircuitRow {
                        addr: value_from_u64!(PAD),
                        addr_u: value_from_u64!(PAD),
                        addr_u_diff: value_from_u64!(0),
                        addr_u_diff_limbs: vec![value_from_u64!(0)],
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err());
        }
    }
}
