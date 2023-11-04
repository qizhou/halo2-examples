use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

use super::u32::{U32CheckConfig, U32Constrained};

#[derive(Debug, Clone)]
// Memory constraint table with
// addr | eid | last_write
// where the table is ordered by addr, and then eid
// last_write == 1 for the address's last write
pub(crate) struct MemConstrained<F: FieldExt> {
    addr: U32Constrained<F>,
    addr_diff: U32Constrained<F>,
    eid: U32Constrained<F>,
    eid_diff: U32Constrained<F>,
    last_write: AssignedCell<Assigned<F>, F>,
    addr_diff_inv: AssignedCell<Assigned<F>, F>,
}

#[derive(Debug, Clone)]
struct MemCheckConfig<F: FieldExt, const NUM_LIMBS: usize> {
    q_sel: Selector,
    q_int: Selector,
    addr: U32CheckConfig<F, NUM_LIMBS>,
    addr_diff: U32CheckConfig<F, NUM_LIMBS>,
    eid: U32CheckConfig<F, NUM_LIMBS>,
    eid_diff: U32CheckConfig<F, NUM_LIMBS>,
    last_write: Column<Advice>,
    addr_diff_inv: Column<Advice>,
}

impl<F: FieldExt, const NUM_LIMBS: usize> MemCheckConfig<F, NUM_LIMBS> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        addr: Column<Advice>,
        addr_diff: Column<Advice>,
        eid: Column<Advice>,
        eid_diff: Column<Advice>,
        last_write: Column<Advice>,
    ) -> Self {
        let q_sel = meta.complex_selector();
        let q_int = meta.complex_selector();
        let addr_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let addr_chip = U32CheckConfig::configure(meta, q_int, addr, addr_limbs);
        let addr_diff_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let addr_diff_chip = U32CheckConfig::configure(meta, q_int, addr_diff, addr_diff_limbs);
        let eid_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let eid_chip = U32CheckConfig::configure(meta, q_int, eid, eid_limbs);
        let eid_diff_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let eid_diff_chip = U32CheckConfig::configure(meta, q_int, eid_diff, eid_diff_limbs);
        let addr_diff_inv = meta.advice_column();

        meta.create_gate("mem check", |meta| {
            let q_sel = meta.query_selector(q_sel);

            let addr_prev = meta.query_advice(addr, Rotation::prev());
            let addr = meta.query_advice(addr, Rotation::cur());

            let addr_diff = meta.query_advice(addr_diff, Rotation::cur());

            let eid_prev = meta.query_advice(eid, Rotation::prev());
            let eid = meta.query_advice(eid, Rotation::cur());

            let eid_diff = meta.query_advice(eid_diff, Rotation::cur());

            let last_write_prev = meta.query_advice(last_write, Rotation::prev());

            let addr_diff_inv = meta.query_advice(addr_diff_inv, Rotation::cur());

            let is_addr_diff_zero_expr =
                Expression::Constant(F::one()) - addr_diff.clone() * addr_diff_inv;

            vec![
                q_sel.clone() * (addr.clone() - addr_prev.clone() - addr_diff.clone()), // addr must be non-decreasing
                q_sel.clone()
                    * is_addr_diff_zero_expr.clone()
                    * (eid - eid_prev - Expression::Constant(F::one()) - eid_diff), // if addr == prev_addr, then eid must be increasing
                q_sel.clone() * is_addr_diff_zero_expr.clone() * last_write_prev.clone(), // if addr == prev_addr, then last_write_prev == 0
                q_sel.clone()
                    * addr_diff.clone()
                    * (Expression::Constant(F::one()) - last_write_prev), // if addr > prev_addr, last_write_prev == 1
                q_sel * addr_diff * is_addr_diff_zero_expr, // addr_diff zero check
            ]
        });

        Self {
            q_sel,
            q_int,
            addr: addr_chip,
            addr_diff: addr_diff_chip,
            eid: eid_chip,
            eid_diff: eid_diff_chip,
            last_write,
            addr_diff_inv,
        }
    }

    pub fn assign_row_x(
        &self,
        region: &mut Region<'_, F>,
        addr_value: Value<Assigned<F>>,
        addr_limbs: Vec<Value<Assigned<F>>>,
        addr_diff_value: Value<Assigned<F>>,
        addr_diff_limbs: Vec<Value<Assigned<F>>>,
        eid_value: Value<Assigned<F>>,
        eid_limbs: Vec<Value<Assigned<F>>>,
        eid_diff_value: Value<Assigned<F>>,
        eid_diff_limbs: Vec<Value<Assigned<F>>>,
        last_write: Value<Assigned<F>>,
        offset: usize,
    ) -> Result<MemConstrained<F>, Error> {
        if offset > 0 {
            self.q_sel.enable(region, offset)?;
        }
        self.q_int.enable(region, offset)?;

        Ok(MemConstrained {
            addr: self
                .addr
                .assign_region_x(region, addr_value, addr_limbs, offset)?,
            addr_diff: self.addr_diff.assign_region_x(
                region,
                addr_diff_value,
                addr_diff_limbs,
                offset,
            )?,
            eid: self
                .eid
                .assign_region_x(region, eid_value, eid_limbs, offset)?,
            eid_diff: self.eid_diff.assign_region_x(
                region,
                eid_diff_value,
                eid_diff_limbs,
                offset,
            )?,
            last_write: region.assign_advice(
                || "last_write",
                self.last_write,
                offset,
                || last_write,
            )?,
            addr_diff_inv: region.assign_advice(
                || "addr_diff_inv",
                self.addr_diff_inv,
                offset,
                || addr_diff_value.invert(),
            )?,
        })
    }

    pub fn assign_first_row(
        &self,
        region: &mut Region<'_, F>,
        addr_value: Value<Assigned<F>>,
        addr_limbs: Vec<Value<Assigned<F>>>,
        addr_diff_value: Value<Assigned<F>>,
        addr_diff_limbs: Vec<Value<Assigned<F>>>,
        eid_value: Value<Assigned<F>>,
        eid_limbs: Vec<Value<Assigned<F>>>,
        eid_diff_value: Value<Assigned<F>>,
        eid_diff_limbs: Vec<Value<Assigned<F>>>,
        last_write: Value<Assigned<F>>,
    ) -> Result<MemConstrained<F>, Error> {
        let offset: usize = 0;

        self.q_int.enable(region, offset)?;

        Ok(MemConstrained {
            addr: self.addr.assign_region(region, addr_value, addr_limbs)?,
            addr_diff: self
                .addr_diff
                .assign_region(region, addr_diff_value, addr_diff_limbs)?,
            eid: self.eid.assign_region(region, eid_value, eid_limbs)?,
            eid_diff: self
                .eid_diff
                .assign_region(region, eid_diff_value, eid_diff_limbs)?,
            last_write: region.assign_advice(
                || "last_write",
                self.last_write,
                offset,
                || last_write,
            )?,
            addr_diff_inv: region.assign_advice(
                || "addr_diff_inv",
                self.addr_diff_inv,
                offset,
                || addr_diff_value.invert(),
            )?,
        })
    }

    pub fn load_tables(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.addr.load_tables(layouter)?;
        self.addr_diff.load_tables(layouter)?;
        self.eid.load_tables(layouter)?;
        self.eid_diff.load_tables(layouter)?;
        Ok(())
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
    struct MyCircuitRow<F: FieldExt, const NUM_LIMBS: usize> {
        addr: Value<Assigned<F>>,
        addr_limbs: Vec<Value<Assigned<F>>>,
        eid: Value<Assigned<F>>,
        eid_limbs: Vec<Value<Assigned<F>>>,
        addr_diff: Value<Assigned<F>>,
        addr_diff_limbs: Vec<Value<Assigned<F>>>,
        eid_diff: Value<Assigned<F>>,
        eid_diff_limbs: Vec<Value<Assigned<F>>>,
        last_write: Value<Assigned<F>>,
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
        type Config = MemCheckConfig<F, NUM_LIMBS>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let addr_value = meta.advice_column();
            let addr_diff_value = meta.advice_column();
            let eid_value = meta.advice_column();
            let eid_diff_value = meta.advice_column();
            let last_write = meta.advice_column();
            MemCheckConfig::configure(
                meta,
                addr_value,
                addr_diff_value,
                eid_value,
                eid_diff_value,
                last_write,
            )
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
                    config.assign_first_row(
                        &mut region,
                        self.rows[0].addr,
                        self.rows[0].addr_limbs.clone(),
                        self.rows[0].addr_diff,
                        self.rows[0].addr_diff_limbs.clone(),
                        self.rows[0].eid,
                        self.rows[0].eid_limbs.clone(),
                        self.rows[0].eid_diff,
                        self.rows[0].eid_diff_limbs.clone(),
                        self.rows[0].last_write,
                    )?;

                    for offset in 1..NUM_ROWS {
                        config.assign_row_x(
                            &mut region,
                            self.rows[offset].addr,
                            self.rows[offset].addr_limbs.clone(),
                            self.rows[offset].addr_diff,
                            self.rows[offset].addr_diff_limbs.clone(),
                            self.rows[offset].eid,
                            self.rows[offset].eid_limbs.clone(),
                            self.rows[offset].eid_diff,
                            self.rows[offset].eid_diff_limbs.clone(),
                            self.rows[offset].last_write,
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
            let circuit = MyCircuit::<Fp, 1, 1> {
                rows: [MyCircuitRow {
                    addr: Value::known(Fp::from(251 as u64).into()),
                    addr_limbs: vec![Value::known(Fp::from(251 as u64).into())],
                    eid: Value::known(Fp::from(42 as u64).into()),
                    eid_limbs: vec![Value::known(Fp::from(42 as u64).into())],
                    addr_diff: Value::known(Fp::from(46 as u64).into()),
                    addr_diff_limbs: vec![Value::known(Fp::from(46 as u64).into())],
                    eid_diff: Value::known(Fp::from(41 as u64).into()),
                    eid_diff_limbs: vec![Value::known(Fp::from(41 as u64).into())],
                    last_write: Value::known(Fp::from(0 as u64).into()),
                }],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            let circuit = MyCircuit::<Fp, 1, 2> {
                rows: [
                    MyCircuitRow {
                        addr: Value::known(Fp::from(251 as u64).into()),
                        addr_limbs: vec![Value::known(Fp::from(251 as u64).into())],
                        eid: Value::known(Fp::from(42 as u64).into()),
                        eid_limbs: vec![Value::known(Fp::from(42 as u64).into())],
                        addr_diff: Value::known(Fp::from(46 as u64).into()),
                        addr_diff_limbs: vec![Value::known(Fp::from(46 as u64).into())],
                        eid_diff: Value::known(Fp::from(41 as u64).into()),
                        eid_diff_limbs: vec![Value::known(Fp::from(41 as u64).into())],
                        last_write: Value::known(Fp::from(1 as u64).into()),
                    },
                    MyCircuitRow {
                        addr: Value::known(Fp::from(253 as u64).into()),
                        addr_limbs: vec![Value::known(Fp::from(253 as u64).into())],
                        eid: Value::known(Fp::from(20 as u64).into()),
                        eid_limbs: vec![Value::known(Fp::from(20 as u64).into())],
                        addr_diff: Value::known(Fp::from(2 as u64).into()),
                        addr_diff_limbs: vec![Value::known(Fp::from(2 as u64).into())],
                        eid_diff: Value::known(Fp::from(0 as u64).into()),
                        eid_diff_limbs: vec![Value::known(Fp::from(0 as u64).into())],
                        last_write: Value::known(Fp::from(0 as u64).into()),
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            // error: expect last_write = 1, actual = 0
            let circuit = MyCircuit::<Fp, 1, 2> {
                rows: [
                    MyCircuitRow {
                        addr: Value::known(Fp::from(251 as u64).into()),
                        addr_limbs: vec![Value::known(Fp::from(251 as u64).into())],
                        eid: Value::known(Fp::from(42 as u64).into()),
                        eid_limbs: vec![Value::known(Fp::from(42 as u64).into())],
                        addr_diff: Value::known(Fp::from(46 as u64).into()),
                        addr_diff_limbs: vec![Value::known(Fp::from(46 as u64).into())],
                        eid_diff: Value::known(Fp::from(41 as u64).into()),
                        eid_diff_limbs: vec![Value::known(Fp::from(41 as u64).into())],
                        last_write: Value::known(Fp::from(0 as u64).into()),
                    },
                    MyCircuitRow {
                        addr: Value::known(Fp::from(253 as u64).into()),
                        addr_limbs: vec![Value::known(Fp::from(253 as u64).into())],
                        eid: Value::known(Fp::from(20 as u64).into()),
                        eid_limbs: vec![Value::known(Fp::from(20 as u64).into())],
                        addr_diff: Value::known(Fp::from(2 as u64).into()),
                        addr_diff_limbs: vec![Value::known(Fp::from(2 as u64).into())],
                        eid_diff: Value::known(Fp::from(0 as u64).into()),
                        eid_diff_limbs: vec![Value::known(Fp::from(0 as u64).into())],
                        last_write: Value::known(Fp::from(0 as u64).into()),
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err());
        }

        {
            let circuit = MyCircuit::<Fp, 1, 3> {
                rows: [
                    MyCircuitRow {
                        addr: Value::known(Fp::from(251 as u64).into()),
                        addr_limbs: vec![Value::known(Fp::from(251 as u64).into())],
                        eid: Value::known(Fp::from(42 as u64).into()),
                        eid_limbs: vec![Value::known(Fp::from(42 as u64).into())],
                        addr_diff: Value::known(Fp::from(46 as u64).into()),
                        addr_diff_limbs: vec![Value::known(Fp::from(46 as u64).into())],
                        eid_diff: Value::known(Fp::from(41 as u64).into()),
                        eid_diff_limbs: vec![Value::known(Fp::from(41 as u64).into())],
                        last_write: Value::known(Fp::from(0 as u64).into()),
                    },
                    MyCircuitRow {
                        addr: Value::known(Fp::from(251 as u64).into()),
                        addr_limbs: vec![Value::known(Fp::from(251 as u64).into())],
                        eid: Value::known(Fp::from(77 as u64).into()),
                        eid_limbs: vec![Value::known(Fp::from(77 as u64).into())],
                        addr_diff: Value::known(Fp::from(0 as u64).into()),
                        addr_diff_limbs: vec![Value::known(Fp::from(0 as u64).into())],
                        eid_diff: Value::known(Fp::from(34 as u64).into()),
                        eid_diff_limbs: vec![Value::known(Fp::from(34 as u64).into())],
                        last_write: Value::known(Fp::from(1 as u64).into()),
                    },
                    MyCircuitRow {
                        addr: Value::known(Fp::from(253 as u64).into()),
                        addr_limbs: vec![Value::known(Fp::from(253 as u64).into())],
                        eid: Value::known(Fp::from(20 as u64).into()),
                        eid_limbs: vec![Value::known(Fp::from(20 as u64).into())],
                        addr_diff: Value::known(Fp::from(2 as u64).into()),
                        addr_diff_limbs: vec![Value::known(Fp::from(2 as u64).into())],
                        eid_diff: Value::known(Fp::from(0 as u64).into()),
                        eid_diff_limbs: vec![Value::known(Fp::from(0 as u64).into())],
                        last_write: Value::known(Fp::from(0 as u64).into()),
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            // expect last write = 0, actual = 1
            let circuit = MyCircuit::<Fp, 1, 3> {
                rows: [
                    MyCircuitRow {
                        addr: Value::known(Fp::from(251 as u64).into()),
                        addr_limbs: vec![Value::known(Fp::from(251 as u64).into())],
                        eid: Value::known(Fp::from(42 as u64).into()),
                        eid_limbs: vec![Value::known(Fp::from(42 as u64).into())],
                        addr_diff: Value::known(Fp::from(46 as u64).into()),
                        addr_diff_limbs: vec![Value::known(Fp::from(46 as u64).into())],
                        eid_diff: Value::known(Fp::from(41 as u64).into()),
                        eid_diff_limbs: vec![Value::known(Fp::from(41 as u64).into())],
                        last_write: Value::known(Fp::from(1 as u64).into()),
                    },
                    MyCircuitRow {
                        addr: Value::known(Fp::from(251 as u64).into()),
                        addr_limbs: vec![Value::known(Fp::from(251 as u64).into())],
                        eid: Value::known(Fp::from(77 as u64).into()),
                        eid_limbs: vec![Value::known(Fp::from(77 as u64).into())],
                        addr_diff: Value::known(Fp::from(0 as u64).into()),
                        addr_diff_limbs: vec![Value::known(Fp::from(0 as u64).into())],
                        eid_diff: Value::known(Fp::from(34 as u64).into()),
                        eid_diff_limbs: vec![Value::known(Fp::from(34 as u64).into())],
                        last_write: Value::known(Fp::from(1 as u64).into()),
                    },
                    MyCircuitRow {
                        addr: Value::known(Fp::from(253 as u64).into()),
                        addr_limbs: vec![Value::known(Fp::from(253 as u64).into())],
                        eid: Value::known(Fp::from(20 as u64).into()),
                        eid_limbs: vec![Value::known(Fp::from(20 as u64).into())],
                        addr_diff: Value::known(Fp::from(2 as u64).into()),
                        addr_diff_limbs: vec![Value::known(Fp::from(2 as u64).into())],
                        eid_diff: Value::known(Fp::from(0 as u64).into()),
                        eid_diff_limbs: vec![Value::known(Fp::from(0 as u64).into())],
                        last_write: Value::known(Fp::from(0 as u64).into()),
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err());
        }
    }
}
