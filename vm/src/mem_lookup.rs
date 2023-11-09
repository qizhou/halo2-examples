use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Region, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

use super::u32::{U32CheckConfig, U32Constrained};

#[derive(Debug, Clone)]
// With a memory constraint table,
// addr | last_write
// where addr is non-increasing with last_write = 1 if addr > addr_next
// constraint a new table
// addr | last_write
// such that addr is unique except padding or inactive ones (if there is a selector)

pub(crate) struct MemOutputConstrained<F: FieldExt> {
    addr: AssignedCell<Assigned<F>, F>,
    addr_u: AssignedCell<Assigned<F>, F>,
}

#[derive(Debug, Clone)]
struct MemOutputCheckConfig<F: FieldExt, const NUM_LIMBS: usize> {
    q_sel: Selector,
    addr: Column<Advice>,
    addr_u: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const NUM_LIMBS: usize> MemOutputCheckConfig<F, NUM_LIMBS> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        addr: Column<Advice>,
        addr_u: Column<Advice>,
    ) -> Self {
        let q_sel = meta.complex_selector();

        meta.lookup_any("unique check", |meta| {
            let q_sel = meta.query_selector(q_sel);

            let addr = meta.query_advice(addr, Rotation::cur());

            let addr_u = meta.query_advice(addr_u, Rotation::cur());

            vec![(q_sel.clone() * addr.clone(), addr_u.clone())]
            // vec![(q_sel * addr_u, addr)]
            // vec![(q_sel.clone() * addr.clone(), addr_u.clone()), (q_sel * addr_u, addr)]

        });

        Self {
            q_sel,
            addr,
            addr_u,
            _marker: PhantomData,
        }
    }

    pub fn assign_row_x(
        &self,
        region: &mut Region<'_, F>,
        addr_value: Value<Assigned<F>>,
        addr_u_value: Value<Assigned<F>>,
        offset: usize,
    ) -> Result<MemOutputConstrained<F>, Error> {
        self.q_sel.enable(region, offset)?;

        Ok(MemOutputConstrained {
            addr: region.assign_advice(|| "addr", self.addr, offset, || addr_value)?,
            addr_u: region.assign_advice(
                || "addr_u",
                self.addr_u,
                offset,
                || addr_u_value,
            )?,
        })
    }

    pub fn load_tables(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
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

            MemOutputCheckConfig::configure(
                meta,
                addr_value,
                addr_u,
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

                    for offset in 0..NUM_ROWS {
                        config.assign_row_x(
                            &mut region,
                            self.rows[offset].addr,
                            self.rows[offset].addr_u,
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
            let circuit = MyCircuit::<Fp, 1, 3> {
                rows: [
                    MyCircuitRow {
                        addr: Value::known(Fp::from(2 as u64).into()),
                        addr_u: Value::known(Fp::from(2 as u64).into())
                    },
                    MyCircuitRow {
                        addr: Value::known(Fp::from(2 as u64).into()),
                        addr_u: Value::known(Fp::from(3 as u64).into())
                    },
                    MyCircuitRow {
                        addr: Value::known(Fp::from(3 as u64).into()),
                        addr_u: Value::known(Fp::from(2 as u64).into())
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            let circuit = MyCircuit::<Fp, 1, 3> {
                rows: [
                    MyCircuitRow {
                        addr: Value::known(Fp::from(2 as u64).into()),
                        addr_u: Value::known(Fp::from(2 as u64).into())
                    },
                    MyCircuitRow {
                        addr: Value::known(Fp::from(2 as u64).into()),
                        addr_u: Value::known(Fp::from(3 as u64).into())
                    },
                    MyCircuitRow {
                        addr: Value::known(Fp::from(3 as u64).into()),
                        addr_u: Value::known(Fp::from(3 as u64).into())
                    },
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        // {
        //     let circuit = MyCircuit::<Fp, 1, 3> {
        //         rows: [
        //             MyCircuitRow {
        //                 addr: Value::known(Fp::from(2 as u64).into()),
        //                 last_write: Value::known(Fp::from(0 as u64).into()),
        //                 addr_u: Value::known(Fp::from(2 as u64).into())
        //             },
        //             MyCircuitRow {
        //                 addr: Value::known(Fp::from(2 as u64).into()),
        //                 last_write: Value::known(Fp::from(1 as u64).into()),
        //                 addr_u: Value::known(Fp::from(3 as u64).into())
        //             },
        //             MyCircuitRow {
        //                 addr: Value::known(Fp::from(3 as u64).into()),
        //                 last_write: Value::known(Fp::from(1 as u64).into()),
        //                 addr_u: Value::known(Fp::from(4 as u64).into())
        //             },
        //         ],
        //     };

        //     let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        //     assert!(prover.verify().is_err());
        // }
    }
}
