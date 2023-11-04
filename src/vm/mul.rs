use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

use super::u32::{U32CheckConfig, U32Constrained};

#[derive(Debug, Clone)]
/// A range-constrained value in the circuit produced by the RangeCheckConfig.
pub(crate) struct MulConstrained<F: FieldExt> {
    lhs: U32Constrained<F>,
    rhs: U32Constrained<F>,
    out: U32Constrained<F>,
    overflow: U32Constrained<F>,
}

#[derive(Debug, Clone)]
struct MulCheckConfig<F: FieldExt, const NUM_LIMBS: usize> {
    q_sel: Selector,
    lhs: U32CheckConfig<F, NUM_LIMBS>,
    rhs: U32CheckConfig<F, NUM_LIMBS>,
    out: U32CheckConfig<F, NUM_LIMBS>,
    overflow: U32CheckConfig<F, NUM_LIMBS>,
}

impl<F: FieldExt, const NUM_LIMBS: usize> MulCheckConfig<F, NUM_LIMBS> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        lhs_value: Column<Advice>,
        rhs_value: Column<Advice>,
        out_value: Column<Advice>,
        overflow_value: Column<Advice>,
    ) -> Self {
        let q_sel = meta.complex_selector();
        let lhs_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let lhs = U32CheckConfig::configure(meta, q_sel, lhs_value, lhs_limbs);
        let rhs_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let rhs = U32CheckConfig::configure(meta, q_sel, rhs_value, rhs_limbs);
        let out_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let out = U32CheckConfig::configure(meta, q_sel, out_value, out_limbs);
        let overflow_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let overflow = U32CheckConfig::configure(meta, q_sel, overflow_value, overflow_limbs);

        meta.create_gate("mul check", |meta| {
            let q_sel = meta.query_selector(q_sel);
            let lhs_value = meta.query_advice(lhs_value, Rotation::cur());
            let rhs_value = meta.query_advice(rhs_value, Rotation::cur());
            let out_value = meta.query_advice(out_value, Rotation::cur());
            let overflow_value = meta.query_advice(overflow_value, Rotation::cur());

            vec![
                q_sel
                    * (lhs_value * rhs_value
                        - out_value
                        - overflow_value
                            * Expression::Constant(F::from(256_u64.pow(NUM_LIMBS as u32)))),
            ]
        });

        Self {
            q_sel,
            lhs,
            rhs,
            out,
            overflow,
        }
    }

    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        lhs_value: Value<Assigned<F>>,
        lhs_limbs: Vec<Value<Assigned<F>>>,
        rhs_value: Value<Assigned<F>>,
        rhs_limbs: Vec<Value<Assigned<F>>>,
        out_value: Value<Assigned<F>>,
        out_limbs: Vec<Value<Assigned<F>>>,
        overflow_value: Value<Assigned<F>>,
        overflow_limbs: Vec<Value<Assigned<F>>>,
    ) -> Result<MulConstrained<F>, Error> {
        layouter.assign_region(
            || "Assign value",
            |mut region| {
                self.assign_region(
                    &mut region,
                    lhs_value,
                    lhs_limbs.clone(),
                    rhs_value,
                    rhs_limbs.clone(),
                    out_value,
                    out_limbs.clone(),
                    overflow_value,
                    overflow_limbs.clone(),
                )
            },
        )
    }

    pub fn assign_region(
        &self,
        region: &mut Region<'_, F>,
        lhs_value: Value<Assigned<F>>,
        lhs_limbs: Vec<Value<Assigned<F>>>,
        rhs_value: Value<Assigned<F>>,
        rhs_limbs: Vec<Value<Assigned<F>>>,
        out_value: Value<Assigned<F>>,
        out_limbs: Vec<Value<Assigned<F>>>,
        overflow_value: Value<Assigned<F>>,
        overflow_limbs: Vec<Value<Assigned<F>>>,
    ) -> Result<MulConstrained<F>, Error> {
        let offset: usize = 0;

        // Enable q_sel
        self.q_sel.enable(region, offset)?;

        Ok(MulConstrained {
            lhs: self.lhs.assign_region(region, lhs_value, lhs_limbs)?,
            rhs: self.rhs.assign_region(region, rhs_value, rhs_limbs)?,
            out: self.out.assign_region(region, out_value, out_limbs)?,
            overflow: self
                .overflow
                .assign_region(region, overflow_value, overflow_limbs)?,
        })
    }

    pub fn load_tables(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.lhs.load_tables(layouter)?;
        self.rhs.load_tables(layouter)?;
        self.out.load_tables(layouter)?;
        self.overflow.load_tables(layouter)?;
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
    struct MyCircuit<F: FieldExt, const NUM_LIMBS: usize> {
        lhs: Value<Assigned<F>>,
        lhs_limbs: Vec<Value<Assigned<F>>>,
        rhs: Value<Assigned<F>>,
        rhs_limbs: Vec<Value<Assigned<F>>>,
        out: Value<Assigned<F>>,
        out_limbs: Vec<Value<Assigned<F>>>,
        overflow: Value<Assigned<F>>,
        overflow_limbs: Vec<Value<Assigned<F>>>,
    }

    impl<F: FieldExt, const NUM_LIMBS: usize> Circuit<F> for MyCircuit<F, NUM_LIMBS> {
        type Config = MulCheckConfig<F, NUM_LIMBS>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let lhs_value = meta.advice_column();
            let rhs_value = meta.advice_column();
            let out_value = meta.advice_column();
            let overflow_value = meta.advice_column();
            MulCheckConfig::configure(meta, lhs_value, rhs_value, out_value, overflow_value)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.load_tables(&mut layouter)?;

            config.assign(
                layouter.namespace(|| "Assign value"),
                self.lhs,
                self.lhs_limbs.clone(),
                self.rhs,
                self.rhs_limbs.clone(),
                self.out,
                self.out_limbs.clone(),
                self.overflow,
                self.overflow_limbs.clone(),
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_u8() {
        let k = 9;

        {
            let circuit = MyCircuit::<Fp, 1> {
                lhs: Value::known(Fp::from(251 as u64).into()),
                lhs_limbs: vec![Value::known(Fp::from(251 as u64).into())],
                rhs: Value::known(Fp::from(42 as u64).into()),
                rhs_limbs: vec![Value::known(Fp::from(42 as u64).into())],
                out: Value::known(Fp::from(46 as u64).into()),
                out_limbs: vec![Value::known(Fp::from(46 as u64).into())],
                overflow: Value::known(Fp::from(41 as u64).into()),
                overflow_limbs: vec![Value::known(Fp::from(41 as u64).into())],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }
    }

    #[test]
    fn test_u16() {
        let k = 9;

        {
            let circuit = MyCircuit::<Fp, 2> {
                lhs: Value::known(Fp::from(22523 as u64).into()),
                lhs_limbs: vec![
                    Value::known(Fp::from(251 as u64).into()),
                    Value::known(Fp::from(87 as u64).into()),
                ],
                rhs: Value::known(Fp::from(59946 as u64).into()),
                rhs_limbs: vec![
                    Value::known(Fp::from(42 as u64).into()),
                    Value::known(Fp::from(234 as u64).into()),
                ],
                out: Value::known(Fp::from(56622 as u64).into()),
                out_limbs: vec![
                    Value::known(Fp::from(46 as u64).into()),
                    Value::known(Fp::from(221 as u64).into()),
                ],
                overflow: Value::known(Fp::from(20601 as u64).into()),
                overflow_limbs: vec![
                    Value::known(Fp::from(121 as u64).into()),
                    Value::known(Fp::from(80 as u64).into()),
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }
    }
}
