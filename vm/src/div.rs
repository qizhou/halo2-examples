use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Region, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};

use super::u32::{U32CheckConfig, U32Constrained};

#[derive(Debug, Clone)]
// A division check with lhs = rhs * out + rem with out > rem, i.e., out - rem - 1 = diff
pub(crate) struct DivConstrained<F: FieldExt> {
    lhs: U32Constrained<F>,
    rhs: U32Constrained<F>,
    out: U32Constrained<F>,
    rem: U32Constrained<F>,
    diff: U32Constrained<F>,
}

#[derive(Debug, Clone)]
struct DivCheckConfig<F: FieldExt, const NUM_LIMBS: usize> {
    q_sel: Selector,
    lhs: U32CheckConfig<F, NUM_LIMBS>,
    rhs: U32CheckConfig<F, NUM_LIMBS>,
    out: U32CheckConfig<F, NUM_LIMBS>,
    rem: U32CheckConfig<F, NUM_LIMBS>,
    diff: U32CheckConfig<F, NUM_LIMBS>,
}

impl<F: FieldExt, const NUM_LIMBS: usize> DivCheckConfig<F, NUM_LIMBS> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        lhs_value: Column<Advice>,
        rhs_value: Column<Advice>,
        out_value: Column<Advice>,
        rem_value: Column<Advice>,
        diff_value: Column<Advice>,
    ) -> Self {
        let q_sel = meta.complex_selector();
        let lhs_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let lhs = U32CheckConfig::configure(meta, q_sel, lhs_value, lhs_limbs);
        let rhs_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let rhs = U32CheckConfig::configure(meta, q_sel, rhs_value, rhs_limbs);
        let out_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let out = U32CheckConfig::configure(meta, q_sel, out_value, out_limbs);
        let rem_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let rem = U32CheckConfig::configure(meta, q_sel, rem_value, rem_limbs);
        let diff_limbs = (0..NUM_LIMBS).map(|_| meta.advice_column()).collect();
        let diff = U32CheckConfig::configure(meta, q_sel, diff_value, diff_limbs);

        meta.create_gate("mul check", |meta| {
            let q_sel = meta.query_selector(q_sel);
            let lhs_value = meta.query_advice(lhs_value, Rotation::cur());
            let rhs_value = meta.query_advice(rhs_value, Rotation::cur());
            let out_value = meta.query_advice(out_value, Rotation::cur());
            let rem_value = meta.query_advice(rem_value, Rotation::cur());
            let diff_value = meta.query_advice(diff_value, Rotation::cur());

            vec![
                q_sel.clone() * (lhs_value - rhs_value.clone() * out_value - rem_value.clone()),
                q_sel * (rhs_value - rem_value - Expression::Constant(F::one()) - diff_value),
            ]
        });

        Self {
            q_sel,
            lhs,
            rhs,
            out,
            rem,
            diff,
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
        rem_value: Value<Assigned<F>>,
        rem_limbs: Vec<Value<Assigned<F>>>,
        diff_value: Value<Assigned<F>>,
        diff_limbs: Vec<Value<Assigned<F>>>,
    ) -> Result<DivConstrained<F>, Error> {
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
                    rem_value,
                    rem_limbs.clone(),
                    diff_value,
                    diff_limbs.clone(),
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
        rem_value: Value<Assigned<F>>,
        rem_limbs: Vec<Value<Assigned<F>>>,
        diff_value: Value<Assigned<F>>,
        diff_limbs: Vec<Value<Assigned<F>>>,
    ) -> Result<DivConstrained<F>, Error> {
        let offset: usize = 0;

        // Enable q_sel
        self.q_sel.enable(region, offset)?;

        Ok(DivConstrained {
            lhs: self.lhs.assign_region(region, lhs_value, lhs_limbs)?,
            rhs: self.rhs.assign_region(region, rhs_value, rhs_limbs)?,
            out: self.out.assign_region(region, out_value, out_limbs)?,
            rem: self.rem.assign_region(region, rem_value, rem_limbs)?,
            diff: self.diff.assign_region(region, diff_value, diff_limbs)?,
        })
    }

    pub fn load_tables(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.lhs.load_tables(layouter)?;
        self.rhs.load_tables(layouter)?;
        self.out.load_tables(layouter)?;
        self.rem.load_tables(layouter)?;
        self.diff.load_tables(layouter)?;
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
        lhs: Value<Assigned<F>>,
        lhs_limbs: Vec<Value<Assigned<F>>>,
        rhs: Value<Assigned<F>>,
        rhs_limbs: Vec<Value<Assigned<F>>>,
        out: Value<Assigned<F>>,
        out_limbs: Vec<Value<Assigned<F>>>,
        rem: Value<Assigned<F>>,
        rem_limbs: Vec<Value<Assigned<F>>>,
        diff: Value<Assigned<F>>,
        diff_limbs: Vec<Value<Assigned<F>>>,
    }

    impl<F: FieldExt, const NUM_LIMBS: usize> Circuit<F> for MyCircuit<F, NUM_LIMBS> {
        type Config = DivCheckConfig<F, NUM_LIMBS>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let lhs_value = meta.advice_column();
            let rhs_value = meta.advice_column();
            let out_value = meta.advice_column();
            let rem_value = meta.advice_column();
            let diff_value = meta.advice_column();
            DivCheckConfig::configure(meta, lhs_value, rhs_value, out_value, rem_value, diff_value)
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
                self.rem,
                self.rem_limbs.clone(),
                self.diff,
                self.diff_limbs.clone(),
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
                out: Value::known(Fp::from(5 as u64).into()),
                out_limbs: vec![Value::known(Fp::from(5 as u64).into())],
                rem: Value::known(Fp::from(41 as u64).into()),
                rem_limbs: vec![Value::known(Fp::from(41 as u64).into())],
                diff: Value::known(Fp::from(0 as u64).into()),
                diff_limbs: vec![Value::known(Fp::from(0 as u64).into())],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            let circuit = MyCircuit::<Fp, 1> {
                lhs: Value::known(Fp::from(250 as u64).into()),
                lhs_limbs: vec![Value::known(Fp::from(250 as u64).into())],
                rhs: Value::known(Fp::from(50 as u64).into()),
                rhs_limbs: vec![Value::known(Fp::from(50 as u64).into())],
                out: Value::known(Fp::from(5 as u64).into()),
                out_limbs: vec![Value::known(Fp::from(5 as u64).into())],
                rem: Value::known(Fp::from(0 as u64).into()),
                rem_limbs: vec![Value::known(Fp::from(0 as u64).into())],
                diff: Value::known(Fp::from(49 as u64).into()),
                diff_limbs: vec![Value::known(Fp::from(49 as u64).into())],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        {
            let circuit = MyCircuit::<Fp, 1> {
                lhs: Value::known(Fp::from(250 as u64).into()),
                lhs_limbs: vec![Value::known(Fp::from(250 as u64).into())],
                rhs: Value::known(Fp::from(50 as u64).into()),
                rhs_limbs: vec![Value::known(Fp::from(50 as u64).into())],
                out: Value::known(Fp::from(4 as u64).into()),
                out_limbs: vec![Value::known(Fp::from(4 as u64).into())],
                rem: Value::known(Fp::from(50 as u64).into()),
                rem_limbs: vec![Value::known(Fp::from(50 as u64).into())],
                diff: Value::known(Fp::from(0 as u64).into()),
                diff_limbs: vec![Value::known(Fp::from(0 as u64).into())],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            assert!(prover.verify().is_err());
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
                rhs: Value::known(Fp::from(524 as u64).into()),
                rhs_limbs: vec![
                    Value::known(Fp::from(12 as u64).into()),
                    Value::known(Fp::from(2 as u64).into()),
                ],
                out: Value::known(Fp::from(42 as u64).into()),
                out_limbs: vec![
                    Value::known(Fp::from(42 as u64).into()),
                    Value::known(Fp::from(0 as u64).into()),
                ],
                rem: Value::known(Fp::from(515 as u64).into()),
                rem_limbs: vec![
                    Value::known(Fp::from(3 as u64).into()),
                    Value::known(Fp::from(2 as u64).into()),
                ],
                diff: Value::known(Fp::from(8 as u64).into()),
                diff_limbs: vec![
                    Value::known(Fp::from(8 as u64).into()),
                    Value::known(Fp::from(0 as u64).into()),
                ],
            };

            let prover = MockProver::run(k, &circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }
    }
}
