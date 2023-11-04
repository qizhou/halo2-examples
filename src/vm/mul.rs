use halo2_proofs::{arithmetic::FieldExt, plonk::{Selector, Advice, Column, ConstraintSystem, Expression, Assigned, Error}, poly::Rotation, circuit::{Layouter, Value}};

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
        let q_sel = meta.selector();
        
        let lhs = U32CheckConfig::configure(meta, q_sel, lhs_value, (0..NUM_LIMBS).map(|_| meta.advice_column()).collect());
        let rhs = U32CheckConfig::configure(meta, q_sel, rhs_value, (0..NUM_LIMBS).map(|_| meta.advice_column()).collect());
        let out = U32CheckConfig::configure(meta, q_sel, out_value, (0..NUM_LIMBS).map(|_| meta.advice_column()).collect());
        let overflow = U32CheckConfig::configure(meta, q_sel, overflow_value, (0..NUM_LIMBS).map(|_| meta.advice_column()).collect());

        meta.create_gate("mul check", |meta| {
            let q_sel = meta.query_selector(q_sel);
            let lhs_value = meta.query_advice(lhs_value, Rotation::cur());
            let rhs_value = meta.query_advice(rhs_value, Rotation::cur());
            let out_value = meta.query_advice(out_value, Rotation::cur());
            let overflow_value = meta.query_advice(overflow_value, Rotation::cur());
            
            vec![
                q_sel * (lhs_value * rhs_value - out_value - overflow_value * Expression::Constant(F::from(256)))
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
        let lhs =  self.lhs.assign(layouter.namespace(|| "mul_lhs"), lhs_value, lhs_limbs)?;
        let rhs = self.lhs.assign(layouter.namespace(|| "mul_rhs"), rhs_value, rhs_limbs)?;
        let out = self.lhs.assign(layouter.namespace(|| "mul_out"), out_value, out_limbs)?;
        let overflow = self.lhs.assign(layouter.namespace(|| "mul_overflow"), overflow_value, overflow_limbs)?;
       
        layouter.assign_region(
            || "Assign mul value",
            move |mut region| {
                let offset: usize = 0;

                // Enable q_lookup
                self.q_sel.enable(&mut region, offset)?;

                Ok(())
            },
        )?;

        Ok(MulConstrained {
            lhs,
            rhs,
            out,
            overflow,
        })
    }

}
