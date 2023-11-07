use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct DynFibonacciConfig {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub col_n: Column<Advice>,
    pub selector: Selector,
    pub col_active: Column<Advice>,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct DynFibonacciChip<F: FieldExt, const N_ROWS: usize> {
    config: DynFibonacciConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const N_ROWS: usize> DynFibonacciChip<F, N_ROWS> {
    pub fn construct(config: DynFibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> DynFibonacciConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let col_n = meta.advice_column();
        let col_active = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(col_n);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // row | col_a | col_b | col_c | selector | col_n | col_active
            //     |    a      b        c       s     |   n   |
            // Example steps = 3, N_ROWS = 6
            //  0  |    1   |  1   |    2  |    1     |   3   |   1
            //  1  |    1   |  2   |    3  |    1     |   2   |   1
            //  2  |    2   |  3   |    5  |    1     |   1   |   1
            //  3  |    3   |  5   |    5  |    1     |   0   |   0
            //  4  |    3   |  5   |    5* |    1     |   0   |   0
            //  5  |    x   |  x   |    x  |    0     |   0*  |   0
            // (where * are output cells)
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            let n = meta.query_advice(col_n, Rotation::cur());
            let n_next = meta.query_advice(col_n, Rotation::next());
            let q_active = meta.query_advice(col_active, Rotation::cur());
            let q_active_next = meta.query_advice(col_active, Rotation::next());

            vec![
                s.clone() * q_active.clone() * (a.clone() + b.clone() - c.clone()), // if active, c = a + b
                s.clone()
                    * (Expression::Constant(F::one()) - q_active.clone())
                    * (b.clone() - c.clone()), // if !active, c = b
                s.clone()
                    * q_active.clone()
                    * (n.clone() - n_next.clone() - Expression::Constant(F::one())), // if active, then n--
                s.clone() * (Expression::Constant(F::one()) - q_active.clone()) * (n_next - n), // if !active, then n unchanged
                s.clone() * q_active.clone() * (Expression::Constant(F::one()) - q_active.clone()), // q_active must be 0 or 1
                s * (Expression::Constant(F::one()) - q_active) * q_active_next, // if !active, active_next = 0
            ]
        });

        DynFibonacciConfig {
            col_a,
            col_b,
            col_c,
            col_n,
            selector,
            col_active,
            instance,
        }
    }

    pub fn assign_rows(
        &self,
        mut layouter: impl Layouter<F>,
        steps: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "rows",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let a_cell = region.assign_advice_from_instance(
                    || "f(0)",
                    self.config.instance,
                    0,
                    self.config.col_a,
                    0,
                )?;

                let mut b_cell = region.assign_advice_from_instance(
                    || "f(1)",
                    self.config.instance,
                    1,
                    self.config.col_b,
                    0,
                )?;

                let mut c_cell = region.assign_advice(
                    || "a + b",
                    self.config.col_c,
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;

                let mut n_cell = region.assign_advice_from_instance(
                    || "n",
                    self.config.instance,
                    2,
                    self.config.col_n,
                    0,
                )?;

                region.assign_advice(
                    || "active",
                    self.config.col_active,
                    0,
                    || Value::known(F::one()),
                )?;

                for offset in 1..steps {
                    let prev_b = b_cell.clone();
                    let prev_c = c_cell.clone();

                    self.config.selector.enable(&mut region, offset)?;

                    // Copy the value from b & c in previous row to a & b in current row
                    prev_b.copy_advice(|| "a", &mut region, self.config.col_a, offset)?;
                    prev_c.copy_advice(|| "b", &mut region, self.config.col_b, offset)?;

                    b_cell = c_cell;
                    c_cell = region.assign_advice(
                        || "c",
                        self.config.col_c,
                        offset,
                        || prev_b.value().copied() + prev_c.value(),
                    )?;

                    n_cell = region.assign_advice(
                        || "n",
                        self.config.col_n,
                        offset,
                        || n_cell.value().copied() - Value::known(F::one()),
                    )?;

                    region.assign_advice(
                        || "active",
                        self.config.col_active,
                        offset,
                        || Value::known(F::one()),
                    )?;
                }

                for offset in steps..N_ROWS - 1 {
                    let prev_b = b_cell.clone();
                    let prev_c = c_cell.clone();

                    self.config.selector.enable(&mut region, offset)?;

                    // Copy the value from b & c in previous row to a & b in current row
                    prev_b.copy_advice(|| "a", &mut region, self.config.col_a, offset)?;
                    prev_c.copy_advice(|| "b", &mut region, self.config.col_b, offset)?;

                    b_cell = c_cell;
                    c_cell = region.assign_advice(
                        || "c",
                        self.config.col_c,
                        offset,
                        || prev_c.value().copied(),
                    )?;

                    let mut n_cell_value = n_cell.value().copied();
                    if offset == steps {
                        n_cell_value = n_cell_value - Value::known(F::one());
                    }

                    n_cell =
                        region.assign_advice(|| "n", self.config.col_n, offset, || n_cell_value)?;

                    region.assign_advice(
                        || "active",
                        self.config.col_active,
                        offset,
                        || Value::known(F::zero()),
                    )?;
                }

                region.assign_advice(
                    || "active",
                    self.config.col_active,
                    N_ROWS - 1,
                    || Value::known(F::zero()),
                )?;

                // add constrant n == 0
                region.assign_advice(
                    || "n",
                    self.config.col_n,
                    N_ROWS - 1,
                    || Value::known(F::zero()),
                )?;

                Ok(c_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F, const N_ROWS: usize>(PhantomData<F>, usize);

impl<F: FieldExt, const N_ROWS: usize> MyCircuit<F, N_ROWS> {
    fn set_steps(&mut self, steps: usize) {
        self.1 = steps;
    }
}

impl<F: FieldExt, const N_ROWS: usize> Circuit<F> for MyCircuit<F, N_ROWS> {
    type Config = DynFibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        DynFibonacciChip::<F, N_ROWS>::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = DynFibonacciChip::<F, N_ROWS>::construct(config);

        let c_cell = chip.assign_rows(layouter.namespace(|| "rows"), self.1)?;

        chip.expose_public(layouter.namespace(|| "out"), &c_cell, 3)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::MyCircuit;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[test]
    fn fibonacci_example1() {
        let k = 4;

        {
            let a = Fp::from(1); // F[0]
            let b = Fp::from(1); // F[1]
            let out = Fp::from(2); // F[4]

            let circuit = MyCircuit::<Fp, 4>(PhantomData, 1);

            let public_input = vec![a, b, Fp::from(1), out];

            let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
            prover.assert_satisfied();
        }

        {
            let a = Fp::from(1); // F[0]
            let b = Fp::from(1); // F[1]
            let out = Fp::from(5); // F[4]

            let circuit = MyCircuit::<Fp, 4>(PhantomData, 3);

            let public_input = vec![a, b, Fp::from(3), out];

            let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
            prover.assert_satisfied();
        }

        {
            let a = Fp::from(1); // F[0]
            let b = Fp::from(1); // F[1]
            let out = Fp::from(5); // F[4]

            let circuit = MyCircuit::<Fp, 5>(PhantomData, 3);

            let public_input = vec![a, b, Fp::from(3), out];

            let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
            prover.assert_satisfied();
        }

        {
            let a = Fp::from(1); // F[0]
            let b = Fp::from(1); // F[1]
            let out = Fp::from(5); // F[4]

            let circuit = MyCircuit::<Fp, 8>(PhantomData, 3);

            let public_input = vec![a, b, Fp::from(3), out];

            let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
            prover.assert_satisfied();
        }

        {
            let a = Fp::from(1); // F[0]
            let b = Fp::from(1); // F[1]
            let out = Fp::from(8); // F[5]
            let steps = 4;

            let circuit = MyCircuit::<Fp, 8>(PhantomData, steps);

            let public_input = vec![a, b, Fp::from(steps as u64), out];

            let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
            prover.assert_satisfied();
        }
    }

    #[test]
    fn fibonacci_example1_dyn() {
        let k = 4;

        let a = Fp::from(1); // F[0]
        let b = Fp::from(1); // F[1]
        let out = vec![2, 3, 5, 8, 13, 21, 34];

        let mut circuit = MyCircuit::<Fp, 8>(PhantomData, 1);

        for steps in 1..8 {
            circuit.set_steps(steps);

            let public_input = vec![
                a,
                b,
                Fp::from(steps as u64),
                Fp::from(out[steps - 1] as u64),
            ];

            let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
            prover.assert_satisfied();
        }
    }
    //     #[cfg(feature = "dev-graph")]
    //     #[test]
    //     fn plot_fibonacci1() {
    //         use plotters::prelude::*;

    //         let root = BitMapBackend::new("fib-1-layout.png", (1024, 3096)).into_drawing_area();
    //         root.fill(&WHITE).unwrap();
    //         let root = root.titled("Fib 1 Layout", ("sans-serif", 60)).unwrap();

    //         let circuit = MyCircuit::<Fp>(PhantomData);
    //         halo2_proofs::dev::CircuitLayout::default()
    //             .render(4, &circuit, &root)
    //             .unwrap();
    //     }
}
