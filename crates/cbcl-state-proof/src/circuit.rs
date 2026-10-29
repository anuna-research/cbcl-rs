use crate::{profile::Row, Profile};
use ff::Field;
use halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
    pasta::Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector},
    poly::Rotation,
};

type Cell = AssignedCell<Fp, Fp>;
#[derive(Clone, Debug)]
pub(crate) struct Config {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    sums: [Column<Advice>; 5],
    weights: [Column<Fixed>; 5],
    public: Column<Instance>,
    boolean: Selector,
    and: Selector,
    not: Selector,
    growth: Selector,
    accumulate: Selector,
    transition: Selector,
}
#[derive(Clone)]
pub(crate) struct StateCircuit {
    pub(crate) profile: Profile,
    pub(crate) masks: Option<(u16, u16)>,
    #[cfg(test)]
    pub(crate) forge_transition_sum: bool,
}
impl StateCircuit {
    pub(crate) fn empty(profile: &Profile) -> Self {
        Self {
            profile: profile.clone(),
            masks: None,
            #[cfg(test)]
            forge_transition_sum: false,
        }
    }
    pub(crate) fn witness(profile: &Profile, before: u16, after: u16) -> Self {
        Self {
            profile: profile.clone(),
            masks: Some((before, after)),
            #[cfg(test)]
            forge_transition_sum: false,
        }
    }
    pub(crate) fn k(&self) -> u32 {
        let n = self.profile.addresses().len();
        let rows = 3 * (1 << n) * (n + 2) + 8 * n + 64 + self.profile.transitions.len() + 1;
        rows.next_power_of_two().trailing_zeros().max(9)
    }
}
fn constant(
    region: &mut Region<'_, Fp>,
    config: &Config,
    row: &mut usize,
    value: Fp,
) -> Result<Cell, Error> {
    let cell = region.assign_advice_from_constant(|| "constant", config.c, *row, value)?;
    *row += 1;
    Ok(cell)
}
fn not(
    region: &mut Region<'_, Fp>,
    config: &Config,
    row: &mut usize,
    a: &Cell,
) -> Result<Cell, Error> {
    a.copy_advice(|| "operand", region, config.a, *row)?;
    let out = region.assign_advice(|| "not", config.c, *row, || a.value().map(|a| Fp::ONE - *a))?;
    config.not.enable(region, *row)?;
    *row += 1;
    Ok(out)
}
fn and(
    region: &mut Region<'_, Fp>,
    config: &Config,
    row: &mut usize,
    a: &Cell,
    b: &Cell,
) -> Result<Cell, Error> {
    a.copy_advice(|| "left", region, config.a, *row)?;
    b.copy_advice(|| "right", region, config.b, *row)?;
    let out = region.assign_advice(
        || "and",
        config.c,
        *row,
        || a.value().zip(b.value()).map(|(a, b)| *a * *b),
    )?;
    config.and.enable(region, *row)?;
    *row += 1;
    Ok(out)
}
fn select(
    layouter: &mut impl Layouter<Fp>,
    config: &Config,
    bits: &[Cell],
    inverse: &[Cell],
    rows: &[Row],
) -> Result<(Vec<Cell>, Vec<Cell>), Error> {
    let indicators = layouter.assign_region(
        || "exact subset equality",
        |mut region| {
            let mut offset = 0;
            let one = constant(&mut region, config, &mut offset, Fp::ONE)?;
            let mut indicators = Vec::new();
            for mask in 0..rows.len() {
                let mut acc = one.clone();
                for j in 0..bits.len() {
                    let factor = if mask & (1 << j) != 0 {
                        &bits[j]
                    } else {
                        &inverse[j]
                    };
                    acc = and(&mut region, config, &mut offset, &acc, factor)?;
                }
                indicators.push(acc);
            }
            Ok(indicators)
        },
    )?;
    let selected = layouter.assign_region(
        || "selected relation row",
        |mut region| {
            let mut values = [Value::known(Fp::ZERO); 5];
            for column in config.sums {
                region.assign_advice_from_constant(|| "initial sum", column, 0, Fp::ZERO)?;
            }
            let mut last = Vec::new();
            for (i, (indicator, row)) in indicators.iter().zip(rows).enumerate() {
                indicator.copy_advice(|| "indicator", &mut region, config.a, i)?;
                let weights = row.fields();
                last.clear();
                for j in 0..5 {
                    region.assign_fixed(
                        || "relation constant",
                        config.weights[j],
                        i,
                        || Value::known(weights[j]),
                    )?;
                    values[j] = values[j]
                        .zip(indicator.value())
                        .map(|(sum, bit)| sum + *bit * weights[j]);
                    last.push(region.assign_advice(
                        || "sum",
                        config.sums[j],
                        i + 1,
                        || values[j],
                    )?);
                }
                config.accumulate.enable(&mut region, i)?;
            }
            Ok(last)
        },
    )?;
    Ok((selected, indicators))
}
impl Circuit<Fp> for StateCircuit {
    type Config = Config;
    type FloorPlanner = SimpleFloorPlanner;
    fn without_witnesses(&self) -> Self {
        Self::empty(&self.profile)
    }
    fn configure(meta: &mut ConstraintSystem<Fp>) -> Config {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let sums = std::array::from_fn(|_| meta.advice_column());
        let weights = std::array::from_fn(|_| meta.fixed_column());
        let public = meta.instance_column();
        for col in [a, b, c].into_iter().chain(sums) {
            meta.enable_equality(col);
        }
        meta.enable_equality(public);
        let constants = meta.fixed_column();
        meta.enable_constant(constants);
        let boolean = meta.selector();
        let and = meta.selector();
        let not = meta.selector();
        let growth = meta.selector();
        let accumulate = meta.selector();
        let transition = meta.selector();
        meta.create_gate("Boolean selection", |meta| {
            let bit = meta.query_advice(a, Rotation::cur());
            vec![
                meta.query_selector(boolean)
                    * bit.clone()
                    * (bit - halo2_proofs::plonk::Expression::Constant(Fp::ONE)),
            ]
        });
        meta.create_gate("conjunction", |meta| {
            let x = meta.query_advice(a, Rotation::cur());
            let y = meta.query_advice(b, Rotation::cur());
            let z = meta.query_advice(c, Rotation::cur());
            vec![meta.query_selector(and) * (z - x * y)]
        });
        meta.create_gate("complement", |meta| {
            let x = meta.query_advice(a, Rotation::cur());
            let z = meta.query_advice(c, Rotation::cur());
            vec![
                meta.query_selector(not)
                    * (z + x - halo2_proofs::plonk::Expression::Constant(Fp::ONE)),
            ]
        });
        meta.create_gate("accepted set cannot shrink", |meta| {
            let old = meta.query_advice(a, Rotation::cur());
            let new = meta.query_advice(b, Rotation::cur());
            vec![
                meta.query_selector(growth)
                    * old
                    * (halo2_proofs::plonk::Expression::Constant(Fp::ONE) - new),
            ]
        });
        meta.create_gate("fixed relation accumulation", |meta| {
            let q = meta.query_selector(accumulate);
            let bit = meta.query_advice(a, Rotation::cur());
            (0..5)
                .map(|j| {
                    let prev = meta.query_advice(sums[j], Rotation::cur());
                    let next = meta.query_advice(sums[j], Rotation::next());
                    let weight = meta.query_fixed(weights[j]);
                    q.clone() * (next - prev - bit.clone() * weight)
                })
                .collect::<Vec<_>>()
        });
        meta.create_gate("previous-context admission relation", |meta| {
            let old = meta.query_advice(a, Rotation::cur());
            let new = meta.query_advice(b, Rotation::cur());
            let prev = meta.query_advice(c, Rotation::cur());
            let next = meta.query_advice(c, Rotation::next());
            vec![meta.query_selector(transition) * (next - prev - old * new)]
        });
        Config {
            a,
            b,
            c,
            sums,
            weights,
            public,
            boolean,
            and,
            not,
            growth,
            accumulate,
            transition,
        }
    }
    fn synthesize(&self, config: Config, mut layouter: impl Layouter<Fp>) -> Result<(), Error> {
        let n = self.profile.addresses().len();
        let (before, after, not_before, not_after, delta, not_delta) = layouter.assign_region(
            || "set selections",
            |mut region| {
                let mut offset = 0;
                let mut all = Vec::new();
                for side in 0..2 {
                    let mut bits = Vec::new();
                    for j in 0..n {
                        let value = self.masks.map(|(old, new)| {
                            Fp::from(u64::from(
                                (if side == 0 { old } else { new }) & (1 << j) != 0,
                            ))
                        });
                        let cell = region.assign_advice(
                            || "selection",
                            config.a,
                            offset,
                            || value.map_or(Value::unknown(), Value::known),
                        )?;
                        config.boolean.enable(&mut region, offset)?;
                        offset += 1;
                        bits.push(cell);
                    }
                    all.push(bits);
                }
                let before = all.remove(0);
                let after = all.remove(0);
                let mut nb = Vec::new();
                let mut na = Vec::new();
                let mut delta = Vec::new();
                let mut nd = Vec::new();
                for j in 0..n {
                    before[j].copy_advice(|| "old", &mut region, config.a, offset)?;
                    after[j].copy_advice(|| "new", &mut region, config.b, offset)?;
                    config.growth.enable(&mut region, offset)?;
                    offset += 1;
                    nb.push(not(&mut region, &config, &mut offset, &before[j])?);
                    na.push(not(&mut region, &config, &mut offset, &after[j])?);
                    delta.push(and(&mut region, &config, &mut offset, &after[j], &nb[j])?);
                    nd.push(not(&mut region, &config, &mut offset, &delta[j])?);
                }
                Ok((before, after, nb, na, delta, nd))
            },
        )?;
        let (old, old_indicators) = select(
            &mut layouter,
            &config,
            &before,
            &not_before,
            &self.profile.rows,
        )?;
        let (new, new_indicators) = select(
            &mut layouter,
            &config,
            &after,
            &not_after,
            &self.profile.rows,
        )?;
        let (batch, _) = select(
            &mut layouter,
            &config,
            &delta,
            &not_delta,
            &self.profile.rows,
        )?;
        layouter.assign_region(
            || "admitted batch in previous context",
            |mut region| {
                let mut value = Value::known(Fp::ZERO);
                let mut last = region.assign_advice_from_constant(
                    || "initial total",
                    config.c,
                    0,
                    Fp::ZERO,
                )?;
                for (i, (old, new)) in self.profile.transitions.iter().enumerate() {
                    let x = &old_indicators[*old];
                    let y = &new_indicators[*new];
                    x.copy_advice(|| "before equality", &mut region, config.a, i)?;
                    y.copy_advice(|| "after equality", &mut region, config.b, i)?;
                    value = value
                        .zip(x.value())
                        .zip(y.value())
                        .map(|((total, x), y)| total + *x * *y);
                    #[cfg(test)]
                    if self.forge_transition_sum && i + 1 == self.profile.transitions.len() {
                        value = Value::known(Fp::ONE);
                    }
                    last =
                        region.assign_advice(|| "transition total", config.c, i + 1, || value)?;
                    config.transition.enable(&mut region, i)?;
                }
                region.constrain_constant(last.cell(), Fp::ONE)
            },
        )?;
        layouter.assign_region(
            || "admission required",
            |mut region| {
                region.constrain_constant(old[0].cell(), Fp::ONE)?;
                region.constrain_constant(new[0].cell(), Fp::ONE)
            },
        )?;
        let identity = layouter.assign_region(
            || "profile identity",
            |mut region| {
                let mut offset = 0;
                crate::limbs(self.profile.id())
                    .into_iter()
                    .map(|v| constant(&mut region, &config, &mut offset, v))
                    .collect::<Result<Vec<_>, _>>()
            },
        )?;
        let public_cells = identity
            .into_iter()
            .chain(old[1..].iter().cloned())
            .chain(new[1..].iter().cloned())
            .chain(batch[1..3].iter().cloned());
        for (i, cell) in public_cells.enumerate() {
            layouter.constrain_instance(cell.cell(), config.public, i)?;
        }
        Ok(())
    }
}
