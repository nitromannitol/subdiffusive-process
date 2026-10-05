# Theorem C: large-scale Hölder regularity and a Liouville theorem

This pair checks Theorem C, label `t.C`, exposed as
`SubdiffusiveProcess.anomalous_holder_regularity` and proved from
`SubdiffusiveProcess.Paper.t_C`.

**What `Challenge.lean` states.** For `0 < δ ≤ δ₀(d)`, `γ_reg = 1 − C₀ δ √|log δ|`, every
exponent `γ ∈ [½, γ_reg]`, every cutoff `L ∈ ℕ ∪ {∞}` and every outer scale `m`, there is a
random minimal scale `𝓛_L(γ,m)` with an exponential tail. Almost surely, above that scale,
`a_L`-harmonic functions have `L²` oscillation decay `C 3^(−γ(m−n))` and weighted-energy growth
at most `C 3^((1−γ)(m−n))` on every admissible subcube. Almost surely, every entire `a_L`-harmonic
function with `liminf_{R→∞} R^(−γ_reg) inf_c ‖u − c‖_{L²(B_R)} = 0` is constant.

**How to read the encoding.**

- *The law of the environment.* The estimates hold for the law of the potentials on the set of
  environments where the layers converge, written as the pullback `Measure.comap Subtype.val`
  of the model's law to that set. The set is measurable and has probability one (the library
  lemmas `measurableSet_anchoredC11GoodSet` and `measure_anchoredC11GoodSet_eq_one`), so the
  pullback is the model's probability law and the statement is not vacuous.
- *Assumption (g2)* is encoded as in the paper: `E exp(δ⁻² (X⁺)²) ≤ 2`, where `X` is the sum of the
  supremum of `|γ₀|`, of `|∇γ₀|` and the Lipschitz constant of `∇γ₀` on the unit cube. Cubes and
  balls use the sup norm.
- *The Liouville hypothesis* "`liminf = 0`" is encoded as "for every `ε > 0`, the normalized
  oscillation is below `ε R^(γ_reg)` for arbitrarily large `R`". The conclusion is that the function
  agrees almost everywhere with a constant, that is, it has a constant continuous
  representative. No microscopic pointwise Hölder claim is made.
- *Extra conclusions.* The statement also records that `γ_reg` lies in `(½, 1)`, and states the
  Liouville conclusion as a constant continuous representative. These only strengthen the
  paper's statement.

`SolutionBasic.lean` repeats the vocabulary of the challenge on the proof side;
`SolutionBridge.lean` translates it into the library's vocabulary; `Solution.lean` applies the
library theorem. None of them adds a hypothesis. The permitted axioms are `propext`,
`Classical.choice` and `Quot.sound`.
