module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.ResolventBridge
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

@[expose] public section

/-!
# Conservativity of the Section 7 transition semigroup

`MarkovProcess` separates the sub-Markov property from conservativity: the
continuous-path process is built only from a semigroup satisfying
`SubMarkovKernelSemigroup.IsConservative`, that is `P t x univ = 1` for every
time and every starting point.

The manuscript proves exactly this statement for the reversible diffusion: *almost surely,
`P_t 1(x) = 1` for every `t > 0` and `x ∈ ℝ^d`*. Its proof runs through the maximal displacement
estimate: with `s = 1`,
`P_x[τ_{B_R(x)} ≤ t] ≤ C X_{m_R}(x) exp(-cR + C X_{m_R}(x) t_*/T(1)) → 0`,
so the exit times from `B_R(x)` increase to an infinite lifetime.

This file turns that argument into the two transition-kernel bridges that the
`MarkovProcess` interface actually consumes.  Both take the paper's conclusion
in a shape that mentions only the transition kernels — no path space, no exit
time — so neither is circular with the process construction:

* `isConservative_of_tendsto_ball_mass`: the mass of large balls centred at the
  starting point tends to one.  This is the escape-probability form of the
  manuscript's argument, since `P_t 1_{B_R(x)}(x) ≥ 1 - P_x[τ_{B_R(x)} ≤ t]`.
* `isConservative_of_tendsto_integral_c0`: the transition integrals of an
  exhausting sequence of `C₀` functions between `0` and `1` tend to one.  This
  is the "mass one from the constant function" form: the constant function `1`
  is not itself in `C₀(ℝ^d, ℝ)`, so it has to be reached along an exhaustion,
  and the hypothesis is then a statement purely about the `C₀` calculus that a
  resolvent provider controls.

Both are stated for an arbitrary sub-Markov kernel semigroup; the specialization
to the semigroup of a resolvent is recorded at the end.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Process

open Filter MeasureTheory MarkovProcess
open scoped ENNReal NNReal Topology ZeroAtInfty

noncomputable section

/-! ### Mass one from an exhaustion by balls -/

section Ball

variable {alpha : Type*} [PseudoMetricSpace alpha] [MeasurableSpace alpha]

/-- The transition-kernel form of the manuscript's nonexplosion conclusion: from
every starting point and at every time, the transition mass of the ball of
radius `R` about the starting point tends to one as `R → ∞`. -/
def HasNonexplosiveBallMass (P : SubMarkovKernelSemigroup alpha) : Prop :=
  ∀ (t : ℝ≥0) (x : alpha),
    Tendsto (fun R : ℝ ↦ P t x (Metric.closedBall x R)) atTop (𝓝 1)

/-- **Conservativity from nonexplosion.**  A sub-Markov kernel semigroup whose
large-ball transition mass tends to one is conservative. -/
theorem isConservative_of_tendsto_ball_mass {P : SubMarkovKernelSemigroup alpha}
    (h : HasNonexplosiveBallMass P) : P.IsConservative := by
  intro t x
  refine le_antisymm (P.measure_univ_le_one t x) ?_
  refine le_of_tendsto (h t x) ?_
  filter_upwards with R
  exact measure_mono (Set.subset_univ _)

end Ball

/-! ### Mass one from an exhaustion by `C₀` functions -/

section C0

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [OpensMeasurableSpace alpha]

/-- Every transition measure of a sub-Markov kernel semigroup is finite. -/
theorem isFiniteMeasure_apply {alpha : Type*} [MeasurableSpace alpha]
    (P : SubMarkovKernelSemigroup alpha) (t : ℝ≥0) (x : alpha) :
    IsFiniteMeasure (P t x) :=
  ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩

/-- A `C₀` function bounded by one has transition integral at most the total
transition mass. -/
theorem integral_le_measure_univ_toReal (P : SubMarkovKernelSemigroup alpha)
    (t : ℝ≥0) (x : alpha) (f : C₀(alpha, ℝ)) (hf : ∀ y, f y ≤ 1) :
    ∫ y, f y ∂(P t x) ≤ (P t x Set.univ).toReal := by
  let : IsFiniteMeasure (P t x) := isFiniteMeasure_apply P t x
  have hint : Integrable (fun y ↦ f y) (P t x) := by
    simpa using! (f.toBCF).integrable (P t x)
  have hmono : ∫ y, f y ∂(P t x) ≤ ∫ _y, (1 : ℝ) ∂(P t x) :=
    integral_mono hint (integrable_const 1) hf
  simpa [integral_const, measureReal_def, smul_eq_mul] using hmono

/-- **Conservativity from an exhausting `C₀` sequence.**  If there are `C₀`
functions `f n` with `0 ≤ f n ≤ 1` whose transition integrals tend to one at
every time and from every starting point, then the semigroup is conservative.

This is the "`P_t 1 = 1`" statement in the only form
available on a noncompact space, where the constant function `1` does not belong
to `C₀`. -/
theorem isConservative_of_tendsto_integral_c0 {P : SubMarkovKernelSemigroup alpha}
    (f : ℕ → C₀(alpha, ℝ)) (hf1 : ∀ n y, f n y ≤ 1)
    (hlim : ∀ (t : ℝ≥0) (x : alpha),
      Tendsto (fun n ↦ ∫ y, f n y ∂(P t x)) atTop (𝓝 1)) :
    P.IsConservative := by
  intro t x
  have hle : P t x Set.univ ≤ 1 := P.measure_univ_le_one t x
  have hne : P t x Set.univ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hle
  have hreal : (1 : ℝ) ≤ (P t x Set.univ).toReal := by
    refine le_of_tendsto (hlim t x) ?_
    filter_upwards with n
    exact integral_le_measure_univ_toReal P t x (f n) (hf1 n)
  have hone : (1 : ℝ≥0∞) ≤ P t x Set.univ := by
    rw [← ENNReal.ofReal_toReal hne]
    simpa using ENNReal.ofReal_le_ofReal hreal
  exact le_antisymm hle hone

end C0

/-! ### Specialization to the semigroup of a resolvent -/

section Resolvent

open Homogenization

variable {d : ℕ} (R : PositiveC0ContractiveResolvent (Vec d))

/-- Conservativity of the Section 7 transition semigroup from the manuscript's
nonexplosion conclusion. -/
theorem isConservative_semigroupOfResolvent_of_tendsto_ball_mass
    (h : HasNonexplosiveBallMass (semigroupOfResolvent R)) :
    (semigroupOfResolvent R).IsConservative :=
  isConservative_of_tendsto_ball_mass h

/-- Conservativity of the Section 7 transition semigroup from an exhausting `C₀`
sequence. -/
theorem isConservative_semigroupOfResolvent_of_tendsto_integral_c0
    (f : ℕ → C₀(Vec d, ℝ)) (hf1 : ∀ n y, f n y ≤ 1)
    (hlim : ∀ (t : ℝ≥0) (x : Vec d),
      Tendsto (fun n ↦ ∫ y, f n y ∂(semigroupOfResolvent R) t x) atTop (𝓝 1)) :
    (semigroupOfResolvent R).IsConservative :=
  isConservative_of_tendsto_integral_c0 f hf1 hlim

end Resolvent

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Process
