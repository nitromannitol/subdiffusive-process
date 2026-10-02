/-
# Weighted forms `E^w(u, v) = ∫ w dΓ(u, v)`
-/
import SubdiffusiveProcess.DirichletForm.EnergyMeasure

/-!
# Weighted forms

Given a closed form `E` with energy measure `Γ` and a weight `w : X → ℝ`, the
**weighted form** `E^w` is characterized by `E^w(u, v) = ∫ w dΓ(u, v)`.  This
file records that characterization (`DirichletForm.IsWeightedForm`) and derives
the two-sided comparison `(inf w) E ≤ E^w ≤ (sup w) E` from it.

## References

* Fukushima–Oshima–Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  §3.2 (the energy-measure calculus used to build weighted forms).
-/

open MeasureTheory Filter Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

namespace DirichletForm

/-- `F` is the `w`-weighted form of `E`: it has the same domain and
`F(u, v) = ∫ w dΓ(u, v)`.

Inhabited by: `DirichletForm.zeroIsWeightedForm`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`DirichletForm.HasEnergyMeasure`. -/
structure IsWeightedForm (E F : ClosedForm m) (Γ : EnergyMeasure E) (w : X → ℝ) :
    Prop where
  /-- `D(E^w) = D(E)`. -/
  domain_eq : F.domain = E.domain
  /-- `E^w(u) = ∫ w dΓ(u)`. -/
  energy_eq : ∀ u ∈ E.domain, F.form u u = ∫ x, w x ∂(Γ.measure u)
  /-- `E^w(u, v) = ∫ w dΓ(u, v)`. -/
  form_eq : ∀ u ∈ E.domain, ∀ v ∈ E.domain,
    F.form u v = signedIntegralOn (Γ.cross u v) Set.univ w

namespace IsWeightedForm

variable {E F : ClosedForm m} {Γ : EnergyMeasure E} {w : X → ℝ}

/-- A weight bounded above by `b` gives `E^w ≤ b E`. -/
theorem form_le_of_le {b : ℝ} (h : IsWeightedForm E F Γ w) {u : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hint : Integrable w (Γ.measure u)) (hb : ∀ x, w x ≤ b) :
    F.form u u ≤ b * E.form u u := by
  haveI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu⟩
  rw [h.energy_eq u hu, ← Γ.measure_univ u hu]
  calc ∫ x, w x ∂(Γ.measure u) ≤ ∫ _x, b ∂(Γ.measure u) :=
        integral_mono hint (integrable_const b) hb
    _ = b * (Γ.measure u Set.univ).toReal := by
        simp [integral_const, measureReal_def, mul_comm]

/-- A weight bounded below by `a` gives `a E ≤ E^w`. -/
theorem le_form_of_le {a : ℝ} (h : IsWeightedForm E F Γ w) {u : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hint : Integrable w (Γ.measure u)) (ha : ∀ x, a ≤ w x) :
    a * E.form u u ≤ F.form u u := by
  haveI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu⟩
  rw [h.energy_eq u hu, ← Γ.measure_univ u hu]
  calc a * (Γ.measure u Set.univ).toReal = ∫ _x, a ∂(Γ.measure u) := by
        simp [integral_const, measureReal_def, mul_comm]
    _ ≤ ∫ x, w x ∂(Γ.measure u) := integral_mono (integrable_const a) hint ha

/-- The two-sided comparison `a E ≤ E^w ≤ b E` for `a ≤ w ≤ b`. -/
theorem form_mem_Icc {a b : ℝ} (h : IsWeightedForm E F Γ w) {u : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hint : Integrable w (Γ.measure u)) (ha : ∀ x, a ≤ w x)
    (hb : ∀ x, w x ≤ b) : a * E.form u u ≤ F.form u u ∧ F.form u u ≤ b * E.form u u :=
  ⟨h.le_form_of_le hu hint ha, h.form_le_of_le hu hint hb⟩

/-- The weighted form with a weight bounded above by `b` is `LEWithConst b`. -/
theorem leWithConst {b : ℝ} (h : IsWeightedForm E F Γ w)
    (hint : ∀ u ∈ E.domain, Integrable w (Γ.measure u)) (hb : ∀ x, w x ≤ b) :
    ClosedForm.LEWithConst F E b := by
  intro u hu
  exact ⟨h.domain_eq ▸ hu, h.form_le_of_le hu (hint u hu) hb⟩

end IsWeightedForm

section Bounded

variable [OpensMeasurableSpace X]

/-- A bounded continuous function is integrable against a finite measure. -/
theorem integrable_of_continuous_of_bound {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ x : X, |f x| ≤ C) :
    Integrable f μ := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro x
  simpa using hC x

/-- A bounded continuous weight is integrable against every energy measure of the
domain: the integrability hypotheses of `IsWeightedForm.form_le_of_le` and
`IsWeightedForm.le_form_of_le` are automatic for such weights. -/
theorem integrable_of_energyMeasure {E : ClosedForm m} (Γ : EnergyMeasure E) {w : X → ℝ}
    (hw : Continuous w) {C : ℝ} (hC : ∀ x : X, |w x| ≤ C) {u : Lp ℝ 2 m}
    (hu : u ∈ E.domain) : Integrable w (Γ.measure u) := by
  haveI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu⟩
  exact integrable_of_continuous_of_bound hw hC

end Bounded

end DirichletForm
