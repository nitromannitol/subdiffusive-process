/-
# Energy image density (Bouleau–Hirsch)
-/
module

public import SubdiffusiveProcess.DirichletForm.Truncation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Energy image density

The **energy image density** property of Bouleau–Hirsch says that the image of
`Γ(v)` under `v` is absolutely continuous with respect to Lebesgue measure on
`ℝ`.  It is an accepted external input of this library, recorded as the
`Prop`-valued structure `SubdiffusiveProcess.DirichletForm.HasEnergyImageDensity`; it is never an
axiom and never proved here.

The two consequences the applications use are derived from it:
`Γ(v)` gives no mass to the preimage of a Lebesgue-null set, in particular to a
level set `{v = c}` or to the preimage of a countable set.

## References

* N. Bouleau, F. Hirsch, *Dirichlet Forms and Analysis on Wiener Space*,
  de Gruyter, 1991 (energy image density, scalar case).
-/

open MeasureTheory Filter Topology
open scoped NNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

namespace SubdiffusiveProcess.DirichletForm

/-- **External input** (Bouleau–Hirsch): the image of the energy measure `Γ(v)`
under a continuous representative of `v` is absolutely continuous with respect to
Lebesgue measure, and the chain rule holds for normal contractions.

`Prop`-valued hypothesis structure; never an axiom.

Inhabited by: `SubdiffusiveProcess.DirichletForm.zeroHasEnergyImageDensity`. The witness establishes
NON-VACUITY only; inhabitation at the paper's form is the external input
`SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`. -/
structure HasEnergyImageDensity {E : _root_.SubdiffusiveProcess.DirichletForm m}
    (Γ : EnergyMeasure E.toClosedForm) : Prop where
  /-- `Γ(v)(v⁻¹(N)) = 0` for every Lebesgue-null `N ⊆ ℝ`. -/
  measure_preimage_eq_zero : ∀ v ∈ E.toClosedForm.domain, ∀ vc : X → ℝ, Continuous vc → (⇑v =ᵐ[m] vc) →
    ∀ N : Set ℝ, MeasurableSet N → volume N = 0 → Γ.measure v (vc ⁻¹' N) = 0
  /-- `Γ(T(v)) = T'(v)² Γ(v)` for **Lipschitz** `T` with `T 0 = 0`, `T'` any Borel
  version of the a.e. derivative.

  The paper's display is "Lipschitz `T`
  with `T(0) = 0`", with no constraint on the Lipschitz constant.  An earlier
  version of this field said `IsNormalContraction T`, i.e. Lipschitz with
  constant `1`; that is strictly narrower than the paper and was upheld as a
  Fail on review.  The field now quantifies over every Lipschitz `T`. -/
  lipschitz_chain_rule : ∀ v ∈ E.toClosedForm.domain, ∀ vc : X → ℝ, Continuous vc → (⇑v =ᵐ[m] vc) →
    ∀ T : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K T) → T 0 = 0 →
    ∀ Tderiv : ℝ → ℝ, Measurable Tderiv → (∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) →
    ∀ w ∈ E.toClosedForm.domain, (⇑w =ᵐ[m] fun x => T (vc x)) →
    ∀ B : Set X, MeasurableSet B →
      (Γ.measure w B).toReal = ∫ x in B, (Tderiv (vc x)) ^ 2 ∂(Γ.measure v)

namespace HasEnergyImageDensity

variable {E : _root_.SubdiffusiveProcess.DirichletForm m} {Γ : EnergyMeasure E.toClosedForm}

/-- The energy measure gives no mass to a level set. -/
theorem measure_level_set_eq_zero (h : HasEnergyImageDensity Γ) {v : Lp ℝ 2 m}
    (hv : v ∈ E.toClosedForm.domain) {vc : X → ℝ} (hvc : Continuous vc)
    (hae : ⇑v =ᵐ[m] vc) (c : ℝ) :
    Γ.measure v {x : X | vc x = c} = 0 := by
  have := h.measure_preimage_eq_zero v hv vc hvc hae {c} (measurableSet_singleton c)
    (by simp)
  simpa [Set.preimage, Set.mem_singleton_iff] using this

/-- The energy measure gives no mass to the preimage of a countable set. -/
theorem measure_preimage_countable_eq_zero (h : HasEnergyImageDensity Γ) {v : Lp ℝ 2 m}
    (hv : v ∈ E.toClosedForm.domain) {vc : X → ℝ} (hvc : Continuous vc)
    (hae : ⇑v =ᵐ[m] vc) {N : Set ℝ} (hN : N.Countable) :
    Γ.measure v (vc ⁻¹' N) = 0 :=
  h.measure_preimage_eq_zero v hv vc hvc hae N hN.measurableSet (hN.measure_zero volume)

end HasEnergyImageDensity

end SubdiffusiveProcess.DirichletForm
