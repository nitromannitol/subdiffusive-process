module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.DirichletForm.FOTLocality
public import SubdiffusiveProcess.Sobolev.ResponseSpace

@[expose] public section

open MeasureTheory Filter Set Topology TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- Domain-level strong locality relative to the state space. -/
def StronglyLocalOn (E : ClosedForm m) (U : Set X) : Prop :=
  ∀ u ∈ E.domain, ∀ v ∈ E.domain,
    (∃ K : Set X, IsCompact K ∧ K ⊆ U ∧ ∀ᵐ x ∂m, x ∉ K → u x = 0) →
    ∀ (c : ℝ) (W : Set X), IsOpen W →
      (∃ K : Set X, IsCompact K ∧ K ⊆ U ∩ W ∧ ∀ᵐ x ∂m, x ∉ K → v x = 0) →
      (∀ᵐ x ∂m, x ∈ W → u x = c) → E.form u v = 0

/-- The hypotheses of the energy-measure construction, with no calculus premise. -/
structure Data (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) : Prop where
  isOpen : IsOpen U
  full : m Uᶜ = 0
  core : ∃ C, IsCoreOn F.toClosedForm U C
  stronglyLocal : StronglyLocalOn F.toClosedForm U



def HasRepresentativeCalculus (F : _root_.SubdiffusiveProcess.DirichletForm m)
    (Γ : EnergyMeasure F.toClosedForm) : Prop :=
  ∃ rep : ∀ (v : Lp ℝ 2 m), v ∈ F.domain → X → ℝ,
    (∀ (v : Lp ℝ 2 m) (hv : v ∈ F.domain), Measurable (rep v hv)) ∧
    (∀ (v : Lp ℝ 2 m) (hv : v ∈ F.domain), ⇑v =ᵐ[m] rep v hv) ∧
    (∀ (v : Lp ℝ 2 m) (hv : v ∈ F.domain), ∀ K : Set ℝ, IsCompact K → volume K = 0 →
      Γ.measure v ((rep v hv) ⁻¹' K) = 0) ∧
    (∀ (v : Lp ℝ 2 m) (hv : v ∈ F.domain), ∀ T : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K T) → T 0 = 0 →
      ∀ Tderiv : ℝ → ℝ, Measurable Tderiv →
        (∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) →
        ∀ (w : Lp ℝ 2 m) (_hw : w ∈ F.domain),
          (⇑w =ᵐ[m] fun x => T (rep v hv x)) →
          ∀ B : Set X, MeasurableSet B →
            (Γ.measure w B).toReal = ∫ x in B, (Tderiv (rep v hv x)) ^ 2 ∂(Γ.measure v))

end SubdiffusiveProcess.DirichletForm.FOTConstruction
