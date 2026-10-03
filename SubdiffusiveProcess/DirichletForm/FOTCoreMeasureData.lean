module

public import SubdiffusiveProcess.DirichletForm.FOTCoreMeasureFunctional

@[expose] public section

open MeasureTheory Filter Set Topology

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- The Riesz measures on the relative continuous core, before domain completion. -/
structure CoreMeasure (F : _root_.DirichletForm m) (U : Set X) where
  measure : Lp ℝ 2 m → Measure X
  finite : ∀ u, F.toClosedForm.MemCoreOn U u → measure u univ < ⊤
  mass : ∀ u, F.toClosedForm.MemCoreOn U u → (measure u univ).toReal = F.form u u
  carried : ∀ u, F.toClosedForm.MemCoreOn U u → measure u Uᶜ = 0
  regular : ∀ u, F.toClosedForm.MemCoreOn U u → (measure u).Regular
  defining : ∀ u φ, F.toClosedForm.MemCoreOn U u → F.toClosedForm.MemCoreOn U φ →
    ∀ uc φc : X → ℝ, Continuous uc → Continuous φc →
      ⇑u =ᵐ[m] uc → ⇑φ =ᵐ[m] φc →
      ∀ uφ u2 : Lp ℝ 2 m, uφ ∈ F.domain → u2 ∈ F.domain →
        (⇑uφ =ᵐ[m] fun x => uc x * φc x) → (⇑u2 =ᵐ[m] fun x => uc x ^ 2) →
        (∫ x, φc x ∂measure u) = F.form u uφ - (1 / 2 : ℝ) * F.form u2 φ


end DirichletForm.FOTConstruction
