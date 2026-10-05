module

public import SubdiffusiveProcess.Analysis.UniqueMinimizerSourceCongruence
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section9

/-- Equal source restrictions give equal continuous representatives of the
unique killed-form minimizers, on the literal full finite-energy domain. -/
theorem killed_minimizer_representatives_eqOn_of_source_ae_eq
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (nu : Measure (SpatialCoordinates d))
    (E : DomainL2 Q → ℝ≥0∞) (J : DomainL2 Q → SpatialCoordinates d → ℝ)
    (lam : ℝ) (f g : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hfg : (f : SpatialCoordinates d → ℝ) =ᵐ[nu] g)
    (u v : DomainL2 Q) (hu : E u ≠ ⊤)
    (Rf Rg : C(SpatialCoordinates d, ℝ))
    (hRf : (Rf : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set _)] u)
    (hRg : (Rg : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set _)] v) :
    let Func := fun (f : SpatialCoordinates d → ℝ) (w : DomainL2 Q) =>
      (E w).toReal + lam * (∫ x, J w x ^ 2 ∂nu) - 2 * (∫ x, f x * J w x ∂nu)
    (∀ w, E w ≠ ⊤ → Func f u ≤ Func f w) →
    (∀ w, E w ≠ ⊤ → (∀ z, E z ≠ ⊤ → Func g w ≤ Func g z) → w = v) →
    EqOn Rf Rg (Q : Set (SpatialCoordinates d)) := by
  dsimp only
  intro humin hvuniq
  have huv := SubdiffusiveProcess.Analysis.minimizer_eq_of_source_ae_eq nu E J lam f g hfg u v hu humin hvuniq
  subst v
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq (hRf.trans hRg.symm) Q.isOpen
    Rf.continuous.continuousOn Rg.continuous.continuousOn

end SubdiffusiveProcess.Section9
