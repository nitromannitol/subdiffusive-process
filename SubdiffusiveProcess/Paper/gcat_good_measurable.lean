import SubdiffusiveProcess.Lane4.GoodCellCatalogue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped Topology ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The literal good-cell event is measurable whenever its countable coordinate arrays are. -/
theorem gcat_good_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (k0 : ℕ) (lambdaLim cell epshom cdet : ℝ)
    (ZLim DLim : (Fin 3 × (Fin d → Fin 3)) → ∀ D : ℕ,
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ)
    (hZ : ∀ U D code, Measurable (ZLim U D code))
    (hD : ∀ U D code, Measurable (DLim U D code))
    (hlo : ∀ U, Measurable (loLim U)) (hhi : ∀ U, Measurable (hiLim U))
    (herr : Measurable (errLim ())) (hrat : ∀ c, Measurable (ratioLim c)) :
    MeasurableSet (gcat_good k0 lambdaLim cell epshom cdet ZLim DLim loLim hiLim errLim ratioLim) := by
  have hprefix : MeasurableSet {omega | ∀ U D, k0 ≤ D → ∀ code,
      ZLim U D code omega < lambdaLim * (D : ℝ) ∧
      DLim U D code omega < lambdaLim * (D : ℝ)} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun U => MeasurableSet.iInter fun D =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun code =>
        (measurableSet_lt (hZ U D code) measurable_const).inter
          (measurableSet_lt (hD U D code) measurable_const)
  have hell : MeasurableSet {omega | ∀ U, cell ≤ loLim U omega ∧ hiLim U omega ≤ cell⁻¹} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun U =>
      (measurableSet_le measurable_const (hlo U)).inter (measurableSet_le (hhi U) measurable_const)
  have hratio : MeasurableSet {omega | ∀ c, ratioLim c omega ∈ Set.Ioo (1 / 2 : ℝ) 2} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun c => (hrat c) measurableSet_Ioo
  exact hprefix.inter (hell.inter ((measurableSet_le herr measurable_const).inter hratio))

end Paper
