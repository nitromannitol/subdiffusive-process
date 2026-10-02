import SubdiffusiveProcess.Paper.limit_form_killed_consistency
import SubdiffusiveProcess.Paper.lem_cutoffs

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Killed consistency for the literal varying-environment cutoff coefficients on nested cubes. -/
theorem limit_form_killed_consistency_cutoff
    (d : ℕ) (hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (SQ : ResponseSpace (centeredCube zQ R hR0))
    (Sq : ResponseSpace (centeredCube zq r hr0))
    (hSQ : SQ.space = killedSobolevGraph (centeredCube zQ R hR0))
    (hSq : Sq.space = killedSobolevGraph (centeredCube zq r hr0))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (env : ℕ → BilateralField d) (cutoff : ℕ → ℕ)
    (GQ : DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (Gq : DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (LQ : aux_limit_form_package_limit_side d hd zQ R hR0 SQ GQ
      (fun n => Lane4.cutoffPositiveCoefficient M H (env n) (cutoff n) zQ hR0))
    (Lq : aux_limit_form_package_limit_side d hd zq r hr0 Sq Gq
      (fun n => Lane4.cutoffPositiveCoefficient M H (env n) (cutoff n) zq hr0))
 :
    let EQ := LQ.form.toClosedForm
    let Eq := Lq.form.toClosedForm
    ∃ D : Submodule ℝ (DomainL2 (centeredCube zQ R hR0)),
      DirichletForm.IsKilledDomain EQ (centeredCube zq r hr0 : Set (SpatialCoordinates d)) D ∧
      (∀ w : DomainL2 (centeredCube zQ R hR0), w ∈ D ↔
        ∃ u : DomainL2 (centeredCube zq r hr0),
          u ∈ Eq.domain ∧ zeroExtensionLp hqQ u = w) ∧
      (∀ u ∈ Eq.domain, zeroExtensionLp hqQ u ∈ EQ.domain ∧
        EQ.energy (zeroExtensionLp hqQ u) = Eq.energy u) ∧
      (∀ u ∈ Eq.domain, ∀ v ∈ Eq.domain,
        EQ.form (zeroExtensionLp hqQ u) (zeroExtensionLp hqQ v) = Eq.form u v) := by
  apply limit_form_killed_consistency d hd zQ zq R r hR0 hr0 hqQ SQ Sq hSQ hSq
    (fun n => Lane4.cutoffPositiveCoefficient M H (env n) (cutoff n) zQ hR0)
    (fun n => Lane4.cutoffPositiveCoefficient M H (env n) (cutoff n) zq hr0)
    _ GQ Gq LQ Lq
  intro n
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hqQ
      (aux_lem_cutoffs_positiveCoefficient_ae M H (env n) (cutoff n) zQ hR0),
    aux_lem_cutoffs_positiveCoefficient_ae M H (env n) (cutoff n) zq hr0] with x hQ hq
  exact hQ.trans hq.symm

end Paper
