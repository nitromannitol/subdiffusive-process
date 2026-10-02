import SubdiffusiveProcess.Paper.limit_form_killed_consistency

open Set Filter MeasureTheory TopologicalSpace SubdiffusiveProcess Homogenization
open scoped Topology ENNReal NNReal BigOperators ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem mfd_prop_killed_consistency
    (d : ℕ) (hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (SQ : ResponseSpace (centeredCube zQ R hR0))
    (Sq : ResponseSpace (centeredCube zq r hr0))
    (hSQ : SQ.space = killedSobolevGraph (centeredCube zQ R hR0))
    (hSq : Sq.space = killedSobolevGraph (centeredCube zq r hr0))
    (aQ : ℕ → PositiveCoefficient (centeredCube zQ R hR0))
    (aq : ℕ → PositiveCoefficient (centeredCube zq r hr0))
    (hcoeff : ∀ n, ((aQ n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))]
        ((aq n).val : SpatialCoordinates d → ℝ))
    (GQ : DomainL2 (centeredCube zQ R hR0) →L[ℝ] DomainL2 (centeredCube zQ R hR0))
    (Gq : DomainL2 (centeredCube zq r hr0) →L[ℝ] DomainL2 (centeredCube zq r hr0))
    (LQ : aux_limit_form_package_limit_side d hd zQ R hR0 SQ GQ aQ)
    (Lq : aux_limit_form_package_limit_side d hd zq r hr0 Sq Gq aq)
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
        EQ.form (zeroExtensionLp hqQ u) (zeroExtensionLp hqQ v) = Eq.form u v) :=
  limit_form_killed_consistency d hd zQ zq R r hR0 hr0 hqQ
    SQ Sq hSQ hSq aQ aq hcoeff GQ Gq LQ Lq

end Paper
