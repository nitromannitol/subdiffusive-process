import SubdiffusiveProcess.Paper.limit_form_package_controls




set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper
theorem aux_mfd_prop_boundary_cutoffs_lower_exponent
    {d : ℕ} (hd : 2 ≤ d) (zq : SpatialCoordinates d) (rq : ℝ) (h3rq : 0 < 3 * rq)
    (S0 : ResponseSpace (centeredCube zq (3 * rq) h3rq))
    (aC : ℕ → PositiveCoefficient (centeredCube zq (3 * rq) h3rq))
    (A : aux_limit_form_package_analytic_controls d hd zq (3 * rq) h3rq S0 aC)
    (t0 : ℝ) (ht0 : t0 ≤ A.t) : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)) →
      ∃ (W : Set (SpatialCoordinates d)) (chi : ℕ → S0.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen W ∧ K ⊆ W ∧ W ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ W, chic n x = 1) ∧
          (∀ x ∈ (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S0 (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube zq (3 * rq) h3rq : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t0)) := by
    intro K O hK hO hKO hOQ
    obtain ⟨W, chi, chic, B, hW, hKW, hWO, hB, hrest⟩ := A.cutoffs K O hK hO hKO hOQ
    refine ⟨W, chi, chic, B, hW, hKW, hWO, hB, ?_⟩
    intro n
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hrest n
    refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
    intro x hx rr hrr hrr1
    exact (h7 x hx rr hrr hrr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hrr hrr1 ht0) hB))

end Paper
