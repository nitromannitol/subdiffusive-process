module

public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.Numeric
public import SubdiffusiveProcess.Paper.lem_primitive_holder_upgrade
public import SubdiffusiveProcess.Paper.lem_primitive_newtonian_convolution

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem lem_primitive :
  ∀ (d : ℕ), 2 ≤ d →
  ∃ C_log C_holder C_cube : ℝ, 0 < C_log ∧ 0 < C_holder ∧ 0 < C_cube ∧
    ∀ (R : ℝ) (hR : 0 < R) (z : SpatialCoordinates d)
      (f : SpatialCoordinates d → ℝ),
      MemLp f (⊤ : ENNReal) volume →
      (∀ᵐ x ∂volume, x ∉ (closedCube z R hR : Set (SpatialCoordinates d)) → f x = 0) →
      let Kf := (eLpNormEssSup f volume).toReal
      let g : SpatialCoordinates d → Fin d → ℝ := (fun x i =>
        ((d : ℝ) * (volume {w : SpatialCoordinates d |
          Real.sqrt (∑ j : Fin d, (w j) ^ 2) < 1}).toReal)⁻¹ *
          ∫ y, (if x = y then 0 else
            (x i - y i) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ d) * f y)
      (∀ φ : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∑ i : Fin d, ∫ x, g x i * fderiv ℝ φ x (Pi.single i 1)) = -∫ x, f x * φ x) ∧
        -- left half of `eq:mfd-primitive`: the logarithmic modulus
        (∀ x y : SpatialCoordinates d,
          Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
          Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
            C_log * Kf * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
              (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)))) ∧
        -- the scalar comparison between the two right-hand sides
        (∀ x y : SpatialCoordinates d,
          Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
          C_log * Kf * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
            (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ≤
          C_holder * Real.sqrt R * Kf *
            Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ∧
        -- the closing clause of the lemma
        (∀ x ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
          ∀ y ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
            Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
              C_cube * Real.sqrt R * Kf *
                Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ∧
        BddAbove {v : ℝ | ∃ x ∈ (closedCube z R hR : Set (SpatialCoordinates d)),
          ∃ y ∈ (closedCube z R hR : Set (SpatialCoordinates d)), x ≠ y ∧
            v = Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) /
              Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))} ∧
        halfHolderSeminorm (closedCube z R hR : Set (SpatialCoordinates d)) g ≤
          C_cube * Real.sqrt R * Kf := by
  intro d hd
  rcases Paper.lem_primitive_newtonian_convolution d hd with ⟨C_log, hC_log, h_child⟩
  rcases Paper.lem_primitive_holder_upgrade d hd C_log hC_log with ⟨C_holder, C_cube, h_holder, h_cube_pos, h_holder_fn⟩
  refine ⟨C_log, C_holder, C_cube, hC_log, h_holder, h_cube_pos, ?_⟩
  intro R hR z f hMem hSupp
  set Kf := (eLpNormEssSup f volume).toReal with hKf_def
  set g : SpatialCoordinates d → Fin d → ℝ := (fun x i =>
    ((d : ℝ) * (volume {w : SpatialCoordinates d |
      Real.sqrt (∑ j : Fin d, (w j) ^ 2) < 1}).toReal)⁻¹ *
      (∫ y, (if x = y then 0 else
        (x i - y i) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ d) * f y)) with hg_def
  have h_child_res := h_child R hR z f hMem hSupp
  rcases h_child_res with ⟨h_weak, h_log⟩
  have hKf_nonneg : 0 ≤ Kf := by rw [hKf_def]; exact ENNReal.toReal_nonneg
  have h_holder_res := h_holder_fn R hR z Kf g hKf_nonneg (by
    intro x y hxy
    have h := h_log x y hxy
    simpa [hg_def, hKf_def] using h)
  rcases h_holder_res with ⟨h_scalar, h_pointwise, h_bounded, h_cube_seminorm⟩
  -- Now assemble the goal, unfolding Kf and g with field_simp for the g-part
  have h_weak' : ∀ φ : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∑ i : Fin d, ∫ x, g x i * fderiv ℝ φ x (Pi.single i 1)) = -∫ x, f x * φ x := by
    intro φ hφ_cont hφ_cs
    rw [hg_def]
    simpa [mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_weak φ hφ_cont hφ_cs
  have h_log' : ∀ x y : SpatialCoordinates d,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
      Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
        C_log * Kf * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
          (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) := by
    intro x y hxy
    rw [hg_def]
    simpa [mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_log x y hxy
  have h_scalar' : ∀ x y : SpatialCoordinates d,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
      C_log * Kf * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
        (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ≤
      C_holder * Real.sqrt R * Kf *
        Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) := by
    intro x y hxy
    have h := h_scalar x y hxy
    simpa [hKf_def] using h.1
  have h_cube' : halfHolderSeminorm (closedCube z R hR : Set (SpatialCoordinates d)) g ≤
      C_cube * Real.sqrt R * Kf := by
    simpa [hKf_def, hg_def] using h_cube_seminorm
  refine ⟨h_weak', h_log', h_scalar', ?_, ?_, h_cube'⟩
  · simpa only [hKf_def, hg_def] using h_pointwise
  · simpa only [hKf_def, hg_def] using h_bounded

theorem aux_lem_primitive_compat :
  ∀ (d : ℕ), 2 ≤ d →
  ∃ C_log C_holder C_cube : ℝ, 0 < C_log ∧ 0 < C_holder ∧ 0 < C_cube ∧
    ∀ (R : ℝ) (hR : 0 < R) (z : SpatialCoordinates d)
      (f : SpatialCoordinates d → ℝ),
      MemLp f (⊤ : ENNReal) volume →
      (∀ᵐ x ∂volume, x ∉ (closedCube z R hR : Set (SpatialCoordinates d)) → f x = 0) →
      let Kf := (eLpNormEssSup f volume).toReal
      let g : SpatialCoordinates d → Fin d → ℝ := (fun x i =>
        ((d : ℝ) * (volume {w : SpatialCoordinates d |
          Real.sqrt (∑ j : Fin d, (w j) ^ 2) < 1}).toReal)⁻¹ *
          ∫ y, (if x = y then 0 else
            (x i - y i) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ d) * f y)
      (∀ φ : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∑ i : Fin d, ∫ x, g x i * fderiv ℝ φ x (Pi.single i 1)) = -∫ x, f x * φ x) ∧
        -- left half of `eq:mfd-primitive`: the logarithmic modulus
        (∀ x y : SpatialCoordinates d,
          Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
          Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
            C_log * Kf * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
              (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)))) ∧
        -- the scalar comparison between the two right-hand sides
        (∀ x y : SpatialCoordinates d,
          Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
          C_log * Kf * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) *
            (1 + Real.log (R / Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ≤
          C_holder * Real.sqrt R * Kf *
            Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ∧
        -- the closing clause of the lemma
        halfHolderSeminorm (closedCube z R hR : Set (SpatialCoordinates d)) g ≤
          C_cube * Real.sqrt R * Kf := by
  intro d hd
  obtain ⟨Cl, Ch, Cc, hCl, hCh, hCc, hall⟩ := lem_primitive d hd
  refine ⟨Cl, Ch, Cc, hCl, hCh, hCc, ?_⟩
  intro R hR z f hf hs
  obtain ⟨hw, hl, hc, _hp, _hb, hsemi⟩ := hall R hR z f hf hs
  exact ⟨hw, hl, hc, hsemi⟩

end Paper
