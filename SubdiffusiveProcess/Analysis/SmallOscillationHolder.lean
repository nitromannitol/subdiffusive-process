import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Sobolev.GradientLengthL2
import SubdiffusiveProcess.Sobolev.CoefficientEllipticity
import SubdiffusiveProcess.Analysis.AnchoredHolderNorm

/-! Interior Meyers and Morrey estimates with an explicit native energy bound.
The caller supplies logarithmic oscillation and ellipticity; no random-field estimate is asserted. -/

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- A positive lower coefficient bound converts the native gradient norm to weighted energy. -/
theorem gradient_norm_le_sqrt_energy {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (b : ℝ) (hb : 0 < b)
    (hlow : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), b ≤ a.val x)
    (u : SobolevData Ω) :
    ‖sobolevGradient u‖ ≤ Real.sqrt (sobolevCoefficientForm a u u) / Real.sqrt b := by
  have h := Real.sqrt_le_sqrt (sobolevCoefficientForm_ellipticity_lower a hlow u)
  rw [Real.sqrt_mul hb.le, Real.sqrt_sq (norm_nonneg _)] at h
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr
  simpa only [mul_comm] using h

/-- Meyers followed by Morrey gives a Holder representative with the explicit outer gradient norm. -/
theorem smallOscillation_holderSeminorm {d : ℕ}
    (W : SmallPerturbationInput d) (p alpha : ℝ) (hp : 2 ≤ p)
    (halpha : 0 < alpha) (halphap : alpha < 1 - (d : ℝ) / p)
    (z : SpatialCoordinates d) (l : ℝ) (hl : 0 < 4 * l)
    (a : PositiveCoefficient (centeredCube z (4 * l) hl)) (s : ℝ) (hs : 0 < s)
    (hosc : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      |Real.log (a.val x) - Real.log s| ≤ W.osc p)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ)
    (hF : AEMeasurable F (volume.restrict
      (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)))) (hKf : 0 ≤ Kf)
    (hbound : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      |F x| ≤ Kf)
    (u : weakSobolevGraph (centeredCube z (4 * l) hl))
    (heq : ∀ psi : killedSobolevGraph (centeredCube z (4 * l) hl),
      sobolevCoefficientForm a u.val psi.val =
        ∫ x in (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)), F x * psi.val.1 x) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Metric.ball z l)] U) ∧
      IsHolderOn alpha (Metric.closedBall z l) U ∧
      holderSeminorm alpha (Metric.closedBall z l) U ≤
        W.CMorrey p alpha * l ^ (1 - alpha) *
          (W.C p * (‖sobolevGradient u.val‖ / Real.sqrt ((4 * l) ^ d)) +
            W.C p * l * s⁻¹ * Kf) := by
  have hl0 : 0 < l := by linarith only [hl]
  obtain ⟨hmem, hgrad⟩ := W.interior_gradient p hp z l hl a s hs hosc F Kf hF hKf hbound u heq
  obtain ⟨U, hU, htie, hHolder, hsemi⟩ := W.morrey p hp alpha halpha halphap z l hl u hmem
  have houter : (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)) =
      Metric.ball z (2 * l) := by
    change Metric.ball z (4 * l / 2) = Metric.ball z (2 * l)
    congr 1
    ring
  have hinner : Metric.ball z l ⊆
      (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)) := by
    rw [houter]
    exact Metric.ball_subset_ball (by linarith only [hl0])
  rw [Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
    Set.inter_eq_left.mpr hinner] at htie
  have hnorm := normalizedGradientLpNorm_two_cube z (4 * l) hl (sobolevGradient u.val)
  have hnorm' : normalizedGradientLpNorm 2 (Metric.ball z (2 * l)) (sobolevGradient u.val) =
      ‖sobolevGradient u.val‖ / Real.sqrt ((4 * l) ^ d) :=
    (congrArg (fun S => normalizedGradientLpNorm 2 S (sobolevGradient u.val)) houter.symm).trans hnorm
  rw [hnorm'] at hgrad
  exact ⟨U, hU, htie, hHolder, hsemi.trans
    (mul_le_mul_of_nonneg_left hgrad
      (mul_nonneg (W.CMorrey_pos p alpha).le (Real.rpow_nonneg hl0.le _)))⟩

/-- The same interior estimate is controlled by coefficient energy under a positive lower bound. -/
theorem smallOscillation_holderSeminorm_energy {d : ℕ}
    (W : SmallPerturbationInput d) (p alpha : ℝ) (hp : 2 ≤ p)
    (halpha : 0 < alpha) (halphap : alpha < 1 - (d : ℝ) / p)
    (z : SpatialCoordinates d) (l : ℝ) (hl : 0 < 4 * l)
    (a : PositiveCoefficient (centeredCube z (4 * l) hl)) (s b : ℝ)
    (hs : 0 < s) (hb : 0 < b)
    (hosc : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      |Real.log (a.val x) - Real.log s| ≤ W.osc p)
    (hlow : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      b ≤ a.val x)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ)
    (hF : AEMeasurable F (volume.restrict
      (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)))) (hKf : 0 ≤ Kf)
    (hbound : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      |F x| ≤ Kf)
    (u : weakSobolevGraph (centeredCube z (4 * l) hl))
    (heq : ∀ psi : killedSobolevGraph (centeredCube z (4 * l) hl),
      sobolevCoefficientForm a u.val psi.val =
        ∫ x in (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)), F x * psi.val.1 x) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Metric.ball z l)] U) ∧
      IsHolderOn alpha (Metric.closedBall z l) U ∧
      holderSeminorm alpha (Metric.closedBall z l) U ≤
        W.CMorrey p alpha * l ^ (1 - alpha) *
          (W.C p * (Real.sqrt (sobolevCoefficientForm a u.val u.val) /
              Real.sqrt b / Real.sqrt ((4 * l) ^ d)) + W.C p * l * s⁻¹ * Kf) := by
  obtain ⟨U, hU, htie, hHolder, hsemi⟩ :=
    smallOscillation_holderSeminorm W p alpha hp halpha halphap z l hl a s hs hosc
      F Kf hF hKf hbound u heq
  refine ⟨U, hU, htie, hHolder, hsemi.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (W.CMorrey_pos p alpha).le
    (Real.rpow_nonneg (by linarith only [hl]) _))
  refine add_le_add ?_ (le_refl _)
  apply mul_le_mul_of_nonneg_left _ (W.C_pos p).le
  exact div_le_div_of_nonneg_right (gradient_norm_le_sqrt_energy a b hb hlow u.val)
    (Real.sqrt_nonneg _)

/-- Anchoring the Meyers--Morrey representative gives its full rescaled Holder norm. -/
theorem smallOscillation_scaled_cAlphaNorm_energy {d : ℕ}
    (W : SmallPerturbationInput d) (p alpha : ℝ) (hp : 2 ≤ p)
    (halpha : 0 < alpha) (halphap : alpha < 1 - (d : ℝ) / p)
    (z : SpatialCoordinates d) (l : ℝ) (hl : 0 < 4 * l)
    (a : PositiveCoefficient (centeredCube z (4 * l) hl)) (s b : ℝ)
    (hs : 0 < s) (hb : 0 < b)
    (hosc : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      |Real.log (a.val x) - Real.log s| ≤ W.osc p)
    (hlow : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      b ≤ a.val x)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ)
    (hF : AEMeasurable F (volume.restrict
      (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)))) (hKf : 0 ≤ Kf)
    (hbound : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      |F x| ≤ Kf)
    (u : weakSobolevGraph (centeredCube z (4 * l) hl))
    (heq : ∀ psi : killedSobolevGraph (centeredCube z (4 * l) hl),
      sobolevCoefficientForm a u.val psi.val =
        ∫ x in (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)), F x * psi.val.1 x) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Metric.ball z l)] U) ∧
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + (2 * l) • x) - U z) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + (2 * l) • x) - U z) ≤
          (((d : ℝ) + 1) ^ alpha + 1) * ((2 * l) ^ alpha *
            (W.CMorrey p alpha * l ^ (1 - alpha) *
              (W.C p * (Real.sqrt (sobolevCoefficientForm a u.val u.val) /
                  Real.sqrt b / Real.sqrt ((4 * l) ^ d)) + W.C p * l * s⁻¹ * Kf))) := by
  obtain ⟨U, hU, htie, hHolder, hsemi⟩ :=
    smallOscillation_holderSeminorm_energy W p alpha hp halpha halphap z l hl a s b hs hb
      hosc hlow F Kf hF hKf hbound u heq
  have hl0 : 0 < l := by linarith only [hl]
  have h2l : 0 < 2 * l := mul_pos (by norm_num) hl0
  have hclosed : (closedCube z (2 * l) h2l : Set (SpatialCoordinates d)) =
      Metric.closedBall z l := by
    change Metric.closedBall z (2 * l / 2) = Metric.closedBall z l
    rw [mul_div_cancel_left₀ l (by norm_num : (2 : ℝ) ≠ 0)]
  have hK0 : 0 ≤ W.CMorrey p alpha * l ^ (1 - alpha) *
      (W.C p * (Real.sqrt (sobolevCoefficientForm a u.val u.val) /
        Real.sqrt b / Real.sqrt ((4 * l) ^ d)) + W.C p * l * s⁻¹ * Kf) := by
    have hC := (W.C_pos p).le
    have hCM := (W.CMorrey_pos p alpha).le
    positivity
  have hnorm := scaled_cAlphaNorm_sub_center_le z (2 * l) h2l halpha.le hK0 U
    (by simpa only [hclosed] using hHolder) (by simpa only [hclosed] using hsemi)
  exact ⟨U, hU, htie, hnorm⟩

end SubdiffusiveProcess
