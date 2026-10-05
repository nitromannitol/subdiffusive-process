module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevProjectionBasic
public import Homogenization.Besov.Duality.ProjectionLimit
public import Homogenization.Besov.Localization
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy

theorem weightedEnergy_partition_square {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) (j : ℕ) (hf : MemLp f 2 (normalizedCubeMeasure Q)) : descendantsAverage Q j (fun R => (cubeLpNorm R 2 f) ^ (2 : ℝ)) = (cubeLpNorm Q 2 f) ^ (2 : ℝ) := by
  have hQ := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q:=Q) (p:=2) (f:=f) (by norm_num) (by norm_num) hf
  have hI:=integrableOn_of_integrable_normalizedCubeMeasure (Q:=Q) (hf.integrable_norm_rpow (by norm_num) (by norm_num))
  norm_num only [ENNReal.toReal_ofNat] at hQ hI
  rw[hQ,cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _ hI]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  simpa using cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q:=R) (p:=2) (f:=f) (by norm_num) (by norm_num) (memLp_on_descendant_of_memLp hR hf)

theorem weightedEnergy_residual_square {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (j : ℕ) (hu : MemLp u 2 (normalizedCubeMeasure Q)) : cubeBesovDepthAverage Q 2 u j = (cubeLpNorm Q 2 (cubeProjectionResidual Q j u)) ^ (2 : ℝ) := by
  rw [cubeBesovDepthAverage_eq_descendantsAverage_projectionResidual]
  exact weightedEnergy_partition_square Q _ j (weightedProjection_residual_memLp Q u j hu)

theorem weightedEnergy_depth_residual {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (j : ℕ) (hu : MemLp u 2 (normalizedCubeMeasure Q)) : cubeBesovDepthSeminorm Q (1 / 2) 2 u j = cubeBesovDepthWeight Q (1 / 2) j * cubeLpNorm Q 2 (cubeProjectionResidual Q j u) := by
  unfold cubeBesovDepthSeminorm
  rw [weightedEnergy_residual_square Q u j hu]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [sq_rpow_half_eq_of_nonneg (cubeLpNorm_nonneg Q 2 _)]

theorem weightedEnergy_depth_weight_pos {d : ℕ} (Q : TriadicCube d) (j : ℕ) : 0 < cubeBesovDepthWeight Q (1 / 2) j := by
  unfold cubeBesovDepthWeight cubeScaleFactor
  positivity

theorem weightedEnergy_depth_weight_inv {d : ℕ} (Q : TriadicCube d) (j : ℕ) : (cubeBesovDepthWeight Q (1 / 2) j)⁻¹ = cubeBesovScaleWeight (-1 / 2) Q * (3 : ℝ) ^ (-(j : ℝ) / 2) := by
  have hs : 0 ≤ cubeScaleFactor Q := by
    unfold cubeScaleFactor
    positivity
  have hj : 0 ≤ (3 : ℝ) ^ j := by
    positivity
  unfold cubeBesovDepthWeight cubeBesovScaleWeight
  norm_num only [neg_div, neg_neg]
  rw [Real.rpow_neg (div_nonneg hs hj) (1 / 2), inv_inv,
    Real.div_rpow hs hj (1 / 2),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3) j (1 / 2)]
  rw [show (j : ℝ) * (1 / 2) = (j : ℝ) / 2 by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) ((j : ℝ) / 2), div_eq_mul_inv]

theorem weightedEnergy_eLpNorm_eq_ofReal_cubeLpNorm {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) (hf : MemLp f 2 (normalizedCubeMeasure Q)) : eLpNorm f 2 (normalizedCubeMeasure Q) = ENNReal.ofReal (cubeLpNorm Q 2 f) := by
  unfold cubeLpNorm
  exact (ENNReal.ofReal_toReal hf.eLpNorm_ne_top).symm

theorem weightedEnergy_residual_decay_mono (j : ℕ) : (3 : ℝ) ^ (-((j : ℝ) + 1) / 2) ≤ (3 : ℝ) ^ (-(j : ℝ) / 2) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3); linarith

theorem weightedEnergy_inv_bound (W X B : ℝ) (hW : 0 < W) (h : W * X ≤ B) : X ≤ W⁻¹ * B := by
  have hm := mul_le_mul_of_nonneg_left h (inv_pos.mpr hW).le
  simpa [←mul_assoc, inv_mul_cancel₀ hW.ne'] using hm

theorem weightedEnergy_increment_triangle {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (j : ℕ) (_hu : MemLp u 2 (normalizedCubeMeasure Q)) : eLpNorm (cubeIncrement Q (j + 1) u) 2 (normalizedCubeMeasure Q) ≤ eLpNorm (cubeProjectionResidual Q j u) 2 (normalizedCubeMeasure Q) + eLpNorm (cubeProjectionResidual Q (j + 1) u) 2 (normalizedCubeMeasure Q) := by
  rw [weightedProjection_increment_residual Q u j]
  exact eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)

theorem weightedEnergy_two_sum (S B R : ℝ) (hS : 0 ≤ S) (hB : 0 ≤ B) (hR : 0 ≤ R) : ENNReal.ofReal (S * B * R) + ENNReal.ofReal (S * B * R) = ENNReal.ofReal (2 * S * B * R) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem weightedEnergy_residual_lpNorm_le {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (B : ℝ) (hu : MemLp u 2 (normalizedCubeMeasure Q)) (hdepth : ∀ j : ℕ, cubeBesovDepthSeminorm Q (1 / 2) 2 u j ≤ B) (j : ℕ) : cubeLpNorm Q 2 (cubeProjectionResidual Q j u) ≤ cubeBesovScaleWeight (-1 / 2) Q * B * (3 : ℝ) ^ (-(j : ℝ) / 2) := by
  have h := hdepth j
  rw [weightedEnergy_depth_residual Q u j hu] at h
  have h0 := weightedEnergy_inv_bound _ _ _ (weightedEnergy_depth_weight_pos Q j) h
  rw [weightedEnergy_depth_weight_inv] at h0
  simpa [mul_assoc, mul_comm, mul_left_comm] using h0

theorem weightedEnergy_residual_eLpNorm_le {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (B : ℝ) (hu : MemLp u 2 (normalizedCubeMeasure Q)) (hdepth : ∀ j : ℕ, cubeBesovDepthSeminorm Q (1 / 2) 2 u j ≤ B) (j : ℕ) : eLpNorm (cubeProjectionResidual Q j u) 2 (normalizedCubeMeasure Q) ≤ ENNReal.ofReal (cubeBesovScaleWeight (-1 / 2) Q * B * (3 : ℝ) ^ (-(j : ℝ) / 2)) := by
  rw [weightedEnergy_eLpNorm_eq_ofReal_cubeLpNorm Q _ (weightedProjection_residual_memLp Q u j hu)]
  exact ENNReal.ofReal_le_ofReal (weightedEnergy_residual_lpNorm_le Q u B hu hdepth j)

theorem weightedEnergy_scaled_decay (S B : ℝ) (hS : 0 ≤ S) (hB : 0 ≤ B) (j : ℕ) : S * B * (3 : ℝ) ^ (-((j : ℝ) + 1) / 2) ≤ S * B * (3 : ℝ) ^ (-(j : ℝ) / 2) := by
  exact mul_le_mul_of_nonneg_left (weightedEnergy_residual_decay_mono j) (mul_nonneg hS hB)

theorem weightedEnergy_increment_eLpNorm_le {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (B : ℝ) (hB : 0 ≤ B) (hu : MemLp u 2 (normalizedCubeMeasure Q)) (hdepth : ∀ j : ℕ, cubeBesovDepthSeminorm Q (1 / 2) 2 u j ≤ B) (j : ℕ) : eLpNorm (cubeIncrement Q (j + 1) u) 2 (normalizedCubeMeasure Q) ≤ ENNReal.ofReal (2 * cubeBesovScaleWeight (-1 / 2) Q * B * (3 : ℝ) ^ (-(j : ℝ) / 2)) := by
  have h0 := weightedEnergy_residual_eLpNorm_le Q u B hu hdepth j
  have h1 := weightedEnergy_residual_eLpNorm_le Q u B hu hdepth (j + 1)
  have hs := cubeBesovScaleWeight_nonneg (-1 / 2) Q
  have hd := weightedEnergy_scaled_decay (cubeBesovScaleWeight (-1 / 2) Q) B hs hB j
  have h1' := h1.trans (ENNReal.ofReal_le_ofReal (by
    simpa only [Nat.cast_add, Nat.cast_one] using hd))
  exact (weightedEnergy_increment_triangle Q u j hu).trans
    ((add_le_add h0 h1').trans_eq (weightedEnergy_two_sum _ _ _ hs hB (by positivity)))

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
