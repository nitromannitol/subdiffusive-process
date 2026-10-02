import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMeasure
set_option autoImplicit false
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support

theorem weightedSobolev_finish_center_meas {d : ℕ} (Q : TriadicCube d) (b f : Vec d → ℝ) (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) : AEStronglyMeasurable (cubeFluctuation Q f) (weightedSobolevMeasure Q b) := by
  exact (weightedSobolevMeasure_aestronglyMeasurable Q b f hf).sub
    aestronglyMeasurable_const

theorem weightedSobolev_finish_memLp {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (p : ℝ≥0∞) (A : ℝ) (hf : AEStronglyMeasurable f μ) (hbound : eLpNorm f p μ ≤ ENNReal.ofReal A) : MemLp f p μ := by
  exact ⟨hf, hbound.trans_lt ENNReal.ofReal_lt_top⟩

theorem weightedSobolev_finish_norm_add_constant {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (c : ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hf : AEStronglyMeasurable f μ) : eLpNorm f p μ ≤ eLpNorm (fun x => f x - c) p μ + ENNReal.ofReal |c| := by
  have hg : AEStronglyMeasurable (fun x => f x - c) μ :=
    hf.sub aestronglyMeasurable_const
  have ht := eLpNorm_add_le hg (aestronglyMeasurable_const (b := c)) hp
  rw [weightedSobolev_centered_add f c,
    weightedSobolev_norm_const μ p (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) c,
    Real.enorm_eq_ofReal_abs] at ht
  exact ht

theorem weightedSobolev_finish_enn_bound (x : ℝ≥0∞) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : x ≤ ENNReal.ofReal A + ENNReal.ofReal B) : x ≤ ENNReal.ofReal (2 * (A + B)) := by
  have hm : x ≤ ENNReal.ofReal (A + B) := by
    simpa only [ENNReal.ofReal_add hA hB] using h
  exact hm.trans (ENNReal.ofReal_le_ofReal (by linarith))

theorem weightedSobolev_finish_enn_double (x : ℝ≥0∞) (A B : ℝ) (_hA : 0 ≤ A) (hB : 0 ≤ B) (h : x ≤ 2 * ENNReal.ofReal A) : x ≤ ENNReal.ofReal (2 * (A + B)) := by
  have heq : 2 * ENNReal.ofReal A = ENNReal.ofReal (2 * A) := by
    rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  rw [heq] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (by linarith))

theorem weightedSobolev_finish_one_le_weight (M p : ℝ) (hM : 0 ≤ M) (hp : 0 < p) : 1 ≤ (1 + M) ^ (1 / p) := by
  exact Real.one_le_rpow (by linarith) (by positivity)

theorem weightedSobolev_finish_weight_product (M p : ℝ) (hM : 0 ≤ M) : (8 * (1 + M)) ^ (1 / p) = 8 ^ (1 / p) * (1 + M) ^ (1 / p) := by
  exact Real.mul_rpow (by norm_num) (by linarith)

theorem weightedSobolev_finish_weight_square (M p : ℝ) (hM : 0 ≤ M) : ((1 + M) ^ (1 / p)) ^ (2 : ℕ) = (1 + M) ^ (2 / p) := by
  rw [← Real.rpow_two ((1 + M) ^ (1 / p)),
    ← Real.rpow_mul (by linarith : 0 ≤ 1 + M)]
  congr 1
  ring

theorem weightedSobolev_finish_scalar_enlarge (a b x t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 1 ≤ x) (ht : 0 ≤ t) : (2 * (a * x * t + b * t)) ^ 2 ≤ (2 * (a + b)) ^ 2 * x ^ 2 * t ^ 2 := by
  have h1 : 0 ≤ 2 * (a * x * t + b * t) := by positivity
  have hb2 : b ≤ b * x := by nlinarith
  have hbt : b * t ≤ b * x * t := mul_le_mul_of_nonneg_right hb2 ht
  have h2 : 2 * (a * x * t + b * t) ≤ 2 * (a + b) * x * t := by nlinarith
  have h3 := (sq_le_sq₀ h1 (h1.trans h2)).2 h2
  have h4 : (2 * (a + b) * x * t) ^ 2 =
      (2 * (a + b)) ^ 2 * x ^ 2 * t ^ 2 := by ring
  rwa [h4] at h3

theorem weightedSobolev_finish_scalar_factor (Cp Ce F G S E : ℝ) : 2 * (Cp * (F * G) * S * (Ce * S * E) + Ce * S ^ 2 * E) = 2 * ((Cp * F * Ce) * G * (S ^ 2 * E) + Ce * (S ^ 2 * E)) := by
  ring

theorem weightedSobolev_finish_sqrt_factor (S E : ℝ) (hE : 0 ≤ E) : (S ^ 2 * Real.sqrt E) ^ 2 = (S ^ 2) ^ 2 * E := by
  rw [mul_pow, Real.sq_sqrt hE]

theorem weightedSobolev_finish_scalar_bound (Cp Ce M S E p : ℝ) (hCp : 0 ≤ Cp) (hCe : 0 ≤ Ce) (hM : 0 ≤ M) (_hS : 0 ≤ S) (hE : 0 ≤ E) (hp : 0 < p) : (2 * (Cp * (8 * (1 + M)) ^ (1 / p) * S * (Ce * S * Real.sqrt E) + Ce * S ^ 2 * Real.sqrt E)) ^ 2 ≤ (2 * (Cp * 8 ^ (1 / p) * Ce + Ce)) ^ 2 * (1 + M) ^ (2 / p) * (S ^ 2) ^ 2 * E := by
  rw [weightedSobolev_finish_weight_product M p hM,
    weightedSobolev_finish_scalar_factor Cp Ce (8 ^ (1 / p))
      ((1 + M) ^ (1 / p)) S (Real.sqrt E)]
  have h := weightedSobolev_finish_scalar_enlarge (Cp * 8 ^ (1 / p) * Ce) Ce
    ((1 + M) ^ (1 / p)) (S ^ 2 * Real.sqrt E) (by positivity) hCe
    (weightedSobolev_finish_one_le_weight M p hM hp) (by positivity)
  rw [weightedSobolev_finish_weight_square M p hM,
    weightedSobolev_finish_sqrt_factor S E hE] at h
  convert h using 1 ; ring

theorem weightedSobolev_finish_p_enn (p : ℝ) (hp : 1 ≤ p) : 1 ≤ ENNReal.ofReal p := by
  exact ENNReal.one_le_ofReal.mpr hp

theorem weightedSobolev_finish_mean_branch {d : ℕ} (Q : TriadicCube d) (b f : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) (p : ℝ≥0∞) (hp : 1 ≤ p) (hf : MemLp f p (weightedSobolevMeasure Q b)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : eLpNorm (cubeFluctuation Q f) p (weightedSobolevMeasure Q b) ≤ ENNReal.ofReal A) (hz : (∫ x in openCubeSet Q, f x * b x) = 0) : eLpNorm f p (weightedSobolevMeasure Q b) ≤ ENNReal.ofReal (2 * (A + B)) := by
  apply weightedSobolev_finish_enn_double _ A B hA hB
  exact (weightedSobolevMeasure_centered_le Q b f hb p hp hf hz).trans
    (mul_le_mul_right hc 2)

theorem weightedSobolev_finish_constant_branch {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (c A B : ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : AEStronglyMeasurable f μ) (hc : eLpNorm (fun x => f x - c) p μ ≤ ENNReal.ofReal A) (hm : |c| ≤ B) : eLpNorm f p μ ≤ ENNReal.ofReal (2 * (A + B)) := by
  apply weightedSobolev_finish_enn_bound _ A B hA hB
  exact (weightedSobolev_finish_norm_add_constant μ f c p hp hf).trans
    (add_le_add hc (ENNReal.ofReal_le_ofReal hm))

theorem weightedSobolev_finish_norm_bound {d : ℕ} (Q : TriadicCube d) (b f : Vec d → ℝ) (hb : CoefficientOn (openCubeSet Q) b) (p : ℝ) (hp : 1 ≤ p) (hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : eLpNorm (cubeFluctuation Q f) (ENNReal.ofReal p) (weightedSobolevMeasure Q b) ≤ ENNReal.ofReal A) (hm : |cubeAverage Q f| ≤ B ∨ (∫ x in openCubeSet Q, f x * b x) = 0) : eLpNorm f (ENNReal.ofReal p) (weightedSobolevMeasure Q b) ≤ ENNReal.ofReal (2 * (A + B)) := by
  letI := weightedSobolevMeasure_isProbabilityMeasure Q b hb
  have hpE := weightedSobolev_finish_p_enn p hp
  have hcMem := weightedSobolev_finish_memLp (weightedSobolevMeasure Q b)
    (cubeFluctuation Q f) (ENNReal.ofReal p) A
    (weightedSobolev_finish_center_meas Q b f hf) hc
  have hfMem := weightedSobolev_memLp_of_centered (weightedSobolevMeasure Q b) f
    (cubeAverage Q f) (ENNReal.ofReal p) hcMem
  rcases hm with hm | hz
  · exact weightedSobolev_finish_constant_branch (weightedSobolevMeasure Q b) f
      (cubeAverage Q f) A B (ENNReal.ofReal p) hpE hA hB
      (weightedSobolevMeasure_aestronglyMeasurable Q b f hf) hc hm
  · exact weightedSobolev_finish_mean_branch Q b f hb (ENNReal.ofReal p) hpE hfMem
      A B hA hB hc hz

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
