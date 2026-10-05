module

public import SubdiffusiveProcess.Static.HarmonicCellLocalBudget
public import SubdiffusiveProcess.Static.HarmonicCellSmoothDatum

@[expose] public section

/-! # Smooth-gradient and measurable-energy readouts for cell joining -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The sup-norm ball is contained in a dimension-comparable Euclidean ball. -/
theorem metricBall_subset_euclideanBall_dim {d : ℕ} (hd : 1 ≤ d)
    (x : Vec d) {r : ℝ} (hr : 0 < r) :
    Metric.ball x r ⊆ euclideanBall x ((d : ℝ) * r) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  intro y hy
  have hn : ‖y - x‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have heuc : euclideanNorm (y - x) < (d : ℝ) * r :=
    (euclideanNorm_le_dimension_mul_norm _).trans_lt
      (mul_lt_mul_of_pos_left hn (by linarith))
  change vecNormSq (y - x) < ((d : ℝ) * r) ^ 2
  rw [← euclideanNorm_sq]
  exact (sq_lt_sq₀ (euclideanNorm_nonneg _) (by positivity)).mpr heuc

/-- Weighted native vector energy has the lower-integral measurable carrier. -/
theorem aemeasurable_ofReal_weighted_vecSq {d : ℕ} {U : Set (Vec d)}
    (a : Vec d → ℝ) (ha : Measurable a) (F : Vec d → Vec d)
    (hF : MemVectorL2 U F) :
    AEMeasurable (fun x => ENNReal.ofReal (a x * vecNormSq (F x))) (volume.restrict U) := by
  have h := (memHilbertVectorL2_hilbertifyVecField hF).norm.aestronglyMeasurable
  have hh : AEStronglyMeasurable (fun x => euclideanNorm (F x)) (volume.restrict U) := by
    simpa only [hilbertifyVecField, ← euclideanNorm_eq_norm_ofVec] using h
  simp_rw [← euclideanNorm_sq]
  exact (ha.aemeasurable.mul (hh.pow 2).aemeasurable).ennreal_ofReal

/-- A smooth-gradient bound prices the literal truncated energy by the full
Euclidean ball's exact volume. Only the coefficient inside the cell is used. -/
theorem truncated_cell_smooth_energy_le {d : ℕ} [NeZero d]
    (a : Vec d → ℝ) (F : Vec d → Vec d) (x : Vec d)
    {r R H : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (ha : ∀ y ∈ openCubeSet (originCube d 0), a y ≤ R)
    (hF : ∀ y, euclideanNorm (F y) ≤ H) :
    ∫⁻ y in euclideanBall x r ∩ openCubeSet (originCube d 0),
      ENNReal.ofReal (a y * vecNormSq (F y)) ≤
      ENNReal.ofReal (R * H ^ 2 * (volume (euclideanBall (0 : Vec d) 1)).toReal * r ^ d) := by
  let W := euclideanBall x r ∩ openCubeSet (originCube d 0)
  have hW : MeasurableSet W := (isOpen_euclideanBall x r).measurableSet.inter
    (isOpen_openCubeSet _).measurableSet
  calc
    _ ≤ ∫⁻ _y in W, ENNReal.ofReal (R * H ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hW] with y hy
      apply ENNReal.ofReal_le_ofReal
      have hs : vecNormSq (F y) ≤ H ^ 2 := by
        rw [← euclideanNorm_sq]
        exact (sq_le_sq₀ (euclideanNorm_nonneg _) hH).mpr (hF y)
      exact (mul_le_mul_of_nonneg_right (ha y hy.2) (vecNormSq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hs hR)
    _ = ENNReal.ofReal (R * H ^ 2) * volume W := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (R * H ^ 2) * volume (euclideanBall x r) :=
      mul_le_mul_right (measure_mono Set.inter_subset_left) _
    _ = _ := by
      have hv : volume (euclideanBall x r) ≠ ⊤ :=
        Homogenization.Book.Ch01.volume_euclideanBall_ne_top x r
      rw [← ENNReal.ofReal_toReal hv, ← ENNReal.ofReal_mul (by positivity),
        SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.volume_euclideanBall_toReal_eq_unit_mul_pow x hr]
      simp only [SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastUnitBall]
      congr 1
      ring

/-- Every interior unit-cell point belongs to its closed sup-norm ball. -/
theorem unitCell_mem_closedBall {d : ℕ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d 0)) :
    x ∈ Metric.closedBall (0 : Vec d) (1 / 2) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
  intro i
  have hi := (mem_openCubeSet_originCube_iff.mp hx) i
  norm_num only [zpow_zero, mul_one, one_mul] at hi
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hi.1, hi.2]

/-- The smooth part on a sup-norm ball pays the exact cube-ball volume. -/
theorem truncated_metric_cell_smooth_energy_le {d : ℕ}
    (a : Vec d → ℝ) (F : Vec d → Vec d) (x : Vec d)
    {r R H : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (ha : ∀ y ∈ openCubeSet (originCube d 0), a y ≤ R)
    (hF : ∀ y, euclideanNorm (F y) ≤ H) :
    ∫⁻ y in Metric.ball x r ∩ openCubeSet (originCube d 0),
      ENNReal.ofReal (a y * vecNormSq (F y)) ≤
      ENNReal.ofReal (R * H ^ 2 * (2 * r) ^ d) := by
  let W := Metric.ball x r ∩ openCubeSet (originCube d 0)
  have hW : MeasurableSet W := measurableSet_ball.inter (isOpen_openCubeSet _).measurableSet
  calc
    _ ≤ ∫⁻ _y in W, ENNReal.ofReal (R * H ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hW] with y hy
      apply ENNReal.ofReal_le_ofReal
      have hs : vecNormSq (F y) ≤ H ^ 2 := by
        rw [← euclideanNorm_sq]
        exact (sq_le_sq₀ (euclideanNorm_nonneg _) hH).mpr (hF y)
      exact (mul_le_mul_of_nonneg_right (ha y hy.2) (vecNormSq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hs hR)
    _ = ENNReal.ofReal (R * H ^ 2) * volume W := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (R * H ^ 2) * volume (Metric.ball x r) :=
      mul_le_mul_right (measure_mono Set.inter_subset_left) _
    _ = _ := by
      rw [Real.volume_pi_ball x hr, Fintype.card_fin,
        ← ENNReal.ofReal_mul (by positivity)]

end SubdiffusiveProcess.Static
