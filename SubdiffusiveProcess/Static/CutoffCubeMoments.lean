import SubdiffusiveProcess.Section9.CutoffCubeLaws
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Cutoff mass moments on cubes above the cutoff

Partitioning into matching-cutoff cubes propagates both positive and
negative mass moments without a loss depending on the number of cells.
-/

open MeasureTheory ProbabilityTheory Homogenization SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- The reciprocal of a finite positive arithmetic mean is bounded by
the arithmetic mean of the reciprocals. -/
theorem inv_finset_average_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 < a i) :
    (((s.card : ℝ)⁻¹) * ∑ i ∈ s, a i)⁻¹ ≤
      ((s.card : ℝ)⁻¹) * ∑ i ∈ s, (a i)⁻¹ := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hsa : 0 < ∑ i ∈ s, a i := Finset.sum_pos ha hs
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (a i)) (fun i => Real.sqrt ((a i)⁻¹))
  have hprod : ∀ i ∈ s, Real.sqrt (a i) * Real.sqrt ((a i)⁻¹) = 1 := by
    intro i hi
    rw [← Real.sqrt_mul (ha i hi).le, mul_inv_cancel₀ (ha i hi).ne', Real.sqrt_one]
  have hsq0 : ∑ i ∈ s, Real.sqrt (a i) ^ 2 = ∑ i ∈ s, a i :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (ha i hi).le
  have hsq1 : ∑ i ∈ s, Real.sqrt ((a i)⁻¹) ^ 2 = ∑ i ∈ s, (a i)⁻¹ :=
    Finset.sum_congr rfl fun i hi => Real.sq_sqrt (inv_nonneg.mpr (ha i hi).le)
  rw [Finset.sum_congr rfl hprod, Finset.sum_const, nsmul_eq_mul, mul_one, hsq0, hsq1] at hcs
  rw [mul_inv, inv_inv]
  apply (mul_le_mul_iff_left₀ hn).mp
  apply (mul_le_mul_iff_right₀ hsa).mp
  have hn0 := hn.ne'
  have hsa0 := hsa.ne'
  field_simp
  simp only [inv_eq_one_div] at hcs
  nlinarith only [hcs]

/-- Minkowski's inequality for a normalized finite average, without a
cardinality cost. -/
theorem eLpNorm_finset_average_le {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (hs : s.Nonempty) (F : ι → Ω → ℝ)
    (hF : ∀ i ∈ s, Measurable (F i)) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (A : ℝ≥0∞) (hb : ∀ i ∈ s, eLpNorm (F i) p μ ≤ A) :
    eLpNorm (fun ω => (s.card : ℝ)⁻¹ * ∑ i ∈ s, F i ω) p μ ≤ A := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  calc
    _ = ENNReal.ofReal ((s.card : ℝ)⁻¹) * eLpNorm (∑ i ∈ s, F i) p μ := by
      have heq : (fun ω => (s.card : ℝ)⁻¹ * ∑ i ∈ s, F i ω) =
          (s.card : ℝ)⁻¹ • (∑ i ∈ s, F i) := by
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
      rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_nonneg.mpr hn.le)]
    _ ≤ ENNReal.ofReal ((s.card : ℝ)⁻¹) * ∑ i ∈ s, eLpNorm (F i) p μ := by
      apply mul_le_mul_right _ _
      exact eLpNorm_sum_le (fun i hi => (hF i hi).aestronglyMeasurable) hp
    _ ≤ ENNReal.ofReal ((s.card : ℝ)⁻¹) * ∑ _i ∈ s, A := by
      apply mul_le_mul_right _ _
      exact Finset.sum_le_sum hb
    _ = A := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
        ENNReal.ofReal_inv_of_pos hn, ENNReal.ofReal_natCast]
      have hc : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
      rw [ENNReal.inv_mul_cancel hc ENNReal.coe_ne_top, one_mul]

theorem cutoffCubeAverage_pos {d : ℕ} (M : GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (ω : PotentialSample d) :
    0 < SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω := by
  rw [SubdiffusiveProcess.Section9.cutoffCubeAverage, cubeAverage_eq_integral_normalizedCubeMeasure]
  have hi : Integrable (aCutoff M L ω) (normalizedCubeMeasure Q) :=
    (SubdiffusiveProcess.CoarseGrainingVocab.exactCircIntegrable_of_continuous Q
      (continuous_aCutoff M L ω)).block 0 Q (by
        simp only [descendantsAtDepth_zero, Finset.mem_singleton])
  rw [integral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (aCutoff_pos M L ω x).le) hi]
  have hs : Function.support (aCutoff M L ω) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (aCutoff_pos M L ω x).ne'
  rw [hs, normalizedCubeMeasure_apply_univ]
  exact zero_lt_one

/-- The exact partition identity for the positive finite-cutoff mass. -/
theorem cutoffCubeAverage_partition {d : ℕ} (M : GMCModel d) (L : ℕ)
    (Q : TriadicCube d) (j : ℕ) (ω : PotentialSample d) :
    SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, SubdiffusiveProcess.Section9.cutoffCubeAverage M L R ω := by
  have hi : IntegrableOn (aCutoff M L ω) (cubeSet Q) volume :=
    ((continuous_aCutoff M L ω).continuousOn.integrableOn_compact
      (isCompact_closedBall (cubeCenter Q) (cubeRadius Q))).mono_set
        (cubeSet_subset_closedBall Q)
  exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _ hi

/-- Positive moments on every cube above the cutoff are bounded by the
matching-cutoff origin-cube moment. -/
theorem eLpNorm_cutoffCubeAverage_le_origin {d : ℕ} (M : GMCModel d)
    {L k : ℕ} (hLk : L ≤ k) (Q : TriadicCube d) (hQ : Q.scale = (k : ℤ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q) p M.P.toMeasure ≤
      eLpNorm (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M L) p M.P.toMeasure := by
  classical
  let s := descendantsAtDepth Q (k - L)
  have hs : s.Nonempty := descendantsAtDepth_nonempty Q (k - L)
  have hscale : ∀ R ∈ s, R.scale = (L : ℤ) := by
    intro R hR
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hQ]
    omega
  have heq : SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q =
      fun ω => (s.card : ℝ)⁻¹ * ∑ R ∈ s, SubdiffusiveProcess.Section9.cutoffCubeAverage M L R ω := by
    funext ω
    exact cutoffCubeAverage_partition M L Q (k - L) ω
  rw [heq]
  apply eLpNorm_finset_average_le _ s hs _
    (fun R _ => SubdiffusiveProcess.Section9.measurable_cutoffCubeAverage M L R) p hp
  intro R hR
  exact (SubdiffusiveProcess.Section9.cutoffCubeAverage_identDistrib_originCubeAverage M L R
    (hscale R hR)).eLpNorm_eq p |>.le

/-- Negative moments propagate above the cutoff by the same normalized
partition, using the harmonic-mean inequality. -/
theorem eLpNorm_inverse_cutoffCubeAverage_le_origin {d : ℕ} (M : GMCModel d)
    {L k : ℕ} (hLk : L ≤ k) (Q : TriadicCube d) (hQ : Q.scale = (k : ℤ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (fun ω => (SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω)⁻¹) p M.P.toMeasure ≤
      eLpNorm (fun ω => (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M L ω)⁻¹) p M.P.toMeasure := by
  classical
  let s := descendantsAtDepth Q (k - L)
  have hs : s.Nonempty := descendantsAtDepth_nonempty Q (k - L)
  have hscale : ∀ R ∈ s, R.scale = (L : ℤ) := by
    intro R hR
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hQ]
    omega
  let F : TriadicCube d → PotentialSample d → ℝ :=
    fun R ω => (SubdiffusiveProcess.Section9.cutoffCubeAverage M L R ω)⁻¹
  calc
    _ ≤ eLpNorm (fun ω => (s.card : ℝ)⁻¹ * ∑ R ∈ s, F R ω) p M.P.toMeasure := by
      apply eLpNorm_mono_ae
      filter_upwards with ω
      have hleft : 0 ≤ (SubdiffusiveProcess.Section9.cutoffCubeAverage M L Q ω)⁻¹ :=
        inv_nonneg.mpr (cutoffCubeAverage_pos M L Q ω).le
      have hright : 0 ≤ (s.card : ℝ)⁻¹ * ∑ R ∈ s, F R ω := by
        apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact Finset.sum_nonneg fun R _ => inv_nonneg.mpr (cutoffCubeAverage_pos M L R ω).le
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright,
        cutoffCubeAverage_partition M L Q (k - L) ω]
      exact inv_finset_average_le s hs _ (fun R _ => cutoffCubeAverage_pos M L R ω)
    _ ≤ _ := by
      apply eLpNorm_finset_average_le _ s hs F
        (fun R _ => (SubdiffusiveProcess.Section9.measurable_cutoffCubeAverage M L R).inv) p hp
      intro R hR
      exact ((SubdiffusiveProcess.Section9.cutoffCubeAverage_identDistrib_originCubeAverage M L R
        (hscale R hR)).comp measurable_inv).eLpNorm_eq p |>.le

end SubdiffusiveProcess.Static
