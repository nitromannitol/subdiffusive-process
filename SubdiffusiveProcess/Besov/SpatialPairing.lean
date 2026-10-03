module

public import SubdiffusiveProcess.Besov.PartitionAverages

@[expose] public section

open MeasureTheory MeasureTheory.Measure SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- Pass integrability on a cell to its normalized probability measure. -/
theorem integrable_normalizedCubeMeasure {d : ℕ} (R : TriadicCube d) {g : Vec d → ℝ}
    (hg : IntegrableOn g (cubeSet R)) : Integrable g (normalizedCubeMeasure R) := by
  rw [normalizedCubeMeasure, cubeMeasure]
  exact (integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos R)))
    ENNReal.ofReal_ne_top).mpr hg

/-- Local L1 fluctuations are integrable whenever the original function is. -/
theorem fluctuation_memLp_one {d : ℕ} (R : TriadicCube d) {g : Vec d → ℝ}
    (hg : IntegrableOn g (cubeSet R)) :
    MemLp (cubeFluctuation R g) 1 (normalizedCubeMeasure R) := by
  exact memLp_one_iff_integrable.mpr
    ((integrable_normalizedCubeMeasure R hg).sub (integrable_const _))

/-- The next projection is bounded by the largest absolute child mean. -/
theorem projection_succ_maximalChild_bound {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (f : Vec d → ℝ) (hR : R ∈ descendantsAtDepth Q j) :
    ∀ᵐ x ∂normalizedCubeMeasure R,
      |cubeProjection Q (j + 1) f x| ≤ |cubeAverage (maximalChild R f) f| := by
  rw [normalizedCubeMeasure, cubeMeasure]
  apply ae_smul_measure
  apply (ae_restrict_iff' (measurableSet_cubeSet R)).mpr
  apply Filter.Eventually.of_forall
  intro x hx
  obtain ⟨S, hS, hxS⟩ := exists_mem_childCubes_of_mem_cubeSet hx
  have hSQ : S ∈ descendantsAtDepth Q (j + 1) :=
    mem_descendantsAtDepth_succ_iff.mpr ⟨R, hR, hS⟩
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hSQ hxS]
  exact maximalChild_le R S f hS

/-- The local pairing uses the largest child mean against an L1 oscillation. -/
theorem local_spatial_pairing_le {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (f g : Vec d → ℝ) (hR : R ∈ descendantsAtDepth Q j)
    (hg : IntegrableOn g (cubeSet R)) :
    ENNReal.ofReal |cubeAverage R
      (fun x => cubeProjection Q (j + 1) f x * cubeProjectionResidual Q j g x)| ≤
      ENNReal.ofReal |cubeAverage (maximalChild R f) f| *
        eLpNorm (cubeFluctuation R g) 1 (normalizedCubeMeasure R) := by
  have hgf := fluctuation_memLp_one R hg
  have hgf' : MemLp (cubeFluctuation R g) (ENNReal.conjExponent ⊤)
      (normalizedCubeMeasure R) := by simpa [ENNReal.conjExponent] using hgf
  have hproj := cubeProjection_succ_memLp_of_mem_descendantsAtDepth ⊤ f hR
  have hlocal := abs_cubeAverage_mul_cubeProjectionResidual_le_mul_cubeLpNorm_cubeBesovOscillation_of_mem_descendantsAtDepth
    ⊤ (cubeProjection Q (j + 1) f) g hR hproj hgf' (by simp)
  have hnorm : cubeLpNorm R ⊤ (cubeProjection Q (j + 1) f) ≤
      |cubeAverage (maximalChild R f) f| := by
    apply ENNReal.toReal_le_of_le_ofReal (abs_nonneg _)
    rw [eLpNorm_exponent_top hproj.aestronglyMeasurable]
    exact eLpNormEssSup_le_of_ae_bound (by simpa only [Real.norm_eq_abs] using
      (projection_succ_maximalChild_bound f hR))
  have hlocal' : |cubeAverage R
      (fun x => cubeProjection Q (j + 1) f x * cubeProjectionResidual Q j g x)| ≤
      |cubeAverage (maximalChild R f) f| * cubeLpNorm R 1 (cubeFluctuation R g) := by
    simpa [ENNReal.conjExponent, cubeBesovOscillation] using hlocal.trans
      (mul_le_mul_of_nonneg_right hnorm (cubeBesovOscillation_nonneg R _ g))
  exact (ENNReal.ofReal_le_ofReal hlocal').trans_eq (by
    rw [ENNReal.ofReal_mul (abs_nonneg _), cubeLpNorm, ENNReal.ofReal_toReal hgf.eLpNorm_lt_top.ne])

/-- Absolute averages of finite real sums are bounded by the averaged absolute values. -/
theorem ofReal_abs_normalized_sum_le {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (a : ι → ℝ) :
    ENNReal.ofReal |(S.card : ℝ)⁻¹ * ∑ i ∈ S, a i| ≤
      (S.card : ℝ≥0∞)⁻¹ * ∑ i ∈ S, ENNReal.ofReal |a i| := by
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hcard.le),
    ENNReal.ofReal_mul (inv_nonneg.mpr hcard.le), ENNReal.ofReal_inv_of_pos hcard,
    ENNReal.ofReal_natCast]
  apply mul_le_mul_right
  exact (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans_eq
    (ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg (a i))

/-- The normalized pairing increment obeys spatial Holder for any exponent r≥1. -/
theorem spatial_pairing_le_depthAggregations {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (r : ℝ≥0∞) (hr : 1 ≤ r) (f g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet Q)) :
    ENNReal.ofReal |cubeAverage Q
      (fun x => cubeProjection Q (j + 1) f x * cubeProjectionResidual Q j g x)| ≤
      depthAggregation Q j r (fun R => ENNReal.ofReal |cubeAverage (maximalChild R f) f|) *
        depthAggregation Q j (ENNReal.conjExponent r)
          (fun R => eLpNorm (cubeFluctuation R g) 1 (normalizedCubeMeasure R)) := by
  classical
  let H : Vec d → ℝ := fun x => cubeProjection Q (j + 1) f x * cubeProjectionResidual Q j g x
  have hint : IntegrableOn H (cubeSet Q) := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    apply (integrableOn_finset_iUnion (s := descendantsAtDepth Q j) (t := cubeSet)).mpr
    intro R hR
    exact integrableOn_mul_projectionResidual_projection_succ_of_mem_descendantsAtDepth
      1 g f hR (fluctuation_memLp_one R (hg.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)))
      (by simpa [cubeBesovConjExponent, ENNReal.conjExponent] using
        cubeProjection_succ_memLp_of_mem_descendantsAtDepth ⊤ f hR) le_rfl
  have hcard0 : ((descendantsAtDepth Q j).card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)).ne'
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn (Q := Q) (j := j) (f := H) hint]
  change ENNReal.ofReal |((descendantsAtDepth Q j).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth Q j, cubeAverage R H| ≤ _
  calc
    _ ≤ ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, ENNReal.ofReal |cubeAverage R H| :=
      ofReal_abs_normalized_sum_le _ (descendantsAtDepth_nonempty Q j) _
    _ ≤ ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          ENNReal.ofReal |cubeAverage (maximalChild R f) f| *
            eLpNorm (cubeFluctuation R g) 1 (normalizedCubeMeasure R) := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro R hR
      exact local_spatial_pairing_le f g hR
        (hg.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR))
    _ ≤ _ := finiteAggregation_holder _ _ (ENNReal.inv_ne_zero.mpr (by simp))
      (ENNReal.inv_ne_top.mpr hcard0) r hr _ _

/-- Spatial comparison of a telescope increment with the paper's two spatial families. -/
theorem spatial_pairing_le_averages {d : ℕ} (m : ℤ) (j : ℕ)
    (r : ℝ≥0∞) (hr : 1 ≤ r) (f g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet (originCube d m))) :
    ENNReal.ofReal |cubeAverage (originCube d m)
      (fun x => cubeProjection (originCube d m) (j + 1) f x *
        cubeProjectionResidual (originCube d m) j g x)| ≤
      (3 ^ d : ℕ) * (3 ^ d : ℕ) *
        (averageLr (negativeCentres d m (m - (j + 1))) r
          (fun z => ENNReal.ofReal |⨍ x in translatedCube d (m - (j + 1)) z, f x|) *
        averageLr (positiveCentres d m (m - j)) (ENNReal.conjExponent r)
          (fun z => normalizedLp (translatedCube d (m - j) z) 1
            (fun x => g x - ⨍ y in translatedCube d (m - j) z, g y))) := by
  letI : ENNReal.HolderConjugate r (ENNReal.conjExponent r) :=
    ENNReal.HolderConjugate.conjExponent hr
  have hr' : 1 ≤ ENNReal.conjExponent r :=
    ENNReal.HolderConjugate.one_le _ r
  have hsp := spatial_pairing_le_depthAggregations (originCube d m) j r hr f g hg
  have h1 := maximalChild_depthAggregation_le (originCube d m) j r hr f
  have h2 := positive_depthAggregation_le m j (ENNReal.conjExponent r) hr' g
  rw [← negative_average_eq_depthAggregation] at h1
  exact hsp.trans ((mul_le_mul' h1 h2).trans_eq (by ac_rfl))

end SubdiffusiveProcess.Besov
