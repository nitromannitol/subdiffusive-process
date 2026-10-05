module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldOneScore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldOneDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorField
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.CombinedCoefficientRatio

@[expose] public section

/-!
# Deterministic shell-field window rearrangement

The first step of `l.sum.the.errors` expands every finite shell block into its
one-shell constituents before interchanging the scale indices.  This module
records that expansion on the literal `supNormOn` carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Spatial translation acts inside each one-shell sigma-field. -/
theorem measurable_translatePotentialSample_shellSigma {d : ℕ}
    (i : ℕ) (z : Vec d) :
    Measurable[shellSigma d i, shellSigma d i]
      (translatePotentialSample (d := d) z) := by
  unfold shellSigma
  rw [measurable_iff_comap_le, MeasurableSpace.comap_comp]
  change MeasurableSpace.comap
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z ∘
        fun omega : Sample d ↦ omega i)
      inferInstance ≤
    MeasurableSpace.comap (fun omega : Sample d ↦ omega i) inferInstance
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z).comap_le

/-- Stationarity transports one-sided Gamma tails through sample
translation, without a measurability premise on the tail event. -/
theorem isBigOWith_comp_translatePotentialSample {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    {X : Sample d → ℝ} {sigma A : ℝ}
    (hX : IsBigOWith M.P.toMeasure (gammaSigma sigma) X A) :
    IsBigOWith M.P.toMeasure (gammaSigma sigma)
      (fun omega ↦ X (translatePotentialSample z omega)) A := by
  intro t ht
  have hset : upperTailEvent
      (fun omega ↦ X (translatePotentialSample z omega)) (A * t) =
      translatePotentialSample z ⁻¹' upperTailEvent X (A * t) := rfl
  rw [hset]
  change (M.P.toMeasure
    (translatePotentialSample z ⁻¹' upperTailEvent X (A * t))).toReal ≤ _
  rw [Section6Covariance.measure_preimage_translatePotentialSample]
  exact hX ht

/-- A finite shell block on `cube k` is bounded by the sum of the genuinely
one-shell `fieldOneCubeMajorant`s. -/
theorem supNormOn_shellBlock_le_sum_fieldOneCubeMajorant
    {d : ℕ} (k j : ℕ) (omega : Sample d) :
    supNormOn (cube d (k : ℤ)) (shellBlock k j omega) ≤
      ∑ i ∈ Finset.Icc (j + 1) k, fieldOneCubeMajorant i k omega := by
  unfold supNormOn
  apply csSup_le
  · refine ⟨|shellBlock k j omega 0|, 0, ?_, rfl⟩
    · rw [cube, mem_openCubeSet_originCube_iff]
      intro a
      have hpow : 0 < (3 : ℝ) ^ (k : ℤ) := zpow_pos (by norm_num) _
      constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  · rintro _ ⟨x, hx, rfl⟩
    unfold shellBlock
    calc
      |∑ i ∈ Finset.Icc (j + 1) k, omega i x| ≤
          ∑ i ∈ Finset.Icc (j + 1) k, |omega i x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Icc (j + 1) k,
          fieldOneCubeMajorant i k omega := by
        apply Finset.sum_le_sum
        intro i hi
        have hatom := fieldOne_supNormOn_le_largeCubeShellG2
          (d := d) (i := i) (k := k) omega
        have hpoint : |omega i x| ≤
            |omega i x| + (3 : ℝ) ^ i *
              euclideanNorm (shellGradient (omega i) x) := by
          exact le_add_of_nonneg_right
            (mul_nonneg (by positivity) (euclideanNorm_nonneg _))
        have hsup : |omega i x| + (3 : ℝ) ^ i *
              euclideanNorm (shellGradient (omega i) x) ≤
            supNormOn (cube d (k : ℤ)) (fun y ↦
              |omega i y| + (3 : ℝ) ^ i *
                euclideanNorm (shellGradient (omega i) y)) := by
          unfold supNormOn
          apply le_csSup
          · exact ⟨fieldOneCubeMajorant i k omega, by
              rintro a ⟨y, hy, rfl⟩
              rw [abs_of_nonneg (add_nonneg (abs_nonneg _)
                (mul_nonneg (by positivity) (euclideanNorm_nonneg _)))]
              exact (fieldOne_atom_le_largeCubeShellG2 omega hy).trans
                (by unfold fieldOneCubeMajorant; exact le_rfl)⟩
          · exact ⟨x, hx, by
              rw [abs_of_nonneg (add_nonneg (abs_nonneg _)
                (mul_nonneg (by positivity) (euclideanNorm_nonneg _)))]⟩
        exact hpoint.trans (hsup.trans hatom)

/-- One shell on its observation cube is bounded by the same one-shell
majorant. -/
theorem supNormOn_shell_le_fieldOneCubeMajorant
    {d : ℕ} (i k : ℕ) (omega : Sample d) :
    supNormOn (cube d (k : ℤ)) (omega i) ≤ fieldOneCubeMajorant i k omega := by
  unfold supNormOn
  apply csSup_le
  · refine ⟨|omega i 0|, 0, ?_, rfl⟩
    rw [cube, mem_openCubeSet_originCube_iff]
    intro a
    have hpow : 0 < (3 : ℝ) ^ (k : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  · rintro _ ⟨x, hx, rfl⟩
    exact (le_add_of_nonneg_right
      (mul_nonneg (by positivity) (euclideanNorm_nonneg _))).trans
        ((fieldOne_atom_le_largeCubeShellG2 omega hx).trans_eq rfl)

/-- The literal finite-block supremum in `accumulatedError`, at the origin. -/
noncomputable def accumulatedBlockSup {d : ℕ}
    (k : ℕ) (s : ℝ) (omega : Sample d) : ℝ :=
  sSup {a : ℝ | ∃ j ≤ k,
    a = (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
      supNormOn (cube d (k : ℤ)) (shellBlock k j omega)}

/-- Expanding the finite shell block and moving its weight from the lower
cutoff `j` to each retained shell `i` gives a one-shell row. -/
theorem accumulatedBlockSup_le_weighted_fieldOneCubeMajorant
    {d : ℕ} (k : ℕ) {s : ℝ} (hs : 0 < s) (omega : Sample d) :
    accumulatedBlockSup k s omega ≤
      ∑ i ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
          fieldOneCubeMajorant i k omega := by
  unfold accumulatedBlockSup
  apply csSup_le
  · refine ⟨(3 : ℝ) ^ (-(s / 8) * (k : ℝ)) *
        supNormOn (cube d (k : ℤ)) (shellBlock k 0 omega), 0, by omega, ?_⟩
    simp only [Nat.cast_zero, sub_zero]
  · rintro a ⟨j, hjk, rfl⟩
    have hblock := supNormOn_shellBlock_le_sum_fieldOneCubeMajorant
      (d := d) k j omega
    have hweight0 : 0 ≤
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) := by positivity
    calc
      (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
          supNormOn (cube d (k : ℤ)) (shellBlock k j omega) ≤
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
          ∑ i ∈ Finset.Icc (j + 1) k, fieldOneCubeMajorant i k omega :=
        mul_le_mul_of_nonneg_left hblock hweight0
      _ = ∑ i ∈ Finset.Icc (j + 1) k,
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
            fieldOneCubeMajorant i k omega := by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.Icc (j + 1) k,
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
            fieldOneCubeMajorant i k omega := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : j ≤ i := by
          exact (Nat.le_succ j).trans (Finset.mem_Icc.mp hi).1
        have hijR : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hij
        have hdiff : (k : ℝ) - (i : ℝ) ≤ (k : ℝ) - (j : ℝ) :=
          sub_le_sub_left hijR _
        have hexp : -(s / 8) * ((k : ℝ) - (j : ℝ)) ≤
            -(s / 8) * ((k : ℝ) - (i : ℝ)) := by
          exact mul_le_mul_of_nonpos_left hdiff (by linarith)
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
          (fieldOneCubeMajorant_nonneg i k omega)
      _ ≤ ∑ i ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
            fieldOneCubeMajorant i k omega := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          rw [Finset.mem_range]
          exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hi).2
        · intro i hirange hinot
          exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (fieldOneCubeMajorant_nonneg i k omega)

/-- The explicit `omega 0` term is the zeroth member of the same weighted
one-shell row. -/
theorem weighted_shellZero_le_weighted_fieldOneCubeMajorant
    {d : ℕ} (k : ℕ) (s : ℝ) (omega : Sample d) :
    (3 : ℝ) ^ (-(s / 8) * k) * supNormOn (cube d (k : ℤ)) (omega 0) ≤
      (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (0 : ℝ))) *
        fieldOneCubeMajorant 0 k omega := by
  have h := supNormOn_shell_le_fieldOneCubeMajorant (d := d) 0 k omega
  simpa only [Nat.cast_zero, sub_zero] using!
    mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by norm_num) _)

/-! ## Translation to the literal accumulated-error centre -/

theorem supNormOn_translatedCube_shellBlock_eq_origin_translate
    {d : ℕ} (k j : ℕ) (z : Vec d) (omega : Sample d) :
    supNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega) =
      supNormOn (cube d (k : ℤ))
        (shellBlock k j (translatePotentialSample z omega)) := by
  rw [show cube d (k : ℤ) = translatedCube d (k : ℤ) 0 by
    unfold translatedCube; simp]
  calc
    supNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega) =
        supNormOn (translatedCube d (k : ℤ) 0)
          (fun x ↦ shellBlock k j omega (x + z)) := by
      simpa only [add_zero] using!
        (Section6Covariance.supNormOn_translatedCube_comp_add z 0
          (k : ℤ) (shellBlock k j omega)).symm
    _ = supNormOn (translatedCube d (k : ℤ) 0)
        (shellBlock k j (translatePotentialSample z omega)) := by
      congr 2

theorem supNormOn_translatedCube_shell_eq_origin_translate
    {d : ℕ} (i k : ℕ) (z : Vec d) (omega : Sample d) :
    supNormOn (translatedCube d (k : ℤ) z) (omega i) =
      supNormOn (cube d (k : ℤ)) (translatePotentialSample z omega i) := by
  rw [show cube d (k : ℤ) = translatedCube d (k : ℤ) 0 by
    unfold translatedCube; simp]
  calc
    supNormOn (translatedCube d (k : ℤ) z) (omega i) =
        supNormOn (translatedCube d (k : ℤ) 0)
          (fun x ↦ omega i (x + z)) := by
      simpa only [add_zero] using!
        (Section6Covariance.supNormOn_translatedCube_comp_add z 0
          (k : ℤ) (omega i)).symm
    _ = supNormOn (translatedCube d (k : ℤ) 0)
        (translatePotentialSample z omega i) := by rfl

/-- Literal finite shell-block supremum at an arbitrary centre. -/
noncomputable def translatedAccumulatedBlockSup {d : ℕ}
    (k : ℕ) (z : Vec d) (s : ℝ) (omega : Sample d) : ℝ :=
  sSup {a : ℝ | ∃ j ≤ k,
    a = (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (j : ℝ))) *
      supNormOn (translatedCube d (k : ℤ) z) (shellBlock k j omega)}

theorem translatedAccumulatedBlockSup_eq_origin_translate
    {d : ℕ} (k : ℕ) (z : Vec d) (s : ℝ) (omega : Sample d) :
    translatedAccumulatedBlockSup k z s omega =
      accumulatedBlockSup k s (translatePotentialSample z omega) := by
  unfold translatedAccumulatedBlockSup accumulatedBlockSup
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  apply exists_congr
  intro j
  apply and_congr_right
  intro hj
  rw [supNormOn_translatedCube_shellBlock_eq_origin_translate]

/-- The finite shell-block and explicit zeroth-shell terms at an arbitrary
centre are controlled by one translated one-shell row. -/
theorem translatedBlockSup_add_shellZero_le_weighted_fieldOneCubeMajorant
    {d : ℕ} (k : ℕ) (z : Vec d) {s : ℝ} (hs : 0 < s)
    (omega : Sample d) :
    translatedAccumulatedBlockSup k z s omega +
        (3 : ℝ) ^ (-(s / 8) * k) *
          supNormOn (translatedCube d (k : ℤ) z) (omega 0) ≤
      2 * ∑ i ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
          fieldOneCubeMajorant i k (translatePotentialSample z omega) := by
  have hblock := accumulatedBlockSup_le_weighted_fieldOneCubeMajorant
    (d := d) k hs (translatePotentialSample z omega)
  have hzero := weighted_shellZero_le_weighted_fieldOneCubeMajorant
    (d := d) k s (translatePotentialSample z omega)
  rw [← translatedAccumulatedBlockSup_eq_origin_translate] at hblock
  rw [← supNormOn_translatedCube_shell_eq_origin_translate] at hzero
  have hterm :
      (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (0 : ℝ))) *
          fieldOneCubeMajorant 0 k (translatePotentialSample z omega) ≤
        ∑ i ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
            fieldOneCubeMajorant i k (translatePotentialSample z omega) := by
    simpa only [Nat.cast_zero] using! Finset.single_le_sum
      (f := fun i : ℕ ↦
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
          fieldOneCubeMajorant i k (translatePotentialSample z omega))
      (fun i _ ↦ mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (fieldOneCubeMajorant_nonneg i k _))
      (Finset.mem_range.mpr (by omega : 0 < k + 1))
  calc
    _ ≤ (∑ i ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
            fieldOneCubeMajorant i k (translatePotentialSample z omega)) +
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (0 : ℝ))) *
          fieldOneCubeMajorant 0 k (translatePotentialSample z omega) :=
      add_le_add hblock hzero
    _ ≤ 2 * ∑ i ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
            fieldOneCubeMajorant i k (translatePotentialSample z omega) := by
      linarith

/-- The triangular one-shell convolution obtained by summing the finite field
part of `accumulatedError` over `[n,m]`. -/
noncomputable def accumulatedFiniteFieldWindowConvolution {d : ℕ}
    (z : Vec d) (s : ℝ)
    (n m : ℕ) (omega : Sample d) : ℝ :=
  ∑ k ∈ Finset.Icc n m, ∑ i ∈ Finset.range (k + 1),
    (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
      fieldOneCubeMajorant i k (translatePotentialSample z omega)

/-- Summed deterministic shell-field rearrangement from Step 1 of
`l.sum.the.errors`. -/
theorem sum_translatedBlockSup_add_shellZero_le_finiteFieldWindowConvolution
    {d : ℕ} (z : Vec d)
    {s : ℝ} (hs : 0 < s) (n m : ℕ) (omega : Sample d) :
    (∑ k ∈ Finset.Icc n m,
        (translatedAccumulatedBlockSup k z s omega +
          (3 : ℝ) ^ (-(s / 8) * k) *
            supNormOn (translatedCube d (k : ℤ) z) (omega 0))) ≤
      2 * accumulatedFiniteFieldWindowConvolution z s n m omega := by
  unfold accumulatedFiniteFieldWindowConvolution
  calc
    _ ≤ ∑ k ∈ Finset.Icc n m,
        2 * ∑ i ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
            fieldOneCubeMajorant i k (translatePotentialSample z omega) := by
      exact Finset.sum_le_sum fun k _ ↦
        translatedBlockSup_add_shellZero_le_weighted_fieldOneCubeMajorant
          k z hs omega
    _ = 2 * ∑ k ∈ Finset.Icc n m, ∑ i ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
            fieldOneCubeMajorant i k (translatePotentialSample z omega) := by
      rw [Finset.mul_sum]

/-! ## Reindexing by independent shell columns -/

/-- Finite triangular sums may be interchanged without changing their
carrier. -/
theorem sum_Icc_sum_range_eq_sum_range_sum_filter
    {R : Type*} [AddCommMonoid R] (f : ℕ → ℕ → R) (n m : ℕ) :
    ∑ k ∈ Finset.Icc n m, ∑ i ∈ Finset.range (k + 1), f i k =
      ∑ i ∈ Finset.range (m + 1),
        ∑ k ∈ (Finset.Icc n m).filter (fun k ↦ i ≤ k), f i k := by
  classical
  calc
    (∑ k ∈ Finset.Icc n m, ∑ i ∈ Finset.range (k + 1), f i k) =
        ∑ k ∈ Finset.Icc n m,
          ∑ i ∈ Finset.range (m + 1), if i ≤ k then f i k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k ≤ m := (Finset.mem_Icc.mp hk).2
      have hsub : Finset.range (k + 1) ⊆ Finset.range (m + 1) := by
        intro i hi
        rw [Finset.mem_range] at hi ⊢
        omega
      calc
        (∑ i ∈ Finset.range (k + 1), f i k) =
            ∑ i ∈ Finset.range (k + 1), if i ≤ k then f i k else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [ite_eq_left (by simpa only [Nat.lt_succ_iff] using! Finset.mem_range.mp hi)]
        _ = ∑ i ∈ Finset.range (m + 1), if i ≤ k then f i k else 0 := by
          apply Finset.sum_subset hsub
          intro i him hi
          rw [ite_eq_right]
          intro hik
          exact hi (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
    _ = ∑ i ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.Icc n m, if i ≤ k then f i k else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (m + 1),
          ∑ k ∈ (Finset.Icc n m).filter (fun k ↦ i ≤ k), f i k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_filter]

/-- The `i`th finite-field column; it reads only shell `i`. -/
noncomputable def accumulatedFiniteFieldColumn {d : ℕ}
    (z : Vec d) (s : ℝ) (n m i : ℕ) : Sample d → ℝ :=
  fun omega ↦ ∑ k ∈ (Finset.Icc n m).filter (fun k ↦ i ≤ k),
    (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
      fieldOneCubeMajorant i k (translatePotentialSample z omega)

def accumulatedFiniteFieldColumnScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (n m i : ℕ) : ℝ :=
  gammaTriangleConst 2 *
    ∑ k ∈ (Finset.Icc n m).filter (fun k ↦ i ≤ k),
      (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
        fieldOneCubeMajorantScale M i k

theorem measurable_accumulatedFiniteFieldColumn_shellSigma {d : ℕ}
    (z : Vec d) (s : ℝ) (n m i : ℕ) :
    Measurable[shellSigma d i]
      (accumulatedFiniteFieldColumn z s n m i) := by
  unfold accumulatedFiniteFieldColumn
  apply Finset.measurable_sum
  intro k hk
  exact measurable_const.mul
    ((measurable_fieldOneCubeMajorant_shellSigma i k).comp
      (measurable_translatePotentialSample_shellSigma i z))

/-- The reindexed finite-field columns are mutually independent. -/
theorem iIndepFun_accumulatedFiniteFieldColumn {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    (s : ℝ) (n m : ℕ) :
    iIndepFun (fun i : ℕ ↦ accumulatedFiniteFieldColumn z s n m i)
      M.P.toMeasure := by
  rw [iIndepFun_iff]
  intro I E hE
  have hshell : iIndep (shellSigma d) M.P.toMeasure :=
    M.shellPrefix.independent.iIndep
  exact hshell.meas_biInter fun i hi ↦
    (measurable_accumulatedFiniteFieldColumn_shellSigma z s n m i).comap_le
      (E i) (hE i hi)

/-- One shell-column has a Gamma-two scale equal to the triangle sum of its
cube-majorant scales. -/
theorem isBigOWith_gammaTwo_accumulatedFiniteFieldColumn {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d)
    (s : ℝ) {n m i : ℕ} (hnm : n ≤ m) (him : i ≤ m) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (accumulatedFiniteFieldColumn z s n m i)
      (accumulatedFiniteFieldColumnScale M s n m i) := by
  let S := (Finset.Icc n m).filter (fun k ↦ i ≤ k)
  let X : ℕ → Sample d → ℝ := fun k omega ↦
    (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
      fieldOneCubeMajorant i k (translatePotentialSample z omega)
  let a : ℕ → ℝ := fun k ↦
    (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
      fieldOneCubeMajorantScale M i k
  have hS : S.Nonempty := by
    refine ⟨max n i, ?_⟩
    change max n i ∈ (Finset.Icc n m).filter (fun k ↦ i ≤ k)
    rw [Finset.mem_filter, Finset.mem_Icc]
    omega
  have ha : ∀ k ∈ S, 0 < a k := by
    intro k hk
    unfold a
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (fieldOneCubeMajorantScale_pos M i k)
  have hX0 : ∀ k omega, 0 ≤ X k omega := by
    intro k omega
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (fieldOneCubeMajorant_nonneg i k _)
  have hXm : ∀ k, Measurable (X k) := by
    intro k
    exact measurable_const.mul
      (((measurable_fieldOneCubeMajorant_shellSigma i k).mono
        (shellSigma_le i) le_rfl).comp
          (Section6Covariance.measurable_translatePotentialSample z))
  have hXbig : ∀ k ∈ S,
      IsBigO M.P.toMeasure (gammaSigma 2) (X k) (a k) := by
    intro k hk
    have hbase := isBigOWith_comp_translatePotentialSample M z
      (isBigOWith_gammaTwo_fieldOneCubeMajorant M i k)
    have hscaled := hbase.const_mul
      (c := (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))))
      (Real.rpow_nonneg (by norm_num)
        (-(s / 8) * ((k : ℝ) - (i : ℝ))))
    have hscaled' : IsBigOWith M.P.toMeasure (gammaSigma 2) (X k) (a k) := by
      simpa only [X, a] using! hscaled
    simpa only [IsBigO, abs_of_nonneg (hX0 k _)] using! hscaled'
  have hfinite := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
    (μ := M.P.toMeasure) S (X := X) (a := a) (σ := 2)
    (by norm_num) hS ha hXbig (fun k _ ↦ hXm k)
  simpa only [accumulatedFiniteFieldColumn,
    accumulatedFiniteFieldColumnScale, S, X, a, IsBigO,
    abs_of_nonneg (Finset.sum_nonneg fun k _ ↦ hX0 k _)] using! hfinite

theorem accumulatedFiniteFieldColumnScale_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
    {n m i : ℕ} (hnm : n ≤ m) (him : i ≤ m) :
    0 < accumulatedFiniteFieldColumnScale M s n m i := by
  unfold accumulatedFiniteFieldColumnScale
  apply mul_pos gammaTriangleConst_pos
  let S := (Finset.Icc n m).filter (fun k ↦ i ≤ k)
  have hmaxmem : max n i ∈ S := by
    change max n i ∈ (Finset.Icc n m).filter (fun k ↦ i ≤ k)
    rw [Finset.mem_filter, Finset.mem_Icc]
    omega
  exact Finset.sum_pos' (fun k _ ↦ mul_nonneg
    (Real.rpow_nonneg (by norm_num) _) (fieldOneCubeMajorantScale_pos M i k).le)
    ⟨max n i, hmaxmem, mul_pos
      (Real.rpow_pos_of_pos (by norm_num) _)
      (fieldOneCubeMajorantScale_pos M i (max n i))⟩

/-- Largest exact shell-column scale on the active interval. -/
noncomputable def accumulatedFiniteFieldActiveScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (s : ℝ) (n m : ℕ) : ℝ :=
  if h : n ≤ m then
    (Finset.Icc n m).sup' (Finset.nonempty_Icc.mpr h)
      (fun i ↦ accumulatedFiniteFieldColumnScale M s n m i)
  else 0

theorem accumulatedFiniteFieldActiveScale_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
    {n m : ℕ} (hnm : n ≤ m) :
    0 < accumulatedFiniteFieldActiveScale M s n m := by
  rw [accumulatedFiniteFieldActiveScale, dite_eq_left hnm]
  have hnmem : n ∈ Finset.Icc n m := Finset.mem_Icc.mpr ⟨le_rfl, hnm⟩
  exact (accumulatedFiniteFieldColumnScale_pos M s hnm hnm).trans_le
    (Finset.le_sup' (fun i ↦ accumulatedFiniteFieldColumnScale M s n m i) hnmem)

theorem accumulatedFiniteFieldColumnScale_le_active {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ)
    {n m i : ℕ} (hnm : n ≤ m) (hi : i ∈ Finset.Icc n m) :
    accumulatedFiniteFieldColumnScale M s n m i ≤
      accumulatedFiniteFieldActiveScale M s n m := by
  rw [accumulatedFiniteFieldActiveScale, dite_eq_left hnm]
  exact Finset.le_sup' (fun j ↦ accumulatedFiniteFieldColumnScale M s n m j) hi

def accumulatedFiniteFieldScaleBound {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ) : ℝ :=
  gammaTriangleConst 2 *
    (fieldOneCubeMajorantScale M 0 0 +
      16 * fieldOneGammaDimScale M *
        (Real.sqrt (s / 8))⁻¹ * (s / 8)⁻¹)

theorem fieldOneGammaDimScale_pos_stopping {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    0 < fieldOneGammaDimScale M := by
  unfold fieldOneGammaDimScale
  have hd : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact mul_pos
    (mul_pos (by positivity)
      (Real.sqrt_pos.mpr (mul_pos shellCoverLogConst_pos hd)))
    (mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos)

theorem accumulatedFiniteFieldScaleBound_pos {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ} (hs : 0 < s) :
    0 < accumulatedFiniteFieldScaleBound M s := by
  unfold accumulatedFiniteFieldScaleBound
  apply mul_pos gammaTriangleConst_pos
  exact add_pos_of_pos_of_nonneg (fieldOneCubeMajorantScale_pos M 0 0)
    (by positivity [fieldOneGammaDimScale_pos_stopping M])

/-- The exact active-column maximum is bounded uniformly in the window. -/
theorem accumulatedFiniteFieldActiveScale_le_bound {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hs : 0 < s) (hs1 : s / 8 ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    accumulatedFiniteFieldActiveScale M s n m ≤
      accumulatedFiniteFieldScaleBound M s := by
  rw [accumulatedFiniteFieldActiveScale, dite_eq_left hnm]
  apply Finset.sup'_le
  intro i hi
  have hni : n ≤ i := (Finset.mem_Icc.mp hi).1
  have him : i ≤ m := (Finset.mem_Icc.mp hi).2
  have hfilter : (Finset.Icc n m).filter (fun k ↦ i ≤ k) =
      Finset.Icc i m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  let t : ℝ := s / 8
  have ht : 0 < t := by dsimp only [t]; positivity
  have hsplit : Finset.Icc i m = insert i (Finset.Icc (i + 1) m) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  let b : ℕ → ℝ := fun k ↦
    (3 : ℝ) ^ (-t * ((k : ℝ) - (i : ℝ))) *
      fieldOneCubeMajorantScale M i k
  have hb0 : b i = fieldOneCubeMajorantScale M 0 0 := by
    unfold b fieldOneCubeMajorantScale
    simp only [sub_self, mul_zero, Real.rpow_zero, one_mul]
  have hfirst :
      (3 : ℝ) ^ (-t * ((i : ℝ) - (i : ℝ))) *
          fieldOneCubeMajorantScale M i i =
        fieldOneCubeMajorantScale M 0 0 := by
    simpa only [b] using! hb0
  have htail :
      ∑ k ∈ Finset.Icc (i + 1) m, b k ≤
        ∑' q : ℕ, fieldOneScoreTermScale M t 1 i i q := by
    rw [show Finset.Icc (i + 1) m = Finset.Ico (i + 1) (m + 1) by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    have hpoint : ∀ q : ℕ,
        b (i + 1 + q) ≤ fieldOneScoreTermScale M t 1 i i q := by
      intro q
      have hcoeff :
          (3 : ℝ) ^ (-t * (((i + 1 + q : ℕ) : ℝ) - (i : ℝ))) ≤
            (3 : ℝ) ^ (-t * (q : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have ht0 := ht
        push_cast
        nlinarith
      unfold b
      simpa [fieldOneScoreTermScale, fieldOneIndexDistance, t] using!
        mul_le_mul_of_nonneg_right hcoeff
          (fieldOneCubeMajorantScale_pos M i (i + 1 + q)).le
    calc
      (∑ q ∈ Finset.range (m + 1 - (i + 1)), b (i + 1 + q)) ≤
          ∑ q ∈ Finset.range (m + 1 - (i + 1)),
            fieldOneScoreTermScale M t 1 i i q :=
        Finset.sum_le_sum fun q _ ↦ hpoint q
      _ ≤ ∑' q : ℕ, fieldOneScoreTermScale M t 1 i i q :=
        (summable_fieldOneScoreTermScale M ht one_pos i i).sum_le_tsum _
          (fun q _ ↦ by
            unfold fieldOneScoreTermScale
            exact mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num)
                (Real.rpow_nonneg (by norm_num) _))
                (Real.rpow_nonneg (by norm_num) _))
              (fieldOneCubeMajorantScale_pos M i _).le)
  have hscore := tsum_fieldOneScoreTermScale_le M ht hs1 one_pos i i
  norm_num at hscore
  unfold accumulatedFiniteFieldColumnScale accumulatedFiniteFieldScaleBound
  rw [hfilter, hsplit, Finset.sum_insert (by
    simp only [Finset.mem_Icc]; omega), show s / 8 = t by rfl, hfirst]
  apply mul_le_mul_of_nonneg_left _ gammaTriangleConst_pos.le
  simpa only [b, add_comm] using!
    add_le_add_left (htail.trans hscore) (fieldOneCubeMajorantScale M 0 0)

noncomputable def centeredAccumulatedFiniteFieldColumn {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (z : Vec d) (s : ℝ) (n m i : ℕ) : Sample d → ℝ :=
  fun omega ↦ accumulatedFiniteFieldColumn z s n m i omega -
    ∫ eta, accumulatedFiniteFieldColumn z s n m i eta ∂M.P.toMeasure

theorem measurable_centeredAccumulatedFiniteFieldColumn {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (z : Vec d) (s : ℝ) (n m i : ℕ) :
    Measurable (centeredAccumulatedFiniteFieldColumn M z s n m i) := by
  unfold centeredAccumulatedFiniteFieldColumn
  exact ((measurable_accumulatedFiniteFieldColumn_shellSigma z s n m i).mono
    (shellSigma_le i) le_rfl).sub measurable_const

theorem iIndepFun_centeredAccumulatedFiniteFieldColumn {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (z : Vec d) (s : ℝ) (n m : ℕ) :
    iIndepFun (fun i : ℕ ↦ centeredAccumulatedFiniteFieldColumn M z s n m i)
      M.P.toMeasure := by
  have hbase := iIndepFun_accumulatedFiniteFieldColumn M z s n m
  have hcenter := hbase.comp
    (fun i : ℕ ↦ fun x : ℝ ↦ x -
      ∫ eta, accumulatedFiniteFieldColumn z s n m i eta ∂M.P.toMeasure)
    (fun _ ↦ measurable_id.sub measurable_const)
  simpa only [centeredAccumulatedFiniteFieldColumn, Function.comp_apply] using! hcenter

theorem isBigO_centeredAccumulatedFiniteFieldColumn_active {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (z : Vec d) (s : ℝ) {n m i : ℕ}
    (hnm : n ≤ m) (hi : i ∈ Finset.Icc n m) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (centeredAccumulatedFiniteFieldColumn M z s n m i)
      ((1 + gammaMomentConst 2) *
        accumulatedFiniteFieldActiveScale M s n m) := by
  have him : i ≤ m := (Finset.mem_Icc.mp hi).2
  let A := accumulatedFiniteFieldColumnScale M s n m i
  have hA : 0 < A := accumulatedFiniteFieldColumnScale_pos M s hnm him
  let Y := accumulatedFiniteFieldColumn (d := d) z s n m i
  have hY0 : ∀ omega, 0 ≤ Y omega := by
    intro omega
    unfold Y accumulatedFiniteFieldColumn
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg
      (Real.rpow_nonneg (by norm_num) _)
      (fieldOneCubeMajorant_nonneg i k _)
  have hYm : Measurable Y :=
    (measurable_accumulatedFiniteFieldColumn_shellSigma z s n m i).mono
      (shellSigma_le i) le_rfl
  have hcol : IsBigOWith M.P.toMeasure (gammaSigma 2) Y A := by
    simpa only [Y, A] using!
      isBigOWith_gammaTwo_accumulatedFiniteFieldColumn M z s hnm him
  have hmean := integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo
    hA hYm hY0 hcol
  have hraw := isBigO_gammaTwo_sub_const_of_isBigOWith_nonneg
    hA.le hmean.2.1 hY0 hcol
  have hscale := accumulatedFiniteFieldColumnScale_le_active M s hnm hi
  unfold centeredAccumulatedFiniteFieldColumn
  change IsBigO M.P.toMeasure (gammaSigma 2)
    (fun omega ↦ Y omega - ∫ eta, Y eta ∂M.P.toMeasure) _
  refine hraw.mono_scale ?_
  calc
    A + ∫ eta, accumulatedFiniteFieldColumn z s n m i eta ∂M.P.toMeasure ≤
        A + gammaMomentConst 2 * A := by
      simpa only [Y, add_comm] using! add_le_add_left hmean.2.2 A
    _ = (1 + gammaMomentConst 2) * A := by ring
    _ ≤ (1 + gammaMomentConst 2) *
        accumulatedFiniteFieldActiveScale M s n m := by
      gcongr
      exact add_nonneg zero_le_one (gammaMomentConst_pos (by norm_num)).le

theorem integral_centeredAccumulatedFiniteFieldColumn_eq_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (z : Vec d) (s : ℝ) {n m i : ℕ}
    (hnm : n ≤ m) (hi : i ∈ Finset.Icc n m) :
    ∫ omega, centeredAccumulatedFiniteFieldColumn M z s n m i omega
        ∂M.P.toMeasure = 0 := by
  have him : i ≤ m := (Finset.mem_Icc.mp hi).2
  let A := accumulatedFiniteFieldColumnScale M s n m i
  have hA : 0 < A := accumulatedFiniteFieldColumnScale_pos M s hnm him
  have hint := (integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo
    hA
    ((measurable_accumulatedFiniteFieldColumn_shellSigma z s n m i).mono
      (shellSigma_le i) le_rfl)
    (fun omega ↦ Finset.sum_nonneg fun k _ ↦ mul_nonneg
      (Real.rpow_nonneg (by norm_num) _)
      (fieldOneCubeMajorant_nonneg i k _))
    (isBigOWith_gammaTwo_accumulatedFiniteFieldColumn M z s hnm him)).1
  unfold centeredAccumulatedFiniteFieldColumn
  rw [integral_sub hint (integrable_const _)]
  simp

noncomputable def centeredAccumulatedFiniteFieldActiveWindow {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (z : Vec d) (s : ℝ) (n m : ℕ) : Sample d → ℝ :=
  fun omega ↦ ∑ i ∈ Finset.Icc n m,
    centeredAccumulatedFiniteFieldColumn M z s n m i omega

/-- The genuinely active finite-field columns have the central-limit scale
`sqrt(m+1-n)`. -/
theorem isBigO_centeredAccumulatedFiniteFieldActiveWindow {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (z : Vec d) (s : ℝ) {n m : ℕ} (hnm : n ≤ m) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (centeredAccumulatedFiniteFieldActiveWindow M z s n m)
      (Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
          ((1 + gammaMomentConst 2) *
            accumulatedFiniteFieldActiveScale M s n m)) := by
  let K := (1 + gammaMomentConst 2) *
    accumulatedFiniteFieldActiveScale M s n m
  have hK : 0 < K := mul_pos
    (add_pos one_pos (gammaMomentConst_pos (by norm_num)))
    (accumulatedFiniteFieldActiveScale_pos M s hnm)
  have hsum := Ch04.isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
    (μ := M.P.toMeasure)
    (X := fun i : ℕ ↦ centeredAccumulatedFiniteFieldColumn M z s n m i)
    (s := Finset.Icc n m) (σ := 2) (K := K)
    (iIndepFun_centeredAccumulatedFiniteFieldColumn M z s n m)
    (fun i ↦ measurable_centeredAccumulatedFiniteFieldColumn M z s n m i)
    (Finset.nonempty_Icc.mpr hnm) (by norm_num) (by norm_num) hK
    (fun i hi ↦ by simpa only [K] using!
      isBigO_centeredAccumulatedFiniteFieldColumn_active M z s hnm hi)
    (fun i hi ↦ integral_centeredAccumulatedFiniteFieldColumn_eq_zero
      M z s hnm hi)
  rw [Nat.card_Icc] at hsum
  simpa only [centeredAccumulatedFiniteFieldActiveWindow, K] using! hsum

theorem isBigO_centeredAccumulatedFiniteFieldActiveWindow_le_bound {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (z : Vec d) {s : ℝ} (hs : 0 < s) (hs1 : s / 8 ≤ 1)
    {n m : ℕ} (hnm : n ≤ m) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (centeredAccumulatedFiniteFieldActiveWindow M z s n m)
      (Ch04.gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
          ((1 + gammaMomentConst 2) * accumulatedFiniteFieldScaleBound M s)) := by
  refine (isBigO_centeredAccumulatedFiniteFieldActiveWindow M z s hnm).mono_scale ?_
  have hactive := accumulatedFiniteFieldActiveScale_le_bound M hs hs1 hnm
  have hcore : 0 < gammaSigmaExpRegimeConst 2 := by
    unfold gammaSigmaExpRegimeConst
    exact (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1))
      (gammaMomentConst_pos (by norm_num))).trans_le (le_max_left _ _)
  have hC : 0 ≤ Ch04.gammaSigmaIndependentSumConst 2 := by
    rw [Ch04.gammaSigmaIndependentSumConst, ite_eq_right (by norm_num),
      Ch04.gammaSigmaExpRegimeEndpointConst,
      gammaSigmaExpRegimeEndpointConst, ite_eq_right (by norm_num)]
    exact (mul_pos (by norm_num) hcore).le
  have hsqrt : 0 ≤ Real.sqrt ((m + 1 - n : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hmoment : 0 ≤ 1 + gammaMomentConst 2 :=
    add_nonneg zero_le_one (gammaMomentConst_pos (by norm_num)).le
  have hinner := mul_le_mul_of_nonneg_left hactive hmoment
  exact mul_le_mul_of_nonneg_left hinner (mul_nonneg hC hsqrt)

theorem accumulatedFiniteFieldWindowConvolution_eq_sum_columns {d : ℕ}
    (z : Vec d) (s : ℝ) (n m : ℕ) (omega : Sample d) :
    accumulatedFiniteFieldWindowConvolution z s n m omega =
      ∑ i ∈ Finset.range (m + 1),
        accumulatedFiniteFieldColumn z s n m i omega := by
  unfold accumulatedFiniteFieldWindowConvolution accumulatedFiniteFieldColumn
  exact sum_Icc_sum_range_eq_sum_range_sum_filter
    (fun i k ↦
      (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
      fieldOneCubeMajorant i k (translatePotentialSample z omega)) n m

/-- Columns born strictly before the observation window.  Keeping this as a
separate carrier is what preserves the geometric `n-i` gain. -/
noncomputable def accumulatedFiniteFieldLowWindow {d : ℕ}
    (z : Vec d) (s : ℝ) (n m : ℕ) : Sample d → ℝ :=
  fun omega ↦ ∑ i ∈ Finset.range n,
    accumulatedFiniteFieldColumn z s n m i omega

/-- Columns whose shell index lies in the observation window. -/
noncomputable def accumulatedFiniteFieldActiveWindow {d : ℕ}
    (z : Vec d) (s : ℝ) (n m : ℕ) : Sample d → ℝ :=
  fun omega ↦ ∑ i ∈ Finset.Icc n m,
    accumulatedFiniteFieldColumn z s n m i omega

/-- Exact low/active decomposition of the manuscript's finite shell-field
triangle. -/
theorem accumulatedFiniteFieldWindowConvolution_eq_low_add_active {d : ℕ}
    (z : Vec d) (s : ℝ) {n m : ℕ} (hnm : n ≤ m) (omega : Sample d) :
    accumulatedFiniteFieldWindowConvolution z s n m omega =
      accumulatedFiniteFieldLowWindow z s n m omega +
        accumulatedFiniteFieldActiveWindow z s n m omega := by
  rw [accumulatedFiniteFieldWindowConvolution_eq_sum_columns]
  unfold accumulatedFiniteFieldLowWindow accumulatedFiniteFieldActiveWindow
  rw [show Finset.Icc n m = Finset.Ico n (m + 1) by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  exact (Finset.sum_range_add_sum_Ico (f := fun i ↦
    accumulatedFiniteFieldColumn z s n m i omega) (by omega : n ≤ m + 1)).symm

theorem sum_Icc_sub_le_tsum {f : ℕ → ℝ} {n m : ℕ}
    (hf0 : ∀ q, 0 ≤ f q) (hfsum : Summable f) :
    (∑ k ∈ Finset.Icc n m, f (k - n)) ≤ ∑' q, f q := by
  let S := (Finset.Icc n m).image (fun k ↦ k - n)
  have hEq : (∑ k ∈ Finset.Icc n m, f (k - n)) = ∑ q ∈ S, f q := by
    change (∑ k ∈ Finset.Icc n m, f (k - n)) =
      ∑ q ∈ (Finset.Icc n m).image (fun k ↦ k - n), f q
    rw [Finset.sum_image]
    intro a ha b hb hab
    have ha' : a ∈ Finset.Icc n m := ha
    have hb' : b ∈ Finset.Icc n m := hb
    have han := (Finset.mem_Icc.mp ha').1
    have hbn := (Finset.mem_Icc.mp hb').1
    change a - n = b - n at hab
    omega
  rw [hEq]
  exact hfsum.sum_le_tsum S (fun q _ ↦ hf0 q)

theorem sum_range_reverse_le_tsum {f : ℕ → ℝ} (n : ℕ)
    (hf0 : ∀ q, 0 ≤ f q) (hfsum : Summable f) :
    (∑ i ∈ Finset.range n, f (n - i)) ≤ ∑' q, f q := by
  let S := (Finset.range n).image (fun i ↦ n - i)
  have hEq : (∑ i ∈ Finset.range n, f (n - i)) = ∑ q ∈ S, f q := by
    change (∑ i ∈ Finset.range n, f (n - i)) =
      ∑ q ∈ (Finset.range n).image (fun i ↦ n - i), f q
    rw [Finset.sum_image]
    intro a ha b hb hab
    have ha' : a ∈ Finset.range n := ha
    have hb' : b ∈ Finset.range n := hb
    have han := (Finset.mem_range.mp ha').le
    have hbn := (Finset.mem_range.mp hb').le
    change n - a = n - b at hab
    omega
  rw [hEq]
  exact hfsum.sum_le_tsum S (fun q _ ↦ hf0 q)

/-- The pre-window finite-field columns have a uniform geometric total
scale.  This is the quantitative half of the shell-field window
rearrangement; crucially, it is independent of the absolute start scale
`n`. -/
theorem sum_accumulatedFiniteFieldColumnScale_low_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hs : 0 < s) (hs1 : s / 8 ≤ 1) (n m : ℕ) :
    (∑ i ∈ Finset.range n, accumulatedFiniteFieldColumnScale M s n m i) ≤
      gammaTriangleConst 2 * fieldOneGammaDimScale M *
        (6 / (s / 8) ^ 2) ^ 2 := by
  let t : ℝ := s / 8
  let Q : ℝ := fieldOneGeometricBase t
  let F : ℕ → ℝ := fun q ↦ Q ^ q * ((q : ℝ) + 1)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hQ0 : 0 ≤ Q := by exact fieldOneGeometricBase_nonneg t
  have hQ1 : Q < 1 := fieldOneGeometricBase_lt_one ht
  have hnorm : ‖Q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hQ0]
  have hFsum : Summable F := by
    have hNQ : Summable fun q : ℕ ↦ (q : ℝ) * Q ^ q :=
      (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
    have hQsum : Summable fun q : ℕ ↦ Q ^ q :=
      summable_geometric_of_norm_lt_one hnorm
    convert hNQ.add hQsum using 1
    ext q
    unfold F
    ring
  have hF0 : ∀ q, 0 ≤ F q := fun q ↦ by
    unfold F
    positivity
  have hFbound : (∑' q, F q) ≤ 6 / t ^ 2 := by
    simpa only [F, Q] using!
      tsum_fieldOneGeometricBase_mul_succ_le ht hs1
  have hcolumn : ∀ i ∈ Finset.range n,
      accumulatedFiniteFieldColumnScale M s n m i ≤
        gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (F (n - i) * (∑' q, F q)) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hfilter : (Finset.Icc n m).filter (fun k ↦ i ≤ k) =
        Finset.Icc n m := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    have hterm : ∀ k ∈ Finset.Icc n m,
        (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
            fieldOneCubeMajorantScale M i k ≤
          fieldOneGammaDimScale M * (F (n - i) * F (k - n)) := by
      intro k hk
      have hnk := (Finset.mem_Icc.mp hk).1
      have hik : i < k := lt_of_lt_of_le hin hnk
      have hscale0 := fieldOneCubeMajorantScale_le_sqrt M i i (k - i - 1)
      have hscale : fieldOneCubeMajorantScale M i k ≤
          fieldOneGammaDimScale M * Real.sqrt ((k - i : ℕ) : ℝ) := by
        simp only [fieldOneIndexDistance, sub_self, Int.natAbs_zero,
          zero_add] at hscale0
        have hidx : i + 1 + (k - i - 1) = k := by omega
        have hrad : k - i - 1 + 1 = k - i := by omega
        rw [hidx] at hscale0
        norm_num at hscale0
        have hradR : ((k - i - 1 : ℕ) : ℝ) + 1 = ((k - i : ℕ) : ℝ) := by
          exact_mod_cast hrad
        rw [hradR] at hscale0
        exact hscale0
      have hsqrt : Real.sqrt ((k - i : ℕ) : ℝ) ≤
          (((n - i : ℕ) : ℝ) + 1) * (((k - n : ℕ) : ℝ) + 1) := by
        have hki : 1 ≤ k - i := by omega
        have hsqrtSelf : Real.sqrt ((k - i : ℕ) : ℝ) ≤ (k - i : ℕ) := by
          rw [Real.sqrt_le_iff]
          constructor
          · positivity
          · have : (1 : ℝ) ≤ (k - i : ℕ) := by exact_mod_cast hki
            nlinarith
        have hsplit : k - i = (n - i) + (k - n) := by omega
        rw [hsplit] at hsqrtSelf
        rw [hsplit]
        push_cast at hsqrtSelf ⊢
        have hab : 0 ≤ ((n - i : ℕ) : ℝ) * ((k - n : ℕ) : ℝ) :=
          mul_nonneg (by positivity) (by positivity)
        nlinarith
      have hweight :
          (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) =
            Q ^ (n - i) * Q ^ (k - n) := by
        have hsplit : k - i = (n - i) + (k - n) := by omega
        rw [← Nat.cast_sub hik.le]
        rw [hsplit, Nat.cast_add]
        rw [show s / 8 = t by rfl]
        rw [show -t * (((n - i : ℕ) : ℝ) + ((k - n : ℕ) : ℝ)) =
          (-t * ((n - i : ℕ) : ℝ)) + (-t * ((k - n : ℕ) : ℝ)) by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        rw [show -t * ((n - i : ℕ) : ℝ) =
          -(t * ((n - i : ℕ) : ℝ)) by ring,
          show -t * ((k - n : ℕ) : ℝ) =
          -(t * ((k - n : ℕ) : ℝ)) by ring,
          fieldOne_qWeight_eq_pow, fieldOne_qWeight_eq_pow]
      rw [hweight]
      unfold F
      have hD0 : 0 ≤ fieldOneGammaDimScale M := by
        unfold fieldOneGammaDimScale
        have hlog : 0 < 1 + Real.log 2 := by
          have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          linarith
        exact mul_nonneg
          (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
          (mul_nonneg (Real.rpow_nonneg hlog.le _) M.shellPrefix.delta_pos.le)
      calc
        _ ≤ (Q ^ (n - i) * Q ^ (k - n)) *
            (fieldOneGammaDimScale M * Real.sqrt ((k - i : ℕ) : ℝ)) := by
          gcongr
        _ ≤ (Q ^ (n - i) * Q ^ (k - n)) *
            (fieldOneGammaDimScale M *
              ((((n - i : ℕ) : ℝ) + 1) * (((k - n : ℕ) : ℝ) + 1))) := by
          gcongr
        _ = _ := by ring
    unfold accumulatedFiniteFieldColumnScale
    rw [hfilter]
    have hsumPoint := Finset.sum_le_sum fun k hk ↦ hterm k hk
    have hinner := sum_Icc_sub_le_tsum hF0 hFsum (n := n) (m := m)
    have hD0 : 0 ≤ fieldOneGammaDimScale M := by
      unfold fieldOneGammaDimScale
      have hlog : 0 < 1 + Real.log 2 := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith
      exact mul_nonneg
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (mul_nonneg (Real.rpow_nonneg hlog.le _) M.shellPrefix.delta_pos.le)
    calc
      gammaTriangleConst 2 *
          ∑ k ∈ Finset.Icc n m,
            (3 : ℝ) ^ (-(s / 8) * ((k : ℝ) - (i : ℝ))) *
              fieldOneCubeMajorantScale M i k ≤
        gammaTriangleConst 2 *
          ∑ k ∈ Finset.Icc n m,
            fieldOneGammaDimScale M * (F (n - i) * F (k - n)) := by
          exact mul_le_mul_of_nonneg_left hsumPoint gammaTriangleConst_pos.le
      _ = gammaTriangleConst 2 * fieldOneGammaDimScale M * F (n - i) *
          (∑ k ∈ Finset.Icc n m, F (k - n)) := by
        rw [show (∑ k ∈ Finset.Icc n m,
            fieldOneGammaDimScale M * (F (n - i) * F (k - n))) =
          (fieldOneGammaDimScale M * F (n - i)) *
            ∑ k ∈ Finset.Icc n m, F (k - n) by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring]
        ring
      _ ≤ gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (F (n - i) * (∑' q, F q)) := by
        have hpref : 0 ≤ gammaTriangleConst 2 * fieldOneGammaDimScale M *
            F (n - i) := by
          exact mul_nonneg (mul_nonneg gammaTriangleConst_pos.le hD0) (hF0 _)
        exact (mul_le_mul_of_nonneg_left hinner hpref).trans_eq (by ring)
      _ = _ := by ring
  have hsumColumns := Finset.sum_le_sum hcolumn
  have hreverse := sum_range_reverse_le_tsum n hF0 hFsum
  have htri0 : 0 ≤ gammaTriangleConst 2 := gammaTriangleConst_pos.le
  have hD0 : 0 ≤ fieldOneGammaDimScale M := by
    unfold fieldOneGammaDimScale
    have hlog : 0 < 1 + Real.log 2 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith
    exact mul_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.rpow_nonneg hlog.le _) M.shellPrefix.delta_pos.le)
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (F (n - i) * (∑' q, F q)) := hsumColumns
    _ = gammaTriangleConst 2 * fieldOneGammaDimScale M *
        ((∑ i ∈ Finset.range n, F (n - i)) * (∑' q, F q)) := by
      calc
        _ = ∑ i ∈ Finset.range n,
            (gammaTriangleConst 2 * fieldOneGammaDimScale M *
              (∑' q, F q)) * F (n - i) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (gammaTriangleConst 2 * fieldOneGammaDimScale M *
              (∑' q, F q)) *
            ∑ i ∈ Finset.range n, F (n - i) := by rw [Finset.mul_sum]
        _ = _ := by ring
    _ ≤ gammaTriangleConst 2 * fieldOneGammaDimScale M *
        ((∑' q, F q) * (∑' q, F q)) := by
      gcongr
    _ ≤ gammaTriangleConst 2 * fieldOneGammaDimScale M *
        ((6 / t ^ 2) * (6 / t ^ 2)) := by
      gcongr
    _ = _ := by rw [show t = s / 8 by rfl]; ring

theorem isBigO_accumulatedFiniteFieldLowWindow {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d) {s : ℝ}
    (hs : 0 < s) (hs1 : s / 8 ≤ 1) {n m : ℕ} (hnm : n ≤ m) :
    IsBigO M.P.toMeasure (gammaSigma 2)
      (accumulatedFiniteFieldLowWindow z s n m)
      (gammaTriangleConst 2 *
        (gammaTriangleConst 2 * fieldOneGammaDimScale M *
          (6 / (s / 8) ^ 2) ^ 2)) := by
  by_cases hn : n = 0
  · subst n
    have hbase := (isBigOWith_gammaTwo_accumulatedFiniteFieldColumn
      M z s (n := 0) (m := m) (i := 0) (by omega) (by omega)).const_mul
        (c := 0) (by norm_num)
    have hzero : IsBigO M.P.toMeasure (gammaSigma 2)
        (fun _ : Sample d ↦ (0 : ℝ)) 0 := by simpa [IsBigO] using! hbase
    have hfun : accumulatedFiniteFieldLowWindow z s 0 m =
        (fun _ : Sample d ↦ (0 : ℝ)) := by
      funext omega
      simp [accumulatedFiniteFieldLowWindow]
    rw [hfun]
    exact hzero.mono_scale (by
      have htri := gammaTriangleConst_pos (σ := 2)
      have hD : 0 ≤ fieldOneGammaDimScale M := by
        unfold fieldOneGammaDimScale
        have hlog : 0 < 1 + Real.log 2 := by
          have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          linarith
        exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
          (mul_nonneg (Real.rpow_nonneg hlog.le _) M.shellPrefix.delta_pos.le)
      positivity)
  · let X : ℕ → Sample d → ℝ := fun i ↦ accumulatedFiniteFieldColumn z s n m i
    let a : ℕ → ℝ := fun i ↦ accumulatedFiniteFieldColumnScale M s n m i
    have hsum := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := M.P.toMeasure) (Finset.range n) (X := X) (a := a) (σ := 2)
      (by norm_num) (Finset.nonempty_range_iff.mpr hn)
      (fun i hi ↦ by
        have hin : i < n := Finset.mem_range.mp hi
        exact accumulatedFiniteFieldColumnScale_pos M s hnm
          (hin.le.trans hnm))
      (fun i hi ↦ by
        have hin : i < n := Finset.mem_range.mp hi
        have hcol := isBigOWith_gammaTwo_accumulatedFiniteFieldColumn
          M z s hnm (hin.le.trans hnm)
        have hnonneg : ∀ omega,
            0 ≤ accumulatedFiniteFieldColumn z s n m i omega := by
          intro omega
          unfold accumulatedFiniteFieldColumn
          exact Finset.sum_nonneg fun k _ ↦
            mul_nonneg (Real.rpow_nonneg (by norm_num) _)
              (fieldOneCubeMajorant_nonneg i k _)
        simpa only [X, a, IsBigO, abs_of_nonneg (hnonneg _)] using! hcol)
      (fun i _ ↦ (measurable_accumulatedFiniteFieldColumn_shellSigma
        z s n m i).mono (shellSigma_le i) le_rfl)
    have hsum' : IsBigO M.P.toMeasure (gammaSigma 2)
        (accumulatedFiniteFieldLowWindow z s n m)
        (gammaTriangleConst 2 * ∑ i ∈ Finset.range n, a i) := by
      simpa only [accumulatedFiniteFieldLowWindow, X] using! hsum
    refine hsum'.mono_scale ?_
    have hscale := sum_accumulatedFiniteFieldColumnScale_low_le M hs hs1 n m
    exact mul_le_mul_of_nonneg_left (by simpa only [a] using! hscale)
      gammaTriangleConst_pos.le

theorem accumulatedFiniteFieldActiveWindow_le_centered_add_mean {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (z : Vec d) {s : ℝ}
    (hs : 0 < s) (hs1 : s / 8 ≤ 1) {n m : ℕ} (hnm : n ≤ m)
    (omega : Sample d) :
    accumulatedFiniteFieldActiveWindow z s n m omega ≤
      centeredAccumulatedFiniteFieldActiveWindow M z s n m omega +
        ((m + 1 - n : ℕ) : ℝ) *
          (gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s) := by
  have hmean : ∀ i ∈ Finset.Icc n m,
      ∫ eta, accumulatedFiniteFieldColumn z s n m i eta ∂M.P.toMeasure ≤
        gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s := by
    intro i hi
    have him := (Finset.mem_Icc.mp hi).2
    have hA := accumulatedFiniteFieldColumnScale_pos M s hnm him
    have hraw := (integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo
      hA ((measurable_accumulatedFiniteFieldColumn_shellSigma z s n m i).mono
        (shellSigma_le i) le_rfl)
      (fun omega ↦ Finset.sum_nonneg fun k _ ↦ mul_nonneg
        (Real.rpow_nonneg (by norm_num) _)
        (fieldOneCubeMajorant_nonneg i k _))
      (isBigOWith_gammaTwo_accumulatedFiniteFieldColumn M z s hnm him)).2.2
    exact hraw.trans (mul_le_mul_of_nonneg_left
      ((accumulatedFiniteFieldColumnScale_le_active M s hnm hi).trans
        (accumulatedFiniteFieldActiveScale_le_bound M hs hs1 hnm))
      (gammaMomentConst_pos (by norm_num)).le)
  have hcard : (Finset.Icc n m).card = m + 1 - n := by rw [Nat.card_Icc]
  unfold accumulatedFiniteFieldActiveWindow
    centeredAccumulatedFiniteFieldActiveWindow
    centeredAccumulatedFiniteFieldColumn
  calc
    (∑ i ∈ Finset.Icc n m, accumulatedFiniteFieldColumn z s n m i omega) =
        (∑ i ∈ Finset.Icc n m,
          (accumulatedFiniteFieldColumn z s n m i omega -
            ∫ eta, accumulatedFiniteFieldColumn z s n m i eta ∂M.P.toMeasure)) +
          ∑ i ∈ Finset.Icc n m,
            ∫ eta, accumulatedFiniteFieldColumn z s n m i eta ∂M.P.toMeasure := by
      rw [Finset.sum_sub_distrib]
      ring
    _ ≤ (∑ i ∈ Finset.Icc n m,
          (accumulatedFiniteFieldColumn z s n m i omega -
            ∫ eta, accumulatedFiniteFieldColumn z s n m i eta ∂M.P.toMeasure)) +
          ∑ _i ∈ Finset.Icc n m,
            gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s := by
      gcongr with i hi
      exact hmean i hi
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
