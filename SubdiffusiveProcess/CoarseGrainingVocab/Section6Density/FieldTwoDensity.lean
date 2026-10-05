module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ExponentialFieldConcentration
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ExponentialSequenceArithmetic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldTwoScore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.LayerIndependence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows

@[expose] public section

/-!
# Density adapter for the second field event

This module implements the two product reductions in the proof of
`l.exp.goodscales`.  The finite moving block is read by
`concentration_exp_field`; the infinite suffix is reduced to the translated
one-shell sequence used by `concentration_exp_sequence`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open Filter MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- The one-shell sequence in the manuscript's infinite-product reduction.
The factor `12 = 4 * 3` makes the geometric coefficient exactly `3⁻q`. -/
def fieldTwoSuffixSequence {d : ℕ} : ℤ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  fun i omega ↦ if 0 ≤ i then
    12 * (translatedShellG2 i.toNat 0 omega + largeCubeShellG2 i.toNat 1 omega)
  else 0

def fieldTwoSuffixSequenceScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) : ℝ :=
  12 * gammaTriangleConst 2 *
    (((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) +
      ((3 * Real.log ((shellCoverShifts d 1).card : ℝ)) ^ (2 : ℝ)⁻¹) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))

theorem fieldTwoSuffixSequenceScale_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    0 < fieldTwoSuffixSequenceScale M := by
  unfold fieldTwoSuffixSequenceScale
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have hcard : 1 < ((shellCoverShifts d 1).card : ℝ) := by
    exact_mod_cast shellCoverShifts_card_ge_two M 1
  have hcover := Real.log_pos hcard
  have hbase : 0 < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta :=
    mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos
  have hlarge : 0 <
      ((3 * Real.log ((shellCoverShifts d 1).card : ℝ)) ^ (2 : ℝ)⁻¹) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) :=
    mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hcover) _) hbase
  exact mul_pos (mul_pos (by norm_num) (gammaTriangleConst_pos (σ := 2)))
    (add_pos hbase hlarge)

theorem fieldTwoSuffixSequence_nonneg {d : ℕ} (i : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ fieldTwoSuffixSequence i omega := by
  unfold fieldTwoSuffixSequence
  split_ifs
  · exact mul_nonneg (by norm_num)
      (add_nonneg (translatedShellG2_nonneg _ _ _)
        (largeCubeShellG2_nonneg _ _ _))
  · exact le_rfl

theorem measurable_fieldTwoSuffixSequence {d : ℕ} (i : ℤ) :
    Measurable (fieldTwoSuffixSequence (d := d) i) := by
  unfold fieldTwoSuffixSequence
  split_ifs
  · exact measurable_const.mul
      ((measurable_translatedShellG2 i.toNat 0).add
        (measurable_largeCubeShellG2 i.toNat 1))
  · exact measurable_const

theorem isBigOWith_gammaTwo_fieldTwoSuffixSequence {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (i : ℤ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fieldTwoSuffixSequence (d := d) i) (fieldTwoSuffixSequenceScale M) := by
  by_cases hi : 0 ≤ i
  · unfold fieldTwoSuffixSequenceScale
    have hadd := isBigOWith_gammaTwo_add_nonneg M
      (measurable_translatedShellG2 i.toNat 0)
      (measurable_largeCubeShellG2 i.toNat 1)
      (translatedShellG2_nonneg i.toNat 0)
      (largeCubeShellG2_nonneg i.toNat 1)
      (by
        have hlog : 0 < 1 + Real.log 2 := by
          have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          linarith
        exact mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos)
      (by
        have hcard : 1 < ((shellCoverShifts d 1).card : ℝ) := by
          exact_mod_cast shellCoverShifts_card_ge_two M 1
        have hlog := Real.log_pos hcard
        have htwo : 0 < 1 + Real.log 2 := by
          have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
          linarith
        exact mul_pos
          (Real.rpow_pos_of_pos (mul_pos (by norm_num) hlog) _)
          (mul_pos (Real.rpow_pos_of_pos htwo _) M.shellPrefix.delta_pos))
      (isBigOWith_gammaTwo_translatedShellG2 M i.toNat 0)
      (isBigOWith_gammaTwo_largeCubeShellG2 M i.toNat 1)
    convert hadd.const_mul (by norm_num : (0 : ℝ) ≤ 12) using 1
    · funext omega
      simp [fieldTwoSuffixSequence, hi]
    · ring
  · have hzero : fieldTwoSuffixSequence (d := d) i = fun _ ↦ 0 := by
      funext omega
      simp [fieldTwoSuffixSequence, hi]
    rw [hzero]
    intro t ht
    have hpos : 0 < fieldTwoSuffixSequenceScale M * t :=
      mul_pos (fieldTwoSuffixSequenceScale_pos M) (zero_lt_one.trans_le ht)
    simp [upperTailEvent, hpos.not_gt]
    positivity

private theorem shellSigma_eq_singleton (d i : ℕ) :
    shellSigma d i = potentialShellIndexSigma (d := d) ({i} : Set ℕ) := by
  apply le_antisymm
  · exact le_iSup_of_le i (le_iSup_of_le (Set.mem_singleton i) le_rfl)
  · refine iSup_le fun k ↦ iSup_le fun hk ↦ ?_
    rw [Set.mem_singleton_iff] at hk
    subst k
    exact le_rfl

private theorem measurable_fieldTwoSuffixSequence_shellSigma {d : ℕ}
    (i : ℕ) : Measurable[shellSigma d i]
      (fieldTwoSuffixSequence (d := d) (i : ℤ)) := by
  rw [shellSigma_eq_singleton]
  change Measurable[potentialShellIndexSigma ({i} : Set ℕ)]
    (fun omega => if 0 ≤ (i : ℤ) then
      12 * (translatedShellG2 i 0 omega + largeCubeShellG2 i 1 omega) else 0)
  simp only [Int.natCast_nonneg, ite_true]
  exact measurable_const.mul
    ((measurable_translatedShellG2_potentialShellIndexSigma
      (d := d) (Set.mem_singleton i) 0).add
      (measurable_largeCubeShellG2_potentialShellIndexSigma
        (d := d) (Set.mem_singleton i) 1))

theorem iIndepFun_fieldTwoSuffixSequence {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    iIndepFun (fieldTwoSuffixSequence (d := d)) M.P.toMeasure := by
  let A : Set ℤ := Set.Ici 0
  apply iIndepFun_of_iIndepFun_subtype_of_constant A
      (fieldTwoSuffixSequence (d := d))
  · let e : A → ℕ := fun i ↦ i.1.toNat
    have he : Function.Injective e := by
      intro i j hij
      apply Subtype.ext
      have hi : 0 ≤ i.1 := i.2
      have hj : 0 ≤ j.1 := j.2
      calc
        i.1 = (i.1.toNat : ℤ) := (Int.toNat_of_nonneg hi).symm
        _ = (j.1.toNat : ℤ) := by exact_mod_cast hij
        _ = j.1 := Int.toNat_of_nonneg hj
    have hshell : iIndep (fun i : A => shellSigma d (e i)) M.P.toMeasure := by
      have h := M.shellPrefix.independent.precomp he
      rw [iIndepFun_iff_iIndep] at h
      exact h
    rw [iIndepFun_iff_iIndep]
    exact iIndep_of_le hshell fun i => by
      have hi : 0 ≤ i.1 := i.2
      have heq : ((e i : ℕ) : ℤ) = i.1 := by
        exact Int.toNat_of_nonneg hi
      simpa only [heq] using
        (measurable_fieldTwoSuffixSequence_shellSigma (d := d) (e i)).comap_le
  · intro i hi
    refine ⟨0, fun omega ↦ ?_⟩
    simp only [A, Set.mem_Ici] at hi
    simp [fieldTwoSuffixSequence, hi]

/-- At a nonnegative starting index, the exponential-sequence logarithm is
the literal sum of the suffix oscillation majorants. -/
theorem ae_expSequenceLog_fieldTwoSuffix_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) :
    (fun omega ↦ ∑' q : ℕ, fieldTwoSuffixLayer k (k + q) omega) ≤ᵐ[M.P.toMeasure]
      expSequenceLog (fieldTwoSuffixSequence (d := d)) (k : ℤ) := by
  filter_upwards [ae_expSequenceLog_eq_tsum
      (fieldTwoSuffixSequenceScale_pos M)
      (fun i ↦ fieldTwoSuffixSequence_nonneg i)
      measurable_fieldTwoSuffixSequence
      (fun i ↦ isBigOWith_gammaTwo_fieldTwoSuffixSequence M i) (k : ℤ),
    ae_summable_fieldTwoSuffixLayer M k,
    ae_summable_expSequenceLogTerm
      (fieldTwoSuffixSequenceScale_pos M)
      (fun i ↦ fieldTwoSuffixSequence_nonneg i)
      measurable_fieldTwoSuffixSequence
      (fun i ↦ isBigOWith_gammaTwo_fieldTwoSuffixSequence M i) (k : ℤ)] with
      omega homega hsuffix hsequence
  rw [homega]
  apply Summable.tsum_le_tsum
  intro q
  unfold expSequenceLogTerm fieldTwoSuffixSequence fieldTwoSuffixLayer
    shellOscillationEnvelope
  have hkq : (0 : ℤ) ≤ (k : ℤ) + (q : ℤ) := by omega
  have hscale : ((k + 1 : ℕ) : ℤ) ≤ ((k + q : ℕ) : ℤ) ↔ 1 ≤ q := by omega
  simp only [hkq, ite_true]
  by_cases hq : q = 0
  · subst q
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, one_mul, Nat.add_zero]
    norm_num
    nlinarith [translatedShellG2_nonneg k 0 omega,
      largeCubeShellG2_nonneg k 1 omega]
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
    rw [ite_eq_left (hscale.mpr hq1)]
    have htoNat : ((k : ℤ) + (q : ℤ)).toNat = k + q := by omega
    rw [htoNat]
    have hpow : (3 : ℝ) ^ (-(q : ℝ)) * 12 =
        4 * (3 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - ((k + q : ℕ) : ℤ)) := by
      rw [show (((k + 1 : ℕ) : ℤ) - ((k + q : ℕ) : ℤ)) = (1 - q : ℤ) by omega,
        zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one,
        zpow_natCast, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
        Real.rpow_natCast]
      field_simp
      ring
    calc
      (3 : ℝ) ^ (-(q : ℝ)) *
          (12 * (translatedShellG2 (k + q) 0 omega +
            largeCubeShellG2 (k + q) 1 omega)) ≥
        (3 : ℝ) ^ (-(q : ℝ)) *
          (12 * translatedShellG2 (k + q) 0 omega) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
        nlinarith [largeCubeShellG2_nonneg (d := d) (k + q) 1 omega]
      _ = 4 * ((3 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - ((k + q : ℕ) : ℤ)) *
          translatedShellG2 (k + q) 0 omega) := by
        calc
          _ = ((3 : ℝ) ^ (-(q : ℝ)) * 12) *
              translatedShellG2 (k + q) 0 omega := by ring
          _ = _ := by rw [hpow]; ring
  · exact hsuffix
  · exact hsequence

/-! ## Literal product events -/

def fieldTwoFiniteBad {d : ℕ} (s : ℝ) (k : ℕ) : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  expFieldBad (d := d) (s / 8) 1 k

def fieldTwoSuffixBad {d : ℕ} (s : ℝ) (k : ℕ) : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) :=
  expSequenceBad (fieldTwoSuffixSequence (d := d)) (s / 8) (k : ℤ)

private theorem translatedCube_zero_eq_cube {d : ℕ} (r : ℤ) :
    translatedCube d r 0 = cube d r := by
  ext x
  simp [translatedCube, cube]

private theorem fieldTwo_pointTerm_summable {d : ℕ}
    (start : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hsum : Summable fun q : ℕ ↦ fieldTwoSuffixLayer start (start + q) omega)
    {x : Vec d} (hx : x ∈ cube d (start + 1)) :
    Summable fun i : ℕ ↦ if start ≤ i then
      4 * |omega i x - omega i 0| else 0 := by
  let F : ℕ → ℝ := fun i ↦ if start ≤ i then
    4 * |omega i x - omega i 0| else 0
  have hshift : Summable fun q : ℕ ↦ F (q + start) := by
    refine Summable.of_nonneg_of_le (fun q ↦ by simp [F]) (fun q ↦ ?_) hsum
    simp only [F, le_add_self, ite_true]
    have hx' : x ∈ translatedCube d ((start + 1 : ℕ) : ℤ) 0 := by
      rw [translatedCube_zero_eq_cube]
      exact hx
    simpa only [Nat.add_comm q start] using
      four_abs_shell_sub_le_fieldTwoSuffixLayer start (start + q) omega hx'
  exact (summable_nat_add_iff start).mp hshift

private theorem fieldTwo_suffix_product_le_exp_tsum {d : ℕ}
    (start : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hsum : Summable fun q : ℕ ↦ fieldTwoSuffixLayer start (start + q) omega)
    {x : Vec d} (hx : x ∈ cube d (start + 1)) :
    0 ≤ (∏' i : ℕ, if start ≤ i then
        Real.exp (4 * |omega i x - omega i 0|) else 1) ∧
      (∏' i : ℕ, if start ≤ i then
          Real.exp (4 * |omega i x - omega i 0|) else 1) ≤
        Real.exp (∑' q : ℕ, fieldTwoSuffixLayer start (start + q) omega) := by
  let F : ℕ → ℝ := fun i ↦ if start ≤ i then
    4 * |omega i x - omega i 0| else 0
  have hF : Summable F := fieldTwo_pointTerm_summable start omega hsum hx
  have hshift : Summable fun q : ℕ ↦ F (q + start) :=
    (summable_nat_add_iff start).mpr hF
  have hshift_le : (∑' q : ℕ, F (q + start)) ≤
      ∑' q : ℕ, fieldTwoSuffixLayer start (start + q) omega := by
    apply Summable.tsum_le_tsum
    · intro q
      simp only [F, le_add_self, ite_true]
      have hx' : x ∈ translatedCube d ((start + 1 : ℕ) : ℤ) 0 := by
        rw [translatedCube_zero_eq_cube]
        exact hx
      simpa only [Nat.add_comm q start] using
        four_abs_shell_sub_le_fieldTwoSuffixLayer start (start + q) omega hx'
    · exact hshift
    · exact hsum
  have hprefix : ∑ i ∈ Finset.range start, F i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [F]
    rw [ite_eq_right]
    exact Nat.not_le_of_lt (Finset.mem_range.mp hi)
  have hfull : (∑' i : ℕ, F i) = ∑' q : ℕ, F (q + start) := by
    have hsplit := hF.sum_add_tsum_nat_add start
    rw [hprefix, zero_add] at hsplit
    exact hsplit.symm
  have htprod : (∏' i : ℕ, if start ≤ i then
      Real.exp (4 * |omega i x - omega i 0|) else 1) =
      Real.exp (∑' i : ℕ, F i) := by
    have heq : (fun i : ℕ => if start ≤ i then
        Real.exp (4 * |omega i x - omega i 0|) else 1) =
        fun i => Real.exp (F i) := by
      funext i
      by_cases hi : start ≤ i <;> simp [F, hi]
    rw [heq]
    exact hF.hasSum.rexp.tprod_eq
  constructor
  · rw [htprod]
    exact (Real.exp_pos _).le
  · rw [htprod, hfull]
    exact Real.exp_le_exp.mpr hshift_le

/-- The full infinite-product comparison, simultaneously for all natural
starting scales and all points in the corresponding observation cube. -/
theorem ae_fieldTwo_suffix_product_le_sequenceLog {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ start : ℕ, ∀ x ∈ cube d (start + 1),
      0 ≤ (∏' i : ℕ, if start ≤ i then
          Real.exp (4 * |omega i x - omega i 0|) else 1) ∧
        (∏' i : ℕ, if start ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1) ≤
          Real.exp (expSequenceLog (fieldTwoSuffixSequence (d := d))
            (start : ℤ) omega) := by
  rw [ae_all_iff]
  intro start
  filter_upwards [ae_summable_fieldTwoSuffixLayer M start,
    ae_expSequenceLog_fieldTwoSuffix_eq M start] with omega hsum hlog
  intro x hx
  refine ⟨(fieldTwo_suffix_product_le_exp_tsum start omega hsum hx).1, ?_⟩
  exact (fieldTwo_suffix_product_le_exp_tsum start omega hsum hx).2.trans
    (Real.exp_le_exp.mpr hlog)

theorem fieldTwo_finite_product_le_expFieldBlockEnvelope {d : ℕ}
    (k j : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ cube d (k + 1 + j)) :
    (∏ i ∈ Finset.Icc (k - j) (k + j), Real.exp |omega i x|) ≤
      Real.exp (expFieldBlockEnvelope k j 1 omega) := by
  apply prod_exp_abs_shell_le_expFieldBlockEnvelope k j 1 omega
  change x ∈ openCubeSet (originCube d ((k + 1 + j : ℕ) : ℤ)) at hx
  exact hx

theorem fieldTwo_finite_exceeds_mem_bad {d : ℕ}
    {s : ℝ} (k j : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ cube d (k + 1 + j))
    (hexceeds : 3 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) <
      ∏ i ∈ Finset.Icc (k - j) (k + j), Real.exp |omega i x|) :
    omega ∈ fieldTwoFiniteBad (d := d) s k := by
  refine ⟨j, (expFieldBlockExceeds_iff omega).2 ?_⟩
  have hprod := fieldTwo_finite_product_le_expFieldBlockEnvelope k j omega hx
  have hpow : (3 : ℝ) ^ ((s * (j : ℝ)) / 8) =
      (3 : ℝ) ^ ((s / 8) * (j : ℝ)) := by congr 1; ring
  rw [hpow] at hexceeds
  have hmul := mul_lt_mul_of_pos_left
    (hexceeds.trans_le hprod)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
      (-((s / 8) * (j : ℝ))))
  rw [show (3 : ℝ) ^ (-((s / 8) * (j : ℝ))) *
      (3 * (3 : ℝ) ^ ((s / 8) * (j : ℝ))) = 3 by
    rw [show (3 : ℝ) ^ (-((s / 8) * (j : ℝ))) *
        (3 * (3 : ℝ) ^ ((s / 8) * (j : ℝ))) =
      3 * ((3 : ℝ) ^ (-((s / 8) * (j : ℝ))) *
        (3 : ℝ) ^ ((s / 8) * (j : ℝ))) by ring,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num] at hmul
  simpa only [fieldTwoFiniteBad] using hmul

theorem fieldTwo_suffix_exceeds_mem_bad {d : ℕ}
    {s : ℝ} (k j : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hmajor : ∀ start : ℕ, ∀ x ∈ cube d (start + 1),
      0 ≤ (∏' i : ℕ, if start ≤ i then
          Real.exp (4 * |omega i x - omega i 0|) else 1) ∧
        (∏' i : ℕ, if start ≤ i then
            Real.exp (4 * |omega i x - omega i 0|) else 1) ≤
          Real.exp (expSequenceLog (fieldTwoSuffixSequence (d := d))
            (start : ℤ) omega))
    {x : Vec d} (hx : x ∈ cube d (k + 1 + j))
    (hexceeds : 3 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) <
      ∏' i : ℕ, if k + j ≤ i then
        Real.exp (4 * |omega i x - omega i 0|) else 1) :
    omega ∈ fieldTwoSuffixBad (d := d) s k := by
  refine ⟨j, ?_⟩
  unfold expSequenceExceeds
  have hcube : x ∈ cube d ((k + j) + 1) := by
    have heq : (k : ℤ) + 1 + (j : ℤ) = ((k + j : ℕ) : ℤ) + 1 := by
      push_cast
      ring
    simpa only [Int.natCast_add, Int.natCast_one, heq] using! hx
  have hprod := (hmajor (k + j) x hcube).2
  have hpow : (3 : ℝ) ^ ((s * (j : ℝ)) / 8) =
      (3 : ℝ) ^ ((s / 8) * (j : ℝ)) := by congr 1; ring
  rw [hpow] at hexceeds
  have hmul := mul_lt_mul_of_pos_left
    (hexceeds.trans_le hprod)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3)
      (-((s / 8) * (j : ℝ))))
  rw [show (3 : ℝ) ^ (-((s / 8) * (j : ℝ))) *
      (3 * (3 : ℝ) ^ ((s / 8) * (j : ℝ))) = 3 by
    rw [show (3 : ℝ) ^ (-((s / 8) * (j : ℝ))) *
        (3 * (3 : ℝ) ^ ((s / 8) * (j : ℝ))) =
      3 * ((3 : ℝ) ^ (-((s / 8) * (j : ℝ))) *
        (3 : ℝ) ^ ((s / 8) * (j : ℝ))) by ring,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num] at hmul
  simpa only [Int.natCast_add, Int.cast_natCast] using hmul

private theorem exists_point_of_lt_supNormOn {d : ℕ}
    {W : Set (Vec d)} (hW : W.Nonempty) (f : Vec d → ℝ) {a : ℝ}
    (h : a < supNormOn W f) :
    ∃ x ∈ W, a < |f x| := by
  unfold supNormOn at h
  have hS : ({r : ℝ | ∃ x ∈ W, r = |f x|}).Nonempty := by
    obtain ⟨x, hx⟩ := hW
    exact ⟨|f x|, x, hx, rfl⟩
  obtain ⟨r, ⟨x, hx, rfl⟩, hr⟩ :=
    exists_lt_of_lt_csSup hS h
  exact ⟨x, hx, hr⟩

/-- Failure of the literal second field condition is, almost surely, covered
by the finite-block and infinite-suffix bad events used in the two Appendix-B
concentration propositions. -/
theorem goodFieldTwo_compl_ae_subset_finite_union_suffix {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ k : ℕ,
      omega ∈ {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldTwo k 0 s omega}ᶜ →
        omega ∈ fieldTwoFiniteBad (d := d) s k ∪ fieldTwoSuffixBad (d := d) s k := by
  filter_upwards [ae_fieldTwo_suffix_product_le_sequenceLog M] with omega hmajor
  intro k hk
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, GoodFieldTwo, not_forall,
    not_le] at hk
  obtain ⟨j, hj⟩ := hk
  let W := translatedCube d ((k + 1 + j : ℕ) : ℤ) 0
  let finitePart : Vec d → ℝ := fun x ↦
    ∏ i ∈ Finset.Icc (k - j) (k + j), Real.exp |omega i x|
  let suffixPart : Vec d → ℝ := fun x ↦
    ∏' i : ℕ, if k + j ≤ i then
      Real.exp (4 * |omega i x - omega i 0|) else 1
  have hW : W.Nonempty := ⟨0, by
    dsimp only [W]
    rw [translatedCube_zero_eq_cube]
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.zero_mem_cube d
      ((k + 1 + j : ℕ) : ℤ)⟩
  obtain ⟨x, hx, hxlarge⟩ := exists_point_of_lt_supNormOn hW
    (fun x ↦ finitePart x + suffixPart x) hj
  have hfinite0 : 0 ≤ finitePart x := by
    dsimp only [finitePart]
    positivity
  have hsuffix0 : 0 ≤ suffixPart x := by
    dsimp only [suffixPart]
    have hxCube : x ∈ cube d ((k + j) + 1) := by
      have heq : k + 1 + j = (k + j) + 1 := by omega
      simpa only [W, translatedCube_zero_eq_cube, Int.natCast_add, Int.natCast_one, heq] using! hx
    exact (hmajor (k + j) x hxCube).1
  rw [abs_of_nonneg (add_nonneg hfinite0 hsuffix0)] at hxlarge
  have hxW : x ∈ cube d (k + 1 + j) := by
    simpa only [W, translatedCube_zero_eq_cube, Int.natCast_add, Int.natCast_one] using! hx
  by_cases hf : 3 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8) < finitePart x
  · exact Or.inl (fieldTwo_finite_exceeds_mem_bad k j omega hxW hf)
  · apply Or.inr
    apply fieldTwo_suffix_exceeds_mem_bad k j omega hmajor hxW
    dsimp only [finitePart, suffixPart] at hxlarge ⊢
    by_contra hs
    push Not at hf hs
    nlinarith

private theorem intervalEventDensity_split_of_subset {Ω : Type*}
    (C A B : ℕ → Set Ω) (theta : ℝ) (m0 K : ℕ) (omega : Ω)
    (hsub : ∀ k, omega ∈ C k → omega ∈ A k ∪ B k)
    (hbad : theta ≤ intervalEventDensity C m0 K omega) :
    theta / 2 ≤ intervalEventDensity A m0 K omega ∨
      theta / 2 ≤ intervalEventDensity B m0 K omega := by
  let I := Finset.Icc m0 (m0 + K)
  have hpoint : ∀ k, eventIndicator (C k) omega ≤
      eventIndicator (A k) omega + eventIndicator (B k) omega := by
    intro k
    by_cases hC : omega ∈ C k
    · rcases hsub k hC with hA | hB
      · by_cases hB' : omega ∈ B k <;>
          simp [eventIndicator, hC, hA, hB']
      · by_cases hA' : omega ∈ A k <;>
          simp [eventIndicator, hC, hA', hB]
    · by_cases hA : omega ∈ A k <;> by_cases hB : omega ∈ B k <;>
        simp [eventIndicator, hC, hA, hB]
  have hsum : ∑ k ∈ I, eventIndicator (C k) omega ≤
      (∑ k ∈ I, eventIndicator (A k) omega) +
        ∑ k ∈ I, eventIndicator (B k) omega := by
    calc
      _ ≤ ∑ k ∈ I,
          (eventIndicator (A k) omega + eventIndicator (B k) omega) :=
        Finset.sum_le_sum fun k _ ↦ hpoint k
      _ = _ := by rw [Finset.sum_add_distrib]
  have hden : 0 < ((K : ℝ) + 1) := by positivity
  have htotal : theta ≤ intervalEventDensity A m0 K omega +
      intervalEventDensity B m0 K omega := by
    unfold intervalEventDensity at hbad ⊢
    have hdiv := (div_le_div_iff_of_pos_right hden).2 hsum
    calc
      theta ≤ (∑ k ∈ I, eventIndicator (C k) omega) / ((K : ℝ) + 1) := hbad
      _ ≤ ((∑ k ∈ I, eventIndicator (A k) omega) +
          ∑ k ∈ I, eventIndicator (B k) omega) / ((K : ℝ) + 1) := hdiv
      _ = _ := by ring
  by_contra h
  push Not at h
  linarith

private theorem sum_intIndicator_eq_natIndicator {d : ℕ}
    (s : ℝ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (m0 K : ℕ) :
    (∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 + K : ℕ) : ℤ),
        if omega ∈ expSequenceBad (fieldTwoSuffixSequence (d := d))
            (s / 8) k then (1 : ℝ) else 0) =
      ∑ k ∈ Finset.Icc m0 (m0 + K),
        eventIndicator (fieldTwoSuffixBad (d := d) s k) omega := by
  classical
  apply Finset.sum_bij (fun k _ ↦ k.toNat)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro a ha b hb hab
    have ha0 : 0 ≤ a := by
      have ham := (Finset.mem_Icc.mp ha).1
      have hm0 : (0 : ℤ) ≤ (m0 : ℤ) := Int.natCast_nonneg m0
      omega
    have hb0 : 0 ≤ b := by
      have hbm := (Finset.mem_Icc.mp hb).1
      have hm0 : (0 : ℤ) ≤ (m0 : ℤ) := Int.natCast_nonneg m0
      omega
    omega
  · intro k hk
    refine ⟨(k : ℤ), ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hk ⊢
      exact ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩
    · simp
  · intro k hk
    have hk0 : 0 ≤ k := by
      have hkm := (Finset.mem_Icc.mp hk).1
      have hm0 : (0 : ℤ) ≤ (m0 : ℤ) := Int.natCast_nonneg m0
      omega
    simp only [fieldTwoSuffixBad, eventIndicator,
      Int.toNat_of_nonneg hk0]

theorem expSequenceDensityEvent_fieldTwoSuffix_eq {d : ℕ}
    (s theta : ℝ) (m0 K : ℕ) :
    expSequenceDensityEvent (fieldTwoSuffixSequence (d := d))
        (s / 8) theta (m0 : ℤ) K =
      {omega | theta ≤ intervalEventDensity
        (fieldTwoSuffixBad (d := d) s) m0 K omega} := by
  ext omega
  simp only [expSequenceDensityEvent, Set.mem_ofPred_eq, intervalEventDensity]
  have hu : (m0 : ℤ) + (K : ℤ) = ((m0 + K : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hu]
  rw [sum_intIndicator_eq_natIndicator s omega m0 K]
  rw [div_eq_mul_inv]
  ring_nf

/-- The exact two-concentration reduction for the second field event.  Its
two right-hand terms are the finite block and infinite suffix estimates from
the manuscript. -/
theorem measure_goodFieldTwo_badDensity_le_components {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s theta : ℝ) (m0 K : ℕ) :
    M.P.toMeasure {omega | theta ≤ intervalEventDensity
        (fun k ↦ {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldTwo k 0 s omega}ᶜ) m0 K omega} ≤
      M.P.toMeasure {omega | theta / 2 ≤ intervalEventDensity
        (fieldTwoFiniteBad (d := d) s) m0 K omega} +
      M.P.toMeasure {omega | theta / 2 ≤ intervalEventDensity
        (fieldTwoSuffixBad (d := d) s) m0 K omega} := by
  let E : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) := {omega | theta ≤ intervalEventDensity
    (fun k ↦ {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldTwo k 0 s omega}ᶜ) m0 K omega}
  let EF : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) := {omega | theta / 2 ≤ intervalEventDensity
    (fieldTwoFiniteBad (d := d) s) m0 K omega}
  let ES : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) := {omega | theta / 2 ≤ intervalEventDensity
    (fieldTwoSuffixBad (d := d) s) m0 K omega}
  let EU : Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) := {omega | omega ∈ EF ∨ omega ∈ ES}
  have hsub : E ≤ᵐ[M.P.toMeasure] EU := by
    filter_upwards [goodFieldTwo_compl_ae_subset_finite_union_suffix M s] with
        omega hcover homega
    exact intervalEventDensity_split_of_subset
      (fun k ↦ {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldTwo k 0 s omega}ᶜ)
      (fieldTwoFiniteBad (d := d) s) (fieldTwoSuffixBad (d := d) s)
      theta m0 K omega (fun k ↦ hcover k) homega
  calc
    M.P.toMeasure E ≤ M.P.toMeasure EU := measure_mono_ae hsub
    _ = M.P.toMeasure (EF ∪ ES) := by rfl
    _ ≤ M.P.toMeasure EF + M.P.toMeasure ES := measure_union_le _ _

theorem measure_goodFieldTwo_badDensity_le_exp_add_exp {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {s theta : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hscale1 : fieldTwoSuffixSequenceScale M ≤ 1)
    (hfiniteSmall : M.delta ≤ (expFieldConcentrationConst d)⁻¹ * (s / 8) *
      Real.sqrt (min (theta / 2) (((1 : ℕ) : ℝ)⁻¹)))
    (hsuffixSmall : fieldTwoSuffixSequenceScale M ≤
      expSequenceConcentrationConst⁻¹ * (s / 8) * Real.sqrt (theta / 2))
    (m0 K : ℕ) :
    M.P.toMeasure {omega | theta ≤ intervalEventDensity
        (fun k ↦ {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldTwo k 0 s omega}ᶜ) m0 K omega} ≤
      ENNReal.ofReal (Real.exp
        (-((s / 8) ^ 2 * (theta / 2) /
          (96 * expFieldMomentDenom * M.delta ^ 2)) * ((K : ℝ) + 1))) +
      ENNReal.ofReal (Real.exp
        (-((s / 8) ^ 2 * (theta / 2)) /
          (expSequenceConcentrationConst * fieldTwoSuffixSequenceScale M ^ 2) *
            ((K : ℝ) + 1))) := by
  refine (measure_goodFieldTwo_badDensity_le_components M s theta m0 K).trans ?_
  apply add_le_add
  · simpa only [fieldTwoFiniteBad] using!
      concentration_exp_field M
        (s := s / 8) (theta := theta / 2) (by positivity) (by linarith)
        (by positivity) (by linarith) (h := 1) (by omega) hfiniteSmall m0 K
  · rw [← expSequenceDensityEvent_fieldTwoSuffix_eq s (theta / 2) m0 K]
    exact concentration_exp_sequence
      (fieldTwoSuffixSequenceScale_pos M) hscale1
      (by positivity) (by linarith) (by positivity) (by linarith)
      fieldTwoSuffixSequence_nonneg measurable_fieldTwoSuffixSequence
      (iIndepFun_fieldTwoSuffixSequence M)
      (isBigOWith_gammaTwo_fieldTwoSuffixSequence M) hsuffixSmall (m0 : ℤ) K

/-! ## Source-scale universal constant -/

def fieldTwoSuffixScaleConst (d : ℕ) : ℝ :=
  12 * gammaTriangleConst 2 *
    (((1 + Real.log 2) ^ (2 : ℝ)⁻¹) +
      ((3 * Real.log ((shellCoverShifts d 1).card : ℝ)) ^ (2 : ℝ)⁻¹) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹))

theorem fieldTwoSuffixSequenceScale_eq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    fieldTwoSuffixSequenceScale M = fieldTwoSuffixScaleConst d * M.delta := by
  unfold fieldTwoSuffixSequenceScale fieldTwoSuffixScaleConst
  ring

theorem fieldTwoSuffixScaleConst_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    0 < fieldTwoSuffixScaleConst d := by
  have h := fieldTwoSuffixSequenceScale_pos M
  rw [fieldTwoSuffixSequenceScale_eq M] at h
  rcases (mul_pos_iff.mp h) with hp | hn
  · exact hp.1
  · exact False.elim ((not_lt_of_ge M.shellPrefix.delta_pos.le) hn.2)

def fieldTwoRateDenom (d : ℕ) : ℝ :=
  12288 * expFieldMomentDenom +
    128 * expSequenceConcentrationConst * fieldTwoSuffixScaleConst d ^ 2

theorem fieldTwoRateDenom_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    0 < fieldTwoRateDenom d := by
  unfold fieldTwoRateDenom
  exact add_pos
    (mul_pos (by norm_num) expFieldMomentDenom_pos)
    (mul_pos (mul_pos (by norm_num) expSequenceConcentrationConst_pos)
      (sq_pos_of_pos (fieldTwoSuffixScaleConst_pos M)))

def fieldTwoDensityConst (d : ℕ) : ℝ :=
  1 + 16 * expFieldConcentrationConst d +
    16 * expSequenceConcentrationConst * fieldTwoSuffixScaleConst d +
    2 * fieldTwoSuffixScaleConst d +
    4 * fieldTwoRateDenom d * (1 + Real.log 2)

theorem fieldTwoDensityConst_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    0 < fieldTwoDensityConst d := by
  unfold fieldTwoDensityConst
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hF := expFieldConcentrationConst_pos d
  have hS := expSequenceConcentrationConst_pos
  have hD := fieldTwoSuffixScaleConst_pos M
  have hR := fieldTwoRateDenom_pos M
  positivity

private theorem sqrt_half_eq {theta : ℝ} (htheta : 0 ≤ theta) :
    Real.sqrt (theta / 2) = Real.sqrt theta / Real.sqrt 2 := by
  rw [Real.sqrt_div htheta]

/-- Source-form density estimate for `GoodFieldTwo`, with all truncation and
two-product constants absorbed into one dimension-only constant. -/
theorem measure_goodFieldTwo_badDensity_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {s theta : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hsmall : M.delta ≤ (fieldTwoDensityConst d)⁻¹ * s * Real.sqrt theta)
    (m0 K : ℕ) :
    M.P.toMeasure {omega | theta ≤ intervalEventDensity
        (fun k ↦ {omega : _root_.SubdiffusiveProcess.Model.PotentialSample d | GoodFieldTwo k 0 s omega}ᶜ) m0 K omega} ≤
      ENNReal.ofReal (Real.exp
        (-(s ^ 2 * theta /
          (2 * fieldTwoRateDenom d * M.delta ^ 2)) * ((K : ℝ) + 1))) := by
  let C := fieldTwoDensityConst d
  let D := fieldTwoSuffixScaleConst d
  let R := fieldTwoRateDenom d
  have hdelta := M.shellPrefix.delta_pos
  have hC : 0 < C := fieldTwoDensityConst_pos M
  have hD : 0 < D := fieldTwoSuffixScaleConst_pos M
  have hR : 0 < R := fieldTwoRateDenom_pos M
  have hbudget : C * M.delta ≤ s * Real.sqrt theta := by
    calc
      C * M.delta ≤ C * (C⁻¹ * s * Real.sqrt theta) :=
        mul_le_mul_of_nonneg_left hsmall hC.le
      _ = s * Real.sqrt theta := by field_simp [hC.ne']
  have hCfield : 16 * expFieldConcentrationConst d ≤ C := by
    unfold C fieldTwoDensityConst
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hS := expSequenceConcentrationConst_pos.le
    have hD0 := hD.le
    have hR0 := hR.le
    nlinarith [expFieldConcentrationConst_pos d]
  have hCseq : 16 * expSequenceConcentrationConst * D ≤ C := by
    unfold C fieldTwoDensityConst D
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hF := (expFieldConcentrationConst_pos d).le
    have hS := expSequenceConcentrationConst_pos.le
    have hD0 := hD.le
    have hR0 := hR.le
    nlinarith
  have hCD : 2 * D ≤ C := by
    unfold C fieldTwoDensityConst D
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hF := (expFieldConcentrationConst_pos d).le
    have hS := expSequenceConcentrationConst_pos.le
    have hD0 := hD.le
    have hR0 := hR.le
    nlinarith
  have hsqrtTheta0 := Real.sqrt_nonneg theta
  have hsqrtTheta1 : Real.sqrt theta ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt htheta1
  have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hfiniteSmall : M.delta ≤ (expFieldConcentrationConst d)⁻¹ * (s / 8) *
      Real.sqrt (min (theta / 2) (((1 : ℕ) : ℝ)⁻¹)) := by
    have hfirst : 16 * expFieldConcentrationConst d * M.delta ≤
        s * Real.sqrt theta :=
      (mul_le_mul_of_nonneg_right hCfield hdelta.le).trans hbudget
    have hthetaHalf : theta / 2 ≤ 1 := by linarith
    have hone : (((1 : ℕ) : ℝ)⁻¹) = 1 := by norm_num
    rw [hone, min_eq_left hthetaHalf, sqrt_half_eq htheta.le]
    have hEF := expFieldConcentrationConst_pos d
    have hsqrt2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
    rw [show (expFieldConcentrationConst d)⁻¹ * (s / 8) *
        (Real.sqrt theta / Real.sqrt 2) =
          s * Real.sqrt theta /
            (8 * expFieldConcentrationConst d * Real.sqrt 2) by
      field_simp [hEF.ne', hsqrt2.ne']
      ]
    rw [le_div_iff₀ (mul_pos (mul_pos (by norm_num) hEF) hsqrt2)]
    calc
      M.delta * (8 * expFieldConcentrationConst d * Real.sqrt 2) ≤
          M.delta * (16 * expFieldConcentrationConst d) := by
        apply mul_le_mul_of_nonneg_left _ hdelta.le
        nlinarith only [hsqrtTwo, hEF]
      _ = 16 * expFieldConcentrationConst d * M.delta := by ring
      _ ≤ s * Real.sqrt theta := hfirst
  have hsuffixSmall : fieldTwoSuffixSequenceScale M ≤
      expSequenceConcentrationConst⁻¹ * (s / 8) * Real.sqrt (theta / 2) := by
    rw [fieldTwoSuffixSequenceScale_eq M, sqrt_half_eq htheta.le]
    have hfirst : 16 * expSequenceConcentrationConst * D * M.delta ≤
        s * Real.sqrt theta :=
      (mul_le_mul_of_nonneg_right hCseq hdelta.le).trans hbudget
    have hES := expSequenceConcentrationConst_pos
    have hsqrt2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
    rw [show expSequenceConcentrationConst⁻¹ * (s / 8) *
        (Real.sqrt theta / Real.sqrt 2) =
          s * Real.sqrt theta /
            (8 * expSequenceConcentrationConst * Real.sqrt 2) by
      field_simp [hES.ne', hsqrt2.ne']
      ]
    rw [le_div_iff₀ (mul_pos (mul_pos (by norm_num) hES) hsqrt2)]
    calc
      D * M.delta * (8 * expSequenceConcentrationConst * Real.sqrt 2) ≤
          D * M.delta * (16 * expSequenceConcentrationConst) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD.le hdelta.le)
        nlinarith only [hsqrtTwo, hES]
      _ = 16 * expSequenceConcentrationConst * D * M.delta := by ring
      _ ≤ s * Real.sqrt theta := hfirst
  have hscale1 : fieldTwoSuffixSequenceScale M ≤ 1 := by
    rw [fieldTwoSuffixSequenceScale_eq M]
    have hfirst : 2 * D * M.delta ≤ s * Real.sqrt theta :=
      (mul_le_mul_of_nonneg_right hCD hdelta.le).trans hbudget
    have hs1sqrt : s * Real.sqrt theta ≤ 1 := by
      calc
        s * Real.sqrt theta ≤ s * 1 :=
          mul_le_mul_of_nonneg_left hsqrtTheta1 hs.le
        _ = s := mul_one s
        _ ≤ 1 := hs1
    nlinarith
  have hraw := measure_goodFieldTwo_badDensity_le_exp_add_exp M hs hs1 htheta
    htheta1 hscale1 hfiniteSmall hsuffixSmall m0 K
  let A := s ^ 2 * theta / M.delta ^ 2 * ((K : ℝ) + 1)
  have hA0 : 0 ≤ A := by
    unfold A
    exact mul_nonneg
      (div_nonneg (mul_nonneg (sq_nonneg s) htheta.le) (sq_nonneg M.delta))
      (by positivity)
  have hRf : 12288 * expFieldMomentDenom ≤ R := by
    unfold R fieldTwoRateDenom
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) expSequenceConcentrationConst_pos.le)
        (sq_nonneg _))
  have hRs : 128 * expSequenceConcentrationConst * D ^ 2 ≤ R := by
    unfold R fieldTwoRateDenom D
    exact le_add_of_nonneg_left
      (mul_nonneg (by norm_num) expFieldMomentDenom_pos.le)
  have hsmallExp :
      Real.exp (-((s / 8) ^ 2 * (theta / 2) /
          (96 * expFieldMomentDenom * M.delta ^ 2)) * ((K : ℝ) + 1)) ≤
        Real.exp (-A / R) := by
    apply Real.exp_le_exp.2
    have heq : ((s / 8) ^ 2 * (theta / 2) /
          (96 * expFieldMomentDenom * M.delta ^ 2)) * ((K : ℝ) + 1) =
        A / (12288 * expFieldMomentDenom) := by
      unfold A
      field_simp [hdelta.ne', expFieldMomentDenom_pos.ne']
      ring
    rw [neg_mul, heq]
    simpa only [neg_div] using neg_le_neg (div_le_div_of_nonneg_left hA0
      (mul_pos (by norm_num) expFieldMomentDenom_pos) hRf)
  have hsuffixExp :
      Real.exp (-((s / 8) ^ 2 * (theta / 2)) /
          (expSequenceConcentrationConst * fieldTwoSuffixSequenceScale M ^ 2) *
            ((K : ℝ) + 1)) ≤ Real.exp (-A / R) := by
    apply Real.exp_le_exp.2
    rw [fieldTwoSuffixSequenceScale_eq M]
    change -((s / 8) ^ 2 * (theta / 2)) /
          (expSequenceConcentrationConst * (D * M.delta) ^ 2) *
            ((K : ℝ) + 1) ≤ -A / R
    have heq : ((s / 8) ^ 2 * (theta / 2)) /
          (expSequenceConcentrationConst * (D * M.delta) ^ 2) *
            ((K : ℝ) + 1) =
        A / (128 * expSequenceConcentrationConst * D ^ 2) := by
      unfold A
      field_simp [hdelta.ne', hD.ne', expSequenceConcentrationConst_pos.ne']
      ring
    rw [neg_div, neg_mul, heq]
    simpa only [neg_div] using neg_le_neg (div_le_div_of_nonneg_left hA0
      (mul_pos (mul_pos (by norm_num) expSequenceConcentrationConst_pos)
        (sq_pos_of_pos hD)) hRs)
  have hAR : 2 * Real.log 2 ≤ A / R := by
    have hCexp : 4 * R * (1 + Real.log 2) ≤ C := by
      unfold C fieldTwoDensityConst R
      have hF := (expFieldConcentrationConst_pos d).le
      have hS := expSequenceConcentrationConst_pos.le
      have hD0 := hD.le
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    have hsqBudget := pow_le_pow_left₀
      (mul_nonneg hC.le hdelta.le) hbudget 2
    have hthetaSq : (Real.sqrt theta) ^ 2 = theta := Real.sq_sqrt htheta.le
    have hbase : C ^ 2 ≤ s ^ 2 * theta / M.delta ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hdelta)]
      nlinarith only [hsqBudget, hthetaSq]
    have hK1 : 1 ≤ (K : ℝ) + 1 := by norm_num
    have hAle : C ^ 2 ≤ A := by
      unfold A
      have hmul := mul_le_mul_of_nonneg_left hK1
        (div_nonneg (mul_nonneg (sq_nonneg s) htheta.le) (sq_nonneg M.delta))
      exact hbase.trans (by simpa only [mul_one] using hmul)
    rw [le_div_iff₀ hR]
    have hlog0 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hC1 : 1 ≤ C := by
      unfold C fieldTwoDensityConst
      have hF0 : 0 ≤ 16 * expFieldConcentrationConst d :=
        mul_nonneg (by norm_num) (expFieldConcentrationConst_pos d).le
      have hS0 : 0 ≤ 16 * expSequenceConcentrationConst *
          fieldTwoSuffixScaleConst d :=
        mul_nonneg (mul_nonneg (by norm_num) expSequenceConcentrationConst_pos.le)
          (fieldTwoSuffixScaleConst_pos M).le
      have hD0 : 0 ≤ 2 * fieldTwoSuffixScaleConst d :=
        mul_nonneg (by norm_num) (fieldTwoSuffixScaleConst_pos M).le
      have hR0 : 0 ≤ 4 * fieldTwoRateDenom d * (1 + Real.log 2) := by
        exact mul_nonneg
          (mul_nonneg (by norm_num) (fieldTwoRateDenom_pos M).le)
          (by linarith)
      linarith
    calc
      2 * Real.log 2 * R ≤ 4 * R * (1 + Real.log 2) := by nlinarith
      _ ≤ C := hCexp
      _ ≤ C ^ 2 := by nlinarith only [hC1]
      _ ≤ A := hAle
  have habsorb : 2 * Real.exp (-A / R) ≤ Real.exp (-A / (2 * R)) := by
    rw [show 2 * Real.exp (-A / R) =
        Real.exp (Real.log 2 + (-A / R)) by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]]
    apply Real.exp_le_exp.2
    have hhalf : A / (2 * R) = (A / R) / 2 := by
      field_simp [hR.ne']
    rw [show -A / R = -(A / R) by rw [neg_div],
      show -A / (2 * R) = -(A / (2 * R)) by rw [neg_div], hhalf]
    nlinarith only [hAR]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-A / R)) +
        ENNReal.ofReal (Real.exp (-A / R)) :=
      hraw.trans (add_le_add (ENNReal.ofReal_le_ofReal hsmallExp)
        (ENNReal.ofReal_le_ofReal hsuffixExp))
    _ = ENNReal.ofReal (2 * Real.exp (-A / R)) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (Real.exp (-A / (2 * R))) :=
      ENNReal.ofReal_le_ofReal habsorb
    _ = _ := by
      congr 2
      unfold A R
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
