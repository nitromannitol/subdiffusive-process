module

public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ShellColumns
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge
public import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodFieldTwo

@[expose] public section

/-!
# Local finite-suffix scores for `GoodFieldTwo`

The literal second field condition contains an infinite suffix product.  This
module replaces its logarithm by finite, one-shell-measurable oscillation
scores.  The finite truncations have honest `ColumnsIndep`; almost-sure
summability identifies their limit with the full suffix envelope.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open scoped BigOperators ENNReal

noncomputable section

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

private theorem shellSigma_eq_singleton (d i : ℕ) :
    shellSigma d i = potentialShellIndexSigma (d := d) ({i} : Set ℕ) := by
  apply le_antisymm
  · exact le_iSup_of_le i (le_iSup_of_le (Set.mem_singleton i) le_rfl)
  · refine iSup_le fun k ↦ iSup_le fun hk ↦ ?_
    rw [Set.mem_singleton_iff] at hk
    subst k
    exact le_rfl

/-! ## Literal suffix layers -/

/-- Four times the shell-`i` oscillation envelope on the scale-`k+1` cube. -/
def fieldTwoSuffixLayer {d : ℕ} (k i : ℕ) : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  fun omega ↦ 4 * shellOscillationEnvelope i ((k + 1 : ℕ) : ℤ) omega

theorem fieldTwoSuffixLayer_nonneg {d : ℕ} (k i : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ fieldTwoSuffixLayer k i omega :=
  mul_nonneg (by norm_num) (shellOscillationEnvelope_nonneg i _ omega)

theorem measurable_fieldTwoSuffixLayer_shellSigma {d : ℕ} (k i : ℕ) :
    Measurable[shellSigma d i] (fieldTwoSuffixLayer (d := d) k i) := by
  unfold fieldTwoSuffixLayer shellOscillationEnvelope
  by_cases h : ((k + 1 : ℕ) : ℤ) ≤ (i : ℤ)
  · simp only [h, ite_true]
    rw [shellSigma_eq_singleton]
    exact measurable_const.mul (measurable_const.mul
      (measurable_translatedShellG2_potentialShellIndexSigma
        (d := d) (Set.mem_singleton i) 0))
  · simp only [h, ite_false]
    rw [shellSigma_eq_singleton]
    exact measurable_const.mul (measurable_const.mul
      (measurable_largeCubeShellG2_potentialShellIndexSigma
        (d := d) (Set.mem_singleton i) _))

theorem four_abs_shell_sub_le_fieldTwoSuffixLayer {d : ℕ}
    (k i : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ translatedCube d ((k + 1 : ℕ) : ℤ) 0) :
    4 * |omega i x - omega i 0| ≤ fieldTwoSuffixLayer k i omega := by
  have hx' : x ∈ openCubeSet (originCube d ((k + 1 : ℕ) : ℤ)) := by
    rcases hx with ⟨u, hu, rfl⟩
    simpa only [zero_add, cube] using! hu
  have hzero : (0 : Vec d) ∈ openCubeSet (originCube d ((k + 1 : ℕ) : ℤ)) := by
    rw [mem_openCubeSet_originCube_iff]
    intro a
    have hp : 0 < (3 : ℝ) ^ ((k + 1 : ℕ) : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  have hforward := sub_le_cubeOscillation_of_continuous
    ((k + 1 : ℕ) : ℤ) (omega i).1.1.continuous hx' hzero
  have hbackward := sub_le_cubeOscillation_of_continuous
    ((k + 1 : ℕ) : ℤ) (omega i).1.1.continuous hzero hx'
  have habs : |omega i x - omega i 0| ≤
      cubeOscillation ((k + 1 : ℕ) : ℤ) (omega i) := by
    rw [abs_le]
    constructor
    · linarith only [hbackward]
    · exact hforward
  exact (mul_le_mul_of_nonneg_left habs (by norm_num)).trans
    (mul_le_mul_of_nonneg_left
      (cubeOscillation_le_shellOscillationEnvelope i _ omega) (by norm_num))

def fieldTwoSuffixLogTrunc {d : ℕ} (N k : ℕ) : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  fun omega ↦ ∑ q ∈ Finset.range N, fieldTwoSuffixLayer k (k + q) omega

theorem fieldTwoSuffixLogTrunc_nonneg {d : ℕ} (N k : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ fieldTwoSuffixLogTrunc N k omega :=
  Finset.sum_nonneg fun q _ ↦ fieldTwoSuffixLayer_nonneg k (k + q) omega

theorem sum_four_abs_shell_sub_le_fieldTwoSuffixLogTrunc {d : ℕ}
    (N k : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ translatedCube d ((k + 1 : ℕ) : ℤ) 0) :
    (∑ q ∈ Finset.range N, 4 * |omega (k + q) x - omega (k + q) 0|) ≤
      fieldTwoSuffixLogTrunc N k omega :=
  Finset.sum_le_sum fun q _ ↦
    four_abs_shell_sub_le_fieldTwoSuffixLayer k (k + q) omega hx

theorem prod_exp_four_abs_shell_sub_le_exp_fieldTwoSuffixLogTrunc {d : ℕ}
    (N k : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {x : Vec d}
    (hx : x ∈ translatedCube d ((k + 1 : ℕ) : ℤ) 0) :
    (∏ q ∈ Finset.range N,
        Real.exp (4 * |omega (k + q) x - omega (k + q) 0|)) ≤
      Real.exp (fieldTwoSuffixLogTrunc N k omega) := by
  rw [← Real.exp_sum]
  exact Real.exp_le_exp.mpr
    (sum_four_abs_shell_sub_le_fieldTwoSuffixLogTrunc N k omega hx)

theorem ae_summable_fieldTwoSuffixLayer {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      Summable fun q : ℕ ↦ fieldTwoSuffixLayer k (k + q) omega := by
  filter_upwards [ae_summable_sensitivityLayer M k ((k + 1 : ℕ) : ℤ)] with
      omega hsum
  apply (summable_nat_add_iff 1).mp
  convert hsum.mul_left 4 using 1
  funext q
  unfold fieldTwoSuffixLayer sensitivityLayer sensitivityShellIndex
  congr 2
  omega

theorem ae_tendsto_fieldTwoSuffixLogTrunc {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      Filter.Tendsto (fun N ↦ fieldTwoSuffixLogTrunc N k omega) Filter.atTop
        (nhds (∑' q : ℕ, fieldTwoSuffixLayer k (k + q) omega)) := by
  filter_upwards [ae_summable_fieldTwoSuffixLayer M k] with omega hsum
  simpa only [fieldTwoSuffixLogTrunc] using hsum.hasSum.tendsto_sum_nat

/-! ## One-shell Gamma-two normalization -/

/-- Natural-index form of one active, weighted suffix entry. -/
def fieldTwoSuffixWeightedLayer {d : ℕ} (s K : ℝ) (k i : ℕ) :
    _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦
  K * (3 : ℝ) ^ (s * ((i : ℝ) - (k : ℝ))) *
    fieldTwoSuffixLayer k i omega

/-- Its exact Gamma-two scale inherited from the shell oscillation envelope. -/
def fieldTwoSuffixWeightedLayerScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s K : ℝ) (k i : ℕ) : ℝ :=
  (4 * K * (3 : ℝ) ^ (s * ((i : ℝ) - (k : ℝ)))) *
    ((2 * max 1 (Real.sqrt (shellCoverLogConst * (d : ℝ)))) *
      (3 : ℝ) ^ (((k + 1 : ℕ) : ℤ) - (i : ℤ)) *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta))

theorem fieldTwoSuffixWeightedLayerScale_pos {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K : ℝ} (hK : 0 < K)
    (k i : ℕ) :
    0 < fieldTwoSuffixWeightedLayerScale M s K k i := by
  unfold fieldTwoSuffixWeightedLayerScale
  have hlog : 0 < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  exact mul_pos
    (mul_pos (mul_pos (by norm_num) hK) (Real.rpow_pos_of_pos (by norm_num) _))
    (mul_pos
      (mul_pos (by positivity) (zpow_pos (by norm_num) _))
      (mul_pos (Real.rpow_pos_of_pos hlog _) M.shellPrefix.delta_pos))

theorem fieldTwoSuffixWeightedLayer_nonneg {d : ℕ} {s K : ℝ}
    (hK : 0 ≤ K) (k i : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ fieldTwoSuffixWeightedLayer s K k i omega := by
  unfold fieldTwoSuffixWeightedLayer
  exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (by norm_num) _))
    (fieldTwoSuffixLayer_nonneg _ _ _)

theorem isBigOWith_gammaTwo_fieldTwoSuffixWeightedLayer {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K : ℝ} (hK : 0 ≤ K)
    (k i : ℕ) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fieldTwoSuffixWeightedLayer (d := d) s K k i)
      (fieldTwoSuffixWeightedLayerScale M s K k i) := by
  have hc : 0 ≤ 4 * K * (3 : ℝ) ^ (s * ((i : ℝ) - (k : ℝ))) := by
    positivity
  have hbase :=
    (isBigOWith_gammaTwo_shellOscillationEnvelope M i ((k + 1 : ℕ) : ℤ)).const_mul hc
  convert hbase using 1
  · funext omega
    simp only [fieldTwoSuffixWeightedLayer, fieldTwoSuffixLayer]
    ring
  · simp only [fieldTwoSuffixWeightedLayerScale]

/-- Moment normalization in the exact form consumed by
`concentration_for_scales`; only a numerical scale inequality remains. -/
theorem lintegral_fieldTwoSuffixWeightedLayer_rpow_le_one {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s K p : ℝ}
    (hK : 0 < K) (hp : 1 ≤ p) (k i : ℕ)
    (hnorm : gammaMomentConst 2 * Real.sqrt p *
        fieldTwoSuffixWeightedLayerScale M s K k i ≤ 1) :
    ∫⁻ omega,
        ENNReal.ofReal ((fieldTwoSuffixWeightedLayer s K k i omega) ^ p)
      ∂M.P.toMeasure ≤ 1 := by
  have hraw := lintegral_rpow_le_of_isBigOWith_gammaSigma
    (μ := M.P.toMeasure) (Y := fieldTwoSuffixWeightedLayer (d := d) s K k i)
    (K := fieldTwoSuffixWeightedLayerScale M s K k i) (σ := 2) (p := p)
    (by norm_num) (fieldTwoSuffixWeightedLayerScale_pos M hK k i) hp
    (fieldTwoSuffixWeightedLayer_nonneg hK.le k i)
    (((measurable_fieldTwoSuffixLayer_shellSigma k i).const_mul _).mono
      (shellSigma_le i) le_rfl).aemeasurable
    (isBigOWith_gammaTwo_fieldTwoSuffixWeightedLayer M hK.le k i)
  refine hraw.trans ?_
  rw [ENNReal.ofReal_le_one]
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hbase : 0 ≤ gammaMomentConst 2 * p ^ (2 : ℝ)⁻¹ *
      fieldTwoSuffixWeightedLayerScale M s K k i := by
    exact mul_nonneg
      (mul_nonneg (gammaMomentConst_pos (by norm_num)).le
        (Real.rpow_nonneg (by positivity) _))
      (fieldTwoSuffixWeightedLayerScale_pos M hK k i).le
  apply Real.rpow_le_one hbase
  · simpa only [Real.sqrt_eq_rpow, one_div] using hnorm
  · exact hp0.le

/-! ## The truncated Appendix-B array -/

/-- The factor `3^(s(i-k))` compensates `Yk`'s row weight on an active entry. -/
def fieldTwoSuffixScoreArray {d : ℕ} (N : ℕ) (s K : ℝ) :
    ℤ → ℤ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
  fun k i omega ↦
    if 0 ≤ k ∧ 0 ≤ i ∧ k ≤ i ∧ i < k + (N : ℤ) then
      K * (3 : ℝ) ^ (s * ((i - k : ℤ) : ℝ)) *
        fieldTwoSuffixLayer k.toNat i.toNat omega
    else 0

theorem fieldTwoSuffixScoreArray_nonneg {d : ℕ} (N : ℕ) {s K : ℝ}
    (hK : 0 ≤ K) (k i : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ fieldTwoSuffixScoreArray (d := d) N s K k i omega := by
  unfold fieldTwoSuffixScoreArray
  split_ifs
  · exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (by norm_num) _))
      (fieldTwoSuffixLayer_nonneg _ _ _)
  · exact le_rfl

theorem measurable_fieldTwoSuffixScoreArray {d : ℕ}
    (N : ℕ) (s K : ℝ) (k i : ℤ) :
    Measurable (fieldTwoSuffixScoreArray (d := d) N s K k i) := by
  unfold fieldTwoSuffixScoreArray
  split_ifs
  · exact measurable_const.mul
      ((measurable_fieldTwoSuffixLayer_shellSigma k.toNat i.toNat).mono
        (shellSigma_le i.toNat) le_rfl)
  · exact measurable_const

theorem columnsIndep_fieldTwoSuffixScoreArray {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) (s K : ℝ)
    {r : ℕ} (hr : 1 ≤ r) :
    SubdiffusiveProcess.Concentration.ColumnsIndep M.P.toMeasure
      (fieldTwoSuffixScoreArray (d := d) N s K) r := by
  apply columnsIndep_of_nonnegative_shellColumn_of_constant M _ hr
  · intro k i hi
    unfold fieldTwoSuffixScoreArray
    split_ifs
    · exact measurable_const.mul
        (measurable_fieldTwoSuffixLayer_shellSigma k.toNat i.toNat)
    · exact measurable_const
  · intro k i hi
    refine ⟨0, fun omega ↦ ?_⟩
    simp [fieldTwoSuffixScoreArray, show ¬0 ≤ i by omega]

theorem Yk_fieldTwoSuffixScoreArray_eq {d : ℕ}
    (N k : ℕ) (s K : ℝ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    SubdiffusiveProcess.Concentration.Yk (fieldTwoSuffixScoreArray (d := d) N s K)
        s (k : ℤ) omega =
      K * fieldTwoSuffixLogTrunc N k omega := by
  rw [SubdiffusiveProcess.Concentration.Yk, tsum_eq_sum
    (s := Finset.Ico (k : ℤ) ((k + N : ℕ) : ℤ))]
  · rw [Int.Ico_eq_finset_map, Finset.sum_map]
    have hlen : ((((k + N : ℕ) : ℤ) - (k : ℤ)).toNat) = N := by omega
    rw [hlen]
    unfold fieldTwoSuffixLogTrunc
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    change SubdiffusiveProcess.Concentration.wt s (k : ℤ) ((k : ℤ) + (q : ℤ)) *
        fieldTwoSuffixScoreArray N s K (k : ℤ) ((k : ℤ) + (q : ℤ)) omega =
      K * fieldTwoSuffixLayer k (k + q) omega
    have hqN : q < N := Finset.mem_range.mp hq
    have hactive : (0 : ℤ) ≤ (k : ℤ) ∧ 0 ≤ (k : ℤ) + (q : ℤ) ∧
        (k : ℤ) ≤ (k : ℤ) + (q : ℤ) ∧
          (k : ℤ) + (q : ℤ) < (k : ℤ) + (N : ℤ) := by omega
    rw [fieldTwoSuffixScoreArray, ite_eq_left hactive]
    have hsub : (k : ℤ) + (q : ℤ) - (k : ℤ) = (q : ℤ) := by ring
    have htoNat : ((k : ℤ) + (q : ℤ)).toNat = k + q := by omega
    rw [hsub, htoNat]
    push_cast
    rw [SubdiffusiveProcess.Concentration.wt]
    have hidist : SubdiffusiveProcess.Concentration.idist (k : ℤ)
        ((k : ℤ) + (q : ℤ)) = q := by simp [SubdiffusiveProcess.Concentration.idist]
    rw [hidist]
    simp only [Int.toNat_natCast]
    rw [show (3 : ℝ) ^ (-(s * (q : ℝ))) *
        (K * (3 : ℝ) ^ (s * (q : ℝ)) * fieldTwoSuffixLayer k (k + q) omega) =
      K * ((3 : ℝ) ^ (-(s * (q : ℝ))) * (3 : ℝ) ^ (s * (q : ℝ))) *
        fieldTwoSuffixLayer k (k + q) omega by ring,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  · intro i hi
    change SubdiffusiveProcess.Concentration.wt s (k : ℤ) i *
      (if 0 ≤ (k : ℤ) ∧ 0 ≤ i ∧ (k : ℤ) ≤ i ∧
          i < (k : ℤ) + (N : ℤ) then
        K * (3 : ℝ) ^ (s * ((i - (k : ℤ) : ℤ) : ℝ)) *
          fieldTwoSuffixLayer k i.toNat omega else 0) = 0
    rw [ite_eq_right]
    · ring
    · intro h
      exact hi (Finset.mem_Ico.mpr ⟨h.2.2.1, h.2.2.2⟩)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
