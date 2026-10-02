import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.IntervalPackingIndependence
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ShellColumns
import SubdiffusiveProcess.CoarseGrainingVocab.ShellSensitivity
import Homogenization.Probability.IndependentSums.GammaSigmaExpRegime.FiniteSums

/-!
# Common-cell absolute shell blocks

This file supplies the finite-truncation carrier used in Appendix B's
exponential-field concentration proposition.  The existing small-cube block
envelope controls the absolute value of a signed shell sum.  The exponential
product instead requires the sum of the shell absolute values.  We therefore
majorize each shell on one common physical cell and combine those one-shell
majorants before taking the finite spatial maximum.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open Homogenization.IndependentSums
open scoped BigOperators ENNReal

noncomputable section

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem shellSigma_eq_singleton (d i : ℕ) :
    shellSigma d i = potentialShellIndexSigma (d := d) ({i} : Set ℕ) := by
  apply le_antisymm
  · exact le_iSup_of_le i (le_iSup_of_le (Set.mem_singleton i) le_rfl)
  · refine iSup_le fun k ↦ iSup_le fun hk ↦ ?_
    rw [Set.mem_singleton_iff] at hk
    subst k
    exact le_rfl

/-- One-shell majorant of `|omega i x|` on the physical cell `z + cu_r`. -/
def absoluteSmallShellEnvelope {d : ℕ} (i : ℕ) (r : ℤ) (z : Vec d)
    (omega : Sample d) : ℝ :=
  |omega i z| + translatedSmallShellEnvelope i r z omega

theorem absoluteSmallShellEnvelope_nonneg {d : ℕ} (i : ℕ) (r : ℤ)
    (z : Vec d) (omega : Sample d) :
    0 ≤ absoluteSmallShellEnvelope i r z omega :=
  add_nonneg (abs_nonneg _) (translatedSmallShellEnvelope_nonneg _ _ _ _)

theorem measurable_absoluteSmallShellEnvelope {d : ℕ} (i : ℕ) (r : ℤ)
    (z : Vec d) : Measurable (absoluteSmallShellEnvelope i r z) := by
  unfold absoluteSmallShellEnvelope
  exact ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval z).comp
    (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate i)).norm.add
      (measurable_translatedSmallShellEnvelope i r z)

theorem measurable_absoluteSmallShellEnvelope_shellSigma {d : ℕ}
    (i : ℕ) (r : ℤ) (z : Vec d) :
    Measurable[shellSigma d i] (absoluteSmallShellEnvelope i r z) := by
  rw [shellSigma_eq_singleton]
  letI : MeasurableSpace (Sample d) := potentialShellIndexSigma ({i} : Set ℕ)
  unfold absoluteSmallShellEnvelope translatedSmallShellEnvelope
  exact ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval z).comp
    (measurable_potentialCoordinate_shellIndexSigma (Set.mem_singleton i))).norm.add
      (measurable_const.mul
        (measurable_translatedShellG2_potentialShellIndexSigma
          (Set.mem_singleton i) _))

/-- The common-cell majorant controls the literal shell absolute value. -/
theorem abs_shell_le_absoluteSmallShellEnvelope {d : ℕ}
    (i : ℕ) (r : ℤ) (z : Vec d) (hri : r ≤ (i : ℤ))
    (omega : Sample d) {x : Vec d}
    (hx : x - z ∈ openCubeSet (originCube d r)) :
    |omega i x| ≤ absoluteSmallShellEnvelope i r z omega := by
  have hosc := abs_shell_sub_le_translatedSmallShellEnvelope
    i r hri z omega hx
  unfold absoluteSmallShellEnvelope
  calc
    |omega i x| ≤ |omega i z| + |omega i x - omega i z| := by
      calc
        |omega i x| = |omega i z + (omega i x - omega i z)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    _ ≤ |omega i z| + translatedSmallShellEnvelope i r z omega :=
      add_le_add (le_refl _) hosc

/-- Exact one-shell Gamma-two scale of the absolute common-cell majorant. -/
def absoluteSmallShellScale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (i : ℕ) (r : ℤ) : ℝ :=
  gammaTriangleConst 2 *
    (((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) +
      translatedSmallShellScale M i r)

theorem absoluteSmallShellScale_pos {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (i : ℕ) (r : ℤ) :
    0 < absoluteSmallShellScale M i r := by
  unfold absoluteSmallShellScale
  exact mul_pos gammaTriangleConst_pos
    (add_pos
      (mul_pos (Real.rpow_pos_of_pos (by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith) _) M.shellPrefix.delta_pos)
      (translatedSmallShellScale_pos M i r))

theorem isBigOWith_gammaTwo_absoluteSmallShellEnvelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (i : ℕ) (r : ℤ) (z : Vec d) :
    IsBigOWith M.P.toMeasure (gammaSigma 2)
      (absoluteSmallShellEnvelope i r z) (absoluteSmallShellScale M i r) := by
  have hpoint : IsBigOWith M.P.toMeasure (gammaSigma 2)
      (fun omega : Sample d ↦ |omega i z|)
      ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta) := by
    simpa [IsBigO, abs_abs] using
      (isBigO_gammaTwo_potentialCoordinate_apply M i z)
  simpa only [absoluteSmallShellEnvelope, absoluteSmallShellScale] using
    isBigOWith_gammaTwo_add_nonneg M
      (((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval z).comp
        (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate i)).norm)
      (measurable_translatedSmallShellEnvelope i r z)
      (fun _ ↦ abs_nonneg _)
      (translatedSmallShellEnvelope_nonneg i r z)
      (mul_pos (Real.rpow_pos_of_pos (by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith) _) M.shellPrefix.delta_pos)
      (translatedSmallShellScale_pos M i r)
      hpoint (isBigOWith_gammaTwo_translatedSmallShellEnvelope M i r z)

/-! ## Independent absolute blocks on one fixed cell -/

/-- Sum of the absolute one-shell majorants on one common physical cell. -/
def absoluteSmallBlockEnvelope {d : ℕ} (lower upper : ℕ) (r : ℤ)
    (z : Vec d) (omega : Sample d) : ℝ :=
  ∑ i ∈ Finset.Icc lower upper, absoluteSmallShellEnvelope i r z omega

theorem absoluteSmallBlockEnvelope_nonneg {d : ℕ}
    (lower upper : ℕ) (r : ℤ) (z : Vec d) (omega : Sample d) :
    0 ≤ absoluteSmallBlockEnvelope lower upper r z omega :=
  Finset.sum_nonneg fun i _ ↦ absoluteSmallShellEnvelope_nonneg i r z omega

theorem measurable_absoluteSmallBlockEnvelope {d : ℕ}
    (lower upper : ℕ) (r : ℤ) (z : Vec d) :
    Measurable (absoluteSmallBlockEnvelope lower upper r z) := by
  unfold absoluteSmallBlockEnvelope
  exact Finset.measurable_sum _ fun i _ ↦
    measurable_absoluteSmallShellEnvelope i r z

/-- The common-cell block controls the sum of literal shell absolute values. -/
theorem sum_abs_shell_le_absoluteSmallBlockEnvelope {d : ℕ}
    (lower upper : ℕ) (r : ℤ) (z : Vec d)
    (hr : r ≤ (lower : ℤ)) (omega : Sample d) {x : Vec d}
    (hx : x - z ∈ openCubeSet (originCube d r)) :
    (∑ i ∈ Finset.Icc lower upper, |omega i x|) ≤
      absoluteSmallBlockEnvelope lower upper r z omega := by
  apply Finset.sum_le_sum
  intro i hi
  exact abs_shell_le_absoluteSmallShellEnvelope i r z
    (hr.trans (by exact_mod_cast (Finset.mem_Icc.mp hi).1)) omega hx

/-- Shell-coordinate independence passes to the common-cell absolute
majorants. -/
theorem iIndepFun_absoluteSmallShellEnvelope {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (r : ℤ) (z : Vec d) :
    iIndepFun (fun i : ℕ ↦ absoluteSmallShellEnvelope i r z)
      M.P.toMeasure := by
  rw [iIndepFun_iff]
  intro s E hE
  have hshell : iIndep (shellSigma d) M.P.toMeasure :=
    M.shellPrefix.independent.iIndep
  exact hshell.meas_biInter fun i hi ↦
    (measurable_absoluteSmallShellEnvelope_shellSigma i r z).comap_le
      (E i) (hE i hi)

/-- Dimension-free scale constant for one absolute shell on a cell no larger
than its own correlation scale. -/
def absoluteSmallShellConst : ℝ :=
  gammaTriangleConst 2 *
    (2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹)

theorem absoluteSmallShellConst_pos : 0 < absoluteSmallShellConst := by
  unfold absoluteSmallShellConst
  exact mul_pos gammaTriangleConst_pos (mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _))

theorem absoluteSmallShellScale_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {lower i : ℕ}
    (hli : lower ≤ i) :
    absoluteSmallShellScale M i (lower : ℤ) ≤
      absoluteSmallShellConst * M.delta := by
  have hexp : (lower : ℤ) - (i : ℤ) ≤ 0 := by omega
  have hpow : (3 : ℝ) ^ ((lower : ℤ) - (i : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ (by norm_num) hexp
  have hbase : 0 ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_nonneg (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) _
  have hdelta : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hgamma : 0 ≤ gammaTriangleConst 2 := gammaTriangleConst_pos.le
  unfold absoluteSmallShellScale translatedSmallShellScale
    absoluteSmallShellConst
  calc
    gammaTriangleConst 2 *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta +
          (3 : ℝ) ^ ((lower : ℤ) - (i : ℤ)) *
            ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) ≤
      gammaTriangleConst 2 *
        ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta +
          1 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta)) := by
        gcongr
    _ = gammaTriangleConst 2 *
        (2 * (1 + Real.log 2) ^ (2 : ℝ)⁻¹) * M.delta := by ring

/-- The exact finite-truncation Chernoff estimate on one fixed common cell. -/
theorem measureReal_absoluteSmallBlockEnvelope_upperTail_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (lower upper : ℕ)
    (z : Vec d) (l a : ℝ) (hl : 0 ≤ l) :
    M.P.toMeasure.real
        (upperTailEvent
          (absoluteSmallBlockEnvelope lower upper (lower : ℤ) z) a) ≤
      Real.exp
        (-l * a + ((Finset.Icc lower upper).card : ℝ) *
          (Real.log 2 + gammaSigmaLargeMgfConst 2 *
            ((absoluteSmallShellConst * M.delta) * l) ^
              gammaExpConjExponent 2)) := by
  apply
    measureReal_upperTailEvent_finset_sum_le_exp_card_mul_of_iIndepFun_of_isBigO_gammaSigma_of_one_lt
      (μ := M.P.toMeasure)
      (X := fun i : ℕ ↦ absoluteSmallShellEnvelope i (lower : ℤ) z)
      (s := Finset.Icc lower upper) (σ := 2)
      (K := absoluteSmallShellConst * M.delta) (l := l) (a := a)
  · exact iIndepFun_absoluteSmallShellEnvelope M (lower : ℤ) z
  · exact fun i ↦ measurable_absoluteSmallShellEnvelope i (lower : ℤ) z
  · norm_num
  · exact mul_pos absoluteSmallShellConst_pos M.shellPrefix.delta_pos
  · exact hl
  · intro i hi
    have hli := (Finset.mem_Icc.mp hi).1
    have hwith := (isBigOWith_gammaTwo_absoluteSmallShellEnvelope
      M i (lower : ℤ) z).mono_scale (absoluteSmallShellScale_le M hli)
    simpa [IsBigO, abs_of_nonneg
      (absoluteSmallShellEnvelope_nonneg i (lower : ℤ) z _)] using hwith

/-! ## One spatial maximum after the independent shell assembly -/

/-- Maximum of the absolute block envelopes over a common scale-`lower`
cover of the observation cube. -/
def coveredAbsoluteBlockEnvelope {d : ℕ}
    (lower upper observation : ℕ) (omega : Sample d) : ℝ :=
  (shellCoverShifts d ((observation : ℤ) - (lower : ℤ))).sup'
    (shellCoverShifts_nonempty d ((observation : ℤ) - (lower : ℤ)))
    (fun p ↦ absoluteSmallBlockEnvelope lower upper (lower : ℤ)
      (physicalShellCoverCenter lower p) omega)

theorem coveredAbsoluteBlockEnvelope_nonneg {d : ℕ}
    (lower upper observation : ℕ) (omega : Sample d) :
    0 ≤ coveredAbsoluteBlockEnvelope lower upper observation omega := by
  unfold coveredAbsoluteBlockEnvelope
  obtain ⟨p, hp⟩ :=
    shellCoverShifts_nonempty d ((observation : ℤ) - (lower : ℤ))
  exact (absoluteSmallBlockEnvelope_nonneg lower upper (lower : ℤ)
    (physicalShellCoverCenter lower p) omega).trans
      (Finset.le_sup' (fun q ↦ absoluteSmallBlockEnvelope lower upper
        (lower : ℤ) (physicalShellCoverCenter lower q) omega) hp)

theorem measurable_coveredAbsoluteBlockEnvelope {d : ℕ}
    (lower upper observation : ℕ) :
    Measurable (coveredAbsoluteBlockEnvelope (d := d) lower upper observation) := by
  let Y : Sample d → ℝ :=
    (shellCoverShifts d ((observation : ℤ) - (lower : ℤ))).sup'
      (shellCoverShifts_nonempty d ((observation : ℤ) - (lower : ℤ)))
      fun p ↦ absoluteSmallBlockEnvelope lower upper (lower : ℤ)
        (physicalShellCoverCenter lower p)
  have hY : Measurable Y := Finset.measurable_sup'
    (shellCoverShifts_nonempty d ((observation : ℤ) - (lower : ℤ)))
    (fun p _ ↦ measurable_absoluteSmallBlockEnvelope lower upper
      (lower : ℤ) (physicalShellCoverCenter lower p))
  have heq : Y = coveredAbsoluteBlockEnvelope lower upper observation := by
    funext omega
    exact Finset.sup'_apply
      (shellCoverShifts_nonempty d ((observation : ℤ) - (lower : ℤ)))
      (fun p ↦ absoluteSmallBlockEnvelope lower upper (lower : ℤ)
        (physicalShellCoverCenter lower p)) omega
  rwa [← heq]

/-- Every point of the observation cube is controlled by one common covering
cell, uniformly for all shells in the truncated block. -/
theorem sum_abs_shell_le_coveredAbsoluteBlockEnvelope {d : ℕ}
    (lower upper observation : ℕ) (omega : Sample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (observation : ℤ))) :
    (∑ i ∈ Finset.Icc lower upper, |omega i x|) ≤
      coveredAbsoluteBlockEnvelope lower upper observation omega := by
  obtain ⟨p, hpFin, hp⟩ := exists_physicalShellCoverCenter_mem
    lower (observation : ℤ) hx
  exact (sum_abs_shell_le_absoluteSmallBlockEnvelope lower upper
    (lower : ℤ) (physicalShellCoverCenter lower p) (le_refl _)
      omega hp).trans
    (Finset.le_sup'
      (fun q ↦ absoluteSmallBlockEnvelope lower upper (lower : ℤ)
        (physicalShellCoverCenter lower q) omega) hpFin)

/-- Raw union-bound tail for the common spatial maximum.  The covering
cardinality is deliberately kept outside the Gamma scale. -/
theorem measureReal_coveredAbsoluteBlockEnvelope_upperTail_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (lower upper observation : ℕ) (l a : ℝ) (hl : 0 ≤ l) :
    M.P.toMeasure.real
        (upperTailEvent
          (coveredAbsoluteBlockEnvelope (d := d) lower upper observation) a) ≤
      ((shellCoverShifts d
          ((observation : ℤ) - (lower : ℤ))).card : ℝ) *
        Real.exp
          (-l * a + ((Finset.Icc lower upper).card : ℝ) *
            (Real.log 2 + gammaSigmaLargeMgfConst 2 *
              ((absoluteSmallShellConst * M.delta) * l) ^
                gammaExpConjExponent 2)) := by
  let S := shellCoverShifts d ((observation : ℤ) - (lower : ℤ))
  let X : (Fin d → ℤ) → Sample d → ℝ := fun p ↦
    absoluteSmallBlockEnvelope lower upper (lower : ℤ)
      (physicalShellCoverCenter lower p)
  have hsubset : upperTailEvent
      (coveredAbsoluteBlockEnvelope (d := d) lower upper observation) a ⊆
      ⋃ p ∈ S, upperTailEvent (X p) a := by
    intro omega homega
    rw [mem_upperTailEvent] at homega
    have hmax : a < S.sup' (shellCoverShifts_nonempty d
        ((observation : ℤ) - (lower : ℤ))) (fun p ↦ X p omega) := by
      simpa only [S, X, coveredAbsoluteBlockEnvelope] using homega
    obtain ⟨p, hp, hpa⟩ := (Finset.lt_sup'_iff _).mp hmax
    simp only [Set.mem_iUnion]
    exact ⟨p, ⟨hp, hpa⟩⟩
  calc
    M.P.toMeasure.real
        (upperTailEvent
          (coveredAbsoluteBlockEnvelope (d := d) lower upper observation) a) ≤
      M.P.toMeasure.real (⋃ p ∈ S, upperTailEvent (X p) a) :=
        measureReal_mono hsubset (measure_ne_top M.P.toMeasure _)
    _ ≤ ∑ p ∈ S, M.P.toMeasure.real (upperTailEvent (X p) a) :=
      MeasureTheory.measureReal_biUnion_finset_le S _
    _ ≤ ∑ _p ∈ S, Real.exp
          (-l * a + ((Finset.Icc lower upper).card : ℝ) *
            (Real.log 2 + gammaSigmaLargeMgfConst 2 *
              ((absoluteSmallShellConst * M.delta) * l) ^
                gammaExpConjExponent 2)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact measureReal_absoluteSmallBlockEnvelope_upperTail_le
        M lower upper (physicalShellCoverCenter lower p) l a hl
    _ = (S.card : ℝ) * Real.exp
          (-l * a + ((Finset.Icc lower upper).card : ℝ) *
            (Real.log 2 + gammaSigmaLargeMgfConst 2 *
              ((absoluteSmallShellConst * M.delta) * l) ^
                gammaExpConjExponent 2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := rfl

/-- Logarithmic form of the shared-cover estimate. -/
theorem three_mul_log_card_shellCoverShifts_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {r : ℤ} (hr : 0 < r) :
    3 * Real.log ((shellCoverShifts d r).card : ℝ) ≤
      shellCoverLogConst * (d : ℝ) * (r : ℝ) := by
  have hfac := shellCover_gaussianFactor_le_sqrt M hr
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by ring, ← Real.sqrt_eq_rpow] at hfac
  have hcardOne : (1 : ℝ) ≤ ((shellCoverShifts d r).card : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero.mpr (shellCoverShifts_nonempty d r)))
  have hleft0 : 0 ≤ 3 * Real.log ((shellCoverShifts d r).card : ℝ) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hcardOne)
  have hCd : 0 ≤ shellCoverLogConst * (d : ℝ) :=
    mul_nonneg shellCoverLogConst_pos.le (Nat.cast_nonneg d)
  have hr0 : 0 ≤ (r : ℝ) := by exact_mod_cast hr.le
  have hsquare := mul_self_le_mul_self (Real.sqrt_nonneg _) hfac
  calc
    3 * Real.log ((shellCoverShifts d r).card : ℝ) =
        Real.sqrt (3 * Real.log ((shellCoverShifts d r).card : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt hleft0]
    _ ≤ (Real.sqrt (shellCoverLogConst * (d : ℝ)) *
          Real.sqrt (r : ℝ)) ^ 2 := by
      simpa only [pow_two] using hsquare
    _ = shellCoverLogConst * (d : ℝ) * (r : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hCd, Real.sq_sqrt hr0]

/-! ## The manuscript's finite truncated requirement -/

/-- The nonnegative-shell truncation of the symmetric integer block
`[k-j,k+j]`.  Negative field indices in the manuscript are deterministic
zero, hence disappear from the logarithm. -/
def expFieldBlockEnvelope {d : ℕ} (k j h : ℕ) : Sample d → ℝ :=
  coveredAbsoluteBlockEnvelope (k - j) (k + j) (k + h + j)

def expFieldThreshold (s : ℝ) (j : ℕ) : ℝ :=
  Real.log 3 + s * (j : ℝ) * Real.log 3

/-- The finite-radius exponential-field exceedance in logarithmic form. -/
def expFieldBlockExceeds {d : ℕ} (s : ℝ) (k : ℕ) (j h : ℕ) :
    Set (Sample d) :=
  upperTailEvent (expFieldBlockEnvelope (d := d) k j h)
    (expFieldThreshold s j)

theorem measurable_expFieldBlockEnvelope {d : ℕ} (k j h : ℕ) :
    Measurable (expFieldBlockEnvelope (d := d) k j h) :=
  measurable_coveredAbsoluteBlockEnvelope (k - j) (k + j) (k + h + j)

theorem measurableSet_expFieldBlockExceeds {d : ℕ}
    (s : ℝ) (k j h : ℕ) :
    MeasurableSet (expFieldBlockExceeds (d := d) s k j h) :=
  measurableSet_lt measurable_const (measurable_expFieldBlockEnvelope k j h)

/-- A truncated block reads exactly the finite shell interval occurring in
its exponent.  This is the measurability premise used by the fixed packed
configuration factorization. -/
theorem measurable_expFieldBlockEnvelope_intervalSigma {d : ℕ}
    (k j h : ℕ) :
    @Measurable (Sample d) ℝ
      (⨆ i ∈ Finset.Icc (k - j) (k + j), shellSigma d i) inferInstance
      (expFieldBlockEnvelope (d := d) k j h) := by
  let I := Finset.Icc (k - j) (k + j)
  let S := shellCoverShifts d
    (((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ))
  letI : MeasurableSpace (Sample d) := ⨆ i ∈ I, shellSigma d i
  let Y : Sample d → ℝ := S.sup'
    (shellCoverShifts_nonempty d
      (((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ))) fun p ↦
      absoluteSmallBlockEnvelope (k - j) (k + j) ((k - j : ℕ) : ℤ)
        (physicalShellCoverCenter (k - j) p)
  have hY : Measurable Y := Finset.measurable_sup'
    (shellCoverShifts_nonempty d
      (((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ))) (fun p _ ↦ by
      unfold absoluteSmallBlockEnvelope
      apply Finset.measurable_sum
      intro i hi
      exact (measurable_absoluteSmallShellEnvelope_shellSigma i
        ((k - j : ℕ) : ℤ) (physicalShellCoverCenter (k - j) p)).mono
          (le_iSup₂_of_le i hi le_rfl) le_rfl)
  have heq : Y = expFieldBlockEnvelope (d := d) k j h := by
    funext omega
    exact Finset.sup'_apply
      (shellCoverShifts_nonempty d
        (((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ)))
      (fun p ↦ absoluteSmallBlockEnvelope (k - j) (k + j)
        ((k - j : ℕ) : ℤ) (physicalShellCoverCenter (k - j) p)) omega
  rwa [← heq]

theorem measurableSet_expFieldBlockExceeds_intervalSigma {d : ℕ}
    (s : ℝ) (k j h : ℕ) :
    @MeasurableSet (Sample d)
      (⨆ i ∈ Finset.Icc (k - j) (k + j), shellSigma d i)
      (expFieldBlockExceeds (d := d) s k j h) := by
  exact measurableSet_lt measurable_const
    (measurable_expFieldBlockEnvelope_intervalSigma k j h)

/-- The truncated literal exponential product at every point of the
observation cube is dominated by the common-cell carrier. -/
theorem prod_exp_abs_shell_le_expFieldBlockEnvelope {d : ℕ}
    (k j h : ℕ) (omega : Sample d) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d ((k + h + j : ℕ) : ℤ))) :
    (∏ i ∈ Finset.Icc (k - j) (k + j), Real.exp |omega i x|) ≤
      Real.exp (expFieldBlockEnvelope k j h omega) := by
  rw [← Real.exp_sum]
  exact Real.exp_le_exp.mpr
    (sum_abs_shell_le_coveredAbsoluteBlockEnvelope
      (k - j) (k + j) (k + h + j) omega hx)

theorem expFieldBlockExceeds_iff {d : ℕ} {s : ℝ} {k j h : ℕ}
    (omega : Sample d) :
    omega ∈ expFieldBlockExceeds (d := d) s k j h ↔
      3 < (3 : ℝ) ^ (-(s * (j : ℝ))) *
        Real.exp (expFieldBlockEnvelope k j h omega) := by
  simp only [expFieldBlockExceeds, mem_upperTailEvent, expFieldThreshold]
  let A : ℝ := (3 : ℝ) ^ (s * (j : ℝ))
  let B : ℝ := (3 : ℝ) ^ (-(s * (j : ℝ)))
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hB : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  have hcancel : A * B = 1 := by
    unfold A B
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show s * (j : ℝ) + -(s * (j : ℝ)) = 0 by ring,
      Real.rpow_zero]
  have hpow : 0 < (3 : ℝ) ^ (-(s * (j : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hthree : (0 : ℝ) < 3 := by norm_num
  have hthresholdExp :
      Real.exp (Real.log 3 + s * (j : ℝ) * Real.log 3) = 3 * A := by
    rw [Real.exp_add, Real.exp_log hthree]
    dsimp [A]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 2
    ring
  constructor <;> intro hlt
  · have hexp := Real.exp_lt_exp.2 hlt
    have hexp' : 3 * A < Real.exp (expFieldBlockEnvelope k j h omega) := by
      rw [← hthresholdExp]
      exact hexp
    have hmul := mul_lt_mul_of_pos_left hexp' hB
    change 3 < B * Real.exp (expFieldBlockEnvelope k j h omega)
    calc
      3 = B * (3 * A) := by rw [show B * (3 * A) = 3 * (A * B) by ring,
        hcancel, mul_one]
      _ < B * Real.exp (expFieldBlockEnvelope k j h omega) := hmul
  · change 3 < B * Real.exp (expFieldBlockEnvelope k j h omega) at hlt
    have hmul := mul_lt_mul_of_pos_left hlt hA
    have hexp' : 3 * A < Real.exp (expFieldBlockEnvelope k j h omega) := by
      calc
        3 * A = A * 3 := by ring
        _ < A * (B * Real.exp (expFieldBlockEnvelope k j h omega)) := hmul
        _ = Real.exp (expFieldBlockEnvelope k j h omega) := by
          rw [← mul_assoc, hcancel, one_mul]
    apply Real.exp_lt_exp.1
    rw [hthresholdExp]
    exact hexp'

theorem expFieldBlock_card_le (k j : ℕ) :
    (Finset.Icc (k - j) (k + j)).card ≤ 2 * j + 1 := by
  rw [Nat.card_Icc]
  omega

/-- Exact finite-truncation probability estimate before the universal
constant arithmetic of `p.concentration.for.scales.exp.field`. -/
theorem measureReal_expFieldBlockExceeds_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) (k j h : ℕ) (l : ℝ) (hl : 0 ≤ l) :
    M.P.toMeasure.real (expFieldBlockExceeds (d := d) s k j h) ≤
      ((shellCoverShifts d
        (((k + h + j : ℕ) : ℤ) - ((k - j : ℕ) : ℤ))).card : ℝ) *
      Real.exp
        (-l * expFieldThreshold s j +
          ((Finset.Icc (k - j) (k + j)).card : ℝ) *
            (Real.log 2 + gammaSigmaLargeMgfConst 2 *
              ((absoluteSmallShellConst * M.delta) * l) ^
                gammaExpConjExponent 2)) := by
  exact measureReal_coveredAbsoluteBlockEnvelope_upperTail_le M
    (k - j) (k + j) (k + h + j) l (expFieldThreshold s j) hl

/-- The nonnegative truncation of pairwise separated centered integer
intervals is still pairwise disjoint. -/
theorem natShellBlocks_pairwiseDisjoint_of_centered_separated
    (K : Finset ℕ) (radius : ℕ → ℕ)
    (hsep : ∀ a ∈ K, ∀ b ∈ K, a ≠ b →
      centeredIntIntervalsSeparated (a : ℤ) (radius a) (b : ℤ) (radius b)) :
    (K : Set ℕ).PairwiseDisjoint
      (fun k ↦ Finset.Icc (k - radius k) (k + radius k)) := by
  intro a ha b hb hab
  change Disjoint (Finset.Icc (a - radius a) (a + radius a))
    (Finset.Icc (b - radius b) (b + radius b))
  rw [Finset.disjoint_left]
  intro i hia hib
  have hiaInt : (i : ℤ) ∈ centeredIntInterval (a : ℤ) (radius a) := by
    rw [centeredIntInterval, Finset.mem_Icc]
    have hi := Finset.mem_Icc.mp hia
    constructor <;> omega
  have hibInt : (i : ℤ) ∈ centeredIntInterval (b : ℤ) (radius b) := by
    rw [centeredIntInterval, Finset.mem_Icc]
    have hi := Finset.mem_Icc.mp hib
    constructor <;> omega
  exact Finset.disjoint_left.mp (hsep a ha b hb hab).1 hiaInt
    (centeredIntInterval_subset_separatedIntInterval (b : ℤ) (radius b) hibInt)

/-- Fixed separated exponential-field block events factorize exactly.  This
is the stochastic input consumed after the greedy interval configuration has
been fixed. -/
theorem measure_biInter_expFieldBlockExceeds_eq_prod {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) (h : ℕ) (K : Finset ℕ) (radius : ℕ → ℕ)
    (hsep : ∀ a ∈ K, ∀ b ∈ K, a ≠ b →
      centeredIntIntervalsSeparated (a : ℤ) (radius a) (b : ℤ) (radius b)) :
    M.P.toMeasure (⋂ k ∈ K, expFieldBlockExceeds (d := d) s k (radius k) h) =
      ∏ k ∈ K, M.P.toMeasure (expFieldBlockExceeds (d := d) s k (radius k) h) := by
  apply measure_biInter_eq_prod_of_iIndep_finsetBlocks
    M.shellPrefix.independent.iIndep shellSigma_le K
    (fun k ↦ Finset.Icc (k - radius k) (k + radius k))
    (natShellBlocks_pairwiseDisjoint_of_centered_separated K radius hsep)
    (fun k ↦ expFieldBlockExceeds (d := d) s k (radius k) h)
  intro k hk
  exact measurableSet_expFieldBlockExceeds_intervalSigma s k (radius k) h

/-- Integer-centre form used by the packed configuration selected from the
manuscript's scale window. -/
theorem measure_biInter_expFieldBlockExceeds_int_eq_prod {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s : ℝ) (h : ℕ) (K : Finset ℤ) (radius : ℤ → ℕ)
    (hK0 : ∀ k ∈ K, 0 ≤ k)
    (hsep : ∀ a ∈ K, ∀ b ∈ K, a ≠ b →
      centeredIntIntervalsSeparated a (radius a) b (radius b)) :
    M.P.toMeasure
        (⋂ k ∈ K, expFieldBlockExceeds (d := d) s k.toNat (radius k) h) =
      ∏ k ∈ K,
        M.P.toMeasure (expFieldBlockExceeds (d := d) s k.toNat (radius k) h) := by
  apply measure_biInter_eq_prod_of_iIndep_finsetBlocks
    M.shellPrefix.independent.iIndep shellSigma_le K
    (fun k ↦ Finset.Icc (k.toNat - radius k) (k.toNat + radius k))
  · intro a ha b hb hab
    change Disjoint (Finset.Icc (a.toNat - radius a) (a.toNat + radius a))
      (Finset.Icc (b.toNat - radius b) (b.toNat + radius b))
    rw [Finset.disjoint_left]
    intro i hia hib
    have haCast : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (hK0 a ha)
    have hbCast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (hK0 b hb)
    have hiaInt : (i : ℤ) ∈ centeredIntInterval a (radius a) := by
      rw [centeredIntInterval, Finset.mem_Icc]
      have hi := Finset.mem_Icc.mp hia
      constructor <;> omega
    have hibInt : (i : ℤ) ∈ centeredIntInterval b (radius b) := by
      rw [centeredIntInterval, Finset.mem_Icc]
      have hi := Finset.mem_Icc.mp hib
      constructor <;> omega
    exact Finset.disjoint_left.mp (hsep a ha b hb hab).1 hiaInt
      (centeredIntInterval_subset_separatedIntInterval b (radius b) hibInt)
  · intro k hk
    exact measurableSet_expFieldBlockExceeds_intervalSigma s k.toNat (radius k) h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
