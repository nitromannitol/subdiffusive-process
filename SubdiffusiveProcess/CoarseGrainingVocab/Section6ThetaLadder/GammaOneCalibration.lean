module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.GammaRegRange
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.GammaOneTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.TranslatedStoppingEvent

@[expose] public section

/-!
# Theta-perturbed ladder: fixed-exponent Gamma-one calibration

The branch-independent finite-cutoff Gamma-one theorem is stated uniformly in
the Holder exponent.  This file chooses the small-contrast window needed at
the theta ladder's fixed exponent `3/4`, translates the stopping event to an
arbitrary parent centre, and weakens the rate to the
`delta^2 * |log delta|^2` shape consumed by the bounded-multiplier theorem.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private theorem abs_log_le_inv {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) :
    |Real.log delta| ≤ 1 / delta := by
  have hlog : Real.log delta ≤ 0 :=
    Real.log_nonpos hdelta.le hdeltaOne
  rw [abs_of_nonpos hlog, ← Real.log_inv]
  have hinv : 0 < delta⁻¹ := inv_pos.mpr hdelta
  have hbound := Real.log_le_sub_one_of_pos hinv
  rw [one_div]
  linarith

/-- The elementary small-delta estimate used to enter the fixed `3/4`
Gamma-one window. -/
theorem delta_mul_sqrt_abs_log_le_sqrt {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    delta * Real.sqrt |Real.log delta| ≤ Real.sqrt delta := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.mul_sqrt_abs_log_le_sqrt (delta := delta) (hd := hdelta) (hd1 := hdeltaOne)

/-- The branch-independent Gamma-one theorem, specialized all the way to the
translated fixed-`3/4` event and the exceptional-probability shape used by the
bounded-multiplier consumer. -/
theorem exists_translatedThetaLadderGammaOneCalibration
    (d : ℕ) [NeZero d] (step : ℕ) {C1 C2 : ℝ}
    (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ c ≤ 1 ∧
      ∃ j0 : ℕ, 0 < j0 ∧
        ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ c →
        ∀ L m : ℕ, ∀ z : Vec d,
          M.P.toMeasure
              (translatedThetaLadderStoppingEvent
                M L C1 C2 step m j0 z)ᶜ ≤
            ENNReal.ofReal
              (C * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) := by
  obtain ⟨K, hK, htail⟩ := exists_thetaLadderGammaOneTail d step hC1 hC2
  let c0 : ℝ := min (min K⁻¹ (1 / (16 * K ^ 2))) (Real.exp (-1))
  let c : ℝ := min c0 (1 / (16 * K))
  let j0 : ℕ := Nat.ceil (K + 1)
  have hKinv : 0 < K⁻¹ := inv_pos.mpr hK
  have hquad : 0 < (1 : ℝ) / (16 * K ^ 2) := by positivity
  have hexp : 0 < Real.exp (-1) := Real.exp_pos _
  have hc0 : 0 < c0 := by
    dsimp only [c0]
    exact lt_min (lt_min hKinv hquad) hexp
  have hrate : 0 < (1 : ℝ) / (16 * K) := by positivity
  have hc : 0 < c := by
    dsimp only [c]
    exact lt_min hc0 hrate
  have hcOne : c ≤ 1 := by
    have hcexp : c ≤ Real.exp (-1) :=
      (min_le_left c0 (1 / (16 * K))).trans (min_le_right _ _)
    exact hcexp.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hjceil : K + 1 ≤ (j0 : ℝ) := by
    dsimp only [j0]
    exact Nat.le_ceil (K + 1)
  have hj0 : 0 < j0 := by
    exact_mod_cast (lt_of_lt_of_le (by linarith : (0 : ℝ) < K + 1) hjceil)
  refine ⟨c, K, hc, hK, hcOne, j0, hj0, ?_⟩
  intro M hdelta L m z
  have hdeltaPos : 0 < M.delta := M.shellPrefix.delta_pos
  have hdeltaK : M.delta ≤ K⁻¹ :=
    hdelta.trans ((min_le_left c0 (1 / (16 * K))).trans
      ((min_le_left (min K⁻¹ (1 / (16 * K ^ 2)))
        (Real.exp (-1))).trans (min_le_left _ _)))
  have hdeltaQuad : M.delta ≤ 1 / (16 * K ^ 2) :=
    hdelta.trans ((min_le_left c0 (1 / (16 * K))).trans
      ((min_le_left (min K⁻¹ (1 / (16 * K ^ 2)))
        (Real.exp (-1))).trans (min_le_right _ _)))
  have hdeltaExp : M.delta ≤ Real.exp (-1) :=
    hdelta.trans ((min_le_left c0 (1 / (16 * K))).trans
      (min_le_right _ _))
  have hdeltaOne : M.delta ≤ 1 :=
    hdeltaExp.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hlogLe : Real.log M.delta ≤ -1 :=
    (Real.log_le_iff_le_exp hdeltaPos).mpr hdeltaExp
  have hlog : 1 ≤ |Real.log M.delta| := by
    rw [abs_of_nonpos (hlogLe.trans (by norm_num))]
    linarith
  have hsqrtDelta : K * Real.sqrt M.delta ≤ 1 / 4 := by
    have hsq : K ^ 2 * M.delta ≤ 1 / 16 := by
      calc
        K ^ 2 * M.delta ≤ K ^ 2 * (1 / (16 * K ^ 2)) :=
          mul_le_mul_of_nonneg_left hdeltaQuad (sq_nonneg K)
        _ = 1 / 16 := by field_simp
    have hrootSq : Real.sqrt M.delta ^ 2 = M.delta :=
      Real.sq_sqrt hdeltaPos.le
    have hnonneg : 0 ≤ K * Real.sqrt M.delta :=
      mul_nonneg hK.le (Real.sqrt_nonneg _)
    nlinarith [hsq]
  have hwindowTerm :
      K * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ) ≤ 1 / 4 := by
    have hsqrtEq : |Real.log M.delta| ^ (1 / 2 : ℝ) =
        Real.sqrt |Real.log M.delta| :=
      (Real.sqrt_eq_rpow _).symm
    rw [hsqrtEq]
    have hsmall := delta_mul_sqrt_abs_log_le_sqrt hdeltaPos hdeltaOne
    calc
      K * M.delta * Real.sqrt |Real.log M.delta| =
          K * (M.delta * Real.sqrt |Real.log M.delta|) := by ring
      _ ≤ K * Real.sqrt M.delta :=
        mul_le_mul_of_nonneg_left hsmall hK.le
      _ ≤ 1 / 4 := hsqrtDelta
  have hwindow : thetaLadderExponent ∈ Set.Icc (1 / 2 : ℝ)
      (1 - K * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)) := by
    constructor
    · exact thetaLadderExponent_mem.1
    · rw [thetaLadderExponent]
      linarith
  have htail0 := htail M hdeltaK hwindow L m j0 hj0
  have htail1 := measure_thetaLadderStoppingEvent_compl_le_deltaLogSq
    hK hjceil hlog htail0
  have htranslated := measure_compl_translatedThetaLadderStoppingEvent_le
    M L C1 C2 step m j0 z htail1
  have hcrate : c ≤ 1 / (16 * K) := min_le_right _ _
  have hden : 0 < M.delta ^ 2 * |Real.log M.delta| ^ 2 := by positivity
  have hexpMono :
      Real.exp
          (-(1 / (16 * K)) /
            (M.delta ^ 2 * |Real.log M.delta| ^ 2)) ≤
        Real.exp
          (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) := by
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg hcrate) hden.le
  exact htranslated.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hexpMono hK.le))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
