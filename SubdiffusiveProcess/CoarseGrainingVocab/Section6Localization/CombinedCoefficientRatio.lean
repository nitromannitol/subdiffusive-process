module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.ResponseTransport

@[expose] public section

/-!
# Section 6 localization: the combined coefficient ratio

This module proves the exact algebraic display
`e.combined.coefficient.ratio.reg` from Step 2 of
`p.good.scale.mathcal.E`.  It combines the
cutoff increment from `n` to `m` with the centered annealed-normalizer error
from `NormalizerSwap`, while retaining the tail coefficient divided by its
global cube average as one factor.

The module boundary mirrors the transition from carrier transport to the
shell/gauge budget in
`Algsuperdiff/Section4/Provider/Annular/ResponseTransport.lean` and
`Algsuperdiff/Section4/Provider/Annular/ShellGaugeBudget.lean`.  Only exact
identities are proved here; good-event bounds and mean-value estimates belong
to the next layer.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Translating the sample translates the shell block pointwise. -/
theorem shellBlock_translatePotentialSample
    (m n : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (z x : Vec d) :
    shellBlock m n (translatePotentialSample z omega) x =
      shellBlock m n omega (x + z) := by
  simp only [shellBlock, translatePotentialSample,
    _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply]

/-- Translating the sample translates the tail coefficient pointwise. -/
theorem tailCoefficient_translatePotentialSample
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z x : Vec d) :
    tailCoefficient M L m (translatePotentialSample z omega) x =
      tailCoefficient M L m omega (x + z) := by
  simp only [tailCoefficient, _root_.SubdiffusiveProcess.Model.aCutoff,
    translatePotentialSample,
    _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply]

/-- The combined tail-average, shell-block, and annealed-normalizer ratio in
local translated coordinates. -/
def combinedCoefficientRatio
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z x : Vec d) : ℝ :=
  (tailCoefficient M L m (translatePotentialSample z omega) x /
      tailCoefficientCubeAverage M L m omega) *
    Real.exp (shellBlock m n (translatePotentialSample z omega) x +
      normalizerLogError M m n)

/-- The reciprocal combined ratio, kept in the factored form used by the
manuscript's long-ratio estimate. -/
def combinedCoefficientRatioInv
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z x : Vec d) : ℝ :=
  Real.exp (-(shellBlock m n (translatePotentialSample z omega) x +
      normalizerLogError M m n)) *
    (tailCoefficientCubeAverage M L m omega /
      tailCoefficient M L m (translatePotentialSample z omega) x)

/-- The finite-cutoff quotient is the exponential of the centered shell block
`g_{m,n} - (m-n) tauSq`. -/
theorem aCutoff_div_eq_exp_shellBlock
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m n : ℕ} (hnm : n ≤ m)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M n omega x =
      Real.exp (shellBlock m n omega x -
        _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) := by
  let f : ℕ → ℝ := fun k => omega k x - _root_.SubdiffusiveProcess.Model.tauSq M.P
  have hsum : (∑ k ∈ Finset.range (m + 1), f k) -
      ∑ k ∈ Finset.range (n + 1), f k =
        ∑ k ∈ Finset.Icc (n + 1) m, f k := by
    rw [← Finset.sum_Ico_eq_sub f (by omega : n + 1 ≤ m + 1)]
    congr 1
  rw [_root_.SubdiffusiveProcess.Model.aCutoff, _root_.SubdiffusiveProcess.Model.aCutoff,
    ← Real.exp_sub]
  congr 1
  rw [hsum]
  simp only [f, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Nat.card_Icc]
  unfold shellBlock
  congr 1
  push_cast
  ring_nf

/-- The normalized cutoff quotient factors into the tail coefficient divided
by an arbitrary nonzero normalizer and the combined shell/rho exponential. -/
theorem normalizedCutoffRatio_eq_tailCoefficient_div_mul_exp
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d)
    {b : ℝ} (hb : b ≠ 0) :
    (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
        b) /
        (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x / ahom M n) =
      (tailCoefficient M L m omega x /
        b) *
        Real.exp (shellBlock m n omega x + normalizerLogError M m n) := by
  have hL : 0 < _root_.SubdiffusiveProcess.Model.aCutoff M L omega x :=
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x
  have hm : 0 < _root_.SubdiffusiveProcess.Model.aCutoff M m omega x :=
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x
  have hn : 0 < _root_.SubdiffusiveProcess.Model.aCutoff M n omega x :=
    _root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x
  have hahomm : 0 < ahom M m := ahom_pos M m
  have hahomn : 0 < ahom M n := ahom_pos M n
  have hcutoff := aCutoff_div_eq_exp_shellBlock M hnm omega x
  have hnormalizer := ahom_ratio_eq_exp_normalizerLogError M m n
  have hexp :
      (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega x) *
          (ahom M n / ahom M m) =
        Real.exp (shellBlock m n omega x + normalizerLogError M m n) := by
    rw [hcutoff, hnormalizer, ← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  unfold tailCoefficient
  rw [min_eq_left hmL]
  field_simp

/-- The preceding factorization at the manuscript's global tail-average
normalizer. -/
theorem normalizedCutoffRatio_eq_tailCoefficientRatio_mul_exp
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
        tailCoefficientCubeAverage M L m omega) /
        (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x / ahom M n) =
      (tailCoefficient M L m omega x /
        tailCoefficientCubeAverage M L m omega) *
        Real.exp (shellBlock m n omega x + normalizerLogError M m n) := by
  exact normalizedCutoffRatio_eq_tailCoefficient_div_mul_exp M hnm hmL omega x
    (tailCoefficientCubeAverage_pos M L m omega).ne'

/-- Reciprocal form of the combined coefficient-ratio identity. -/
theorem normalizedCutoffRatio_inv_eq_exp_neg_mul_tailCoefficient_div
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d)
    {b : ℝ} (hb : b ≠ 0) :
    (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x / ahom M n) /
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          b) =
      Real.exp (-(shellBlock m n omega x + normalizerLogError M m n)) *
        (b /
          tailCoefficient M L m omega x) := by
  have h := normalizedCutoffRatio_eq_tailCoefficient_div_mul_exp
    M hnm hmL omega x hb
  calc
    (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x / ahom M n) /
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
            b) =
        ((_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          b) /
          (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x / ahom M n))⁻¹ := by
            rw [inv_div]
    _ = ((tailCoefficient M L m omega x /
          b) *
          Real.exp (shellBlock m n omega x + normalizerLogError M m n))⁻¹ := by
            rw [h]
    _ = Real.exp (-(shellBlock m n omega x + normalizerLogError M m n)) *
          (b /
            tailCoefficient M L m omega x) := by
            rw [mul_inv_rev, ← Real.exp_neg, inv_div]

/-- The combined coefficient-ratio identity on a translated local cube, while
the normalizer remains the global cube average of the untranslated sample. -/
theorem translatedNormalizedCutoffRatio_eq_tailCoefficientRatio_mul_exp
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z x : Vec d) :
    (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega) x /
        tailCoefficientCubeAverage M L m omega) /
        (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x /
          ahom M n) =
      (tailCoefficient M L m (translatePotentialSample z omega) x /
        tailCoefficientCubeAverage M L m omega) *
        Real.exp (shellBlock m n (translatePotentialSample z omega) x +
          normalizerLogError M m n) := by
  exact normalizedCutoffRatio_eq_tailCoefficient_div_mul_exp M hnm hmL
    (translatePotentialSample z omega) x
      (tailCoefficientCubeAverage_pos M L m omega).ne'

/-- Reciprocal translated form of the combined coefficient-ratio identity. -/
theorem translatedNormalizedCutoffRatio_inv_eq_exp_neg_mul_tailCoefficientRatio_inv
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z x : Vec d) :
    (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x /
        ahom M n) /
        (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega) x /
          tailCoefficientCubeAverage M L m omega) =
      Real.exp (-(shellBlock m n (translatePotentialSample z omega) x +
        normalizerLogError M m n)) *
        (tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m (translatePotentialSample z omega) x) := by
  exact normalizedCutoffRatio_inv_eq_exp_neg_mul_tailCoefficient_div M hnm hmL
    (translatePotentialSample z omega) x
      (tailCoefficientCubeAverage_pos M L m omega).ne'

/-- The forward deviation in the exact orientation used by the second
`scalarRatioLInf` term of `cutoffRatioError`. -/
theorem translatedCutoffRatio_forward_sub_one_eq_combined
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z x : Vec d) :
    ((ahom M n / tailCoefficientCubeAverage M L m omega) *
          _root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega) x) /
        _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x - 1 =
      (tailCoefficient M L m (translatePotentialSample z omega) x /
          tailCoefficientCubeAverage M L m omega) *
        Real.exp (shellBlock m n (translatePotentialSample z omega) x +
          normalizerLogError M m n) - 1 := by
  have h := translatedNormalizedCutoffRatio_eq_tailCoefficientRatio_mul_exp
    M hnm hmL omega z x
  have hL := _root_.SubdiffusiveProcess.Model.aCutoff_pos M L
    (translatePotentialSample z omega) x
  have hn := _root_.SubdiffusiveProcess.Model.aCutoff_pos M n
    (translatePotentialSample z omega) x
  have hbar := tailCoefficientCubeAverage_pos M L m omega
  have hahom := ahom_pos M n
  rw [show ((ahom M n / tailCoefficientCubeAverage M L m omega) *
          _root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega) x) /
        _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x =
      (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega) x /
        tailCoefficientCubeAverage M L m omega) /
      (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x /
        ahom M n) by field_simp]
  rw [h]

/-- The reciprocal deviation in the exact orientation used by the first
`scalarRatioLInf` term of `cutoffRatioError`. -/
theorem translatedCutoffRatio_reverse_sub_one_eq_combined
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z x : Vec d) :
    ((tailCoefficientCubeAverage M L m omega / ahom M n) *
          _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x) /
        _root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega) x - 1 =
      Real.exp (-(shellBlock m n (translatePotentialSample z omega) x +
          normalizerLogError M m n)) *
        (tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m (translatePotentialSample z omega) x) - 1 := by
  have h :=
    translatedNormalizedCutoffRatio_inv_eq_exp_neg_mul_tailCoefficientRatio_inv
      M hnm hmL omega z x
  have hL := _root_.SubdiffusiveProcess.Model.aCutoff_pos M L
    (translatePotentialSample z omega) x
  have hn := _root_.SubdiffusiveProcess.Model.aCutoff_pos M n
    (translatePotentialSample z omega) x
  have hbar := tailCoefficientCubeAverage_pos M L m omega
  have hahom := ahom_pos M n
  rw [show ((tailCoefficientCubeAverage M L m omega / ahom M n) *
          _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x) /
        _root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega) x =
      (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x /
        ahom M n) /
      (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega) x /
        tailCoefficientCubeAverage M L m omega) by field_simp]
  rw [h]

/-- The forward `L^infinity` ratio error equals the combined-ratio error. -/
theorem scalarRatioLInf_forward_eq_combinedCoefficientRatio
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (U : Ch02.Domain d) :
    scalarRatioLInf U
        (fun x => (ahom M n / tailCoefficientCubeAverage M L m omega) *
          _root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega) x)
        (_root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega)) =
      scalarRatioLInf U (combinedCoefficientRatio M L m n omega z)
        (fun _ => 1) := by
  unfold scalarRatioLInf
  congr 1
  simp only [SubdiffusiveProcess.RawLp.eLpNorm_top_exponent]
  apply eLpNormEssSup_congr_ae
  filter_upwards with x
  rw [translatedCutoffRatio_forward_sub_one_eq_combined M hnm hmL omega z x]
  simp only [combinedCoefficientRatio, div_one]

/-- The reciprocal `L^infinity` ratio error equals the reciprocal
combined-ratio error. -/
theorem scalarRatioLInf_reverse_eq_combinedCoefficientRatioInv
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (U : Ch02.Domain d) :
    scalarRatioLInf U
        (fun x => (tailCoefficientCubeAverage M L m omega / ahom M n) *
          _root_.SubdiffusiveProcess.Model.aCutoff M n (translatePotentialSample z omega) x)
        (_root_.SubdiffusiveProcess.Model.aCutoff M L (translatePotentialSample z omega)) =
      scalarRatioLInf U (combinedCoefficientRatioInv M L m n omega z)
        (fun _ => 1) := by
  unfold scalarRatioLInf
  congr 1
  simp only [SubdiffusiveProcess.RawLp.eLpNorm_top_exponent]
  apply eLpNormEssSup_congr_ae
  filter_upwards with x
  rw [translatedCutoffRatio_reverse_sub_one_eq_combined M hnm hmL omega z x]
  simp only [combinedCoefficientRatioInv, div_one]

/-- `cutoffRatioError` rewritten exactly as the two squared combined-ratio
errors that the good-event layer must estimate. -/
theorem cutoffRatioError_tailAverage_eq_combined
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (z : Vec d)
    (U : Ch02.Domain d) :
    cutoffRatioError M n L (translatePotentialSample z omega) U
        (tailCoefficientCubeAverage M L m omega) =
      scalarRatioLInf U (combinedCoefficientRatioInv M L m n omega z)
          (fun _ => 1) ^ 2 +
        scalarRatioLInf U (combinedCoefficientRatio M L m n omega z)
          (fun _ => 1) ^ 2 := by
  unfold cutoffRatioError
  rw [scalarRatioLInf_reverse_eq_combinedCoefficientRatioInv M hnm hmL omega z U,
    scalarRatioLInf_forward_eq_combinedCoefficientRatio M hnm hmL omega z U]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
