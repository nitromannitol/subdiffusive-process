module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.DepthGammaOne
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseResidueWindow
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseWindowSplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseWindowEstimate

@[expose] public section

/-!
# The response window with a sharp (log-free) mean slot

The proved parameterized response window reinserts the row means through
`integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo`, i.e. it
estimates `∫ row` by `gammaMomentConst 2 · A` where `A` is the row's Gamma-two
scale.  That is the *only* use the mean half makes of the Gamma-two
hypothesis — the centering is already at the true integral
(`centeredCutoffParameterizedResponseRow` subtracts `∫ row`, not `A`).

Substituting any other valid first-moment bound `mu1` therefore leaves the
whole construction intact, and this module records that generalization.  With
`mu1` supplied by
`exists_integral_cutoffParameterizedResponseRow_le` (`ResponseFirstMoment.lean`)
the mean slot becomes log-free in `δ`, which is what conjunct (2) of
`p.cutoff.regularity.good.scales` requires and what the Gamma-two route cannot
deliver (see §A.4 ).

Everything here is additive: no proved declaration is modified, so every
existing consumer of the parameterized window is untouched.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Reinsert the retained row means using an arbitrary valid first-moment
bound `mu1`, rather than the Gamma-two surrogate `gammaMomentConst 2 · A`.

This is the generalization of
`Section6Cutoff.sum_cutoffParameterizedResponseRow_le_centered_add_mean_bound`;
instantiating `mu1 := gammaMomentConst 2 * A` recovers it exactly. -/
theorem sum_cutoffParameterizedResponseRow_le_centered_add_sharp_mean
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (s : ℝ) (n m : ℕ)
    {mu1 : ℝ}
    (hmu1 : ∀ j : ℕ,
      ∫ eta, cutoffParameterizedResponseRow M L s j eta ∂M.P.toMeasure ≤ mu1)
    (omega : Sample d) :
    (∑ j ∈ Finset.Icc n m,
      cutoffParameterizedResponseRow M L s j omega) ≤
      centeredCutoffParameterizedResponseWindow M L s n m omega +
        ((m + 1 - n : ℕ) : ℝ) * mu1 := by
  have hcard : (Finset.Icc n m).card = m + 1 - n := Nat.card_Icc n m
  have hsplit :
      (∑ j ∈ Finset.Icc n m,
        cutoffParameterizedResponseRow M L s j omega) =
        centeredCutoffParameterizedResponseWindow M L s n m omega +
          ∑ j ∈ Finset.Icc n m,
            ∫ eta, cutoffParameterizedResponseRow M L s j eta
              ∂M.P.toMeasure := by
    unfold centeredCutoffParameterizedResponseWindow
      centeredCutoffParameterizedResponseRow
    rw [Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  have hbound : (∑ j ∈ Finset.Icc n m,
      ∫ eta, cutoffParameterizedResponseRow M L s j eta ∂M.P.toMeasure) ≤
      ((m + 1 - n : ℕ) : ℝ) * mu1 := by
    calc (∑ j ∈ Finset.Icc n m,
        ∫ eta, cutoffParameterizedResponseRow M L s j eta ∂M.P.toMeasure)
        ≤ ∑ _j ∈ Finset.Icc n m, mu1 :=
          Finset.sum_le_sum fun j _ => hmu1 j
      _ = ((Finset.Icc n m).card : ℝ) * mu1 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((m + 1 - n : ℕ) : ℝ) * mu1 := by rw [hcard]
  linarith

/-- The active response window with the sharp mean slot. -/
theorem cutoffParameterizedAccumulatedResponseActiveWindow_le_centered_add_sharp_mean
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (n m : ℕ) {mu1 : ℝ}
    (hmu1 : ∀ j : ℕ,
      ∫ eta, cutoffParameterizedResponseRow M L s j eta ∂M.P.toMeasure ≤ mu1)
    (omega : Sample d) :
    cutoffParameterizedAccumulatedResponseActiveWindow M L s n m omega ≤
      (8 / s) *
        (centeredCutoffParameterizedResponseWindow M L s n m omega +
          ((m + 1 - n : ℕ) : ℝ) * mu1) :=
  (cutoffParameterizedAccumulatedResponseActiveWindow_le_rows
      M L hs hs1 n m omega).trans
    (mul_le_mul_of_nonneg_left
      (sum_cutoffParameterizedResponseRow_le_centered_add_sharp_mean
        M L s n m hmu1 omega)
      (div_nonneg (by norm_num) hs.le))

/-- The response-window mean bound with a sharp first-moment slot.  Identical
to `Section6Cutoff.cutoffParameterizedAccumulatedResponseWindowMeanBound`
except that the Gamma-two surrogate `gammaMomentConst 2 · A` is replaced by an
arbitrary valid first-moment bound `mu1`. -/
def cutoffParameterizedAccumulatedResponseWindowSharpMeanBound
    (s mu1 : ℝ) (n m : ℕ) : ℝ :=
  ((m + 1 - n : ℕ) : ℝ) * (2 * (8 / s) * mu1)

/-- The translated response window with the sharp mean slot.  The fluctuation
carrier and its Gamma-two scale are unchanged, so
`Section6Cutoff.isBigO_cutoffParameterizedAccumulatedResponseWindowFluctuation`
still applies verbatim. -/
theorem ae_sum_translatedCutoffParameterizedAccumulatedResponseSup_le_sharp_mean
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (z : Vec d)
    {n m : ℕ} (hnm : n ≤ m) {mu1 : ℝ}
    (hmu1 : ∀ j : ℕ,
      ∫ eta, cutoffParameterizedResponseRow M L s j eta ∂M.P.toMeasure ≤ mu1) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        translatedCutoffParameterizedAccumulatedResponseSup
          M L s k z omega) ≤
        cutoffParameterizedAccumulatedResponseWindowSharpMeanBound s mu1 n m +
          cutoffParameterizedAccumulatedResponseWindowFluctuation
            M L s z n m omega := by
  have horigin :=
    ae_sum_cutoffParameterizedAccumulatedResponseSup_le_windowConvolution
      M L hs hs1 n m
  have htranslated :=
    (Section6Covariance.measurePreserving_translatePotentialSample
      M z).quasiMeasurePreserving.ae horigin
  filter_upwards [htranslated] with omega hwindow
  have hlow := cutoffParameterizedAccumulatedResponseLowWindow_le_decay_rows
    M L hs hs1 n m (translatePotentialSample z omega)
  have hactive :=
    cutoffParameterizedAccumulatedResponseActiveWindow_le_centered_add_sharp_mean
      M L hs hs1 n m hmu1 (translatePotentialSample z omega)
  have hsplit :=
    cutoffParameterizedAccumulatedResponseWindowConvolution_eq_low_add_active
      M L s hnm (translatePotentialSample z omega)
  calc
    (∑ k ∈ Finset.Icc n m,
        translatedCutoffParameterizedAccumulatedResponseSup
          M L s k z omega) =
        ∑ k ∈ Finset.Icc n m,
          cutoffParameterizedAccumulatedResponseSup M L s k
            (translatePotentialSample z omega) := by
      refine Finset.sum_congr rfl fun k _hk => ?_
      exact translatedCutoffParameterizedAccumulatedResponseSup_eq_origin_translate
        M L s k z omega
    _ ≤ 2 * cutoffParameterizedAccumulatedResponseWindowConvolution
          M L s n m (translatePotentialSample z omega) := hwindow
    _ = 2 * (cutoffParameterizedAccumulatedResponseLowWindow M L s n m
          (translatePotentialSample z omega) +
        cutoffParameterizedAccumulatedResponseActiveWindow M L s n m
          (translatePotentialSample z omega)) := by rw [hsplit]
    _ ≤ 2 * ((8 / s) *
          cutoffParameterizedAccumulatedResponseLowRows M L s n
            (translatePotentialSample z omega) +
        (8 / s) *
          (centeredCutoffParameterizedResponseWindow M L s n m
              (translatePotentialSample z omega) +
            ((m + 1 - n : ℕ) : ℝ) * mu1)) :=
      mul_le_mul_of_nonneg_left (add_le_add hlow hactive) (by norm_num)
    _ = cutoffParameterizedAccumulatedResponseWindowSharpMeanBound s mu1 n m +
          cutoffParameterizedAccumulatedResponseWindowFluctuation
            M L s z n m omega := by
      unfold cutoffParameterizedAccumulatedResponseWindowSharpMeanBound
        cutoffParameterizedAccumulatedResponseWindowFluctuation
      ring

/-! ## Monotonicity of `SubdiffusiveProcess.OGammaLE` in its observable -/

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- `SubdiffusiveProcess.OGammaLE` is monotone in the observable: a smaller observable
inherits the bound.  Conjunct (2) uses this to pass from the fluctuation
carrier to the centred average that the statement names. -/
theorem ogammaLE_mono_observable {sigma A : ℝ} {X Y : Omega → ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hXm : Measurable X)
    (hle : ∀ᵐ omega ∂mu, X omega ≤ Y omega)
    (hY : SubdiffusiveProcess.OGammaLE mu sigma A Y) :
    SubdiffusiveProcess.OGammaLE mu sigma A X := by
  have hpoint : ∀ᵐ omega ∂mu,
      Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma) ≤
        Real.exp ((A⁻¹ * max (Y omega) 0) ^ sigma) := by
    filter_upwards [hle] with omega homega
    have hmax : max (X omega) 0 ≤ max (Y omega) 0 :=
      max_le_max homega le_rfl
    have hnn : 0 ≤ A⁻¹ * max (X omega) 0 :=
      mul_nonneg (inv_nonneg.mpr hA.le) (le_max_right _ _)
    exact Real.exp_le_exp.2
      (Real.rpow_le_rpow hnn
        (mul_le_mul_of_nonneg_left hmax (inv_nonneg.mpr hA.le)) hsigma.le)
  have hmeas : Measurable
      (fun omega => Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma)) :=
    (((measurable_const.mul (hXm.max measurable_const)).pow_const sigma)).exp
  have hint : Integrable
      (fun omega => Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma)) mu := by
    refine hY.1.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hpoint] with omega homega
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact homega
  exact ⟨hint, le_trans (integral_mono_ae hint hY.1 hpoint) hY.2⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity
