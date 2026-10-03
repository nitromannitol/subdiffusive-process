module

public import SubdiffusiveProcess.Section6SumErrors.ResponseWindow
public import SubdiffusiveProcess.Section6SumErrors.ResponseMean
public import SubdiffusiveProcess.Section6SumErrors.FieldLowWindow

@[expose] public section

/-!
# WindowCarriers

The literal frozen accumulated error is bounded by response, field and gradient carriers over any window and any positive order.
-/

namespace SubdiffusiveProcess.Section6SumErrors.Response
open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

theorem measurable_accumulatedResponseLowRows (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) :
    Measurable ((accumulatedResponseLowRows s) M n) := by
  unfold accumulatedResponseLowRows
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul ((measurable_holderResponseRow s) M j)

theorem accumulatedError_none_s_eq_parts (s : ℝ) {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Homogenization.Vec d)
    (omega : Sample d) :
    accumulatedError M none k z s omega =
      (translatedAccumulatedResponseSup s) M k z omega +
        translatedAccumulatedBlockSup k z s omega +
        (3 : ℝ) ^ (-(s / 8) * k) *
          supNormOn (translatedCube d (k : ℤ) z) (omega 0) +
        ∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0 := by
  unfold accumulatedError translatedAccumulatedResponseSup
    translatedAccumulatedBlockSup
  simp only [Option.getD_none, min_self]

theorem ae_sum_accumulatedError_le_carriers (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Homogenization.Vec d)
    {n m : ℕ} (hnm : n ≤ m) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        accumulatedError M none k z s omega) ≤
        2 * ((accumulatedResponseLowWindow s) M n m
              (translatePotentialSample z omega) +
            (accumulatedResponseActiveWindow s) M n m
              (translatePotentialSample z omega)) +
        2 * (accumulatedFiniteFieldLowWindow z s n m omega +
            accumulatedFiniteFieldActiveWindow z s n m omega) +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := by
  have hresponse0 := (ae_sum_accumulatedResponseSup_le_windowConvolution s hs hs1) M n m
  have hresponse :=
    (Section6Covariance.measurePreserving_translatePotentialSample M z).quasiMeasurePreserving.ae
      hresponse0
  filter_upwards [hresponse, ae_sum_accumulatedGradientSuffix_le M z hnm]
    with omega hresp hgrad
  have hfinite :=
    sum_translatedBlockSup_add_shellZero_le_finiteFieldWindowConvolution
      z hs n m omega
  have hrespEq := (accumulatedResponseWindowConvolution_eq_low_add_active s)
    M hnm (translatePotentialSample z omega)
  have hfieldEq := accumulatedFiniteFieldWindowConvolution_eq_low_add_active
    z s hnm omega
  calc
    (∑ k ∈ Finset.Icc n m,
        accumulatedError M none k z s omega) =
      (∑ k ∈ Finset.Icc n m,
          (translatedAccumulatedResponseSup s) M k z omega) +
        (∑ k ∈ Finset.Icc n m,
          (translatedAccumulatedBlockSup k z s omega +
            (3 : ℝ) ^ (-(s / 8) * k) *
              supNormOn (translatedCube d (k : ℤ) z) (omega 0))) +
        (∑ k ∈ Finset.Icc n m, ∑' j : ℕ, if k ≤ j then
          (3 : ℝ) ^ k * vectorSupNormOn (translatedCube d (k : ℤ) z)
            (shellGradient (omega j)) else 0) := by
      simp_rw [(accumulatedError_none_s_eq_parts s)]
      simp_rw [Finset.sum_add_distrib]
      ring
    _ ≤ 2 * (accumulatedResponseWindowConvolution s) M n m
          (translatePotentialSample z omega) +
        2 * accumulatedFiniteFieldWindowConvolution z s n m omega +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := by
      have hresp' : (∑ k ∈ Finset.Icc n m,
          (translatedAccumulatedResponseSup s) M k z omega) ≤
          2 * (accumulatedResponseWindowConvolution s) M n m
            (translatePotentialSample z omega) := by
        simpa only [(translatedAccumulatedResponseSup_eq_origin_translate s)]
          using hresp
      linarith
    _ = _ := by rw [hrespEq, hfieldEq]

/-- The sum of centered and geometrically decaying fluctuation carriers. -/
noncomputable def accumulatedErrorWindowFluctuation (s : ℝ) {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Homogenization.Vec d)
    (n m : ℕ) : Sample d → ℝ :=
  fun omega ↦
    2 * (8 / s) *
      ((accumulatedResponseLowRows s) M n (translatePotentialSample z omega) +
        (centeredHolderResponseWindow s) M n m (translatePotentialSample z omega)) +
    2 * (accumulatedFiniteFieldLowWindow z s n m omega +
      centeredAccumulatedFiniteFieldActiveWindow M z s n m omega) +
    (3 / 2 : ℝ) *
      (centeredAccumulatedGradientWindow M z n m omega +
        accumulatedGradientEnvelope m z omega)

/-- The deterministic accumulated-error mean bound over a scale window. -/
def accumulatedErrorWindowMeanBound (s : ℝ) {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (B : ℝ) (n m : ℕ) : ℝ :=
  ((m + 1 - n : ℕ) : ℝ) *
    (2 * (8 / s) * B +
      2 * (IndependentSums.gammaMomentConst 2 * accumulatedFiniteFieldScaleBound M s) +
      (3 / 2 : ℝ) *
        (IndependentSums.gammaMomentConst 2 * accumulatedGradientOwnRowScale M))

/-- The Gaussian scale of the active response-window sum. -/
def accumulatedResponseActiveWindowScale (d : ℕ) (A : ℝ) (n m : ℕ) : ℝ :=
  Ch04.gammaTriangleConst 2 * (responseScoreRange d : ℝ) *
    (Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) * A))

/-- The Gaussian scale obtained by combining all fluctuation carriers. -/
def accumulatedErrorWindowFluctuationScale (s : ℝ) {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (A : ℝ) (n m : ℕ) : ℝ :=
  let T := Ch04.gammaTriangleConst 2
  let Rlow := 2 * (8 / s) *
    (Ch04.gammaTriangleConst 2 * ((8 / s) * A))
  let Ractive := 2 * (8 / s) *
    accumulatedResponseActiveWindowScale d A n m
  let Flow := 2 * (Ch04.gammaTriangleConst 2 *
    (Ch04.gammaTriangleConst 2 * fieldOneGammaDimScale M *
      (24 / (s / 8) ^ 3)))
  let Factive := 2 * (Ch04.gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
      ((1 + IndependentSums.gammaMomentConst 2) *
        accumulatedFiniteFieldScaleBound M s))
  let Gactive := (3 / 2 : ℝ) *
    (Ch04.gammaSigmaIndependentSumConst 2 *
      Real.sqrt ((m + 1 - n : ℕ) : ℝ) *
        ((1 + IndependentSums.gammaMomentConst 2) *
          accumulatedGradientOwnRowScale M))
  let Gtail := (3 / 2 : ℝ) * accumulatedGradientEnvelopeScale M
  T * (T * (T * (T * (T * (Rlow + Ractive) + Flow) + Factive) + Gactive) + Gtail)

theorem ae_sum_accumulatedError_le_mean_add_fluctuation (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1)
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (z : Homogenization.Vec d)
    {n m : ℕ} (hnm : n ≤ m)
    (B : ℝ) (hmean : ∀ j : ℕ, ∫ omega, holderResponseRow s M j omega ∂M.P.toMeasure ≤ B) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        accumulatedError M none k z s omega) ≤
        (accumulatedErrorWindowMeanBound s) M B n m +
          (accumulatedErrorWindowFluctuation s) M z n m omega := by
  filter_upwards [(ae_sum_accumulatedError_le_carriers s hs hs1) M z hnm] with omega hcarrier
  have hrespLow := (accumulatedResponseLowWindow_le_decay_rows s hs hs1)
    M n m (translatePotentialSample z omega)
  have hrespLow' : (accumulatedResponseLowWindow s) M n m
      (translatePotentialSample z omega) ≤
      (8 / s) * (accumulatedResponseLowRows s) M n
        (translatePotentialSample z omega) := by
    simpa only [accumulatedResponseLowRows] using hrespLow
  have hrespActive : accumulatedResponseActiveWindow s M n m (translatePotentialSample z omega) ≤
      (8 / s) * (centeredHolderResponseWindow s M n m (translatePotentialSample z omega) +
        ((m + 1 - n : ℕ) : ℝ) * B) := by
    have hrows := accumulatedResponseActiveWindow_le_rows s hs hs1 M n m
      (translatePotentialSample z omega)
    have hsum : (∑ j ∈ Finset.Icc n m, holderResponseRow s M j (translatePotentialSample z omega)) ≤
        centeredHolderResponseWindow s M n m (translatePotentialSample z omega) +
          ((m + 1 - n : ℕ) : ℝ) * B := by
      calc
        _ = centeredHolderResponseWindow s M n m (translatePotentialSample z omega) +
            ∑ j ∈ Finset.Icc n m, ∫ eta, holderResponseRow s M j eta ∂M.P.toMeasure := by
          unfold centeredHolderResponseWindow centeredHolderResponseRow
          rw [Finset.sum_sub_distrib]
          ring
        _ ≤ centeredHolderResponseWindow s M n m (translatePotentialSample z omega) +
            ∑ j ∈ Finset.Icc n m, B := by gcongr with j hj; exact hmean j
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    exact hrows.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hfieldActive := accumulatedFiniteFieldActiveWindow_le_centered_add_mean
    M z hs (by linarith) hnm omega
  have hgradMean := sum_accumulatedGradientOwnRow_le_centered_add_mean
    M z n m omega
  unfold accumulatedErrorWindowMeanBound accumulatedErrorWindowFluctuation
  have hconst : 0 ≤ 8 / s := by positivity [hs]
  calc
    _ ≤ 2 * ((accumulatedResponseLowWindow s) M n m
              (translatePotentialSample z omega) +
            (accumulatedResponseActiveWindow s) M n m
              (translatePotentialSample z omega)) +
        2 * (accumulatedFiniteFieldLowWindow z s n m omega +
            accumulatedFiniteFieldActiveWindow z s n m omega) +
        (3 / 2 : ℝ) *
          ((∑ k ∈ Finset.Icc n m, accumulatedGradientOwnRow k z omega) +
            accumulatedGradientEnvelope m z omega) := hcarrier
    _ ≤ 2 * ((8 / s) * (accumulatedResponseLowRows s) M n
              (translatePotentialSample z omega) +
            (8 / s) *
              ((centeredHolderResponseWindow s) M n m
                  (translatePotentialSample z omega) +
                ((m + 1 - n : ℕ) : ℝ) * B)) +
        2 * (accumulatedFiniteFieldLowWindow z s n m omega +
          (centeredAccumulatedFiniteFieldActiveWindow M z s n m omega +
            ((m + 1 - n : ℕ) : ℝ) *
              (IndependentSums.gammaMomentConst 2 *
                accumulatedFiniteFieldScaleBound M s))) +
        (3 / 2 : ℝ) *
          ((centeredAccumulatedGradientWindow M z n m omega +
              ((m + 1 - n : ℕ) : ℝ) *
                (IndependentSums.gammaMomentConst 2 * accumulatedGradientOwnRowScale M)) +
            accumulatedGradientEnvelope m z omega) := by
      gcongr
    _ = ((m + 1 - n : ℕ) : ℝ) *
          (2 * (8 / s) * B +
            2 * (IndependentSums.gammaMomentConst 2 *
              accumulatedFiniteFieldScaleBound M s) +
            (3 / 2 : ℝ) *
              (IndependentSums.gammaMomentConst 2 * accumulatedGradientOwnRowScale M)) +
        (2 * (8 / s) *
          ((accumulatedResponseLowRows s) M n (translatePotentialSample z omega) +
            (centeredHolderResponseWindow s) M n m (translatePotentialSample z omega)) +
        2 * (accumulatedFiniteFieldLowWindow z s n m omega +
          centeredAccumulatedFiniteFieldActiveWindow M z s n m omega) +
        (3 / 2 : ℝ) *
          (centeredAccumulatedGradientWindow M z n m omega +
            accumulatedGradientEnvelope m z omega)) := by ring


end
end SubdiffusiveProcess.Section6SumErrors.Response
