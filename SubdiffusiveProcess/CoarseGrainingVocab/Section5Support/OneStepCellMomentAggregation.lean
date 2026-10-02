import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletEnergyContinuity

/-!
# Stochastic aggregation of the one-step cell errors

Step 2 of the one-step upper and lower estimates uses the positive cell error

`A^2 + A^(3/2) B^(1/2)`.

This file packages the only probabilistic calculation in that passage.  The
fourth moments of `A` and `B` put the cell error in `L^2`; Cauchy--Schwarz then
pairs it with the second moment of the coarse ellipticity observable.  The
statement is measure-generic so the same theorem applies to each cell and to
the product of the sample law with a finite uniform cell law.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The source's positive Besov/Poincare cell error, written with square roots
instead of fractional powers. -/
def oneStepCellBesovError (A B : ℝ) : ℝ :=
  A ^ 2 + A * Real.sqrt A * Real.sqrt B

theorem oneStepCellBesovError_nonneg {A B : ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) :
    0 ≤ oneStepCellBesovError A B := by
  unfold oneStepCellBesovError
  positivity

/-- Pointwise fourth-moment compression behind the Step 2 Holder estimate.
The numerical constant is deliberately loose; only dimension-independent
finiteness and the powers of `A` and `B` matter downstream. -/
theorem oneStepCellBesovError_sq_le {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    oneStepCellBesovError A B ^ 2 ≤ 9 * (A ^ 4 + B ^ 4) := by
  have hsqrt := sqrt_mul_sqrt_le_half_add hA hB
  have hAB : A * B ≤ (A ^ 2 + B ^ 2) / 2 := by
    nlinarith [sq_nonneg (A - B)]
  have hcross : A * Real.sqrt A * Real.sqrt B ≤
      (3 * A ^ 2 + B ^ 2) / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt hA
    nlinarith
  have herror : oneStepCellBesovError A B ≤
      2 * (A ^ 2 + B ^ 2) := by
    unfold oneStepCellBesovError
    nlinarith [sq_nonneg A, sq_nonneg B]
  have herror0 := oneStepCellBesovError_nonneg hA hB
  have hsq := pow_le_pow_left₀ herror0 herror 2
  have hsumSq : (A ^ 2 + B ^ 2) ^ 2 ≤ 2 * (A ^ 4 + B ^ 4) := by
    nlinarith [sq_nonneg (A ^ 2 - B ^ 2)]
  nlinarith

/-- The cell error is square-integrable under fourth moments of `A` and `B`.
This is the exact integrability prerequisite for the subsequent stochastic
Cauchy--Schwarz step. -/
theorem integrable_sq_oneStepCellBesovError
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {A B : Omega → ℝ}
    (hA : Measurable A) (hB : Measurable B)
    (hA0 : 0 ≤ᵐ[mu] A) (hB0 : 0 ≤ᵐ[mu] B)
    (hA4 : Integrable (fun omega => A omega ^ 4) mu)
    (hB4 : Integrable (fun omega => B omega ^ 4) mu) :
    Integrable (fun omega => oneStepCellBesovError (A omega) (B omega) ^ 2) mu := by
  have hmajor : Integrable (fun omega => 9 * (A omega ^ 4 + B omega ^ 4)) mu :=
    (hA4.add hB4).const_mul 9
  refine hmajor.mono' ?_ ?_
  · exact (((hA.pow_const 2).add
      ((hA.mul (Real.continuous_sqrt.measurable.comp hA)).mul
        (Real.continuous_sqrt.measurable.comp hB))).pow_const 2).aestronglyMeasurable
  · filter_upwards [hA0, hB0] with omega hAomega hBomega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact oneStepCellBesovError_sq_le hAomega hBomega

/-- Step 2 stochastic cell aggregation.  A second moment of the ellipticity
factor and fourth moments of the two localization observables control the
expected oscillatory cell energy. -/
theorem integral_mul_oneStepCellBesovError_le
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu]
    {Lambda A B : Omega → ℝ}
    (hLambda : Measurable Lambda) (hA : Measurable A) (hB : Measurable B)
    (hLambda0 : 0 ≤ᵐ[mu] Lambda)
    (hA0 : 0 ≤ᵐ[mu] A) (hB0 : 0 ≤ᵐ[mu] B)
    (hLambda2 : Integrable (fun omega => Lambda omega ^ 2) mu)
    (hA4 : Integrable (fun omega => A omega ^ 4) mu)
    (hB4 : Integrable (fun omega => B omega ^ 4) mu) :
    ∫ omega, Lambda omega * oneStepCellBesovError (A omega) (B omega) ∂mu ≤
      3 * Real.sqrt (∫ omega, Lambda omega ^ 2 ∂mu) *
        Real.sqrt (∫ omega, A omega ^ 4 + B omega ^ 4 ∂mu) := by
  have hError2 := integrable_sq_oneStepCellBesovError hA hB hA0 hB0 hA4 hB4
  have hError0 : 0 ≤ᵐ[mu] fun omega =>
      oneStepCellBesovError (A omega) (B omega) := by
    filter_upwards [hA0, hB0] with omega hAomega hBomega
    exact oneStepCellBesovError_nonneg hAomega hBomega
  have hErrorMeas : Measurable fun omega =>
      oneStepCellBesovError (A omega) (B omega) :=
    (hA.pow_const 2).add
      ((hA.mul (Real.continuous_sqrt.measurable.comp hA)).mul
        (Real.continuous_sqrt.measurable.comp hB))
  have hLambdaMem : MemLp Lambda 2 mu :=
    (memLp_two_iff_integrable_sq hLambda.aestronglyMeasurable).2 hLambda2
  have hErrorMem : MemLp
      (fun omega => oneStepCellBesovError (A omega) (B omega)) 2 mu :=
    (memLp_two_iff_integrable_sq hErrorMeas.aestronglyMeasurable).2 hError2
  have hLambdaMem' : MemLp Lambda (ENNReal.ofReal 2) mu := by
    simpa using hLambdaMem
  have hErrorMem' : MemLp
      (fun omega => oneStepCellBesovError (A omega) (B omega))
        (ENNReal.ofReal 2) mu := by
    simpa using hErrorMem
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg hholder
    hLambda0 hError0 hLambdaMem' hErrorMem'
  have hsumInt : Integrable (fun omega => A omega ^ 4 + B omega ^ 4) mu :=
    hA4.add hB4
  have hErrorIntegral :
      ∫ omega, oneStepCellBesovError (A omega) (B omega) ^ 2 ∂mu ≤
        9 * ∫ omega, A omega ^ 4 + B omega ^ 4 ∂mu := by
    calc
      ∫ omega, oneStepCellBesovError (A omega) (B omega) ^ 2 ∂mu ≤
          ∫ omega, 9 * (A omega ^ 4 + B omega ^ 4) ∂mu := by
        exact integral_mono_ae hError2 ((hA4.add hB4).const_mul 9) <| by
          filter_upwards [hA0, hB0] with omega hAomega hBomega
          exact oneStepCellBesovError_sq_le hAomega hBomega
      _ = 9 * ∫ omega, A omega ^ 4 + B omega ^ 4 ∂mu := by
        rw [integral_const_mul]
  have hsumNonneg : 0 ≤ ∫ omega, A omega ^ 4 + B omega ^ 4 ∂mu :=
    integral_nonneg fun omega => by positivity
  have hsqrtNine : Real.sqrt (9 : ℝ) = 3 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 9 by norm_num)
    have hsqrt0 := Real.sqrt_nonneg (9 : ℝ)
    nlinarith
  have hsqrtError :
      Real.sqrt (∫ omega,
          oneStepCellBesovError (A omega) (B omega) ^ 2 ∂mu) ≤
        3 * Real.sqrt (∫ omega, A omega ^ 4 + B omega ^ 4 ∂mu) := by
    calc
      Real.sqrt (∫ omega,
          oneStepCellBesovError (A omega) (B omega) ^ 2 ∂mu) ≤
          Real.sqrt (9 * ∫ omega, A omega ^ 4 + B omega ^ 4 ∂mu) :=
        Real.sqrt_le_sqrt hErrorIntegral
      _ = Real.sqrt 9 *
          Real.sqrt (∫ omega, A omega ^ 4 + B omega ^ 4 ∂mu) :=
        Real.sqrt_mul (by norm_num : 0 ≤ (9 : ℝ)) _
      _ = 3 * Real.sqrt (∫ omega, A omega ^ 4 + B omega ^ 4 ∂mu) := by
        rw [hsqrtNine]
  calc
    ∫ omega, Lambda omega * oneStepCellBesovError (A omega) (B omega) ∂mu ≤
        Real.sqrt (∫ omega, Lambda omega ^ 2 ∂mu) *
          Real.sqrt (∫ omega,
            oneStepCellBesovError (A omega) (B omega) ^ 2 ∂mu) := by
      simpa only [Real.rpow_two, sq_abs, Real.sqrt_eq_rpow] using hcs
    _ ≤ Real.sqrt (∫ omega, Lambda omega ^ 2 ∂mu) *
          (3 * Real.sqrt (∫ omega, A omega ^ 4 + B omega ^ 4 ∂mu)) :=
      mul_le_mul_of_nonneg_left hsqrtError (Real.sqrt_nonneg _)
    _ = 3 * Real.sqrt (∫ omega, Lambda omega ^ 2 ∂mu) *
        Real.sqrt (∫ omega, A omega ^ 4 + B omega ^ 4 ∂mu) := by ring

/-- Cauchy--Schwarz for a normalized finite cell average.  This is kept in
the real carrier because the one-step proof takes expectations before the
thermodynamic limit. -/
theorem normalized_finset_sum_mul_le_sqrt_mul_sqrt
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (f g : ι → ℝ) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i * g i ≤
      Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i ^ 2) *
        Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, g i ^ 2) := by
  have hcard : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s f g
  have hsumF : 0 ≤ ∑ i ∈ s, f i ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsumG : 0 ≤ ∑ i ∈ s, g i ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hinv : 0 ≤ (s.card : ℝ)⁻¹ := inv_nonneg.mpr hcard.le
  calc
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i * g i ≤
        ((s.card : ℝ)⁻¹) *
          (Real.sqrt (∑ i ∈ s, f i ^ 2) *
            Real.sqrt (∑ i ∈ s, g i ^ 2)) :=
      mul_le_mul_of_nonneg_left hcs hinv
    _ = Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i ^ 2) *
        Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, g i ^ 2) := by
      rw [Real.sqrt_mul hinv, Real.sqrt_mul hinv]
      conv_lhs =>
        rw [← Real.sq_sqrt hinv]
      ring

/-- The finite-cell version of the Step 2 stochastic estimate.  It uses the
averaged fourth moments printed in the source, rather than replacing them by
a uniform-in-cell bound. -/
theorem normalized_finset_integral_mul_oneStepCellBesovError_le
    {ι Omega : Type*} [DecidableEq ι] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (s : Finset ι) (hs : s.Nonempty)
    (Lambda A B : ι → Omega → ℝ)
    (hLambda : ∀ i ∈ s, Measurable (Lambda i))
    (hA : ∀ i ∈ s, Measurable (A i))
    (hB : ∀ i ∈ s, Measurable (B i))
    (hLambda0 : ∀ i ∈ s, 0 ≤ᵐ[mu] Lambda i)
    (hA0 : ∀ i ∈ s, 0 ≤ᵐ[mu] A i)
    (hB0 : ∀ i ∈ s, 0 ≤ᵐ[mu] B i)
    (hLambda2 : ∀ i ∈ s, Integrable (fun omega => Lambda i omega ^ 2) mu)
    (hA4 : ∀ i ∈ s, Integrable (fun omega => A i omega ^ 4) mu)
    (hB4 : ∀ i ∈ s, Integrable (fun omega => B i omega ^ 4) mu) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
        ∫ omega, Lambda i omega *
          oneStepCellBesovError (A i omega) (B i omega) ∂mu ≤
      3 * Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s,
          ∫ omega, Lambda i omega ^ 2 ∂mu) *
        Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s,
          ∫ omega, A i omega ^ 4 + B i omega ^ 4 ∂mu) := by
  let f : ι → ℝ := fun i => Real.sqrt (∫ omega, Lambda i omega ^ 2 ∂mu)
  let g : ι → ℝ := fun i =>
    Real.sqrt (∫ omega, A i omega ^ 4 + B i omega ^ 4 ∂mu)
  have hcell : ∀ i ∈ s,
      ∫ omega, Lambda i omega *
          oneStepCellBesovError (A i omega) (B i omega) ∂mu ≤
        3 * f i * g i := by
    intro i hi
    exact integral_mul_oneStepCellBesovError_le
      (hLambda i hi) (hA i hi) (hB i hi)
      (hLambda0 i hi) (hA0 i hi) (hB0 i hi)
      (hLambda2 i hi) (hA4 i hi) (hB4 i hi)
  have hcard : 0 ≤ (s.card : ℝ)⁻¹ := by positivity
  have hsum :
      ((s.card : ℝ)⁻¹) * ∑ i ∈ s,
          ∫ omega, Lambda i omega *
            oneStepCellBesovError (A i omega) (B i omega) ∂mu ≤
        3 * (((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i * g i) := by
    calc
      _ ≤ ((s.card : ℝ)⁻¹) * ∑ i ∈ s, 3 * f i * g i := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i hi => hcell i hi) hcard
      _ = 3 * (((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i * g i) := by
        simp only [Finset.mul_sum]
        ring_nf
  have hcs := normalized_finset_sum_mul_le_sqrt_mul_sqrt s hs f g
  have hfSq : ∀ i ∈ s, f i ^ 2 = ∫ omega, Lambda i omega ^ 2 ∂mu := by
    intro i hi
    dsimp only [f]
    rw [Real.sq_sqrt]
    exact integral_nonneg fun omega => sq_nonneg _
  have hgSq : ∀ i ∈ s, g i ^ 2 =
      ∫ omega, A i omega ^ 4 + B i omega ^ 4 ∂mu := by
    intro i hi
    dsimp only [g]
    rw [Real.sq_sqrt]
    exact integral_nonneg fun omega => by positivity
  have hfSum : (∑ i ∈ s, f i ^ 2) =
      ∑ i ∈ s, ∫ omega, Lambda i omega ^ 2 ∂mu := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hfSq i hi
  have hgSum : (∑ i ∈ s, g i ^ 2) =
      ∑ i ∈ s, ∫ omega, A i omega ^ 4 + B i omega ^ 4 ∂mu := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hgSq i hi
  calc
    _ ≤ 3 * (((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i * g i) := hsum
    _ ≤ 3 * (Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i ^ 2) *
        Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, g i ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ = _ := by
      rw [hfSum, hgSum]
      ring

/-- Numerical close of the manuscript's `delta^15` cell-moment estimate.
If the ellipticity factor has second moment at most `L^2` and the combined
fourth-moment budget is at most `2 E^4`, the Step 2 error is at most
`6 L E^2`.  In the source `E = C delta^15`, hence the power `delta^30`. -/
theorem three_mul_sqrt_mul_sqrt_le_six_mul_sq
    {X Y L E : ℝ} (hY0 : 0 ≤ Y) (hL : 0 ≤ L)
    (hX : X ≤ L ^ 2) (hY : Y ≤ 2 * E ^ 4) :
    3 * Real.sqrt X * Real.sqrt Y ≤ 6 * L * E ^ 2 := by
  have hsqrtX : Real.sqrt X ≤ L :=
    Real.sqrt_le_left hL |>.2 hX
  have hY' : Y ≤ (2 * E ^ 2) ^ 2 := by
    calc
      Y ≤ 2 * E ^ 4 := hY
      _ ≤ 4 * E ^ 4 := by
        have hE4 : 0 ≤ E ^ 4 := by positivity
        linarith
      _ = (2 * E ^ 2) ^ 2 := by ring
  have hsqrtY : Real.sqrt Y ≤ 2 * E ^ 2 :=
    Real.sqrt_le_left (by positivity) |>.2 hY'
  have hsqrtX0 := Real.sqrt_nonneg X
  have hsqrtY0 := Real.sqrt_nonneg Y
  nlinarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
