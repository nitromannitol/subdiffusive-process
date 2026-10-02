import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.RandomFactorMeasurability
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FullResponseMoments
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.EllipticityErrorAggregation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PaperErrorBridge

/-!
# The coefficient-only Dirichlet energy factor

This file supplies the missing all-scale `q = 2` aggregation of the sharp
one-cube ellipticity comparison.  It then specializes that comparison to the
two normalized ellipticity factors used in the Dirichlet right-hand side.

The numerical constant is dimension-free.  The only nonlocal step is the
weighted Cauchy--Schwarz inequality

`sum w_n sqrt D_n <= sqrt (sum w_n D_n)`

for the geometric probability weights.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

namespace ErrorComparison

/-- Weighted Cauchy--Schwarz for a summable probability mass and a summable
nonnegative first moment. -/
private theorem tsum_mul_sqrt_le_sqrt_tsum_mul
    (w D : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hD : ∀ n, 0 ≤ D n)
    (hsumW : Summable w) (hsumD : Summable fun n ↦ w n * D n) :
    (∑' n, w n * Real.sqrt (D n)) ≤
      Real.sqrt ((∑' n, w n) * ∑' n, w n * D n) := by
  have hroot : Summable fun n ↦ w n * Real.sqrt (D n) := by
    apply Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg (hw n) (Real.sqrt_nonneg _))
      (fun n ↦ ?_)
      (hsumW.add hsumD)
    have hsqrt : Real.sqrt (D n) ≤ 1 + D n := by
      nlinarith [Real.sq_sqrt (hD n), Real.sqrt_nonneg (D n)]
    calc
      w n * Real.sqrt (D n) ≤ w n * (1 + D n) :=
        mul_le_mul_of_nonneg_left hsqrt (hw n)
      _ = w n + w n * D n := by ring
  apply hroot.tsum_le_of_sum_le
  intro s
  have hsumW_nonneg : 0 ≤ ∑ n ∈ s, w n :=
    Finset.sum_nonneg fun n _ ↦ hw n
  have hsumD_nonneg : 0 ≤ ∑ n ∈ s, w n * D n :=
    Finset.sum_nonneg fun n _ ↦ mul_nonneg (hw n) (hD n)
  have hcs : (∑ n ∈ s, w n * Real.sqrt (D n)) ≤
      Real.sqrt (∑ n ∈ s, w n) *
        Real.sqrt (∑ n ∈ s, w n * D n) := by
    have h := Real.sum_sqrt_mul_sqrt_le
      (s := s) (f := w) (g := fun n ↦ w n * D n)
      hw (fun n ↦ mul_nonneg (hw n) (hD n))
    convert h using 1
    · apply Finset.sum_congr rfl
      intro n hn
      calc
        w n * Real.sqrt (D n) = (Real.sqrt (w n)) ^ 2 * Real.sqrt (D n) := by
          rw [Real.sq_sqrt (hw n)]
        _ = Real.sqrt (w n) * (Real.sqrt (w n) * Real.sqrt (D n)) := by ring
        _ = Real.sqrt (w n) * Real.sqrt (w n * D n) := by
          rw [Real.sqrt_mul (hw n)]
  have hsumW_le : (∑ n ∈ s, w n) ≤ ∑' n, w n :=
    hsumW.sum_le_tsum s fun n _ ↦ hw n
  have hsumD_le : (∑ n ∈ s, w n * D n) ≤ ∑' n, w n * D n :=
    hsumD.sum_le_tsum s fun n _ ↦ mul_nonneg (hw n) (hD n)
  calc
    (∑ n ∈ s, w n * Real.sqrt (D n)) ≤
        Real.sqrt (∑ n ∈ s, w n) *
          Real.sqrt (∑ n ∈ s, w n * D n) := hcs
    _ ≤ Real.sqrt (∑' n, w n) * Real.sqrt (∑' n, w n * D n) := by
      gcongr
    _ = Real.sqrt ((∑' n, w n) * ∑' n, w n * D n) := by
      rw [Real.sqrt_mul (tsum_nonneg hw)]

/-- The sharp one-cube upper comparison survives a finite descendant maximum. -/
private theorem inv_mul_maxDescendantBMatrixNormAtScale_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (F : Ch02.TriadicCoeffFamily d) {sigma : ℝ} (hsigma : 0 < sigma) :
    sigma⁻¹ * Ch02.maxDescendantBMatrixNormAtScale Q k F ≤
      1 + 2 * Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
          (scalarMatrix (d := d) sigma) +
        Real.sqrt (2 * Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
          (scalarMatrix (d := d) sigma)) := by
  let D := Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
    (scalarMatrix (d := d) sigma)
  let C := 1 + 2 * D + Real.sqrt (2 * D)
  have hD : 0 ≤ D :=
    Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk F _
  have hne := descendantsAtScale_nonempty Q hk
  have hpoint : ∀ R ∈ descendantsAtScale Q k,
      Ch02.coarseBMatrixNorm R F ≤ sigma * C := by
    intro R hR
    have hRone :=
      Section4Recursion.ErrorComparison.inv_mul_coarseBMatrixNorm_le_one_add_add_sqrt
        R F hsigma
    have hMle :=
      Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        F (scalarMatrix (d := d) sigma) hR
    have hroot : Real.sqrt (2 * Ch02.normalizedBlockResponseMax R F
        (scalarMatrix (d := d) sigma)) ≤ Real.sqrt (2 * D) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left hMle (by norm_num)
    have hRle : sigma⁻¹ * Ch02.coarseBMatrixNorm R F ≤ C := by
      dsimp only [C, D]
      linarith
    exact (inv_mul_le_iff₀ hsigma).mp hRle
  have hmax : Ch02.maxDescendantBMatrixNormAtScale Q k F ≤ sigma * C := by
    simpa [Ch02.maxDescendantBMatrixNormAtScale] using
      Ch02.finsetSupReal_le (descendantsAtScale Q k) hne hpoint
  calc
    sigma⁻¹ * Ch02.maxDescendantBMatrixNormAtScale Q k F ≤
        sigma⁻¹ * (sigma * C) :=
      mul_le_mul_of_nonneg_left hmax (inv_nonneg.2 hsigma.le)
    _ = C := by field_simp

/-- Lower-inverse counterpart of
`inv_mul_maxDescendantBMatrixNormAtScale_le`. -/
private theorem mul_maxDescendantSigmaStarInvMatrixNormAtScale_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (F : Ch02.TriadicCoeffFamily d) {sigma : ℝ} (hsigma : 0 < sigma) :
    sigma * Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F ≤
      1 + 2 * Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
          (scalarMatrix (d := d) sigma) +
        Real.sqrt (2 * Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
          (scalarMatrix (d := d) sigma)) := by
  let D := Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
    (scalarMatrix (d := d) sigma)
  let C := 1 + 2 * D + Real.sqrt (2 * D)
  have hD : 0 ≤ D :=
    Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk F _
  have hne := descendantsAtScale_nonempty Q hk
  have hpoint : ∀ R ∈ descendantsAtScale Q k,
      Ch02.coarseSigmaStarInvMatrixNorm R F ≤ sigma⁻¹ * C := by
    intro R hR
    have hRone :=
      Section4Recursion.ErrorComparison.mul_coarseSigmaStarInvMatrixNorm_le_one_add_add_sqrt
        R F hsigma
    have hMle :=
      Ch02.normalizedBlockResponseMax_le_maxDescendantNormalizedBlockResponseAtScale
        F (scalarMatrix (d := d) sigma) hR
    have hroot : Real.sqrt (2 * Ch02.normalizedBlockResponseMax R F
        (scalarMatrix (d := d) sigma)) ≤ Real.sqrt (2 * D) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left hMle (by norm_num)
    have hRle : sigma * Ch02.coarseSigmaStarInvMatrixNorm R F ≤ C := by
      dsimp only [C, D]
      linarith
    exact (le_inv_mul_iff₀ hsigma).mpr hRle
  have hmax : Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F ≤
      sigma⁻¹ * C := by
    simpa [Ch02.maxDescendantSigmaStarInvMatrixNormAtScale] using
      Ch02.finsetSupReal_le (descendantsAtScale Q k) hne hpoint
  calc
    sigma * Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F ≤
        sigma * (sigma⁻¹ * C) := mul_le_mul_of_nonneg_left hmax hsigma.le
    _ = C := by field_simp

/-- The dimension-free upper half of `e.bound.Lambdas.by.Es` at `q = 2`.
This is the all-scale aggregation advertised by
`OneCubeEllipticityComparison.lean`. -/
theorem max_weightedEllipticity_le_one_add_two_mul_sq_add_sqrt_two_mul
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Ch02.TriadicCoeffFamily d) {s sigma : ℝ}
    (hs : 0 < s) (hsigma : 0 < sigma) :
    max (sigma⁻¹ * Ch02.LambdaSq Q s (.finite 2) F)
        (sigma * (Ch02.lambdaSq Q s (.finite 2) F)⁻¹) ≤
      1 + 2 *
          (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
            (scalarMatrix (d := d) sigma)) ^ 2 +
        Real.sqrt 2 *
          Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
            (scalarMatrix (d := d) sigma) := by
  let w : ℕ → ℝ := fun n ↦ Ch02.geometricWeight s 2 n
  let D : ℕ → ℝ := fun n ↦
    Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) F
      (scalarMatrix (d := d) sigma)
  let B : ℕ → ℝ := fun n ↦
    Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F
  let S : ℕ → ℝ := fun n ↦
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F
  have hw : ∀ n, 0 ≤ w n := by
    intro n
    simpa [w, Ch02.geometricWeight_eq_old] using
      (Homogenization.geometricWeight_nonneg (s := s) (q := (2 : ℝ)) n
        (by positivity : 0 ≤ s * 2))
  have hD : ∀ n, 0 ≤ D n := by
    intro n
    exact Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F _
  have hsumW : Summable w := by
    simpa [w, Ch02.geometricWeight_eq_old] using
      (Homogenization.summable_geometricWeight (s := s) (q := 2) (by positivity))
  have hsumD : Summable fun n ↦ w n * D n := by
    simpa [w, D] using
      Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
        Q F (scalarMatrix (d := d) sigma) hs
  have hsumB : Summable fun n ↦ w n * B n := by
    have h := Ch02.summable_B_series_pointwiseCoeffField Q F hs
      (by norm_num : (0 : ℝ) < 2)
    simpa [w, B, Real.rpow_one] using h
  have hsumS : Summable fun n ↦ w n * S n := by
    have h := Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q F hs
      (by norm_num : (0 : ℝ) < 2)
    simpa [w, S, Real.rpow_one] using h
  have hW : (∑' n, w n) = 1 := by
    simpa [w, Ch02.geometricWeight_eq_old] using
      (Homogenization.tsum_geometricWeight_eq_one (s := s) (q := 2)
        (by positivity))
  have hE : (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
      (scalarMatrix (d := d) sigma)) ^ 2 = ∑' n, w n * D n := by
    simpa [w, D] using
      Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs F
        (scalarMatrix (d := d) sigma)
  have hroot : (∑' n, w n * Real.sqrt (D n)) ≤
      Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
        (scalarMatrix (d := d) sigma) := by
    have hcs := tsum_mul_sqrt_le_sqrt_tsum_mul w D hw hD hsumW hsumD
    rw [hW, one_mul, ← hE] at hcs
    have hE0 : 0 ≤ Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
        (scalarMatrix (d := d) sigma) := by
      unfold Ch02.HomogenizationErrorOnCube Ch02.HomogenizationError
        Ch02.HomogenizationErrorFinite
      apply Real.rpow_nonneg
      apply tsum_nonneg
      intro n
      exact mul_nonneg
        (by
          simpa [Ch02.geometricWeight_eq_old] using
            (Homogenization.geometricWeight_nonneg (s := s) (q := (2 : ℝ)) n
              (by positivity : 0 ≤ s * 2)))
        (Real.rpow_nonneg
          (Ch02.scaleResponseAtScale_infinity_nonneg Q
            (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F
            (scalarMatrix (d := d) sigma)) _)
    simpa [Real.sqrt_sq hE0] using hcs
  have hLambda : Ch02.LambdaSq Q s (.finite 2) F = ∑' n, w n * B n := by
    have h := Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 2 F
      (by norm_num : (0 : ℝ) < 2) (by positivity : 0 ≤ s * 2)
    simpa [w, B, Real.rpow_one] using h
  have hlambda : (Ch02.lambdaSq Q s (.finite 2) F)⁻¹ = ∑' n, w n * S n := by
    have h := Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 2 F
      (by norm_num : (0 : ℝ) < 2) (by positivity : 0 ≤ s * 2)
    simpa [w, S, Real.rpow_one, Real.rpow_neg_one] using h
  have hbound (c : ℝ) (X : ℕ → ℝ)
      (hsumX : Summable fun n ↦ w n * X n)
      (hpoint : ∀ n, c * X n ≤ 1 + 2 * D n + Real.sqrt (2 * D n)) :
      c * (∑' n, w n * X n) ≤
        1 + 2 * (∑' n, w n * D n) +
          Real.sqrt 2 * (∑' n, w n * Real.sqrt (D n)) := by
    have hsumRoot : Summable fun n ↦ w n * Real.sqrt (D n) := by
      apply Summable.of_nonneg_of_le
        (fun n ↦ mul_nonneg (hw n) (Real.sqrt_nonneg _))
        (fun n ↦ ?_)
        (hsumW.add hsumD)
      have hsqrt : Real.sqrt (D n) ≤ 1 + D n := by
        nlinarith [Real.sq_sqrt (hD n), Real.sqrt_nonneg (D n)]
      calc
        w n * Real.sqrt (D n) ≤ w n * (1 + D n) :=
          mul_le_mul_of_nonneg_left hsqrt (hw n)
        _ = w n + w n * D n := by ring
    have hterm : ∀ n, w n * (c * X n) ≤
        w n * (1 + 2 * D n + Real.sqrt (2 * D n)) := fun n ↦
      mul_le_mul_of_nonneg_left (hpoint n) (hw n)
    calc
      c * (∑' n, w n * X n) = ∑' n, c * (w n * X n) :=
        (hsumX.tsum_mul_left c).symm
      _ = ∑' n, w n * (c * X n) := by
        apply tsum_congr
        intro n
        ring
      _ ≤ ∑' n, w n * (1 + 2 * D n + Real.sqrt (2 * D n)) := by
        apply Summable.tsum_le_tsum hterm
        · exact (hsumX.mul_left c).congr (fun n ↦ by ring)
        · convert (hsumW.add ((hsumD.mul_left 2).add
              (hsumRoot.mul_left (Real.sqrt 2)))) using 1
          funext n
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          ring
      _ = 1 + 2 * (∑' n, w n * D n) +
          Real.sqrt 2 * (∑' n, w n * Real.sqrt (D n)) := by
        rw [show (fun n ↦ w n * (1 + 2 * D n + Real.sqrt (2 * D n))) =
            fun n ↦ w n + (2 * (w n * D n) +
              Real.sqrt 2 * (w n * Real.sqrt (D n))) by
          funext n
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          ring,
          hsumW.tsum_add ((hsumD.mul_left 2).add
            (hsumRoot.mul_left (Real.sqrt 2))),
          (hsumD.mul_left 2).tsum_add (hsumRoot.mul_left (Real.sqrt 2)),
          hsumD.tsum_mul_left, hsumRoot.tsum_mul_left, hW]
        ring
  have hupper := hbound sigma⁻¹ B hsumB fun n ↦
    inv_mul_maxDescendantBMatrixNormAtScale_le Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F hsigma
  have hlower := hbound sigma S hsumS fun n ↦
    mul_maxDescendantSigmaStarInvMatrixNormAtScale_le Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F hsigma
  rw [← hLambda] at hupper
  rw [← hlambda] at hlower
  have hrootTerm : Real.sqrt 2 * (∑' n, w n * Real.sqrt (D n)) ≤
      Real.sqrt 2 * Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) F
        (scalarMatrix (d := d) sigma) :=
    mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg 2)
  rw [← hE] at hupper hlower
  apply max_le
  · linarith
  · linarith

end ErrorComparison

/-- Taking a square root turns the quadratic error envelope into the linear
envelope used in the Dirichlet energy row. -/
private theorem sqrt_le_one_add_two_mul_of_le
    {X E : ℝ} (hE : 0 ≤ E)
    (h : X ≤ 1 + 2 * E ^ 2 + Real.sqrt 2 * E) :
    Real.sqrt X ≤ 1 + 2 * E := by
  have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      X ≤ 1 + 2 * E ^ 2 + Real.sqrt 2 * E := h
      _ ≤ (1 + 2 * E) ^ 2 := by nlinarith

/-- The literal full `q = 2` response error controls both normalized
ellipticity factors at every larger regularity exponent.  The finiteness
premise is later supplied almost everywhere by the response moment row; it is
necessary because the real readout of `⊤ : ℝ≥0∞` is zero. -/
theorem max_sqrt_weightedEllipticity_le_dirichletEllipticityEnvelope
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    {s t : ℝ} (hs : 0 < s) (hst : s / 2 ≤ t)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hfinite : paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        (s / 2) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L) ≠ ⊤) :
    max
        (Real.sqrt ((ahom M L)⁻¹ *
          Ch02.LambdaSq (originCube d (N : ℤ)) t (.finite 2)
            (aCutoffFamily M L omega)))
        (Real.sqrt (ahom M L *
          (Ch02.lambdaSq (originCube d (N : ℤ)) t (.finite 2)
            (aCutoffFamily M L omega))⁻¹)) ≤
      dirichletEllipticityEnvelope M L N s omega := by
  let Q := originCube d (N : ℤ)
  let F := aCutoffFamily M L omega
  let sigma := ahom M L
  let E := Ch02.HomogenizationErrorOnCube Q (s / 2) .infinity (.finite 2) F
    (scalarMatrix (d := d) sigma)
  have hu : 0 < s / 2 := by linarith
  have hsigma : 0 < sigma := by simpa [sigma] using ahom_pos M L
  have hF : ∀ R, (F.coeffOn R).IsSymmetric := by
    intro R
    exact (aCutoffEnvelopeScalarTriadicCoeffData M L omega).onCube R
      |>.isSymmetric
  have hE0 : 0 ≤ E := by
    unfold E Ch02.HomogenizationErrorOnCube Ch02.HomogenizationError
      Ch02.HomogenizationErrorFinite
    exact Real.rpow_nonneg (tsum_nonneg fun n ↦
      mul_nonneg
        (by
          simpa [Ch02.geometricWeight_eq_old] using
            (Homogenization.geometricWeight_nonneg
              (s := s / 2) (q := (2 : ℝ)) n (by positivity)))
        (Real.rpow_nonneg
          (Ch02.scaleResponseAtScale_infinity_nonneg Q
            (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F
            (scalarMatrix (d := d) sigma)) _)) _
  have hEpaper : E ≤ dirichletFullResponseTwo M L N s omega := by
    change E ≤ (paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
      (s / 2) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)).toReal
    rw [← ENNReal.ofReal_le_iff_le_toReal hfinite]
    simpa [Q, F, sigma, dirichletFullResponseTwo] using
      Section6HarmonicApproximation.ofReal_homogenizationErrorOnCube_infinity_two_le_paper
        Q F hF hu hsigma
  have hbase :=
    ErrorComparison.max_weightedEllipticity_le_one_add_two_mul_sq_add_sqrt_two_mul
      Q F hu hsigma
  have hLambda : Ch02.LambdaSq Q t (.finite 2) F ≤
      Ch02.LambdaSq Q (s / 2) (.finite 2) F := by
    rcases hst.eq_or_lt with hEq | hlt
    · rw [hEq]
    · exact Ch02.LambdaSq_finite_antitone Q F hu hlt (by norm_num)
  have hlambdaInv : (Ch02.lambdaSq Q t (.finite 2) F)⁻¹ ≤
      (Ch02.lambdaSq Q (s / 2) (.finite 2) F)⁻¹ := by
    rcases hst.eq_or_lt with hEq | hlt
    · rw [hEq]
    · have hmono : Ch02.lambdaSq Q (s / 2) (.finite 2) F ≤
          Ch02.lambdaSq Q t (.finite 2) F :=
        Ch02.lambdaSq_finite_mono Q F hu hlt (by norm_num)
      exact inv_anti₀ (Ch02.lambdaSq_finite_pos Q F hu (by norm_num)) hmono
  have hUpper : sigma⁻¹ * Ch02.LambdaSq Q t (.finite 2) F ≤
      1 + 2 * E ^ 2 + Real.sqrt 2 * E := by
    calc
      sigma⁻¹ * Ch02.LambdaSq Q t (.finite 2) F ≤
          sigma⁻¹ * Ch02.LambdaSq Q (s / 2) (.finite 2) F :=
        mul_le_mul_of_nonneg_left hLambda (inv_nonneg.mpr hsigma.le)
      _ ≤ max (sigma⁻¹ * Ch02.LambdaSq Q (s / 2) (.finite 2) F)
          (sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) F)⁻¹) := le_max_left _ _
      _ ≤ 1 + 2 * E ^ 2 + Real.sqrt 2 * E := by simpa [E] using hbase
  have hLower : sigma * (Ch02.lambdaSq Q t (.finite 2) F)⁻¹ ≤
      1 + 2 * E ^ 2 + Real.sqrt 2 * E := by
    calc
      sigma * (Ch02.lambdaSq Q t (.finite 2) F)⁻¹ ≤
          sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) F)⁻¹ :=
        mul_le_mul_of_nonneg_left hlambdaInv hsigma.le
      _ ≤ max (sigma⁻¹ * Ch02.LambdaSq Q (s / 2) (.finite 2) F)
          (sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) F)⁻¹) := le_max_right _ _
      _ ≤ 1 + 2 * E ^ 2 + Real.sqrt 2 * E := by simpa [E] using hbase
  have hUpperRoot := sqrt_le_one_add_two_mul_of_le hE0 hUpper
  have hLowerRoot := sqrt_le_one_add_two_mul_of_le hE0 hLower
  have hEnvelope : 1 + 2 * E ≤
      dirichletEllipticityEnvelope M L N s omega := by
    unfold dirichletEllipticityEnvelope
    linarith
  simpa [Q, F, sigma] using max_le
    (hUpperRoot.trans hEnvelope) (hLowerRoot.trans hEnvelope)

theorem aux_dedup_d128_ae_ne_top_of_paperENNRealLpNorm_le_ofReal
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p B : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} (hX : Measurable X)
    (hbound : paperENNRealLpNorm mu p X ≤ ENNReal.ofReal B) :
    ∀ᵐ omega ∂mu, X omega ≠ ⊤ := by
  have hnorm : eLpNorm X (ENNReal.ofReal p) mu < ⊤ := by
    rw [← paperENNRealLpNorm_eq_eLpNorm mu hp X]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  have hlintegral := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hnorm
  have hpow : ∀ᵐ omega ∂mu, X omega ^ p < ⊤ := by
    apply ae_lt_top' (hX.pow_const p).aemeasurable
    simpa [ENNReal.toReal_ofReal hp.le, enorm_eq_self] using hlintegral.ne
  filter_upwards [hpow] with omega homega
  exact ((ENNReal.rpow_lt_top_iff_of_pos hp).mp homega).ne

private theorem ae_ne_top_of_paperENNRealLpNorm_le_ofReal
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p B : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} (hX : Measurable X)
    (hbound : paperENNRealLpNorm mu p X ≤ ENNReal.ofReal B) :
    ∀ᵐ omega ∂mu, X omega ≠ ⊤ := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.aux_dedup_d128_ae_ne_top_of_paperENNRealLpNorm_le_ofReal (Omega := Omega) (mu := mu) (p := p) (B := B) (hp := hp) (X := X) (hX := hX) (hbound := hbound)

/-- A finite raw `E2` moment discharges the only finiteness premise in the
pathwise envelope comparison. -/
theorem ae_max_sqrt_weightedEllipticity_le_dirichletEllipticityEnvelope_of_moment
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    {s t p B : ℝ} (hs : 0 < s) (hst : s / 2 ≤ t) (hp : 0 < p)
    (hbound : paperENNRealLpNorm M.P.toMeasure p
      (fun omega ↦ paperHomogenizationError (originCube d (N : ℤ)) (N : ℤ)
        (s / 2) .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) ≤
      ENNReal.ofReal B) :
    ∀ᵐ omega ∂M.P.toMeasure,
      max
          (Real.sqrt ((ahom M L)⁻¹ *
            Ch02.LambdaSq (originCube d (N : ℤ)) t (.finite 2)
              (aCutoffFamily M L omega)))
          (Real.sqrt (ahom M L *
            (Ch02.lambdaSq (originCube d (N : ℤ)) t (.finite 2)
              (aCutoffFamily M L omega))⁻¹)) ≤
        dirichletEllipticityEnvelope M L N s omega := by
  have hfinite := ae_ne_top_of_paperENNRealLpNorm_le_ofReal M.P.toMeasure hp
    (measurable_dirichletFullResponseTwoENNReal M L N s) hbound
  filter_upwards [hfinite] with omega homega
  exact max_sqrt_weightedEllipticity_le_dirichletEllipticityEnvelope
    M L N hs hst omega homega

/-- Every fixed admissible moment of the concrete ellipticity envelope is
bounded uniformly in `L ≤ N`.  The response-error estimate is `O(delta)`;
the standing `delta ≤ 1/2` turns the affine envelope into a fixed constant. -/
theorem exists_dirichletEllipticityEnvelope_moment_bound
    {d : ℕ} [NeZero d] {s xi : ℝ}
    (hs : 0 < s) (hsOne : s ≤ 1) (hxiOne : 1 ≤ xi)
    (hdim : 4 * (d : ℝ) * (s / 2)⁻¹ ≤ xi) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ L N : ℕ, L ≤ N →
          eLpNorm (dirichletEllipticityEnvelope M L N s)
              (ENNReal.ofReal xi) M.P.toMeasure ≤ ENNReal.ofReal C := by
  obtain ⟨delta0, R, hdelta0, hR, hresponse⟩ :=
    exists_dirichletFullResponse_moment_bound hs hsOne hxiOne hdim
  let C := 1 + R
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM L N hLN
  have hE2 := (hresponse M hM L N hLN).2
  have hE2Meas : AEStronglyMeasurable
      (dirichletFullResponseTwo M L N s) M.P.toMeasure :=
    (measurable_dirichletFullResponseTwo M L N s).aestronglyMeasurable
  have hOneMeas : AEStronglyMeasurable
      (fun _ : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ (1 : ℝ))
      M.P.toMeasure := aestronglyMeasurable_const
  have hScaledMeas : AEStronglyMeasurable
      (fun omega ↦ (2 : ℝ) * dirichletFullResponseTwo M L N s omega)
      M.P.toMeasure := by
    simpa [Pi.smul_apply] using hE2Meas.const_smul (2 : ℝ)
  have hxiENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal xi := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hxiOne
  have htriangle := eLpNorm_add_le (p := ENNReal.ofReal xi)
    (μ := M.P.toMeasure) hOneMeas hScaledMeas hxiENN
  have hOneNorm : eLpNorm
      (fun _ : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ (1 : ℝ))
        (ENNReal.ofReal xi) M.P.toMeasure = 1 := by
    rw [eLpNorm_const (1 : ℝ) (ENNReal.ofReal_pos.mpr
      (zero_lt_one.trans_le hxiOne)).ne' (NeZero.ne M.P.toMeasure)]
    norm_num
  have hScaledNorm : eLpNorm (fun omega ↦ (2 : ℝ) *
      dirichletFullResponseTwo M L N s omega)
        (ENNReal.ofReal xi) M.P.toMeasure =
      2 * eLpNorm (dirichletFullResponseTwo M L N s)
        (ENNReal.ofReal xi) M.P.toMeasure := by
    change eLpNorm ((2 : ℝ) • dirichletFullResponseTwo M L N s)
        (ENNReal.ofReal xi) M.P.toMeasure = _
    rw [eLpNorm_const_smul]
    rw [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  calc
    eLpNorm (dirichletEllipticityEnvelope M L N s)
        (ENNReal.ofReal xi) M.P.toMeasure =
        eLpNorm (fun omega ↦ (1 : ℝ) +
          2 * dirichletFullResponseTwo M L N s omega)
            (ENNReal.ofReal xi) M.P.toMeasure := rfl
    _ ≤ eLpNorm (fun _ : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d ↦ (1 : ℝ))
          (ENNReal.ofReal xi) M.P.toMeasure +
        eLpNorm (fun omega ↦ (2 : ℝ) *
          dirichletFullResponseTwo M L N s omega)
            (ENNReal.ofReal xi) M.P.toMeasure := htriangle
    _ = 1 + 2 * eLpNorm (dirichletFullResponseTwo M L N s)
          (ENNReal.ofReal xi) M.P.toMeasure := by
      rw [hOneNorm, hScaledNorm]
    _ ≤ 1 + 2 * ENNReal.ofReal (R * M.delta) := by gcongr
    _ = ENNReal.ofReal (1 + 2 * R * M.delta) := by
      calc
        1 + 2 * ENNReal.ofReal (R * M.delta) =
            ENNReal.ofReal 1 + ENNReal.ofReal 2 * ENNReal.ofReal (R * M.delta) := by
          norm_num
        _ = ENNReal.ofReal 1 + ENNReal.ofReal (2 * (R * M.delta)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ = ENNReal.ofReal (1 + 2 * (R * M.delta)) := by
          rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1)
            (mul_nonneg (by norm_num) (mul_nonneg hR.le M.shellPrefix.delta_pos.le))]
        _ = ENNReal.ofReal (1 + 2 * R * M.delta) := by ring_nf
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by
      dsimp only [C]
      have hhalf := M.shellPrefix.delta_le_half
      have hmul := mul_le_mul_of_nonneg_left hhalf hR.le
      nlinarith)

/-- Common budget for the two response errors and their coefficient-only
ellipticity envelope.  This is the one-call stochastic input expected by the
later Dirichlet random-factor algebra. -/
theorem exists_dirichletResponseAndEllipticity_moment_bound
    {d : ℕ} [NeZero d] {s xi : ℝ}
    (hs : 0 < s) (hsOne : s ≤ 1) (hxiOne : 1 ≤ xi)
    (hdim : 4 * (d : ℝ) * (s / 2)⁻¹ ≤ xi) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
        ∀ L N : ℕ, L ≤ N →
          eLpNorm (dirichletFullResponseOne M L N s)
              (ENNReal.ofReal xi) M.P.toMeasure ≤
              ENNReal.ofReal (C * M.delta) ∧
          eLpNorm (dirichletFullResponseTwo M L N s)
              (ENNReal.ofReal xi) M.P.toMeasure ≤
              ENNReal.ofReal (C * M.delta) ∧
          eLpNorm (dirichletEllipticityEnvelope M L N s)
              (ENNReal.ofReal xi) M.P.toMeasure ≤ ENNReal.ofReal C := by
  obtain ⟨deltaR, CR, hdeltaR, hCR, hresponse⟩ :=
    exists_dirichletFullResponse_moment_bound hs hsOne hxiOne hdim
  obtain ⟨deltaY, CY, hdeltaY, hCY, henvelope⟩ :=
    exists_dirichletEllipticityEnvelope_moment_bound hs hsOne hxiOne hdim
  let delta0 := min deltaR deltaY
  let C := 1 + CR + CY
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    exact lt_min hdeltaR hdeltaY
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨delta0, C, hdelta0, hC, ?_⟩
  intro M hM L N hLN
  have hMR : M.delta ≤ deltaR := hM.trans (min_le_left _ _)
  have hMY : M.delta ≤ deltaY := hM.trans (min_le_right _ _)
  obtain ⟨hE1, hE2⟩ := hresponse M hMR L N hLN
  have hY := henvelope M hMY L N hLN
  have hCRC : CR ≤ C := by dsimp only [C]; linarith
  have hCYC : CY ≤ C := by dsimp only [C]; linarith
  refine ⟨hE1.trans (ENNReal.ofReal_le_ofReal ?_),
    hE2.trans (ENNReal.ofReal_le_ofReal ?_),
    hY.trans (ENNReal.ofReal_le_ofReal hCYC)⟩
  · exact mul_le_mul_of_nonneg_right hCRC M.shellPrefix.delta_pos.le
  · exact mul_le_mul_of_nonneg_right hCRC M.shellPrefix.delta_pos.le

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
