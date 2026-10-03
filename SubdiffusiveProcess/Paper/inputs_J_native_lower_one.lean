module

public import SubdiffusiveProcess.Paper.inputs_J_one_cube_upper
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.LocalAEEq
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.EllipticityErrorAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.LowerEllipticityComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CarrierComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PaperErrorBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyFactor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsRecentring
public import SubdiffusiveProcess.Lane4.Bridge
public import Homogenization.Deterministic.CoarsePoincare.Setup.UniformBounds
@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_J_native_lower_one {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (hSymm : ∀ R, Homogenization.Book.Ch02.CoeffOn.IsSymmetric (F.coeffOn R))
    {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) :
    (1 / 2 : ℝ) *
        (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s
          .infinity (.finite 1) F (Homogenization.scalarMatrix σ)) ^ 2 ≤
      max (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F)
        (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) := by
  let w : ℕ → ℝ := fun n => Homogenization.Book.Ch02.geometricWeight s 1 n
  let B : ℕ → ℝ := fun n =>
    Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
      (Q.scale - (n : ℤ)) F
  let S : ℕ → ℝ := fun n =>
    Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
      (Q.scale - (n : ℤ)) F
  let D : ℕ → ℝ := fun n =>
    Homogenization.Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
      (Q.scale - (n : ℤ)) F (Homogenization.scalarMatrix σ)
  have hw : ∀ n, 0 ≤ w n := by
    intro n
    simpa [w, Homogenization.Book.Ch02.geometricWeight_eq_old] using
      Homogenization.geometricWeight_nonneg (s := s) (q := (1 : ℝ)) n
        (by simpa using mul_nonneg hs.le (by norm_num : (0 : ℝ) ≤ 1))
  have hsumW : Summable w := by
    simpa [w, Homogenization.Book.Ch02.geometricWeight_eq_old] using
      Homogenization.summable_geometricWeight_one hs
  have htsumW : (∑' n, w n) = 1 := by
    simpa [w, Homogenization.Book.Ch02.geometricWeight_eq_old] using
      Homogenization.tsum_geometricWeight_one_eq_one hs
  have hscale : ∀ n : ℕ, Q.scale - (n : ℤ) ≤ Q.scale := by
    intro n
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hBn : ∀ n, 0 ≤ B n := by
    intro n
    exact Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (hscale n) F
  have hSn : ∀ n, 0 ≤ S n := by
    intro n
    exact Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (hscale n) F
  have hDn : ∀ n, 0 ≤ D n := by
    intro n
    exact Homogenization.Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (hscale n) F _
  have hsumB : Summable (fun n => w n * Real.sqrt (B n)) := by
    simpa [w, B, Real.sqrt_eq_rpow] using
      Homogenization.Book.Ch02.summable_B_series_pointwiseCoeffField Q F hs
        (by norm_num : (0 : ℝ) < 1)
  have hsumS : Summable (fun n => w n * Real.sqrt (S n)) := by
    simpa [w, S, Real.sqrt_eq_rpow] using
      Homogenization.Book.Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q F hs
        (by norm_num : (0 : ℝ) < 1)
  have hsumD : Summable (fun n => w n * Real.sqrt (D n)) := by
    simpa [w, D, Homogenization.Book.Ch02.scaleResponseAtScale_infinity_eq,
      Real.sqrt_eq_rpow] using
      Homogenization.Book.Ch02.summable_homogenizationErrorOnCube_infinity_one_terms
        Q F (Homogenization.scalarMatrix σ) hs
  have hsumA : Summable (fun n => w n * Real.sqrt (σ⁻¹ * B n)) := by
    have ht := hsumB.mul_left (Real.sqrt σ⁻¹)
    convert ht using 1
    ext n
    rw [Real.sqrt_mul (inv_nonneg.mpr hσ.le)]
    ring
  have hsumC : Summable (fun n => w n * Real.sqrt (σ * S n)) := by
    have ht := hsumS.mul_left (Real.sqrt σ)
    convert ht using 1
    ext n
    rw [Real.sqrt_mul hσ.le]
    ring
  have hsumR : Summable (fun n =>
      (w n * Real.sqrt (σ⁻¹ * B n) + w n * Real.sqrt (σ * S n)) /
        Real.sqrt 2) := by
    have ht := (hsumA.add hsumC).mul_right (Real.sqrt 2)⁻¹
    convert ht using 1
    funext n
    exact div_eq_mul_inv _ _
  have hLambda :
      Real.sqrt (Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) =
        ∑' n, w n * Real.sqrt (B n) := by
    simpa [w, B, Real.sqrt_eq_rpow] using
      (Homogenization.Book.Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 1 F
        (by norm_num : (0 : ℝ) < 1) (by simpa using hs.le))
  have hlambda :
      Real.sqrt ((Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) =
        ∑' n, w n * Real.sqrt (S n) := by
    have h := Homogenization.Book.Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum
      Q s 1 F (by norm_num : (0 : ℝ) < 1) (by simpa using hs.le)
    have hlam0 : 0 ≤ Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F :=
      Homogenization.Book.Ch02.lambdaSq_nonneg Q F hs (by norm_num)
    calc
      Real.sqrt ((Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) =
          (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg hlam0]
      _ = (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F) ^ (-1 / 2 : ℝ) := by
        congr 1
        ring
      _ = ∑' n, w n * Real.sqrt (S n) := by
        simpa [w, S, Real.sqrt_eq_rpow] using h
  have hE :
      Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 1) F (Homogenization.scalarMatrix σ) =
        ∑' n, w n * Real.sqrt (D n) := by
    rw [Homogenization.Book.Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
    simp only [Homogenization.Book.Ch02.scaleResponseAtScale_infinity_eq]
    simp [w, D, Real.sqrt_eq_rpow]
  have hterm : ∀ n,
      w n * Real.sqrt (D n) ≤
        (w n * Real.sqrt (σ⁻¹ * B n) + w n * Real.sqrt (σ * S n)) /
          Real.sqrt 2 := by
    intro n
    have hA : 0 ≤ σ⁻¹ * B n := mul_nonneg (inv_nonneg.mpr hσ.le) (hBn n)
    have hC : 0 ≤ σ * S n := mul_nonneg hσ.le (hSn n)
    have hDle : D n ≤ (σ⁻¹ * B n + σ * S n) / 2 := by
      apply Homogenization.Book.Ch02.finsetSupReal_le
        (Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ)))
        (Homogenization.descendantsAtScale_nonempty Q (hscale n))
      intro R hR
      have hone := inputs_J_one_cube_upper d R F (hSymm R) hσ
      have hb := SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.le_finsetSupReal
        (Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ)))
        (fun S => Homogenization.Book.Ch02.coarseBMatrixNorm S F) hR
      have hs := SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.le_finsetSupReal
        (Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ)))
        (fun S => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm S F) hR
      have hbm := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hσ.le)
      have hsm := mul_le_mul_of_nonneg_left hs hσ.le
      change Homogenization.Book.Ch02.normalizedBlockResponseMax R F
        (Homogenization.scalarMatrix σ) ≤ _
      change σ⁻¹ * Homogenization.Book.Ch02.coarseBMatrixNorm R F ≤ σ⁻¹ * B n at hbm
      change σ * Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R F ≤ σ * S n at hsm
      linarith
    have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrtA : (Real.sqrt (σ⁻¹ * B n)) ^ 2 = σ⁻¹ * B n := Real.sq_sqrt hA
    have hsqrtC : (Real.sqrt (σ * S n)) ^ 2 = σ * S n := Real.sq_sqrt hC
    have hroot : Real.sqrt (D n) ≤
        (Real.sqrt (σ⁻¹ * B n) + Real.sqrt (σ * S n)) / Real.sqrt 2 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hsq :
            ((Real.sqrt (σ⁻¹ * B n) + Real.sqrt (σ * S n)) /
              Real.sqrt 2) ^ 2 =
              (σ⁻¹ * B n + σ * S n +
                2 * Real.sqrt (σ⁻¹ * B n) * Real.sqrt (σ * S n)) / 2 := by
          rw [div_pow, add_sq, hsqrtA, hsqrtC, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring
        rw [hsq]
        nlinarith [mul_nonneg (Real.sqrt_nonneg (σ⁻¹ * B n))
          (Real.sqrt_nonneg (σ * S n))]
    calc
      w n * Real.sqrt (D n) ≤
          w n * ((Real.sqrt (σ⁻¹ * B n) + Real.sqrt (σ * S n)) /
            Real.sqrt 2) := mul_le_mul_of_nonneg_left hroot (hw n)
      _ = (w n * Real.sqrt (σ⁻¹ * B n) +
          w n * Real.sqrt (σ * S n)) / Real.sqrt 2 := by ring
  have hEbound :
      Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 1) F (Homogenization.scalarMatrix σ) ≤
        (Real.sqrt (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) +
          Real.sqrt (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹)) /
          Real.sqrt 2 := by
    rw [hE]
    calc
      (∑' n, w n * Real.sqrt (D n)) ≤
          ∑' n, (w n * Real.sqrt (σ⁻¹ * B n) +
            w n * Real.sqrt (σ * S n)) / Real.sqrt 2 :=
        Summable.tsum_le_tsum hterm hsumD hsumR
      _ = ((∑' n, w n * Real.sqrt (σ⁻¹ * B n)) +
          (∑' n, w n * Real.sqrt (σ * S n))) / Real.sqrt 2 := by
        simp_rw [div_eq_mul_inv]
        rw [(hsumA.add hsumC).tsum_mul_right, hsumA.tsum_add hsumC]
      _ = _ := by
        have hAroot :
            Real.sqrt (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) =
              ∑' n, w n * Real.sqrt (σ⁻¹ * B n) := by
          calc
            _ = Real.sqrt σ⁻¹ * Real.sqrt
                (Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) := by
              rw [Real.sqrt_mul (inv_nonneg.mpr hσ.le)]
            _ = Real.sqrt σ⁻¹ * (∑' n, w n * Real.sqrt (B n)) := by rw [hLambda]
            _ = _ := (hsumB.tsum_mul_left _).symm.trans (by
              apply tsum_congr
              intro n
              rw [Real.sqrt_mul (inv_nonneg.mpr hσ.le)]
              ring)
        have hCroot :
            Real.sqrt (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) =
              ∑' n, w n * Real.sqrt (σ * S n) := by
          calc
            _ = Real.sqrt σ * Real.sqrt
                ((Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) := by
              rw [Real.sqrt_mul hσ.le]
            _ = Real.sqrt σ * (∑' n, w n * Real.sqrt (S n)) := by rw [hlambda]
            _ = _ := (hsumS.tsum_mul_left _).symm.trans (by
              apply tsum_congr
              intro n
              rw [Real.sqrt_mul hσ.le]
              ring)
        rw [← hAroot, ← hCroot]
  have hE0 : 0 ≤ Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s
      .infinity (.finite 1) F (Homogenization.scalarMatrix σ) :=
    Homogenization.Book.Ch02.HomogenizationErrorOnCube_infinity_one_nonneg
      Q F (Homogenization.scalarMatrix σ) hs
  have hX0 : 0 ≤ Real.sqrt (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s
      (.finite 1) F) := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Real.sqrt (σ *
      (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) := Real.sqrt_nonneg _
  have hXsq : (Real.sqrt (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s
      (.finite 1) F)) ^ 2 = σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s
      (.finite 1) F := Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr hσ.le)
        (Homogenization.Book.Ch02.LambdaSq_nonneg Q F hs (by norm_num)))
  have hYsq : (Real.sqrt (σ *
      (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹)) ^ 2 =
      σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹ := by
    apply Real.sq_sqrt
    exact mul_nonneg hσ.le (inv_nonneg.mpr
      (Homogenization.Book.Ch02.lambdaSq_nonneg Q F hs (by norm_num)))
  have hmax0 : 0 ≤ max
      (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F)
      (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) :=
    le_trans (mul_nonneg (inv_nonneg.mpr hσ.le)
      (Homogenization.Book.Ch02.LambdaSq_nonneg Q F hs (by norm_num)))
      (le_max_left _ _)
  have hsumxy :
      (Real.sqrt (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) +
        Real.sqrt (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹)) ^ 2 ≤
        4 * max (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F)
          (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) := by
    have hxle := le_max_left
      (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F)
      (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹)
    have hyle := le_max_right
      (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F)
      (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹)
    nlinarith [sq_nonneg
      (Real.sqrt (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) -
        Real.sqrt (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹))]
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtE :
      (Real.sqrt (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s
        .infinity (.finite 1) F (Homogenization.scalarMatrix σ))) ^ 2 =
        Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 1) F (Homogenization.scalarMatrix σ) := Real.sq_sqrt hE0
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hscaled :
      Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
          (.finite 1) F (Homogenization.scalarMatrix σ) * Real.sqrt 2 ≤
        Real.sqrt (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) +
          Real.sqrt (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) :=
    (le_div_iff₀ hsqrt2pos).mp hEbound
  have hsqle :
      (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
        (.finite 1) F (Homogenization.scalarMatrix σ) * Real.sqrt 2) ^ 2 ≤
        (Real.sqrt (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) +
          Real.sqrt (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹)) ^ 2 := by
    have hsumNonneg := add_nonneg hX0 hY0
    have hscaledNonneg := mul_nonneg hE0 (Real.sqrt_nonneg 2)
    nlinarith [mul_nonneg (sub_nonneg.mpr hscaled) (add_nonneg hsumNonneg hscaledNonneg)]
  have hmaxge : (1 / 2 : ℝ) *
      (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
        (.finite 1) F (Homogenization.scalarMatrix σ)) ^ 2 ≤
      max (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F)
        (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) := by
    calc
      (1 / 2 : ℝ) *
          (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
            (.finite 1) F (Homogenization.scalarMatrix σ)) ^ 2 =
          (Homogenization.Book.Ch02.HomogenizationErrorOnCube Q s .infinity
            (.finite 1) F (Homogenization.scalarMatrix σ) * Real.sqrt 2) ^ 2 / 4 := by
        rw [mul_pow, hsqrt2sq]
        ring
      _ ≤
          (Real.sqrt (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F) +
            Real.sqrt (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹)) ^ 2 / 4 :=
        div_le_div_of_nonneg_right hsqle (by norm_num)
      _ ≤ max (σ⁻¹ * Homogenization.Book.Ch02.LambdaSq Q s (.finite 1) F)
            (σ * (Homogenization.Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) := by
        nlinarith [hsumxy]
  exact hmaxge

end Paper
