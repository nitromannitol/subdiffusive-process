import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.OneCubeEllipticityComparison
import SubdiffusiveProcess.Providers.Section2.GeneralCoarseGraining
import Homogenization.Book.Ch02.Theorems.HomogenizationError.InfinityOne

/-!
# The `q = 1` ellipticity/error aggregation for the combine event

This file aggregates the dimension-free one-cube square-root estimates against
the paper's geometric probability weights.  It is the scalar `q = 1` analogue
of Algsuperdiff's `ToLambdasUpper.lean`; unlike the library's fallback, it has
no dimension factor at the constant term.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison

open Homogenization
open scoped BigOperators

noncomputable section

theorem sqrt_inv_mul_LambdaSq_le_one_add_sqrt_two_mul_error
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d) {s σ : ℝ}
    (hs : 0 < s) (hσ : 0 < σ) :
    Real.sqrt (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 1) F) ≤
      1 + Real.sqrt 2 *
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
          (scalarMatrix (d := d) σ) := by
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s 1 n
  let B : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F
  let D : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
      (Q.scale - (n : ℤ)) F (scalarMatrix (d := d) σ)
  have hw : ∀ n, 0 ≤ w n := by
    intro n
    simpa [w, Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.geometricWeight_nonneg (s := s) (q := (1 : ℝ)) n
        (by simpa using hs.le))
  have hB : ∀ n, 0 ≤ B n := by
    intro n
    exact Book.Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F
  have hD : ∀ n, 0 ≤ D n := by
    intro n
    exact Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F _
  have hsumW : Summable w := by
    simpa [w, Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.summable_geometricWeight_one (s := s) hs)
  have hsumB : Summable (fun n => w n * Real.sqrt (B n)) := by
    simpa [w, B, Real.sqrt_eq_rpow] using
      (Book.Ch02.summable_B_series_pointwiseCoeffField Q F hs
        (by norm_num : (0 : ℝ) < 1))
  have hsumD : Summable (fun n => w n * Real.sqrt (D n)) := by
    simpa [w, D, Book.Ch02.scaleResponseAtScale_infinity_eq,
      Real.sqrt_eq_rpow] using
      (Book.Ch02.summable_homogenizationErrorOnCube_infinity_one_terms
        Q F (scalarMatrix (d := d) σ) hs)
  have hLambdaHalf :
      Real.sqrt (Book.Ch02.LambdaSq Q s (.finite 1) F) =
        ∑' n, w n * Real.sqrt (B n) := by
    simpa [w, B, Real.sqrt_eq_rpow] using
      (Book.Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q s 1 F
        (by norm_num : (0 : ℝ) < 1) (by simpa using hs.le))
  have hrootEq :
      Real.sqrt (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 1) F) =
        ∑' n, w n * Real.sqrt (σ⁻¹ * B n) := by
    calc
      Real.sqrt (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 1) F) =
          Real.sqrt σ⁻¹ * Real.sqrt (Book.Ch02.LambdaSq Q s (.finite 1) F) := by
        rw [Real.sqrt_mul (inv_nonneg.2 hσ.le)]
      _ = Real.sqrt σ⁻¹ * ∑' n, w n * Real.sqrt (B n) := by rw [hLambdaHalf]
      _ = ∑' n, Real.sqrt σ⁻¹ * (w n * Real.sqrt (B n)) :=
        (hsumB.tsum_mul_left _).symm
      _ = ∑' n, w n * Real.sqrt (σ⁻¹ * B n) := by
        apply tsum_congr
        intro n
        rw [Real.sqrt_mul (inv_nonneg.2 hσ.le)]
        ring
  have hterm : ∀ n, w n * Real.sqrt (σ⁻¹ * B n) ≤
      w n * (1 + Real.sqrt (2 * D n)) := by
    intro n
    apply mul_le_mul_of_nonneg_left _ (hw n)
    exact sqrt_inv_mul_maxDescendantBMatrixNormAtScale_le Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F hσ
  have hsumRight : Summable (fun n => w n * (1 + Real.sqrt (2 * D n))) := by
    have := hsumW.add (hsumD.mul_left (Real.sqrt 2))
    convert this using 1
    funext n
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hrootEq]
  calc
    (∑' n, w n * Real.sqrt (σ⁻¹ * B n)) ≤
        ∑' n, w n * (1 + Real.sqrt (2 * D n)) :=
      (hsumB.mul_left (Real.sqrt σ⁻¹)).congr (fun n => by
        rw [Real.sqrt_mul (inv_nonneg.2 hσ.le)]
        ring) |>.tsum_le_tsum hterm hsumRight
    _ = 1 + Real.sqrt 2 * ∑' n, w n * Real.sqrt (D n) := by
      rw [show (fun n => w n * (1 + Real.sqrt (2 * D n))) =
          fun n => w n + Real.sqrt 2 * (w n * Real.sqrt (D n)) by
        funext n
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring,
        hsumW.tsum_add (hsumD.mul_left (Real.sqrt 2)),
        hsumD.tsum_mul_left,
        show (∑' n, w n) = 1 by
          simpa [w, Book.Ch02.geometricWeight_eq_old] using
            (Homogenization.tsum_geometricWeight_one_eq_one (s := s) hs)]
    _ = 1 + Real.sqrt 2 *
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
          (scalarMatrix (d := d) σ) := by
      rw [Book.Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
      simp only [Book.Ch02.scaleResponseAtScale_infinity_eq]
      simp [w, D, Real.sqrt_eq_rpow]

theorem sqrt_mul_lambdaSq_inv_le_one_add_sqrt_two_mul_error
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d) {s σ : ℝ}
    (hs : 0 < s) (hσ : 0 < σ) :
    Real.sqrt (σ * (Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) ≤
      1 + Real.sqrt 2 *
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
          (scalarMatrix (d := d) σ) := by
  let w : ℕ → ℝ := fun n => Book.Ch02.geometricWeight s 1 n
  let B : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
      (Q.scale - (n : ℤ)) F
  let D : ℕ → ℝ := fun n =>
    Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q
      (Q.scale - (n : ℤ)) F (scalarMatrix (d := d) σ)
  have hw : ∀ n, 0 ≤ w n := by
    intro n
    simpa [w, Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.geometricWeight_nonneg (s := s) (q := (1 : ℝ)) n
        (by simpa using hs.le))
  have hsumW : Summable w := by
    simpa [w, Book.Ch02.geometricWeight_eq_old] using
      (Homogenization.summable_geometricWeight_one (s := s) hs)
  have hsumB : Summable (fun n => w n * Real.sqrt (B n)) := by
    simpa [w, B, Real.sqrt_eq_rpow] using
      (Book.Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q F hs
        (by norm_num : (0 : ℝ) < 1))
  have hsumD : Summable (fun n => w n * Real.sqrt (D n)) := by
    simpa [w, D, Book.Ch02.scaleResponseAtScale_infinity_eq,
      Real.sqrt_eq_rpow] using
      (Book.Ch02.summable_homogenizationErrorOnCube_infinity_one_terms
        Q F (scalarMatrix (d := d) σ) hs)
  have hlambdaHalf :
      Real.sqrt ((Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) =
        ∑' n, w n * Real.sqrt (B n) := by
    have h := Book.Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q s 1 F
      (by norm_num : (0 : ℝ) < 1) (by simpa using hs.le)
    have hlambda0 : 0 ≤ Book.Ch02.lambdaSq Q s (.finite 1) F :=
      Book.Ch02.lambdaSq_nonneg Q F hs (by norm_num)
    calc
      Real.sqrt ((Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) =
          (Book.Ch02.lambdaSq Q s (.finite 1) F) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg hlambda0]
      _ = (Book.Ch02.lambdaSq Q s (.finite 1) F) ^ (-1 / 2 : ℝ) := by
        congr 1
        ring
      _ = ∑' n, w n * Real.sqrt (B n) := by
        simpa [w, B, Real.sqrt_eq_rpow] using h
  have hrootEq :
      Real.sqrt (σ * (Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) =
        ∑' n, w n * Real.sqrt (σ * B n) := by
    calc
      Real.sqrt (σ * (Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) =
          Real.sqrt σ * Real.sqrt ((Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) := by
        rw [Real.sqrt_mul hσ.le]
      _ = Real.sqrt σ * ∑' n, w n * Real.sqrt (B n) := by rw [hlambdaHalf]
      _ = ∑' n, Real.sqrt σ * (w n * Real.sqrt (B n)) :=
        (hsumB.tsum_mul_left _).symm
      _ = ∑' n, w n * Real.sqrt (σ * B n) := by
        apply tsum_congr
        intro n
        rw [Real.sqrt_mul hσ.le]
        ring
  have hterm : ∀ n, w n * Real.sqrt (σ * B n) ≤
      w n * (1 + Real.sqrt (2 * D n)) := by
    intro n
    apply mul_le_mul_of_nonneg_left _ (hw n)
    exact sqrt_mul_maxDescendantSigmaStarInvMatrixNormAtScale_le Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F hσ
  have hsumRight : Summable (fun n => w n * (1 + Real.sqrt (2 * D n))) := by
    have := hsumW.add (hsumD.mul_left (Real.sqrt 2))
    convert this using 1
    funext n
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hrootEq]
  calc
    (∑' n, w n * Real.sqrt (σ * B n)) ≤
        ∑' n, w n * (1 + Real.sqrt (2 * D n)) :=
      (hsumB.mul_left (Real.sqrt σ)).congr (fun n => by
        rw [Real.sqrt_mul hσ.le]
        ring) |>.tsum_le_tsum hterm hsumRight
    _ = 1 + Real.sqrt 2 * ∑' n, w n * Real.sqrt (D n) := by
      rw [show (fun n => w n * (1 + Real.sqrt (2 * D n))) =
          fun n => w n + Real.sqrt 2 * (w n * Real.sqrt (D n)) by
        funext n
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring,
        hsumW.tsum_add (hsumD.mul_left (Real.sqrt 2)),
        hsumD.tsum_mul_left,
        show (∑' n, w n) = 1 by
          simpa [w, Book.Ch02.geometricWeight_eq_old] using
            (Homogenization.tsum_geometricWeight_one_eq_one (s := s) hs)]
    _ = 1 + Real.sqrt 2 *
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
          (scalarMatrix (d := d) σ) := by
      rw [Book.Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
      simp only [Book.Ch02.scaleResponseAtScale_infinity_eq]
      simp [w, D, Real.sqrt_eq_rpow]

/-- The threshold consequence of the sharp all-scale `q = 1` comparison. -/
theorem max_weightedEllipticity_lt_two_of_error_lt_one_fifth
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d) {s σ : ℝ}
    (hs : 0 < s) (hσ : 0 < σ)
    (herror : Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
      (scalarMatrix (d := d) σ) < 1 / 5) :
    max (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 1) F)
        (σ * (Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) < 2 := by
  let E := Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
    (scalarMatrix (d := d) σ)
  have hE0 : 0 ≤ E :=
    Book.Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q F _ hs
  have hsqrt2 : Real.sqrt 2 < 3 / 2 := by
    have hsqrt0 := Real.sqrt_nonneg 2
    have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hupperRoot := sqrt_inv_mul_LambdaSq_le_one_add_sqrt_two_mul_error
    Q F hs hσ
  have hlowerRoot := sqrt_mul_lambdaSq_inv_le_one_add_sqrt_two_mul_error
    Q F hs hσ
  have hupper0 : 0 ≤ σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 1) F :=
    mul_nonneg (inv_nonneg.2 hσ.le)
      (Book.Ch02.LambdaSq_nonneg Q F hs (by norm_num))
  have hlower0 : 0 ≤ σ * (Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹ :=
    mul_nonneg hσ.le
      (inv_nonneg.2 (Book.Ch02.lambdaSq_nonneg Q F hs (by norm_num)))
  have hupperSq := Real.sq_sqrt hupper0
  have hlowerSq := Real.sq_sqrt hlower0
  have hupperSqrt0 := Real.sqrt_nonneg
    (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 1) F)
  have hlowerSqrt0 := Real.sqrt_nonneg
    (σ * (Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹)
  have hE : E < 1 / 5 := herror
  have hsqrtE : Real.sqrt 2 * E < 3 / 10 := by
    calc
      Real.sqrt 2 * E ≤ (3 / 2) * E :=
        mul_le_mul_of_nonneg_right hsqrt2.le hE0
      _ < (3 / 2) * (1 / 5) :=
        mul_lt_mul_of_pos_left hE (by norm_num)
      _ = 3 / 10 := by norm_num
  have hupperRoot' :
      Real.sqrt (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 1) F) < 13 / 10 := by
    dsimp [E] at hsqrtE
    linarith
  have hlowerRoot' :
      Real.sqrt (σ * (Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) < 13 / 10 := by
    dsimp [E] at hsqrtE
    linarith
  apply max_lt
  · nlinarith [sq_nonneg
      (Real.sqrt (σ⁻¹ * Book.Ch02.LambdaSq Q s (.finite 1) F) - 13 / 10)]
  · nlinarith [sq_nonneg
      (Real.sqrt (σ * (Book.Ch02.lambdaSq Q s (.finite 1) F)⁻¹) - 13 / 10)]

/-- The full-block Chapter 2 `q = 1` error is bounded by the paper's scalar-
probe error.  This is the all-scale wrapper around the sharp scalar splitting
proved in the Section 2 provider. -/
theorem ofReal_homogenizationErrorOnCube_le_paperHomogenizationError
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (F : Book.Ch02.TriadicCoeffFamily d)
    (hF : ∀ R, (F.coeffOn R).IsSymmetric) {s σ : ℝ}
    (hs : 0 < s) (hσ : 0 < σ) :
    ENNReal.ofReal
        (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) F
          (scalarMatrix (d := d) σ)) ≤
      paperHomogenizationError Q Q.scale s .infinity (.finite 1) F σ := by
  have hscale : ∀ k : ℤ, k ≤ Q.scale →
      ENNReal.ofReal
          (Book.Ch02.scaleResponseAtScale Q k .infinity F
            (scalarMatrix (d := d) σ)) ≤
        paperScaleResponseAtScale Q k .infinity F σ := by
    intro k hk
    have hmax : ENNReal.ofReal
        (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
          (scalarMatrix (d := d) σ)) ≤
        paperMaxDescendantProbeAtScale Q k F σ := by
      by_cases htop : paperMaxDescendantProbeAtScale Q k F σ = ⊤
      · simp [htop]
      · rw [ENNReal.ofReal_le_iff_le_toReal htop]
        apply Book.Ch02.finsetSupReal_le (descendantsAtScale Q k)
          (descendantsAtScale_nonempty Q hk)
        intro R hR
        have hprobe :=
          SubdiffusiveProcess.Providers.Section2.normalizedBlockResponseMax_le_paperScalarProbeMax
            R F (hF R) hσ
        have hprobe' : ENNReal.ofReal
            (Book.Ch02.normalizedBlockResponseMax R F
              (scalarMatrix (d := d) σ)) ≤
            paperMaxDescendantProbeAtScale Q k F σ :=
          hprobe.trans (le_iSup (fun T : {T : TriadicCube d //
            T ∈ descendantsAtScale Q k} => paperScalarProbeMax T.1 F σ)
              ⟨R, hR⟩)
        exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hprobe'
    simp only [Book.Ch02.scaleResponseAtScale_infinity_eq,
      paperScaleResponseAtScale]
    calc
      ENNReal.ofReal (Real.rpow
          (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
            (scalarMatrix (d := d) σ)) (1 / 2 : ℝ)) =
          (ENNReal.ofReal
            (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q k F
              (scalarMatrix (d := d) σ))) ^ (1 / 2 : ℝ) :=
        (ENNReal.ofReal_rpow_of_nonneg
          (Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q hk F _)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm
      _ ≤ (paperMaxDescendantProbeAtScale Q k F σ) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hmax (by norm_num)
  rw [Book.Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum,
    show paperHomogenizationError Q Q.scale s .infinity (.finite 1) F σ =
        ∑' l : ℕ, ENNReal.ofReal (Book.Ch02.geometricWeight s 1 l) *
          paperScaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity F σ by
      simp [paperHomogenizationError, paperHomogenizationErrorFinite]]
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · apply ENNReal.tsum_le_tsum
    intro l
    rw [ENNReal.ofReal_mul (by
      simpa [Book.Ch02.geometricWeight_eq_old] using
        (Homogenization.geometricWeight_nonneg (s := s) (q := (1 : ℝ)) l
          (by positivity : 0 ≤ s * 1)))]
    exact mul_le_mul' le_rfl (hscale _ (sub_le_self _ (by positivity)))
  · intro l
    exact mul_nonneg
      (by
        simpa [Book.Ch02.geometricWeight_eq_old] using
          (Homogenization.geometricWeight_nonneg (s := s) (q := (1 : ℝ)) l
            (by positivity : 0 ≤ s * 1)))
      (Book.Ch02.scaleResponseAtScale_infinity_nonneg Q
        (sub_le_self _ (by positivity)) F _)
  · exact Book.Ch02.summable_homogenizationErrorOnCube_infinity_one_terms
      Q F (scalarMatrix (d := d) σ) hs

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison
