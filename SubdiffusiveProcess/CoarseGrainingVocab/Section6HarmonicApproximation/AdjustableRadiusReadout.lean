import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EnergyBudgetReadout
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.AdjustableAbsorption
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow.BudgetedRadiusIteration




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section

/-- Fixed numerical specialization of P-118's adjustable absorption.  The
choices `tau = 3/4`, `theta = 1/4`, and `alpha = 2` leave a strict contraction
and turn the radius-price coefficients into absolute constants. -/
theorem radiusProfile_oneThird_le_of_quarter_step
    (f : ℝ → ℝ) {CA CB budgets Mbd : ℝ}
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hbudgets : 0 ≤ budgets)
    (hbdd : ∀ r, (1 / 3 : ℝ) ≤ r → r ≤ 2 / 3 → f r ≤ Mbd)
    (hstep : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 2 / 3 →
      f rho ≤ (1 / 4 : ℝ) * f R +
        (CA * budgets) / (R - rho) ^ (2 : ℕ) + CB * budgets) :
    f (1 / 3 : ℝ) ≤ ((1296 / 5 : ℝ) * CA + (4 / 3 : ℝ) * CB) * budgets := by
  have hiter := Section6HarmonicLocalRow.iterate_absorb_le
    (r0 := (1 / 3 : ℝ)) (r1 := (2 / 3 : ℝ))
    (tau := (3 / 4 : ℝ)) (theta := (1 / 4 : ℝ))
    (A := CA * budgets) (B := CB * budgets) (Mbd := Mbd)
    (alpha := 2) f (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (mul_nonneg hCA hbudgets) (mul_nonneg hCB hbudgets) hbdd hstep
  norm_num at hiter ⊢
  nlinarith

/-- Direct consumer of P-118's budgeted radius-row interface.  At the fixed
choices `theta = 1/4`, `tau = 3/4`, and `beta = 2`, its abstract iteration
constant is the explicit manuscript-independent number `324/5` on the
radius-priced budget and `4/3` on the unpriced budget. -/
theorem radiusProfile_oneThird_le_of_budgetedQuarterStep
    (f : ℝ → ℝ) {CA CB budgets : ℝ}
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hbudgets : 0 ≤ budgets)
    (hbdd : CoarseCaccioppoliRadiusBoundedAbove f)
    (hrow : Section6HarmonicLocalRow.BudgetedRadiusRecurrence f
      (1 / 4 : ℝ) (CA * budgets) (CB * budgets) 2) :
    f (1 / 3 : ℝ) ≤ ((324 / 5 : ℝ) * CA + (4 / 3 : ℝ) * CB) * budgets := by
  have hiter := Section6HarmonicLocalRow.budgetedRadius_iteration
    (F := f) (theta := (1 / 4 : ℝ)) (A := CA * budgets)
    (B := CB * budgets) (beta := 2) (tau := (3 / 4 : ℝ))
    (by norm_num) (mul_nonneg hCA hbudgets) (mul_nonneg hCB hbudgets)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hbdd hrow
  norm_num [Real.rpow_two] at hiter ⊢
  nlinarith

/-- Radius-pair local energy estimates feed the exact four-budget square-root
readout.  The conclusion has no radius profile and no absorption premise. -/
theorem invSqrt_mul_vectorNormalizedL2On_le_of_radiusPairFourBudgets
    {d : ℕ} (W : Set (Vec d)) (a : Vec d → ℝ) (v : Vec d → Vec d)
    (f : ℝ → ℝ) {CA CB Mbd K sigma s O G F H nr : ℝ} {n : ℤ}
    (ha : ∀ x, 0 ≤ a x)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hK : K = (1296 / 5 : ℝ) * CA + (4 / 3 : ℝ) * CB)
    (hsigma : 0 < sigma) (hs : 0 < s)
    (hO : 0 ≤ O) (hG : 0 ≤ G) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (hroot : volumeAverage W (fun x ↦ a x * vecNormSq (v x)) ≤ f (1 / 3 : ℝ))
    (hbdd : ∀ r, (1 / 3 : ℝ) ≤ r → r ≤ 2 / 3 → f r ≤ Mbd)
    (hstep : ∀ rho R, (1 / 3 : ℝ) ≤ rho → rho < R → R ≤ 2 / 3 →
      f rho ≤ (1 / 4 : ℝ) * f R +
        CA * (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 + sigma * G ^ 2 +
          s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2 +
          sigma * s ^ (-4 : ℝ) * (3 : ℝ) ^ (2 * s * nr) * H ^ 2) /
            (R - rho) ^ (2 : ℕ) +
        CB * (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 + sigma * G ^ 2 +
          s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2 +
          sigma * s ^ (-4 : ℝ) * (3 : ℝ) ^ (2 * s * nr) * H ^ 2)) :
    sigma ^ (-1 / 2 : ℝ) * vectorNormalizedL2On W
        (fun x ↦ Real.sqrt (a x) • v x) ≤
      Real.sqrt K *
        ((3 : ℝ) ^ (-n) * O + G +
          sigma⁻¹ * (s ^ (-6 : ℝ) * (3 : ℝ) ^ (s * nr) * F) +
          s ^ (-2 : ℝ) * (3 : ℝ) ^ (s * nr) * H) := by
  let budgets := sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 + sigma * G ^ 2 +
    s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2 +
    sigma * s ^ (-4 : ℝ) * (3 : ℝ) ^ (2 * s * nr) * H ^ 2
  have hbudgets : 0 ≤ budgets := by
    dsimp only [budgets]
    have h1 : 0 ≤ sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 := by positivity
    have h2 : 0 ≤ sigma * G ^ 2 := mul_nonneg hsigma.le (sq_nonneg G)
    have h3 : 0 ≤ s ^ (-12 : ℝ) * sigma⁻¹ *
        (3 : ℝ) ^ (2 * s * nr) * F ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hs.le _) (inv_nonneg.mpr hsigma.le))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg F)
    have h4 : 0 ≤ sigma * s ^ (-4 : ℝ) *
        (3 : ℝ) ^ (2 * s * nr) * H ^ 2 := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hsigma.le (Real.rpow_nonneg hs.le _))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg H)
    positivity
  have hprofile : f (1 / 3 : ℝ) ≤ K * budgets := by
    have hraw := radiusProfile_oneThird_le_of_quarter_step f hCA hCB hbudgets hbdd
      (by
        intro rho R hrho hlt hR
        simpa only [budgets] using hstep rho R hrho hlt hR)
    rw [hK]
    exact hraw
  have henergy : volumeAverage W (fun x ↦ a x * vecNormSq (v x)) ≤
      K * budgets := hroot.trans hprofile
  have hK0 : 0 ≤ K := by
    rw [hK]
    positivity
  apply invSqrt_mul_vectorNormalizedL2On_le_of_manuscriptFourBudgets
    W a v ha hK0 hsigma hs hO hG hF hH
  simpa only [budgets] using henergy

/-- Fully parameterized consumer of P-118's corrected local-row carrier.
The radius-priced and unpriced copies of the same four-square budget are
collected into `K`; no fixed Young parameter is baked into this endpoint. -/
theorem invSqrt_mul_vectorNormalizedL2On_le_of_budgetedRadiusFourBudgets
    {d : ℕ} (W : Set (Vec d)) (a : Vec d → ℝ) (v : Vec d → Vec d)
    (f : ℝ → ℝ)
    {theta tau beta CA CB Ccmp K sigma s O G F H nr : ℝ} {n : ℤ}
    (ha : ∀ x, 0 ≤ a x)
    (hbeta : 0 ≤ beta) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hCcmp : 0 ≤ Ccmp) (hK : 0 ≤ K)
    (htau0 : 0 < tau) (htau1 : tau < 1)
    (htheta0 : 0 ≤ theta) (hcontract : theta < Real.rpow tau beta)
    (hKdef : K = Ccmp *
      ((1 - theta / Real.rpow tau beta)⁻¹ *
          (CA * Real.rpow ((1 - tau) * (2 / 3 : ℝ)) (-beta)) +
        (1 - theta)⁻¹ * CB))
    (hsigma : 0 < sigma) (hs : 0 < s)
    (hO : 0 ≤ O) (hG : 0 ≤ G) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (hroot : volumeAverage W (fun x ↦ a x * vecNormSq (v x)) ≤
      Ccmp * f (1 / 3 : ℝ))
    (hbdd : CoarseCaccioppoliRadiusBoundedAbove f)
    (hrow : Section6HarmonicLocalRow.BudgetedRadiusRecurrence f theta
      (CA * (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 + sigma * G ^ 2 +
        s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2 +
        sigma * s ^ (-4 : ℝ) * (3 : ℝ) ^ (2 * s * nr) * H ^ 2))
      (CB * (sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 + sigma * G ^ 2 +
        s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2 +
        sigma * s ^ (-4 : ℝ) * (3 : ℝ) ^ (2 * s * nr) * H ^ 2)) beta) :
    sigma ^ (-1 / 2 : ℝ) * vectorNormalizedL2On W
        (fun x ↦ Real.sqrt (a x) • v x) ≤
      Real.sqrt K *
        ((3 : ℝ) ^ (-n) * O + G +
          sigma⁻¹ * (s ^ (-6 : ℝ) * (3 : ℝ) ^ (s * nr) * F) +
          s ^ (-2 : ℝ) * (3 : ℝ) ^ (s * nr) * H) := by
  let budgets := sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 + sigma * G ^ 2 +
    s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * nr) * F ^ 2 +
    sigma * s ^ (-4 : ℝ) * (3 : ℝ) ^ (2 * s * nr) * H ^ 2
  have hbudgets : 0 ≤ budgets := by
    dsimp only [budgets]
    have h1 : 0 ≤ sigma * (3 : ℝ) ^ (-(2 * n)) * O ^ 2 := by positivity
    have h2 : 0 ≤ sigma * G ^ 2 := mul_nonneg hsigma.le (sq_nonneg G)
    have h3 : 0 ≤ s ^ (-12 : ℝ) * sigma⁻¹ *
        (3 : ℝ) ^ (2 * s * nr) * F ^ 2 := by positivity
    have h4 : 0 ≤ sigma * s ^ (-4 : ℝ) *
        (3 : ℝ) ^ (2 * s * nr) * H ^ 2 := by positivity
    positivity
  have hprofile := Section6HarmonicLocalRow.budgetedRadius_iteration
    (F := f) (theta := theta) (A := CA * budgets) (B := CB * budgets)
    (beta := beta) (tau := tau) hbeta (mul_nonneg hCA hbudgets)
    (mul_nonneg hCB hbudgets) htau0 htau1 htheta0 hcontract hbdd
    (by simpa only [budgets] using hrow)
  have henergy : volumeAverage W (fun x ↦ a x * vecNormSq (v x)) ≤
      K * budgets := by
    calc
      volumeAverage W (fun x ↦ a x * vecNormSq (v x)) ≤
          Ccmp * f (1 / 3 : ℝ) := hroot
      _ ≤ Ccmp *
          ((1 - theta / Real.rpow tau beta)⁻¹ *
              (CA * budgets * Real.rpow ((1 - tau) * (2 / 3 : ℝ)) (-beta)) +
            (1 - theta)⁻¹ * (CB * budgets)) :=
        mul_le_mul_of_nonneg_left hprofile hCcmp
      _ = K * budgets := by rw [hKdef]; ring
  apply invSqrt_mul_vectorNormalizedL2On_le_of_manuscriptFourBudgets
    W a v ha hK hsigma hs hO hG hF hH
  simpa only [budgets] using henergy

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
