module

public import SubdiffusiveProcess.Assumptions.CoefficientPackaging
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Carrier

@[expose] public section

/-!
# Small-contrast normalization on a short cube

The scalar coefficient is divided by its cutoff value at a reference point
and by the reference multiplier `b`.  A logarithmic Lipschitz bound for the
cutoff and an `epsilon`-contrast bound for the multiplier then give an
explicit distance from the identity.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

private theorem abs_exp_sub_one_le_exp_abs_sub_one (t : ℝ) :
    |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg
      (sub_nonneg.mpr (Real.one_le_exp ht))]
  · have ht0 : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht0, abs_of_nonpos
      (sub_nonpos.mpr (Real.exp_le_one_iff.mpr ht0))]
    have hpos := Real.add_one_le_exp t
    have hneg := Real.add_one_le_exp (-t)
    nlinarith

/-- Multiplying two quantities close to one costs
`kappa * (1 + epsilon) + epsilon`. -/
theorem abs_mul_sub_one_le_of_abs_sub_one_le
    {A T kappa epsilon : ℝ}
    (hA : |A - 1| ≤ kappa) (hT : |T - 1| ≤ epsilon) :
    |A * T - 1| ≤ kappa * (1 + epsilon) + epsilon := by
  have hepsilon : 0 ≤ epsilon := (abs_nonneg (T - 1)).trans hT
  have hTabs : |T| ≤ 1 + epsilon := by
    calc
      |T| = |(T - 1) + 1| := by ring_nf
      _ ≤ |T - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ epsilon + 1 := by
        simpa only [abs_one, add_comm] using add_le_add_right hT 1
      _ = 1 + epsilon := by ring
  calc
    |A * T - 1| = |(A - 1) * T + (T - 1)| := by ring_nf
    _ ≤ |A - 1| * |T| + |T - 1| := by
      simpa only [abs_mul] using abs_add_le ((A - 1) * T) (T - 1)
    _ ≤ kappa * (1 + epsilon) + epsilon := by
      exact add_le_add (mul_le_mul hA hTabs (abs_nonneg T)
        ((abs_nonneg (A - 1)).trans hA)) hT

/-- Logarithmic oscillation controls the relative scalar coefficient with the
exact exponential loss. -/
theorem abs_div_sub_one_le_exp_of_log_oscillation
    {a a0 s : ℝ} (ha : 0 < a) (ha0 : 0 < a0)
    (hlog : |Real.log a - Real.log a0| ≤ s) :
    |a / a0 - 1| ≤ Real.exp s - 1 := by
  have hratio : a / a0 = Real.exp (Real.log a - Real.log a0) := by
    rw [Real.exp_sub, Real.exp_log ha, Real.exp_log ha0]
  rw [hratio]
  exact (abs_exp_sub_one_le_exp_abs_sub_one _).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hlog) 1)

/-- Pointwise scalar normalization on a short cube.  If
`r0 * G ≤ c * epsilonStar`, the explicit identity-distance is
`exp(c*epsilonStar) * (1+epsilonStar) - 1`. -/
theorem abs_normalized_cutoff_multiplier_sub_one_le
    {W : Set (Vec d)} {xP : Vec d} {a theta : Vec d → ℝ}
    {b r0 G c epsilonStar : ℝ}
    (ha : ∀ x ∈ W, 0 < a x) (haP : 0 < a xP) (hb : 0 < b)
    (hrG : 0 ≤ r0 * G) (hscale : r0 * G ≤ c * epsilonStar)
    (hlog : ∀ x ∈ W,
      |Real.log (a x) - Real.log (a xP)| ≤ r0 * G)
    (htheta : ∀ x ∈ W, |b⁻¹ * theta x - 1| ≤ epsilonStar) :
    ∀ x ∈ W,
      |a x * theta x / (a xP * b) - 1| ≤
        Real.exp (c * epsilonStar) * (1 + epsilonStar) - 1 := by
  intro x hx
  have hce : 0 ≤ c * epsilonStar := hrG.trans hscale
  have haRel : |a x / a xP - 1| ≤ Real.exp (c * epsilonStar) - 1 :=
    (abs_div_sub_one_le_exp_of_log_oscillation (ha x hx) haP
      (hlog x hx)).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr hscale) 1)
  have hprod := abs_mul_sub_one_le_of_abs_sub_one_le haRel (htheta x hx)
  have hrewrite : a x * theta x / (a xP * b) =
      (a x / a xP) * (b⁻¹ * theta x) := by
    field_simp [haP.ne', hb.ne']
  rw [hrewrite]
  convert hprod using 1
  ring

/-- Matrix-valued wrapper in the exact carrier consumed by
`smallContrastSchauder`. -/
theorem coefficientIdentityDistanceLE_normalized_cutoff_multiplier
    [NeZero d] {W : Set (Vec d)} (hW : MeasurableSet W)
    {xP : Vec d} {a theta : Vec d → ℝ}
    {b r0 G c epsilonStar : ℝ}
    (ha : ∀ x ∈ W, 0 < a x) (haP : 0 < a xP) (hb : 0 < b)
    (hrG : 0 ≤ r0 * G) (hscale : r0 * G ≤ c * epsilonStar)
    (hlog : ∀ x ∈ W,
      |Real.log (a x) - Real.log (a xP)| ≤ r0 * G)
    (htheta : ∀ x ∈ W, |b⁻¹ * theta x - 1| ≤ epsilonStar) :
    CoefficientIdentityDistanceLE W
      (scalarCoeffField (fun x ↦ a x * theta x / (a xP * b)))
      (Real.exp (c * epsilonStar) * (1 + epsilonStar) - 1) := by
  filter_upwards [ae_restrict_mem hW] with x hx
  have hscalar := abs_normalized_cutoff_multiplier_sub_one_le
    ha haP hb hrG hscale hlog htheta x hx
  change Homogenization.Book.Ch02.matrixOperatorNorm
      (Homogenization.scalarMatrix (a x * theta x / (a xP * b)) - 1) ≤ _
  have hmatrix : Homogenization.scalarMatrix
      (a x * theta x / (a xP * b)) - (1 : Mat d) =
      (a x * theta x / (a xP * b) - 1) • (1 : Mat d) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Homogenization.scalarMatrix]
    · simp [Homogenization.scalarMatrix, hij]
  rw [hmatrix, Homogenization.Book.Ch02.matrixOperatorNorm_smul_one_eq_abs]
  exact hscalar

/-- Specialization to the actual finite cutoff.  The only geometric input
left is the logarithmic oscillation estimate furnished by the maximal
derivative bound on the chosen short cube. -/
theorem coefficientIdentityDistanceLE_aCutoff_mul_normalized
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {W : Set (Vec d)} (hW : MeasurableSet W) {xP : Vec d}
    {theta : Vec d → ℝ} {b r0 G c epsilonStar : ℝ}
    (hb : 0 < b) (hrG : 0 ≤ r0 * G)
    (hscale : r0 * G ≤ c * epsilonStar)
    (hlog : ∀ x ∈ W,
      |Real.log (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x) -
        Real.log (_root_.SubdiffusiveProcess.Model.aCutoff M L omega xP)| ≤ r0 * G)
    (htheta : ∀ x ∈ W, |b⁻¹ * theta x - 1| ≤ epsilonStar) :
    CoefficientIdentityDistanceLE W
      (scalarCoeffField (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * theta x /
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega xP * b)))
      (Real.exp (c * epsilonStar) * (1 + epsilonStar) - 1) := by
  exact coefficientIdentityDistanceLE_normalized_cutoff_multiplier hW
    (fun x _hx ↦ _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x)
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega xP) hb hrG hscale hlog htheta

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
