module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.Analysis

/-- A quantitative stability estimate for quadratic variational minimizers.
The strict midpoint gap is supplied by the actual energy's parallelogram law
and coercivity when this lemma is applied to the killed form. -/
theorem quadratic_minimizer_stability
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (E : V → ℝ) (A : V → W) (lam mu : ℝ) (g h : W)
    (u v mid : V) (κ : ℝ)
    (hu : E u + lam * ‖A u‖ ^ 2 - 2 * ⟪g, A u⟫_ℝ ≤
      E mid + lam * ‖A mid‖ ^ 2 - 2 * ⟪g, A mid⟫_ℝ)
    (hv : E v + mu * ‖A v‖ ^ 2 - 2 * ⟪h, A v⟫_ℝ ≤
      E u + mu * ‖A u‖ ^ 2 - 2 * ⟪h, A u⟫_ℝ)
    (hgap : κ * ‖u - v‖ ^ 2 ≤
      ((E u + lam * ‖A u‖ ^ 2 - 2 * ⟪g, A u⟫_ℝ) +
        (E v + lam * ‖A v‖ ^ 2 - 2 * ⟪g, A v⟫_ℝ)) / 2 -
        (E mid + lam * ‖A mid‖ ^ 2 - 2 * ⟪g, A mid⟫_ℝ)) :
    κ * ‖u - v‖ ^ 2 ≤
      (|lam - mu| * (‖A u‖ ^ 2 + ‖A v‖ ^ 2) +
        2 * ‖g - h‖ * (‖A u‖ + ‖A v‖)) / 2 := by
  have hcoef : (lam - mu) * (‖A v‖ ^ 2 - ‖A u‖ ^ 2) ≤
      |lam - mu| * (‖A u‖ ^ 2 + ‖A v‖ ^ 2) := by
    calc
      _ ≤ |(lam - mu) * (‖A v‖ ^ 2 - ‖A u‖ ^ 2)| := le_abs_self _
      _ = |lam - mu| * |‖A v‖ ^ 2 - ‖A u‖ ^ 2| := abs_mul _ _
      _ ≤ |lam - mu| * (‖A u‖ ^ 2 + ‖A v‖ ^ 2) := by
        gcongr
        exact (abs_sub _ _).trans (by
          rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
          exact le_of_eq (add_comm _ _))
  have hip : |⟪g - h, A v - A u⟫_ℝ| ≤
      ‖g - h‖ * (‖A u‖ + ‖A v‖) := by
    apply (abs_real_inner_le_norm _ _).trans
    calc
      ‖g - h‖ * ‖A v - A u‖ ≤ ‖g - h‖ * (‖A v‖ + ‖A u‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ = _ := by ring
  have hilow := (neg_abs_le ⟪g - h, A v - A u⟫_ℝ).trans' (neg_le_neg hip)
  rw [inner_sub_left, inner_sub_right, inner_sub_right] at hilow
  nlinarith [hgap, hcoef, hilow]

end SubdiffusiveProcess.Analysis
