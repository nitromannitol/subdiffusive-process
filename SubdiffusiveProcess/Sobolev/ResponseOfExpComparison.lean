module

public import SubdiffusiveProcess.Lane3.Interfaces

@[expose] public section




open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess
namespace Lane3

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Pure real-analysis core of `response_perturbation`: given a two-sided `exp(x)`-comparison
sandwich `E ≤ exp x * Y` and `Y ≤ exp x * E` (`x ≥ 0`, `Y ≥ 0`), `|E - Y| ≤ 2 x exp(4x) Y`. -/
theorem aux_response_real_perturb (x E Y : ℝ) (hx : 0 ≤ x) (hY : 0 ≤ Y)
    (hup : E ≤ Real.exp x * Y) (hlo : Y ≤ Real.exp x * E) :
    |E - Y| ≤ 2 * x * Real.exp (4 * x) * Y := by
  have h1 : Real.exp x - 1 ≤ x * Real.exp x := by
    have := Real.add_one_le_exp (-x)
    have hex : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos x]
  have h2 : x * Real.exp x ≤ 2 * x * Real.exp (4 * x) := by
    have : Real.exp x ≤ Real.exp (4 * x) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [Real.exp_pos x]
  have hEnn : 0 ≤ E := by
    by_contra hE
    push_neg at hE
    have : Real.exp x * E < 0 := mul_neg_of_pos_of_neg (Real.exp_pos x) hE
    linarith
  have hlo' : Real.exp (-x) * Y ≤ E := by
    have hex : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-x) * Y ≤ Real.exp (-x) * (Real.exp x * E) :=
          mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le
      _ = E := by rw [← mul_assoc, hex, one_mul]
  have h3 : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h3 hY, mul_le_mul_of_nonneg_right h2 hY,
      mul_le_mul_of_nonneg_right h1 hY, mul_nonneg hx (Real.exp_pos x).le]
  · nlinarith [mul_le_mul_of_nonneg_right h1 hY, mul_le_mul_of_nonneg_right h2 hY]

/-- Generic `Response` smart constructor: any nonnegative `eval` with an `exp_comparison`-shaped
bound gives a full `Response`, via the trivial mass choice `mass g _ := eval g`. -/
def Response.ofExpComparison (eval : Potential Q → ℝ) (eval_nonneg : ∀ g, 0 ≤ eval g)
    (exp_cmp : ∀ g h, eval g ≤ Real.exp ‖g - h‖ * eval h) : Response Q where
  eval := eval
  mass g _ := eval g
  eval_nonneg := eval_nonneg
  mass_nonneg g _ := eval_nonneg g
  mass_mono _ _ _ _ _ _ := le_rfl
  mass_univ _ := rfl
  exp_comparison := exp_cmp
  response_perturbation h g _ _ _ := by
    apply aux_response_real_perturb ‖g‖ _ _ (norm_nonneg g) (eval_nonneg h)
    · have := exp_cmp (h + g) h
      rwa [add_sub_cancel_left] at this
    · have := exp_cmp h (h + g)
      rwa [sub_add_cancel_left, norm_neg] at this
  mass_perturbation h g _ _ _ := by
    have hc := exp_cmp (h + g) h
    rw [add_sub_cancel_left] at hc
    have hn := eval_nonneg h
    have h1 : 1 ≤ 2 * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) := by
      nlinarith [sq_nonneg ‖g‖, Real.exp_pos (4 * ‖g‖), mul_nonneg (sq_nonneg ‖g‖)
        (Real.exp_pos (4 * ‖g‖)).le]
    calc eval (h + g) ≤ Real.exp ‖g‖ * eval h := hc
      _ ≤ 2 * Real.exp ‖g‖ * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) * eval h := by
          have hE := Real.exp_pos ‖g‖
          nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hE.le hn)]

end Lane3
end SubdiffusiveProcess
