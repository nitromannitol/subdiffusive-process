module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Power bookkeeping for local energy obtained from a Holder trace response.
The coefficient and variational estimates must be supplied by the caller. -/
namespace SubdiffusiveProcess

/-- A trace exponent with a positive loss margin dominates the requested energy exponent. -/
theorem dirichlet_cell_cost_le (d : ℕ) (r beta e t CE CL Kr H F S L R E : ℝ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hCE : 0 ≤ CE) (hCL : 0 ≤ CL) (hKr : 0 ≤ Kr)
    (hF : 0 ≤ F) (hS : 0 ≤ S) (ht : t ≤ (d:ℝ)-2+2*beta-2*e) (htd : t ≤ d)
    (hL : L ≤ CL*r^(-2*e)*Kr)
    (hR : R ≤ CE*L*r^((d:ℝ)-2)*(r^beta*H)^2)
    (hE : E ≤ R+2*F*S*r^d) :
    E ≤ (CE*CL+2)*(Kr*H^2+F*S)*r^t := by
  have hLp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hCE)
    (mul_nonneg (Real.rpow_nonneg hr.le ((d:ℝ)-2)) (sq_nonneg (r^beta*H)))
  have hid : CE*(CL*r^(-2*e)*Kr)*(r^((d:ℝ)-2)*(r^beta*H)^2) =
      CE*CL*Kr*H^2*r^((d:ℝ)-2+2*beta-2*e) := by
    rw [mul_pow,← Real.rpow_natCast (r^beta),← Real.rpow_mul hr.le]
    calc _ = CE*CL*Kr*H^2*(r^(-2*e)*r^((d:ℝ)-2)*r^(beta*2)) := by ring
         _ = _ := by rw [← Real.rpow_add hr,← Real.rpow_add hr]; congr 2; ring
  rw [hid] at hLp
  have hp := Real.rpow_le_rpow_of_exponent_ge hr hr1 ht
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ CE*CL*Kr*H^2 by positivity)
  have hd := Real.rpow_le_rpow_of_exponent_ge hr hr1 htd
  rw [Real.rpow_natCast] at hd
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*F*S by positivity)
  have hx : 0 ≤ CE*CL*(F*S)*r^t := by positivity
  have hy : 0 ≤ 2*(Kr*H^2)*r^t := by positivity
  nlinarith only [hE,hR,hLp,hp',hd',hx,hy]

end SubdiffusiveProcess
