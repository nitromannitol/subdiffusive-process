module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Reference coefficient ratios normalize the half Holder forcing row.
This is a scalar transport identity with no stochastic conclusion. -/
namespace SubdiffusiveProcess

/-- A bound on the reciprocal reference ratio controls both forcing terms at a smaller scale. -/
theorem dirichlet_forcing_row_le (j m : ℤ) (r r0 R G H : ℝ)
    (hr : 0 < r) (hr0 : 0 < r0) (hR : 1 ≤ R)
    (hG : 0 ≤ G) (hH : 0 ≤ H) (hrat : r0/r ≤ R) :
    r⁻¹*(3:ℝ)^((j:ℝ)/2)*G+(3:ℝ)^((j:ℝ)/2)*H ≤
      R*(3:ℝ)^(-(((m-j:ℤ):ℝ)/2))*
        (r0⁻¹*(3:ℝ)^((m:ℝ)/2)*G+(3:ℝ)^((m:ℝ)/2)*H) := by
  have hi : r⁻¹ ≤ R*r0⁻¹ := by
    calc r⁻¹ = (r0/r)*r0⁻¹ := by field_simp
         _ ≤ R*r0⁻¹ := mul_le_mul_of_nonneg_right hrat (inv_pos.mpr hr0).le
  have hg := mul_le_mul_of_nonneg_right hi (show 0≤(3:ℝ)^((j:ℝ)/2)*G by positivity)
  have hh := mul_le_mul_of_nonneg_right hR (show 0≤(3:ℝ)^((j:ℝ)/2)*H by positivity)
  have hp : (3:ℝ)^(-(((m-j:ℤ):ℝ)/2))*(3:ℝ)^((m:ℝ)/2) = (3:ℝ)^((j:ℝ)/2) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    simp only [Int.cast_sub]
    ring
  have hident : R*(3:ℝ)^(-(((m-j:ℤ):ℝ)/2))*
        (r0⁻¹*(3:ℝ)^((m:ℝ)/2)*G+(3:ℝ)^((m:ℝ)/2)*H) =
      R*r0⁻¹*(3:ℝ)^((j:ℝ)/2)*G+R*(3:ℝ)^((j:ℝ)/2)*H := by
    calc _ = R*r0⁻¹*((3:ℝ)^(-(((m-j:ℤ):ℝ)/2))*(3:ℝ)^((m:ℝ)/2))*G+
             R*((3:ℝ)^(-(((m-j:ℤ):ℝ)/2))*(3:ℝ)^((m:ℝ)/2))*H := by ring
         _ = _ := by rw [hp]
  rw [hident]
  nlinarith only [hg,hh]

end SubdiffusiveProcess
