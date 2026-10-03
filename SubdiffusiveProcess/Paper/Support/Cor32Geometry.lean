module

public import SubdiffusiveProcess.Paper.Support.Cor32ModelDefinitions

@[expose] public section




open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Paper

lemma aux_cor_32_side_eq (H1 n : ℕ) :
    descendantSide (subdivisionHalfWidth H1) n 1 = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℝ)) := by
  have hcast : 2 * (subdivisionHalfWidth H1 : ℝ) + 1 = (3 : ℝ) ^ H1 := by
    exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
  rw [descendantSide, hcast, ← pow_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_natCast, one_div]

end Paper
