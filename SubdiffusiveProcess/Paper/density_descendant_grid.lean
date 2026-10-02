import SubdiffusiveProcess.Paper.goodext_admissible_grid
import SubdiffusiveProcess.FiniteStopping.ObservationTree
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Every observation descendant of a translated unit root has an integer index
at its exact absolute level H1*n. -/
theorem density_descendant_grid {d : ℕ} (H1 : ℕ)
    (z0 zroot : SpatialCoordinates d) (jroot : Fin d → ℤ)
    (hroot : zroot = fun i => z0 i + (jroot i : ℝ)) :
    ∀ n (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
      ∃ j : Fin d → ℤ,
        descendantCenter (subdivisionHalfWidth H1) zroot 1 n w =
          aux_goodext_admissible_grid_centre z0 (H1 * n, j) := by
  intro n
  induction n with
  | zero =>
    intro w
    refine ⟨jroot, ?_⟩
    change zroot = fun i => z0 i + (3 : ℝ) ^ (-((H1 * 0 : ℕ) : ℤ)) * (jroot i : ℝ)
    simpa only [mul_zero, Nat.cast_zero, neg_zero, zpow_zero, one_mul] using hroot
  | succ n ih =>
    intro w
    obtain ⟨j, hj⟩ := ih (fun i => w i.castSucc)
    let m := subdivisionHalfWidth H1
    let k := H1 * (n + 1)
    let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
    have hL : 2 * (m : ℝ) + 1 = (3 : ℝ) ^ H1 := by
      exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
    have hside : descendantSide m n (1 : ℝ) = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ)) := by
      have h := FiniteStopping.descendantSide_zpow H1 m
        (two_mul_subdivisionHalfWidth_add_one H1) 0 n
      simpa only [zpow_zero, zero_sub] using h
    have hstep : (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ)) = (3 : ℝ) ^ H1 * r := by
      dsimp only [r, k]
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      push_cast
      ring
    refine ⟨fun i => (3 ^ H1 : ℕ) * j i + (w (Fin.last n) i).val - m, ?_⟩
    change oddGridCenter _ _ m (w (Fin.last n)) = _
    rw [hj, hside, hstep]
    funext i
    change (z0 i + (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ)) * (j i : ℝ)) +
      (((w (Fin.last n) i).val : ℝ) - (m : ℝ)) * ((3 : ℝ) ^ H1 * r / (2 * (m : ℝ) + 1)) = _
    rw [hstep, hL]
    have hLne : (3 : ℝ) ^ H1 ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [mul_div_cancel_left₀ r hLne]
    simp only [aux_goodext_admissible_grid_centre, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.cast_ofNat]
    change _ = z0 i + r * ((3 : ℝ) ^ H1 * (j i : ℝ) + (w (Fin.last n) i).val - (m : ℝ))
    ring
end Paper
