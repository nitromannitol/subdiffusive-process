module

public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Lane3.Forms
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Doc ticklist: standalone fine step permits every alpha<alpha1<1; both actual sequences and their sum; Cfin beforem; fixed matching exponent/moments unchanged; no free surrogate. -/
theorem lem_finite_good_cell_uniform
    (alpha alpha1 sigma tau2 Cc : ℝ)
    (hal1 : alpha < alpha1) (hal1' : alpha1 < 1)
    (hsig : 0 < sigma) (htau : 0 < tau2) (hCc : 1 ≤ Cc)
    (hmatch : Cc * (sigma + tau2) < alpha1 - alpha)
    (holderAbove holderBelow : ℕ → ℝ)
    (hAbove : ∀ m : ℕ, 0 ≤ holderAbove m) (hBelow : ∀ m : ℕ, 0 ≤ holderBelow m)
    (habove : ∀ m : ℕ, holderAbove m ≤
      Cc * (3 : ℝ) ^ (Cc * (sigma + tau2) * (m : ℝ)) *
        ((3 : ℝ) ^ (-(m : ℝ))) ^ (alpha1 - alpha))
    (hbelow : ∀ m : ℕ, holderBelow m ≤
      Cc * (3 : ℝ) ^ (Cc * (sigma + tau2) * (m : ℝ)) *
        ((3 : ℝ) ^ (-(m : ℝ))) ^ (alpha1 - alpha)) :
    ∃ Cfin : ℝ, 0 < Cfin ∧ ∀ m : ℕ, holderAbove m + holderBelow m ≤ Cfin := by
  have hCc0 : 0 ≤ Cc := le_trans (by norm_num) hCc
  have hCcpos : 0 < Cc := lt_of_lt_of_le (by norm_num) hCc
  have hgap : Cc * (sigma + tau2) - (alpha1 - alpha) ≤ 0 :=
    le_of_lt (sub_neg.mpr hmatch)
  refine ⟨2 * Cc, by nlinarith, ?_⟩
  intro m
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hexp :
      Cc * (sigma + tau2) * (m : ℝ) + (-(m : ℝ)) * (alpha1 - alpha) ≤ 0 := by
    calc
      Cc * (sigma + tau2) * (m : ℝ) + (-(m : ℝ)) * (alpha1 - alpha) =
          (m : ℝ) * (Cc * (sigma + tau2) - (alpha1 - alpha)) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm hgap
  have hpow :
      (3 : ℝ) ^ (Cc * (sigma + tau2) * (m : ℝ)) *
          ((3 : ℝ) ^ (-(m : ℝ))) ^ (alpha1 - alpha) ≤ 1 := by
    calc
      (3 : ℝ) ^ (Cc * (sigma + tau2) * (m : ℝ)) *
          ((3 : ℝ) ^ (-(m : ℝ))) ^ (alpha1 - alpha) =
          (3 : ℝ) ^ (Cc * (sigma + tau2) * (m : ℝ)) *
            (3 : ℝ) ^ ((-(m : ℝ)) * (alpha1 - alpha)) := by
              rw [← Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))]
      _ = (3 : ℝ) ^
          (Cc * (sigma + tau2) * (m : ℝ) + (-(m : ℝ)) * (alpha1 - alpha)) := by
            rw [← Real.rpow_add (by norm_num : 0 < (3 : ℝ))]
      _ ≤ (3 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 := by rw [Real.rpow_zero]
  have hmajor :
      Cc * ((3 : ℝ) ^ (Cc * (sigma + tau2) * (m : ℝ)) *
          ((3 : ℝ) ^ (-(m : ℝ))) ^ (alpha1 - alpha)) ≤ Cc := by
    calc
      Cc * ((3 : ℝ) ^ (Cc * (sigma + tau2) * (m : ℝ)) *
          ((3 : ℝ) ^ (-(m : ℝ))) ^ (alpha1 - alpha)) ≤ Cc * 1 :=
        mul_le_mul_of_nonneg_left hpow hCc0
      _ = Cc := by ring
  have hmajor' :
      Cc * (3 : ℝ) ^ (Cc * (sigma + tau2) * (m : ℝ)) *
          ((3 : ℝ) ^ (-(m : ℝ))) ^ (alpha1 - alpha) ≤ Cc := by
    simpa [mul_assoc] using hmajor
  have habove' : holderAbove m ≤ Cc := le_trans (habove m) hmajor'
  have hbelow' : holderBelow m ≤ Cc := le_trans (hbelow m) hmajor'
  calc
    holderAbove m + holderBelow m ≤ Cc + Cc := add_le_add habove' hbelow'
    _ = 2 * Cc := by ring

end Paper
