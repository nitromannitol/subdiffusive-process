import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! A finite-horizon root allowance always exists, even away from the countable
mesh on which estimates are available. A real tail bound controls the least
allowance. No measurability or probabilistic assertion is made.
-/
noncomputable section
namespace SubdiffusiveProcess

/-- Beyond the finite horizon every required root-prefix condition is vacuous. -/
theorem finiteRootAllowance_exists (horizon floor : ℕ) (good : ℕ → Prop) :
    ∃ B : ℕ, floor ≤ B ∧ ∀ len : ℕ, B ≤ len → len ≤ horizon → good len := by
  refine ⟨max floor (horizon + 1), le_max_left _ _, ?_⟩
  intro len h1 h2
  have h3 := le_max_right floor (horizon + 1)
  omega

/-- The least allowance controls only prefixes within the finite horizon. -/
def finiteRootAllowance (horizon floor : ℕ) (good : ℕ → Prop) : ℕ :=
  @Nat.find (fun B => floor ≤ B ∧ ∀ len : ℕ, B ≤ len → len ≤ horizon → good len)
    (Classical.decPred _) (finiteRootAllowance_exists horizon floor good)

/-- The least allowance respects its required floor and every admitted prefix. -/
theorem finiteRootAllowance_spec (horizon floor : ℕ) (good : ℕ → Prop) :
    floor ≤ finiteRootAllowance horizon floor good ∧
      ∀ len : ℕ, finiteRootAllowance horizon floor good ≤ len → len ≤ horizon → good len :=
  @Nat.find_spec _ (Classical.decPred _) (finiteRootAllowance_exists horizon floor good)

/-- Any affine real prefix threshold bounds the least finite-horizon allowance. -/
theorem finiteRootAllowance_le (horizon floor : ℕ) (good : ℕ → Prop)
    (B : ℝ) (hB : 0 ≤ B) (hgood : ∀ len : ℕ, B ≤ len → len ≤ horizon → good len) :
    (finiteRootAllowance horizon floor good : ℝ) ≤ B + floor + 1 := by
  classical
  have hceil : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  have hbound : finiteRootAllowance horizon floor good ≤ ⌈B⌉₊ + floor := by
    apply @Nat.find_min' _ (Classical.decPred _) (finiteRootAllowance_exists horizon floor good)
    refine ⟨Nat.le_add_left _ _, ?_⟩
    intro len hlen hhor
    exact hgood len (hceil.trans (by exact_mod_cast (show ⌈B⌉₊ ≤ len by omega))) hhor
  have hc : (⌈B⌉₊ : ℝ) < B + 1 := Nat.ceil_lt_add_one hB
  have hb : (finiteRootAllowance horizon floor good : ℝ) ≤ (⌈B⌉₊ : ℝ) + floor := by
    exact_mod_cast hbound
  linarith only [hc, hb]

end SubdiffusiveProcess
