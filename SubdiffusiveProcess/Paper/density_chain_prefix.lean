module

public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic
@[expose] public section

open Set
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- A simultaneous all-branch bad count survives starting after a fixed prefix.
Only the intercept changes, by theta times the prefix length. -/
theorem density_chain_prefix {A : Type*} (Good : List A → Prop)
    (theta B : ℝ) (htheta : 0 ≤ theta) (hB : 0 ≤ B)
    (hcount : ∀ (J : ℕ) (w : Fin J → A), 1 ≤ J →
      (Set.ncard {i : Fin J | ¬ Good ((List.ofFn w).take (i.val + 1))} : ℝ) ≤
        theta * (J : ℝ) + B) :
    ∀ (base : ℕ) (w0 : Fin base → A) (J : ℕ) (w : Fin J → A),
      (Set.ncard {i : Fin J | ¬ Good (List.ofFn w0 ++ (List.ofFn w).take (i.val + 1))} : ℝ) ≤
        theta * (J : ℝ) + (B + theta * (base : ℝ)) := by
  classical
  intro base w0 J w
  by_cases hJ : 1 ≤ J
  · let whole := Fin.append w0 w
    have htake (i : Fin J) :
        (List.ofFn whole).take ((Fin.natAdd base i).val + 1) =
          List.ofFn w0 ++ (List.ofFn w).take (i.val + 1) := by
      simp only [whole, List.ofFn_fin_append, Fin.val_natAdd, List.take_append, List.length_ofFn]
      rw [List.take_of_length_le (by simp only [List.length_ofFn]; omega)]
      congr 2
      omega
    have hle : Set.ncard {i : Fin J |
        ¬ Good (List.ofFn w0 ++ (List.ofFn w).take (i.val + 1))} ≤
        Set.ncard {i : Fin (base + J) | ¬ Good ((List.ofFn whole).take (i.val + 1))} := by
      apply Set.ncard_le_ncard_of_injOn (Fin.natAdd base)
      · intro i hi
        change ¬ Good ((List.ofFn whole).take ((Fin.natAdd base i).val + 1))
        rwa [htake]
      · intro i _ j _ hij
        exact Fin.ext (by have h := congrArg Fin.val hij; simp only [Fin.val_natAdd] at h; omega)
    have h := hcount (base + J) whole (by omega)
    have hreal : (Set.ncard {i : Fin J |
        ¬ Good (List.ofFn w0 ++ (List.ofFn w).take (i.val + 1))} : ℝ) ≤
        Set.ncard {i : Fin (base + J) | ¬ Good ((List.ofFn whole).take (i.val + 1))} :=
      Nat.cast_le.mpr hle
    push_cast at h
    linarith
  · have hJ0 : J = 0 := by omega
    subst J
    have hempty : {i : Fin 0 | ¬ Good (List.ofFn w0 ++ (List.ofFn w).take (i.val + 1))} = ∅ := by
      ext i
      exact Fin.elim0 i
    rw [hempty, Set.ncard_empty, Nat.cast_zero, mul_zero, zero_add]
    exact add_nonneg hB (mul_nonneg htheta (Nat.cast_nonneg base))
end Paper
