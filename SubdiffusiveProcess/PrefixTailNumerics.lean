module

public import Mathlib

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Paper

theorem aux_prefix_accumulated_error_tail_log_budget {delta : ℝ}
    (hd : 0 < delta) (hd1 : delta ≤ 1) : delta ^ 2 * |Real.log delta| ≤ delta := by
  have h := (Real.abs_log_mul_self_lt delta hd hd1).le
  rw [abs_mul, abs_of_pos hd] at h
  nlinarith [mul_le_mul_of_nonneg_left h hd.le]

theorem aux_prefix_score_window_tail_map {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (g : Ω → Ξ)
    (hg : AEMeasurable g P) (hlaw : Measure.map g P = Q)
    (E : Set Ω) (F : Set Ξ) (hEF : ∀ᵐ om ∂P, om ∈ E → g om ∈ F) :
    P E ≤ Q F := by
  refine (measure_mono_ae hEF).trans ?_
  change P (g ⁻¹' F) ≤ Q F
  simpa only [hlaw] using Measure.le_map_apply hg F

theorem aux_prefix_physical_tail_padded_sum_le
    (N D b : ℕ) (a : ℤ) (X : ℕ → ℝ) (hX : ∀ j, 0 ≤ X j) :
    (∑ j ∈ Finset.Icc a (min (N : ℤ) (a + (D : ℤ) + 2 * (b : ℤ))),
      if 0 ≤ (N : ℤ) - j then X ((N : ℤ) - j).toNat else 0) ≤
    ∑ i ∈ Finset.Icc
      ((N : ℤ) - min (N : ℤ) (a + (D : ℤ) + 2 * (b : ℤ))).toNat
      (((N : ℤ) - min (N : ℤ) (a + (D : ℤ) + 2 * (b : ℤ))).toNat + D + 2 * b), X i := by
  classical
  let u : ℤ := min (N : ℤ) (a + (D : ℤ) + 2 * (b : ℤ))
  let n : ℕ := ((N : ℤ) - u).toNat
  let S : Finset ℤ := Finset.Icc a u
  let f : ℤ → ℕ := fun j => ((N : ℤ) - j).toNat
  have huN : u ≤ (N : ℤ) := min_le_left _ _
  have hua : u ≤ a + (D : ℤ) + 2 * (b : ℤ) := min_le_right _ _
  have hn : (n : ℤ) = (N : ℤ) - u := Int.toNat_of_nonneg (by omega)
  have hmem : ∀ j ∈ S, (f j : ℤ) = (N : ℤ) - j := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact Int.toNat_of_nonneg (by omega)
  have hinj : Set.InjOn f (S : Set ℤ) := by
    intro j hj l hl heq
    have hj' := hmem j hj
    have hl' := hmem l hl
    have heq' : (f j : ℤ) = (f l : ℤ) := congrArg Nat.cast heq
    omega
  have hsub : S.image f ⊆ Finset.Icc n (n + D + 2 * b) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hji := hmem j hj
    have hj' := Finset.mem_Icc.mp hj
    rw [Finset.mem_Icc]
    omega
  calc
    _ = ∑ j ∈ S, X (f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      simp only [if_pos (show 0 ≤ (N : ℤ) - j by omega)]
      rfl
    _ = ∑ i ∈ S.image f, X i := (Finset.sum_image hinj).symm
    _ ≤ ∑ i ∈ Finset.Icc n (n + D + 2 * b), X i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hX i)

end Paper
