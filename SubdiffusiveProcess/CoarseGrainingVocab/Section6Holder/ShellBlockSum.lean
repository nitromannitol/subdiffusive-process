module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.GoodScaleSuffix

@[expose] public section

/-!
# Hölder Step 3: summing the finite shell block

The shell block between a lower scale and the parent is the sum of one-shell
increments.  Each increment is read from its own accumulated-error shell slot,
where its discount is the fixed one-step factor `3^(-s/8)`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open scoped BigOperators

noncomputable section

private abbrev Sample (d : ℕ) := _root_.SubdiffusiveProcess.Model.PotentialSample d

private theorem shellBlock_succ_pred {d : ℕ} (i : ℕ) (hi : 0 < i)
    (omega : Sample d) (x : Vec d) :
    shellBlock i (i - 1) omega x = omega i x := by
  unfold shellBlock
  have hIcc : Finset.Icc (i - 1 + 1) i = {i} := by
    rw [Nat.sub_add_cancel hi, Finset.Icc_self]
  rw [hIcc]
  simp

private theorem translatedCube_mono {d : ℕ} {q i : ℕ} (hqi : q ≤ i)
    (z : Vec d) : translatedCube d (q : ℤ) z ⊆ translatedCube d (i : ℤ) z := by
  rintro x ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  exact Section6ExcessDecay.cube_subset_cube_of_le (by exact_mod_cast hqi) hy

/-- One lower-to-parent shell block is bounded by the accumulated-error sum,
with the exact reciprocal of the one-step discount retained. -/
theorem abs_shellBlock_le_accumulatedError_sum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    {q m : ℕ} (s : ℝ) (z : Vec d) (omega : Sample d)
    {x : Vec d} (hx : x ∈ translatedCube d (q : ℤ) z) :
    |shellBlock m q omega x| ≤
      (∑ i ∈ Finset.Icc (q + 1) m,
        accumulatedError M cutoff i z s omega) /
        (3 : ℝ) ^ (-(s / 8)) := by
  have hw : 0 < (3 : ℝ) ^ (-(s / 8)) := Real.rpow_pos_of_pos (by norm_num) _
  have hpoint : ∀ i ∈ Finset.Icc (q + 1) m,
      |omega i x| ≤ accumulatedError M cutoff i z s omega /
        (3 : ℝ) ^ (-(s / 8)) := by
    intro i hi
    have hqi : q ≤ i := (Nat.le_add_right q 1).trans (Finset.mem_Icc.mp hi).1
    have hi0 : 0 < i := lt_of_lt_of_le (Nat.zero_lt_succ q) (Finset.mem_Icc.mp hi).1
    have hxi : x ∈ translatedCube d (i : ℤ) z := translatedCube_mono hqi z hx
    have hsup : |shellBlock i (i - 1) omega x| ≤
        supNormOn (translatedCube d (i : ℤ) z) (shellBlock i (i - 1) omega) :=
      abs_apply_le_supNormOn_translatedCube (by unfold shellBlock; fun_prop) hxi
    have hslot := weighted_shellBlock_le_accumulatedError
      M cutoff s i (i - 1) z omega (Nat.sub_le i 1)
    have hgap : (i : ℝ) - ((i - 1 : ℕ) : ℝ) = 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ i)]
      push_cast
      ring
    rw [hgap, mul_one] at hslot
    have hdiv : supNormOn (translatedCube d (i : ℤ) z)
          (shellBlock i (i - 1) omega) ≤
        accumulatedError M cutoff i z s omega / (3 : ℝ) ^ (-(s / 8)) :=
      (le_div_iff₀ hw).2 (by simpa only [mul_comm] using hslot)
    have hsup' : |omega i x| ≤
        supNormOn (translatedCube d (i : ℤ) z) (shellBlock i (i - 1) omega) := by
      simpa only [shellBlock_succ_pred i hi0 omega x] using hsup
    exact hsup'.trans hdiv
  have hsumAbs : |∑ i ∈ Finset.Icc (q + 1) m, omega i x| ≤
      ∑ i ∈ Finset.Icc (q + 1) m, |omega i x| :=
    Finset.abs_sum_le_sum_abs _ _
  unfold shellBlock
  calc
    |∑ i ∈ Finset.Icc (q + 1) m, omega i x| ≤
        ∑ i ∈ Finset.Icc (q + 1) m, |omega i x| := hsumAbs
    _ ≤ ∑ i ∈ Finset.Icc (q + 1) m,
        accumulatedError M cutoff i z s omega /
          (3 : ℝ) ^ (-(s / 8)) :=
      Finset.sum_le_sum hpoint
    _ = (∑ i ∈ Finset.Icc (q + 1) m,
        accumulatedError M cutoff i z s omega) /
          (3 : ℝ) ^ (-(s / 8)) := by
      rw [Finset.sum_div]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
