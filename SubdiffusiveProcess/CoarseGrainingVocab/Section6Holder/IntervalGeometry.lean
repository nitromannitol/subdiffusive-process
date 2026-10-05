module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.CombineGoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ReadyStep

@[expose] public section

/-!
# Hölder Step 3: interval geometry

This file records the two deterministic facts used in the sum of the
recurrence defects: boundary contact is monotone along nested truncated
windows, and the half-scale weights have a dimension-free geometric sum.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Boundary contact persists when a window is enlarged. -/
theorem BoundaryTouches.mono {d : ℕ} {U V W : Set (Vec d)}
    (hUV : U ⊆ V) (hU : BoundaryTouches U W) : BoundaryTouches V W := by
  unfold BoundaryTouches at hU ⊢
  obtain ⟨x, hxU, hxW⟩ := Set.nonempty_iff_ne_empty.mpr hU
  exact Set.nonempty_iff_ne_empty.mp ⟨x, closure_mono hUV hxU, hxW⟩

/-- The boundary-contact indicator is monotone in the scale of a truncated
window. -/
theorem boundaryIndicator_truncatedCube_le {d : ℕ} {m j l : ℤ} {z : Vec d}
    (hjl : j ≤ l) :
    (if BoundaryTouches (truncatedCube d m j z) (cube d m) then (1 : ℝ) else 0) ≤
      if BoundaryTouches (truncatedCube d m l z) (cube d m) then 1 else 0 := by
  by_cases hj : BoundaryTouches (truncatedCube d m j z) (cube d m)
  · have hl := BoundaryTouches.mono (truncatedCube_mono d m z hjl) hj
    simp only [ite_eq_left hj, ite_eq_left hl, le_refl]
  · simp only [ite_eq_right hj]
    split_ifs <;> norm_num

private theorem toNat_sub_cast {m n : ℤ} (h : n ≤ m) :
    (((m - n).toNat : ℕ) : ℝ) = ((m - n : ℤ) : ℝ) := by
  have h0 : (0 : ℤ) ≤ m - n := by omega
  exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.toNat_of_nonneg h0)

private theorem rpow_three_mul_eq_pow (c : ℝ) {m n : ℤ} (h : n ≤ m) :
    (3 : ℝ) ^ (c * ((m - n : ℤ) : ℝ)) =
      ((3 : ℝ) ^ c) ^ (m - n).toNat := by
  rw [← toNat_sub_cast h, ← Real.rpow_natCast ((3 : ℝ) ^ c) ((m - n).toNat),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

private theorem geom_sum_le_inv_one_sub {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    ∑ j ∈ Finset.range K, r ^ j ≤ (1 - r)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have hmul := geom_sum_mul r K
  have hpow : (0 : ℝ) ≤ r ^ K := pow_nonneg hr0 K
  have hval : (∑ j ∈ Finset.range K, r ^ j) * (1 - r) = 1 - r ^ K := by
    linear_combination -hmul
  rw [← one_div, le_div_iff₀ hpos, hval]
  linarith

private theorem sum_Icc_le_geometric {L m : ℤ} (hLm : L ≤ m) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (w : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Icc L m, w n = r ^ (m - n).toNat) :
    ∑ n ∈ Finset.Icc L m, w n ≤ (1 - r)⁻¹ := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d167_sum_Icc_le_of_geometric (L := L) (m := m) (hLm := hLm) (r := r) (hr0 := hr0) (hr1 := hr1) (w := w) (hw := hw)

/-- A half-scale geometric row sums to at most `5/2`. -/
theorem sum_Icc_three_neg_half_le {L m : ℤ} (hLm : L ≤ m) :
    ∑ n ∈ Finset.Icc L m,
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((m - n : ℤ) : ℝ)) ≤ 5 / 2 := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.aux_dedup_d267_sum_Icc_three_neg_half_le (L := L) (m := m) (hLm := hLm)

/-- The half-scale row on `[n,l]`, measured from a larger parent scale `m`,
is controlled by its last term. -/
theorem sum_Icc_three_parent_half_le {n l m : ℤ} (hnl : n ≤ l) :
    ∑ j ∈ Finset.Icc n l,
        (3 : ℝ) ^ (-(((m - j : ℤ) : ℝ) / 2)) ≤
      (5 / 2 : ℝ) * (3 : ℝ) ^ (-(((m - l : ℤ) : ℝ) / 2)) := by
  have hgeo := sum_Icc_three_neg_half_le hnl
  have hfactor : ∀ j ∈ Finset.Icc n l,
      (3 : ℝ) ^ (-(((m - j : ℤ) : ℝ) / 2)) =
        (3 : ℝ) ^ (-(((m - l : ℤ) : ℝ) / 2)) *
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((l - j : ℤ) : ℝ)) := by
    intro j hj
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  calc
    (∑ j ∈ Finset.Icc n l,
        (3 : ℝ) ^ (-(((m - j : ℤ) : ℝ) / 2))) =
      ∑ j ∈ Finset.Icc n l,
        (3 : ℝ) ^ (-(((m - l : ℤ) : ℝ) / 2)) *
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((l - j : ℤ) : ℝ)) := by
        exact Finset.sum_congr rfl fun j hj ↦ hfactor j hj
    _ = (3 : ℝ) ^ (-(((m - l : ℤ) : ℝ) / 2)) *
        ∑ j ∈ Finset.Icc n l,
          (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((l - j : ℤ) : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (3 : ℝ) ^ (-(((m - l : ℤ) : ℝ) / 2)) * (5 / 2) :=
      mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg (by norm_num) _)
    _ = (5 / 2 : ℝ) * (3 : ℝ) ^ (-(((m - l : ℤ) : ℝ) / 2)) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
