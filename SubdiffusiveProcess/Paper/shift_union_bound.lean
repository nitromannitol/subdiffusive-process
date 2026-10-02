import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane3.Forms
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.DirichletForm
import SubdiffusiveProcess.Lane3.ResamplingV2
import SubdiffusiveProcess.Lane3.UpperDensity
import SubdiffusiveProcess.Lane3.BandFiltration
import SubdiffusiveProcess.Probability.LayerProductBlocks
import SubdiffusiveProcess.Probability.ResponseCompactness
import SubdiffusiveProcess.Variational.QuadraticSaving
import SubdiffusiveProcess.Compactness.OperatorLimits
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Finite union bound for arbitrary real `L,w` and all dimensions `d`: with
`M = Mm` and shifts `S = {0, 1/M, ..., (M-1)/M}^d`, the fraction of shifts
for which a depth-`n` child of a point is non-padded is bounded by the stated
union estimate.  The hypothesis `hbad` is the one-dimensional count source
`grid_points_near_integers`/`shift_strip_residues`; the conclusion is the
union bound over the `d` coordinates, normalized by `M^d`. -/
theorem shift_union_bound
    (d Mm : ℕ) (hM : 2 ≤ Mm) (L w : ℝ)
    (bad : Fin d → Finset (Fin Mm))
    (hbad : ∀ i : Fin d, ((bad i).card : ℝ) ≤ 2 * ((w + 1) * (Mm : ℝ) / L + 1)) :
    ((Finset.univ.filter
          (fun sigma : Fin d → Fin Mm => ∃ i : Fin d, sigma i ∈ bad i)).card : ℝ) /
        (Mm : ℝ) ^ d ≤
      2 * (d : ℝ) * ((w + 1) / L + 1 / (Mm : ℝ)) := by
  have hM2 : (0:ℝ) < (Mm:ℝ) := by exact_mod_cast (show 0 < Mm by omega)
  have hMne : (Mm:ℝ) ≠ 0 := ne_of_gt hM2
  have hTi : ∀ i : Fin d,
      (Finset.univ.filter (fun sigma : Fin d → Fin Mm => sigma i ∈ bad i)).card
        ≤ (bad i).card * Mm ^ (d - 1) := by
    intro i
    have hcd : Fintype.card {k : Fin d // k ≠ i} = d - 1 := by
      rw [Fintype.card_subtype]
      rw [show ({k : Fin d | k ≠ i} : Finset (Fin d)) = Finset.univ.erase i by
        ext k; simp [Finset.mem_erase]]
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hcard : ((bad i) ×ˢ (Finset.univ : Finset ({k : Fin d // k ≠ i} → Fin Mm))).card
        = (bad i).card * Mm ^ (d - 1) := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcd]
    have h1 : (Finset.univ.filter (fun sigma : Fin d → Fin Mm => sigma i ∈ bad i)).card
        ≤ ((bad i) ×ˢ (Finset.univ : Finset ({k : Fin d // k ≠ i} → Fin Mm))).card := by
      apply Finset.card_le_card_of_injOn
        (fun sigma : Fin d → Fin Mm => (sigma i, fun j : {k : Fin d // k ≠ i} => sigma j.1))
      · intro sigma hsigma
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hsigma
        simpa only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true] using hsigma
      · intro sigma hsigma tau htau hf
        simp only [Prod.mk.injEq] at hf
        obtain ⟨hf1, hf2⟩ := hf
        funext k
        by_cases hk : k = i
        · subst hk; exact hf1
        · simpa using congrFun hf2 ⟨k, hk⟩
    exact le_trans h1 (le_of_eq hcard)
  have hB_nat : (Finset.univ.filter (fun sigma : Fin d → Fin Mm => ∃ i : Fin d, sigma i ∈ bad i)).card
      ≤ ∑ i : Fin d, (bad i).card * Mm ^ (d - 1) := by
    have h1 : (Finset.univ.filter (fun sigma : Fin d → Fin Mm => ∃ i : Fin d, sigma i ∈ bad i))
        = Finset.univ.biUnion (fun i : Fin d => Finset.univ.filter (fun sigma : Fin d → Fin Mm => sigma i ∈ bad i)) := by
      ext sigma
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    rw [h1]
    refine le_trans (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin d)))
        (t := fun i : Fin d => Finset.univ.filter (fun sigma : Fin d → Fin Mm => sigma i ∈ bad i))) ?_
    exact Finset.sum_le_sum (fun i _ => hTi i)
  have hB_real : ((Finset.univ.filter (fun sigma : Fin d → Fin Mm => ∃ i : Fin d, sigma i ∈ bad i)).card : ℝ)
      ≤ (Mm:ℝ)^(d-1) * ∑ i : Fin d, ((bad i).card : ℝ) := by
    have hcast : (((∑ i : Fin d, (bad i).card * Mm ^ (d - 1) : ℕ)) : ℝ)
        = (Mm:ℝ)^(d-1) * ∑ i : Fin d, ((bad i).card : ℝ) := by
      rw [Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.cast_mul, Nat.cast_pow]
      ring
    calc ((Finset.univ.filter (fun sigma : Fin d → Fin Mm => ∃ i : Fin d, sigma i ∈ bad i)).card : ℝ)
        ≤ ((∑ i : Fin d, (bad i).card * Mm ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast hB_nat
      _ = (Mm:ℝ)^(d-1) * ∑ i : Fin d, ((bad i).card : ℝ) := hcast
  have hSsum : ∑ i : Fin d, ((bad i).card : ℝ) ≤ 2 * (d:ℝ) * ((w+1)*(Mm:ℝ)/L+1) := by
    calc ∑ i : Fin d, ((bad i).card : ℝ)
        ≤ ∑ _i : Fin d, (2 * ((w+1)*(Mm:ℝ)/L+1)) := Finset.sum_le_sum (fun i _ => hbad i)
      _ = 2 * (d:ℝ) * ((w+1)*(Mm:ℝ)/L+1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have harith : (2 * (d:ℝ) * ((w+1)*(Mm:ℝ)/L+1)) / (Mm:ℝ)
      = 2 * (d:ℝ) * ((w+1)/L + 1/(Mm:ℝ)) := by
    rcases eq_or_ne L 0 with hL | hL
    · subst hL
      simp only [div_zero, mul_zero, zero_add, mul_one]
      ring
    · field_simp
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have hf : (Finset.univ.filter (fun sigma : Fin 0 → Fin Mm => ∃ i : Fin 0, sigma i ∈ bad i)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro sigma h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      obtain ⟨i, _⟩ := h
      exact absurd i.isLt (Nat.not_lt_zero i.val)
    rw [hf]
    simp
  · have hMpowd : (Mm:ℝ)^d = (Mm:ℝ)^(d-1) * (Mm:ℝ) := by
      conv_lhs => rw [show d = (d-1) + 1 by omega]
      rw [pow_succ]
    calc ((Finset.univ.filter (fun sigma : Fin d → Fin Mm => ∃ i : Fin d, sigma i ∈ bad i)).card : ℝ) / (Mm:ℝ)^d
        ≤ ((Mm:ℝ)^(d-1) * ∑ i : Fin d, ((bad i).card : ℝ)) / (Mm:ℝ)^d := by
          apply div_le_div_of_nonneg_right hB_real
          exact pow_nonneg (le_of_lt hM2) d
      _ = (∑ i : Fin d, ((bad i).card : ℝ)) / (Mm:ℝ) := by
          rw [hMpowd]
          have hp : (Mm:ℝ)^(d-1) ≠ 0 := pow_ne_zero _ hMne
          exact mul_div_mul_left _ _ hp
      _ ≤ (2 * (d:ℝ) * ((w+1)*(Mm:ℝ)/L+1)) / (Mm:ℝ) := by
          apply div_le_div_of_nonneg_right hSsum
          exact le_of_lt hM2
      _ = 2 * (d:ℝ) * ((w+1)/L + 1/(Mm:ℝ)) := harith


end Paper
