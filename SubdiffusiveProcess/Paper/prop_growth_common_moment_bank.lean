module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper

/-- The common moment bank, with its displayed finite family of orders. -/
theorem prop_growth_common_moment_bank
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m k : ℕ) (ps : Fin k → ℝ) (hps : ∀ i, 1 ≤ ps i)
    (X : Fin m → ℕ → Ω → ℝ) (B : Fin m → Fin k → ℝ)
    (hB : ∀ j i, 0 ≤ B j i)
    (hXmem : ∀ j i N, MemLp (X j N) (ENNReal.ofReal (ps i)) P)
    (hXnorm : ∀ j i N,
      eLpNorm (X j N) (ENNReal.ofReal (ps i)) P ≤ ENNReal.ofReal (B j i)) :
  ∃ (K : ℕ → Ω → ℝ) (Cbound : Fin k → ℝ),
    (∀ N ω, 0 ≤ K N ω) ∧
    (∀ j N ω, |X j N ω| ≤ K N ω) ∧
    (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) P) ∧
    (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) P ≤
      ENNReal.ofReal (Cbound i)) := by
  classical
  let K : ℕ → Ω → ℝ := fun N ω => ∑ j : Fin m, |X j N ω|
  let Cbound : Fin k → ℝ := fun i => ∑ j : Fin m, B j i
  refine ⟨K, Cbound, ?_, ?_, ?_, ?_⟩
  · intro N ω
    dsimp [K]
    exact Finset.sum_nonneg (fun j _ => abs_nonneg _)
  · intro j N ω
    dsimp [K]
    exact Finset.single_le_sum (f := fun j : Fin m => |X j N ω|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  · intro i N
    dsimp [K]
    have hsum :
        (∑ j : Fin m, (fun ω => |X j N ω|)) =
          (fun ω => ∑ j : Fin m, |X j N ω|) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [← hsum]
    exact memLp_finsetSum' Finset.univ
      (fun j _ => (hXmem j i N).norm)
  · intro i N
    dsimp [K, Cbound]
    have hsum :
        (∑ j : Fin m, (fun ω => |X j N ω|)) =
          (fun ω => ∑ j : Fin m, |X j N ω|) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [← hsum]
    calc
      eLpNorm (∑ j : Fin m, (fun ω => |X j N ω|)) (ENNReal.ofReal (ps i)) P ≤
          ∑ j : Fin m, eLpNorm (fun ω => |X j N ω|) (ENNReal.ofReal (ps i)) P :=
        eLpNorm_sum_le (p := ENNReal.ofReal (ps i)) (μ := P)
          (f := fun j : Fin m => fun ω => |X j N ω|) (s := Finset.univ)
          ((ENNReal.one_le_ofReal).2 (hps i))
      _ = ∑ j : Fin m, eLpNorm (X j N) (ENNReal.ofReal (ps i)) P := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [Real.norm_eq_abs] using
          (eLpNorm_norm (p := ENNReal.ofReal (ps i)) (μ := P) (X j N) (hXmem j i N).aestronglyMeasurable)
      _ ≤ ∑ j : Fin m, ENNReal.ofReal (B j i) :=
        Finset.sum_le_sum (fun j _ => hXnorm j i N)
      _ = ENNReal.ofReal (∑ j : Fin m, B j i) := by
        symm
        exact ENNReal.ofReal_sum_of_nonneg (fun j _ => hB j i)

end SubdiffusiveProcess.Paper
