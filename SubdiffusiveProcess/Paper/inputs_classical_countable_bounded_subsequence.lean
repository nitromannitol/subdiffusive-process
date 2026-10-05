module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import SubdiffusiveProcess.Paper.inputs_classical_countable_moment_subsequence

@[expose] public section

/-! Classical countable moment-bank subsequence extraction by weighted summation and Fatou.
There are no model-specific quantities or conclusions in this statement.
It is the case `Q = 0`, `p = 1`, `B = 0` of `inputs_classical_countable_moment_subsequence`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Paper

/-- A countable family of uniformly L1-bounded sequences is simultaneously bounded along almost every sample's further subsequence. -/
theorem inputs_classical_countable_bounded_subsequence
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} [Countable ι] (F : ι → ℕ → Ω → ℝ) (C : ι → ℝ≥0)
    (_hmem : ∀ j n, MemLp (F j n) 1 P)
    (_hbound : ∀ j n, eLpNorm (F j n) 1 P ≤ C j) :
    ∀ᵐ om ∂P, ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ n, |F j (seq n) om| ≤ B := by
  obtain ⟨_, _, _, _, hae⟩ := inputs_classical_countable_moment_subsequence P F C _hmem _hbound
    (fun _ _ => 0) 1 le_rfl 0 (fun _ => by simp) (fun _ => by simp)
  filter_upwards [hae] with om ⟨seq, hs, _, h2⟩
  exact ⟨seq, hs, h2⟩

end SubdiffusiveProcess.Paper
