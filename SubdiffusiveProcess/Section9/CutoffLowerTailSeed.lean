/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import SubdiffusiveProcess.Section9.CutoffSmallDisorderTail

/-! # One-cube seed for the cutoff lower-tail bootstrap -/

namespace SubdiffusiveProcess.Section9

open MeasureTheory Homogenization
open SubdiffusiveProcess.Frozen.Assumptions

/-- Below `exp (-u)` with `u ≥ log 2`, a normalized mass differs from one by
at least one half. -/
theorem cutoffOriginCube_lowerTail_subset_centeredFailure {d : ℕ}
    (M : GMCModel d) (m : ℕ) (u : ℝ) (hu : Real.log 2 ≤ u) :
    {omega | cutoffOriginCubeAverage M m omega ≤ Real.exp (-u)} ⊆
      {omega | 1 / 2 ≤ |cutoffOriginCubeAverage M m omega - 1|} := by
  intro omega homega
  change cutoffOriginCubeAverage M m omega ≤ Real.exp (-u) at homega
  change 1 / 2 ≤ |cutoffOriginCubeAverage M m omega - 1|
  have hexp : Real.exp (-u) ≤ (1 / 2 : ℝ) := by
    calc
      Real.exp (-u) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.mpr (neg_le_neg hu)
      _ = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have hmass : cutoffOriginCubeAverage M m omega ≤ 1 / 2 := homega.trans hexp
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- A single dimensional choice of exponent and disorder threshold supplies
the uniform one-cube seed at every cutoff scale and every `u ≥ log 2`. -/
theorem exists_cutoffOriginCube_lowerTail_seed (d : ℕ) :
    ∃ cstar δzero : ℝ, 0 < cstar ∧ 0 < δzero ∧
      ∀ M : GMCModel d, M.delta ≤ δzero → ∀ m : ℕ, ∀ u : ℝ,
        Real.log 2 ≤ u →
        let p := smallDisorderExponent cstar M.delta
        2 ≤ p ∧
          M.P.toMeasure.real {omega |
              cutoffOriginCubeAverage M m omega ≤ Real.exp (-u)} ≤
            Real.exp (-p * Real.log 4) := by
  obtain ⟨cstar, δzero, hcstar, hδzero, htail⟩ :=
    exists_cutoffOriginCube_smallDisorder_tail d
  refine ⟨cstar, δzero, hcstar, hδzero, ?_⟩
  intro M hM m u hu
  obtain ⟨hp, -, hfailure⟩ := htail M hM m
  refine ⟨hp, ?_⟩
  exact (measureReal_mono
    (cutoffOriginCube_lowerTail_subset_centeredFailure M m u hu)
    (measure_ne_top M.P.toMeasure _)).trans hfailure

end SubdiffusiveProcess.Section9
