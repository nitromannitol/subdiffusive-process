module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeCalibration
@[expose] public section

/-! Dimension-only constants and the admissible geometry depth are chosen before the model and before the finite test catalogue. -/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem exists_goodCube_selected_scalar_parameters
    (d : ℕ) (eta : ℝ) (heta : 0 < eta) (A CE : ℝ) (hA : 1 ≤ A) :
    ∃ (C cShell : ℝ) (Cdep j1 : ℕ) (r : ℤ),
      0 < C ∧ 0 < cShell ∧ A ≤ C ∧ CE * A ^ CE ≤ C ∧
      1 < (3 : ℝ) ^ r ∧ ((shellCoverShifts d r).card : ℝ) ≤ C ∧ 1 ≤ C ∧
      1 + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ) ∧
      cShell ≤ 1 / 3 ∧ cShell ≤ Real.sqrt layerTailConstant ∧
      2 * ((1 + Real.log 2) ^ (2 : ℝ)⁻¹ * cShell) ≤ 1 ∧
      2 ≤ j1 ∧ C * (3 : ℝ) ^ (-(3 * (j1 : ℝ) / 2)) ≤ eta / 2 := by
  obtain ⟨r, cShell, hc1, hBr, hc3, hcK, hstep⟩ :=
    exists_goodCubeConstants 1 1 one_pos
  have hcK1 : cShell ≤ Real.sqrt layerTailConstant := by simpa using hcK
  set C : ℝ := max (max A (CE * A ^ CE)) (max 1 ((shellCoverShifts d r).card : ℝ)) with hCdef
  have hAC : A ≤ C := (le_max_left A (CE * A ^ CE)).trans (le_max_left _ _)
  have hCEC : CE * A ^ CE ≤ C := (le_max_right A (CE * A ^ CE)).trans (le_max_left _ _)
  have h1C : (1 : ℝ) ≤ C :=
    (le_max_left (1 : ℝ) ((shellCoverShifts d r).card : ℝ)).trans (le_max_right _ _)
  have hNC : ((shellCoverShifts d r).card : ℝ) ≤ C :=
    (le_max_right (1 : ℝ) _).trans (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le (lt_of_lt_of_le one_pos hA) hAC
  set Cdep : ℕ := ⌈1 + Real.sqrt (d : ℝ)⌉₊ with hCdepdef
  have hCdep : 1 + Real.sqrt (d : ℝ) ≤ (Cdep : ℝ) := Nat.le_ceil _
  obtain ⟨j1, hj1, hsmall⟩ := exists_smallness_depth C eta hC heta
  exact ⟨C, cShell, Cdep, j1, r, hC, hc1, hAC, hCEC, hBr, hNC, h1C, hCdep,
    hc3, hcK1, hstep, hj1, hsmall⟩
end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
