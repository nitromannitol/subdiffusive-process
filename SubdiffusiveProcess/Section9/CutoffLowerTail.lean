/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SubdiffusiveProcess.Section9.CutoffLowerTailRecursion
public import SubdiffusiveProcess.Section9.CutoffLowerTailSeed
public import SubdiffusiveProcess.Section9.SmallDisorderBootstrap

@[expose] public section

/-! # Uniform lower tail for finite-cutoff cube masses -/

namespace SubdiffusiveProcess.Section9

open MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions

/-- The actual finite-cutoff masses have a uniform exponential lower tail at
the small-disorder exponent. -/
theorem exists_cutoffLowerTailSup_smallDisorder (d : ℕ) :
    ∃ cstar a δzero : ℝ, 0 < cstar ∧ 0 < a ∧ 0 < δzero ∧
      ∀ M : GMCModel d, M.delta ≤ δzero → ∀ u : ℝ, Real.log 2 ≤ u →
        let p := smallDisorderExponent cstar M.delta
        cutoffLowerTailSup M u ≤ Real.exp (-a * p * u) := by
  obtain ⟨C, cGaussian, hC, hcGaussian, hrec⟩ :=
    exists_cutoffLowerTailSup_recursion d
  obtain ⟨cstar, δseed, hcstar, hδseed, hseed⟩ :=
    exists_cutoffOriginCube_lowerTail_seed d
  let ell : ℝ := Real.log 2
  let U : ℝ := max (2 * max C 1) (max 1 ((4 / 3 : ℝ) * ell))
  let a : ℝ := Real.log 4 / (2 * U)
  have hUpos : 0 < U := by
    dsimp only [U]
    exact zero_lt_one.trans_le ((le_max_left 1 _).trans (le_max_right _ _))
  have ha : 0 < a := div_pos (Real.log_pos (by norm_num)) (mul_pos (by norm_num) hUpos)
  have hUC : 2 * max C 1 ≤ U := le_max_left _ _
  have hUell : (4 / 3 : ℝ) * ell ≤ U :=
    (le_max_right 1 _).trans (le_max_right _ _)
  obtain ⟨δboot, hδboot, hbudget⟩ :=
    exists_smallDisorderBootstrap_threshold hcstar ha hUpos hcGaussian C
  let δzero := min δseed δboot
  have hδzero : 0 < δzero := lt_min hδseed hδboot
  refine ⟨cstar, a, δzero, hcstar, ha, hδzero, ?_⟩
  intro M hM u hu
  have hMseed : M.delta ≤ δseed := hM.trans (min_le_left _ _)
  have hMboot : M.delta ≤ δboot := hM.trans (min_le_right _ _)
  obtain ⟨hp, hslack, hrate, hlog⟩ :=
    hbudget M.delta M.shellPrefix.delta_pos hMboot
  have hp0 : 0 ≤ smallDisorderExponent cstar M.delta :=
    (by norm_num : (0 : ℝ) ≤ 2).trans hp
  apply lowerTail_geometric_bootstrap
    (cutoffLowerTailSup M)
    (fun v ↦ C * Real.exp
      (-cGaussian * max (v - C) 0 ^ 2 / M.delta ^ 2))
    ell U a (smallDisorderExponent cstar M.delta)
  · dsimp only [ell]
    exact Real.log_nonneg (by norm_num)
  · exact hUpos
  · exact hUell
  · exact fun v _ ↦ cutoffLowerTailSup_nonneg M v
  · intro v hvell hvU
    unfold cutoffLowerTailSup
    apply ciSup_le
    intro m
    obtain ⟨-, hm⟩ := hseed M hMseed m v hvell
    refine hm.trans (Real.exp_le_exp.mpr ?_)
    have haU : a * U = Real.log 4 / 2 := by
      dsimp only [a]
      field_simp [hUpos.ne']
    have hav : a * v ≤ Real.log 4 := by
      have := mul_le_mul_of_nonneg_left hvU ha.le
      rw [haU] at this
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
    nlinarith
  · intro v hUv
    simpa only [div_mul_eq_mul_div] using hrec M v (hUpos.le.trans hUv)
  · intro v hUv
    exact gaussianForcing_le_half hC.le hcGaussian M.shellPrefix.delta_pos
      hUC hUv hrate hlog
  · intro v hUv
    exact lowerTail_recursive_half (mul_nonneg ha.le hp0) hUv hslack
  · exact hu

end SubdiffusiveProcess.Section9
