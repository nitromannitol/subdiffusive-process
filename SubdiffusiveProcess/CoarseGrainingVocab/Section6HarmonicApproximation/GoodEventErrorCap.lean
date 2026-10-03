/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Transport
public import SubdiffusiveProcess.Frozen.Section6.GoodScaleMathcalE

@[expose] public section

/-!
# The local good-event cap for the Section 6 error

The harmonic-approximation statement uses the error at parameter `s / 8` and
at an arbitrary translated cube.  This module extracts the second clause of
the proved `p.good.scale.mathcal.E` export, verifies its rescaled parameter
range, and transports it from translate zero.

This is the GMC counterpart of the error-cap/reindex layer used by
`Algsuperdiff/Section4/Provider/ExcessDecay/ReindexSlot.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- On the harmonic-approximation good event, the local Section 6 error is
bounded by a dimension-only constant. -/
theorem exists_section6HomogenizationError_le_of_goodEvent :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L k : ℕ, k ≤ L →
      ∀ omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d, ∀ z : Vec d,
        omega ∈ goodEvent M none k z 1 (s / 8) →
          section6HomogenizationError M (s / 8) L k omega z ≤ C := by
  obtain ⟨C, hC, hgood⟩ := SubdiffusiveProcess.Frozen.Section6.good_scale_mathcal_e d
  refine ⟨C, hC, ?_⟩
  intro M s hs L k hkL omega z homega
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos hdelta 2)).trans_le hs.1
  have htRange : s / 8 ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) := by
    constructor
    · linarith [hs.1]
    · linarith [hs.2]
  have hepsilonRange : (1 : ℝ) ∈
      Set.Icc ((s / 8)⁻¹ * M.delta ^ 2) 1 := by
    constructor
    · have hsdelta : 8 * M.delta ^ 2 ≤ s := by linarith [hs.1]
      have ht0 : 0 < s / 8 := by positivity
      rw [inv_mul_le_iff₀ ht0]
      norm_num [div_eq_mul_inv]
      nlinarith [hsdelta]
    · exact le_rfl
  refine Section6Covariance.section6HomogenizationError_le_of_translate_zero ?_ z homega
  intro nu hnu
  simpa using (hgood M (s / 8) htRange L k hkL nu).2 1 hepsilonRange hnu

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
