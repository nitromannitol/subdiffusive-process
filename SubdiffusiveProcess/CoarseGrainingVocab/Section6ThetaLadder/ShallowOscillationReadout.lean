module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.OscillationSubsetReadout

@[expose] public section

/-!
# Theta ladder: bounded-depth oscillation readout

At a bounded target depth the desired geometric factor is paid by a fixed
constant.  The analytic input is only literal oscillation monotonicity from
the target to the compact collar.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Topology Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ}

/-- Absorb every depth `j ≤ J` into one fixed oscillation constant. -/
theorem oscillationOn_le_decay_of_boundedDepth
    {S T : Set (Vec d)} {f : Vec d → ℝ} {j J : ℕ} {C c : ℝ}
    (hS : S.Nonempty) (hT : T.Nonempty) (hsub : S ⊆ T)
    (hbdd : BddAbove {q : ℝ | ∃ x ∈ T, ∃ y ∈ T,
      q = |f x - f y|})
    (hc : 0 ≤ c) (hjJ : j ≤ J)
    (hC : 1 ≤ C * (3 : ℝ) ^ (-c * (J : ℝ))) :
    oscillationOn S f ≤
      C * (3 : ℝ) ^ (-c * (j : ℝ)) * oscillationOn T f := by
  have hmono := oscillationOn_le_of_subset_of_bddAbove hS hsub hbdd
  have hosc0 : 0 ≤ oscillationOn T f := by
    unfold oscillationOn
    have hzero : (0 : ℝ) ∈ {q : ℝ | ∃ x ∈ T, ∃ y ∈ T,
        q = |f x - f y|} := by
      obtain ⟨x, hx⟩ := hT
      exact ⟨x, hx, x, hx, by simp⟩
    exact le_csSup hbdd hzero
  have hjJR : (j : ℝ) ≤ (J : ℝ) := by exact_mod_cast hjJ
  have hexp : -c * (J : ℝ) ≤ -c * (j : ℝ) := by
    nlinarith
  have hpow : (3 : ℝ) ^ (-c * (J : ℝ)) ≤
      (3 : ℝ) ^ (-c * (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hfactor : 1 ≤ C * (3 : ℝ) ^ (-c * (j : ℝ)) :=
    hC.trans (mul_le_mul_of_nonneg_left hpow (by
      have hp : 0 < (3 : ℝ) ^ (-c * (J : ℝ)) := by positivity
      nlinarith))
  calc
    oscillationOn S f ≤ oscillationOn T f := hmono
    _ = 1 * oscillationOn T f := by ring
    _ ≤ C * (3 : ℝ) ^ (-c * (j : ℝ)) * oscillationOn T f :=
      mul_le_mul_of_nonneg_right hfactor hosc0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
