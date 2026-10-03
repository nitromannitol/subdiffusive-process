module

public import SubdiffusiveProcess.Frozen.Vocab.TailCoefficient

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-!
# Tail-coefficient scale algebra

These identities isolate the deterministic cutoff bookkeeping used by the
Section 4 block update.  The decomposition follows the scale-splitting pattern
in `Algsuperdiff/Section3/Provider/Homogenization/AmplitudeBridge.lean`.
-/

/-- Below the terminal cutoff, the tail coefficient has its unsimplified
prefix-times-suffix form with `min m L = m`. -/
theorem tailCoefficient_of_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {m L : ℕ} (hmL : m ≤ L)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    tailCoefficient M L m ω x =
      ahom M m * (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω x /
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M m ω x) := by
  simp only [tailCoefficient, min_eq_left hmL]

/-- At and above the terminal cutoff, the suffix cancels and the coefficient
is the deterministic scalar `ahom L`. -/
theorem tailCoefficient_of_ge {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    tailCoefficient M L m ω x = ahom M L := by
  simp only [tailCoefficient, min_eq_right hLm]
  rw [div_self (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L ω x).ne']
  ring

/-- Once both observation scales lie above the terminal cutoff, changing the
observation scale does not change the tail coefficient. -/
theorem tailCoefficient_update_above_cutoff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m n : ℕ}
    (hLm : L ≤ m) (hLn : L ≤ n)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    tailCoefficient M L n ω x = tailCoefficient M L m ω x := by
  rw [tailCoefficient_of_ge M hLn, tailCoefficient_of_ge M hLm]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
