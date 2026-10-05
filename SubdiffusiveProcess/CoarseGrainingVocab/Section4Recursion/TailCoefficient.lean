module

public import SubdiffusiveProcess.Vocab.TailCoefficient

@[expose] public section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-!
# Tail-coefficient scale algebra

These identities isolate the deterministic cutoff bookkeeping used by the
Section 4 block update. The decomposition splits the scales.
-/

/-- Below the terminal cutoff, the tail coefficient has its unsimplified
prefix-times-suffix form with `min m L = m`. -/
theorem tailCoefficient_of_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m L : ℕ} (hmL : m ≤ L)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    tailCoefficient M L m ω x =
      ahom M m * (_root_.SubdiffusiveProcess.Model.aCutoff M L ω x /
        _root_.SubdiffusiveProcess.Model.aCutoff M m ω x) := by
  simp only [tailCoefficient, min_eq_left hmL]

/-- At and above the terminal cutoff, the suffix cancels and the coefficient
is the deterministic scalar `ahom L`. -/
theorem tailCoefficient_of_ge {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    tailCoefficient M L m ω x = ahom M L := by
  simp only [tailCoefficient, min_eq_right hLm]
  rw [div_self (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L ω x).ne']
  ring

/-- Once both observation scales lie above the terminal cutoff, changing the
observation scale does not change the tail coefficient. -/
theorem tailCoefficient_update_above_cutoff {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hLm : L ≤ m) (hLn : L ≤ n)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    tailCoefficient M L n ω x = tailCoefficient M L m ω x := by
  rw [tailCoefficient_of_ge M hLn, tailCoefficient_of_ge M hLm]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
