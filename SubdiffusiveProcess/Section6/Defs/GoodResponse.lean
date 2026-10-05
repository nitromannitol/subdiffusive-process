module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The response condition in the translated good event. -/
noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.GoodResponse {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (cutoff : Option ℕ) (m : ℕ) (y : Vec d) (epsilon s : ℝ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Prop :=
  ∀ j n : ℕ, j ≤ m → n + 2 ≤ j →
    ∀ z : Vec d, OnTriadicGrid n (z - y) → z - y ∈ cube d j \ cube d (j - 1) →
    ∀ e : Vec d, Homogenization.vecNormSq e = 1 →
      section6Response M n (min n (cutoff.getD n)) ω z e ≤
        epsilon ^ 2 * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8)
