module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

open scoped BigOperators

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The second field condition in the translated good event. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.GoodFieldTwo {d : ℕ} (m : ℕ) (y : Vec d) (s : ℝ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) : Prop :=
  ∀ j : ℕ,
    supNormOn (translatedCube d (m + 1 + j) y) (fun x ↦
      (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i x|) +
        ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i y|) else 1) ≤
      6 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)

