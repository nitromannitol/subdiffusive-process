import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

open scoped BigOperators

open SubdiffusiveProcess.CoarseGrainingVocab

/-- The first field condition in the translated good event. -/

noncomputable def SubdiffusiveProcess.CoarseGrainingVocab.GoodFieldOne {d : ℕ} (m : ℕ) (y : Vec d)
    (epsilon s : ℝ) (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : Prop :=
  ∀ j : ℕ,
    Finset.sum (Finset.Icc (m - j) (m + j)) (fun i ↦
        supNormOn (translatedCube d (m + 1 + j) y) (fun x ↦
          |ω i x| + (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (ω i) x))) ≤
      epsilon * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)

