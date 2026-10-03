module

public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper



def d_good_events {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (y : Vec d)
    (epsilon s : ℝ) : Set (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :=
  {ω | (∀ j : ℕ,
        (∑ i ∈ Finset.Icc (m - j) (m + j),
          supNormOn (translatedCube d (m + 1 + j) y) (fun x ↦
            |ω i x| + (3 : ℝ) ^ i * Homogenization.euclideanNorm (shellGradient (ω i) x))) ≤
          epsilon * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)) ∧
      (∀ j : ℕ,
        supNormOn (translatedCube d (m + 1 + j) y) (fun x ↦
          (∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |ω i x|) +
            ∏' i : ℕ, if m + j ≤ i then Real.exp (4 * |ω i x - ω i y|) else 1) ≤
          6 * (3 : ℝ) ^ ((s * (j : ℝ)) / 8)) ∧
      (∀ j n : ℕ, j ≤ m → n + 2 ≤ j →
        ∀ z : Vec d, OnTriadicGrid n (z - y) → z - y ∈ cube d j \ cube d (j - 1) →
        ∀ e : Vec d, Homogenization.vecNormSq e = 1 →
          section6Response M n n ω z e ≤
            epsilon ^ 2 * (3 : ℝ) ^ ((s * ((m : ℝ) - (n : ℝ))) / 8))}

end Paper
