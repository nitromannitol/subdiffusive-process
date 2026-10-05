module

public import SubdiffusiveProcess.Section6.IterationLemma

@[expose] public section

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Paper

/-- Tick list of carried inputs and their manuscript supplier, `l.iteration.lemma.GMC`:
- Concrete measurable bounded nested domains and both cube inclusions.
- Genuine L2 function, finite bad interval, and exact affine minimizers.
- Nonnegative errors and the one-step inequality.
- The constant precedes h, theta, scale indices, domains and data.
- The exact accumulated exponent and both estimates, including the bounded-error parameter.

The complete proposition of the frozen deterministic iteration lemma
`SubdiffusiveProcess.Section6.iteration_lemma` (item (iv) of the deterministic remark,
`l.iteration.lemma.GMC`), with the theorem name and the `d` binder stripped. -/
def deterministic_iteration_input (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 0 < h → ∀ theta ∈ Set.Ioo (0 : ℝ) 1,
    theta ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) → ∀ n m : ℤ, n < m →
    ∀ U : ℤ → Set (Vec d),
      (∀ j, MeasurableSet (U j) ∧ Bornology.IsBounded (U j)) →
      (∀ j ≤ m, U (j - 1) ⊆ U j) →
      (∀ j ≤ m, ∃ x y : Vec d,
        translatedCube d (j - 2) x ⊆ U j ∧ U j ⊆ translatedCube d j y) →
      ∀ u : Vec d → ℝ, MemLp u 2 (volume.restrict (U m)) →
      ∀ bad : Finset ℤ, bad ⊆ Finset.Icc n m →
      ∀ epsilon defect : ℤ → ℝ,
        (∀ j ∈ Finset.Icc n m, 0 ≤ epsilon j ∧ 0 ≤ defect j) →
        ∀ fit : ℤ → Affine d,
          (∀ j ≤ m, fit j ∈ affineMinimizers (U j) u) →
          (∀ j ∈ Finset.Icc n m, j ∉ bad →
            excess (j - h) (U (j - h)) u ≤ theta ^ h * excess j (U j) u +
              epsilon j * Real.sqrt (vecNormSq (fit j).slope) + defect j) →
          let A := C * (h + 1) * (bad.card + 1) +
            C * ∑ j ∈ Finset.Icc n m, epsilon j
          (3 : ℝ) ^ (-n) * normalizedL2On (U n)
              (fun x => u x - averageOn (U n) u) ≤
            Real.exp A * ((3 : ℝ) ^ (-m) * normalizedL2On (U m)
              (fun x => u x - averageOn (U m) u) +
              ∑ j ∈ Finset.Icc n m, defect j) ∧
          ∀ R : ℝ, 0 ≤ R → (∀ j ∈ Finset.Icc n m, epsilon j ≤ R) →
            excess n (U n) u ≤
              theta ^ (-C * (h + 1) * (bad.card + 1)) * Real.exp A *
                (theta ^ (m - n) * excess m (U m) u +
                  R * (3 : ℝ) ^ (-m) * normalizedL2On (U m)
                    (fun x => u x - averageOn (U m) u) +
                  (1 + R) * ∑ j ∈ Finset.Icc n m, defect j)

end SubdiffusiveProcess.Paper
