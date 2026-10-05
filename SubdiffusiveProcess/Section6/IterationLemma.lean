module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Support
public import SubdiffusiveProcess.Providers.Section6.IterationLemma

@[expose] public section

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable


theorem SubdiffusiveProcess.Section6.iteration_lemma (d : ℕ) :
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

:= SubdiffusiveProcess.Providers.Section6.iteration_lemma d
