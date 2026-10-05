module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
public import SubdiffusiveProcess.Providers.Section9.WeightedPathDiscretization
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput (section9CrossingSteps)
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem SubdiffusiveProcess.Section9.weighted_path_discretization (d : ℕ) (hd : 2 ≤ d) :
    section9CrossingSteps d = 1 ∧
    ∀ A : ℕ, 1 ≤ A → ∃ c : ℝ, 0 < c ∧
      ∀ r : ℝ, 0 < r →
        (∀ (a : Fin d → Fin 8) (i : Fin d),
          0 ≤ gridShift d r a i ∧ gridShift d r a i < r) ∧
        (∀ k : Lattice d, ∃ (a : Fin d → Fin 8) (z : Lattice d),
          (gridCube d r k).1 = gridShift d r a + fun i => r * (z i : ℝ)) ∧
        ∀ Q : Lattice d → Cube d,
          (∀ k, (Q k).1 = (gridCube d r k).1) →
          (∀ k, r ≤ (Q k).2 ∧ (Q k).2 ≤ 3 * r) →
          (∀ k : Lattice d,
            {j : Lattice d | ¬ Disjoint
              (centeredAxisCube (Q k).1 (A * (Q k).2))
              (centeredAxisCube (Q j).1 (A * (Q j).2))}.encard ≤
                ((48 * A + 1) ^ d : ℕ)) ∧
          ∀ (z : Vec d) (s R : ℝ), 0 ≤ s → (A : ℝ) * r ≤ R →
            ∀ (p : ContinuousPath (Vec d)) (a b : ℝ≥0), a ≤ b →
              euclideanNorm (p a - z) ≤ s → s + R ≤ euclideanNorm (p b - z) →
              ∃ (N : ℕ) (q : ℕ → Lattice d) (t : ℕ → ℝ≥0),
                IsJStepPath (section9CrossingSteps d) q N ∧
                Set.InjOn q (Set.Icc 0 N) ∧ MonotoneOn t (Set.Icc 0 N) ∧
                a ≤ t 0 ∧ t N ≤ b ∧
                p a ∈ cubeSet (Q (q 0)) ∧ p b ∈ cubeSet (Q (q N)) ∧
                (∀ i ≤ N, p (t i) ∈ middleQuarter (Q (q i))) ∧
                (∀ i < N, ¬ Disjoint
                  (centeredAxisCube (Q (q i)).1 (A * (Q (q i)).2))
                  (centeredAxisCube (Q (q (i + 1))).1 (A * (Q (q (i + 1))).2))) ∧
                ∀ good : Set (Lattice d), ∃ selected : Finset ℕ,
                  (∀ i ∈ selected, i ≤ N ∧ q i ∈ good) ∧
                  Set.Pairwise (selected : Set ℕ) (fun i j => Disjoint
                    (centeredAxisCube (Q (q i)).1 (A * (Q (q i)).2))
                    (centeredAxisCube (Q (q j)).1 (A * (Q (q j)).2))) ∧
                  c * (((Finset.range (N + 1)).filter (fun i => q i ∈ good)).card : ℝ) ≤
                    (selected.card : ℝ)
:= SubdiffusiveProcess.Providers.Section9.weighted_path_discretization d hd
