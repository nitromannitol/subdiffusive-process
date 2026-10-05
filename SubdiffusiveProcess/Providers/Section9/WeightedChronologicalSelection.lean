
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedChronologicalSelectionCount

@[expose] public section

/-!
# Provider for the chronological-selection lemma

Statement file `SubdiffusiveProcess/Section9/WeightedChronologicalSelection.lean`.

The statement below is the block verbatim, under `SubdiffusiveProcess.Providers.Section9`.
Everything is sample-wise and measure-free except the two stopping-time clauses,
which are filtration-structural.

The five clauses are the five repairs of the block.

* **Stopping times**: `stopping_induction`.  The event `{hitAfter ≤ u}` for a
  *closed* target after a stopping time is read off the countably many rational
  samples in `(S, u]` plus the endpoint `u`; the random target is handled by
  partitioning over the countable set of histories `List (WithTop ℕ)`, on each of
  which the target is deterministic, and the refinement from one history to the
  next is stopped-coordinate measurability applied to the Borel fibres of the
  selector.  No right-continuity is used.
* **Alternation**: `entrance_le_departure`, `departure_le_entrance_succ`.
  Both are `le_sInf`/`sInf_le` on the defining infima.
* **Selection**: `exists_selected`.  A finite entrance is attained because
the target is closed (this fails for open quarters),
  only finitely many active quarters contain the attained point, so the source
  order has a least candidate there, and the closed quarter sits strictly inside
  the open cube, which makes the residence nondegenerate.
* **Count**: `entrance_le_of_card`.  Each comparison cube is charged either
  to the stage that removed it from the active family or to the residence
  containing its visit; a selector receives at most `D` charges, so `N ≤ m D`.
  The separation hypothesis on `S` is not needed for the charging bound.
* **Containment**: `departure_le_exitTime`.

`section9CrossingSteps` is not consumed here (percolation consumption: none).
-/

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

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.ChronologicalSelection

theorem SubdiffusiveProcess.Providers.Section9.weighted_chronological_selection
    (d : ℕ) (_hd : 2 ≤ d) (order : LinearOrder ℕ) (U : ℕ → Cube d) (F : Set ℕ) (A : ℝ) (hA : 1 ≤ A)
    (hside : ∀ i ∈ F, 0 < (U i).2)
    (hloc : LocallyFinite (fun i : F => cubeSet (U i)))
    (D : ℕ) (hD : 1 ≤ D)
    (hdegree : ∀ i ∈ F, {j : ℕ | j ∈ F ∧ ¬ Disjoint
      (centeredAxisCube (U i).1 (A * (U i).2))
      (centeredAxisCube (U j).1 (A * (U j).2))}.encard ≤ D)
    (theta0 : ContinuousPath (Vec d) → ℝ≥0∞)
    (htheta0 : IsStoppingTime ContinuousPath.canonicalFiltration theta0) :
    (∀ i : ℕ,
      IsStoppingTime ContinuousPath.canonicalFiltration
        (fun p => entrance order U A F (theta0 p) i p) ∧
      IsStoppingTime ContinuousPath.canonicalFiltration
        (fun p => departure order U A F (theta0 p) i p)) ∧
    (∀ (i : ℕ) (p : ContinuousPath (Vec d)),
      entrance order U A F (theta0 p) i p ≤ departure order U A F (theta0 p) i p ∧
      departure order U A F (theta0 p) i p ≤ entrance order U A F (theta0 p) (i + 1) p) ∧
    (∀ (p : ContinuousPath (Vec d)) (i : ℕ), 1 ≤ i →
      entrance order U A F (theta0 p) i p < ⊤ →
      ∃ j ∈ F, (greedyRun order U A F (theta0 p) p i).2.2.2 = (j : WithTop ℕ) ∧
        p (entrance order U A F (theta0 p) i p).toNNReal ∈ closedQuarter (U j) ∧
        entrance order U A F (theta0 p) i p < departure order U A F (theta0 p) i p) ∧
    (∀ (p : ContinuousPath (Vec d)) (theta : ℝ≥0∞), theta0 p ≤ theta →
      ∀ S : Finset ℕ, (∀ i ∈ S, i ∈ F) →
        Set.Pairwise (S : Set ℕ) (fun i j => Disjoint
          (centeredAxisCube (U i).1 (A * (U i).2))
          (centeredAxisCube (U j).1 (A * (U j).2))) →
        (∀ i ∈ S, ∃ t : ℝ≥0, theta0 p ≤ (t : ℝ≥0∞) ∧
          (t : ℝ≥0∞) ≤ theta ∧ p t ∈ middleQuarter (U i)) →
        ∀ k : ℕ, 1 ≤ k → k * D ≤ S.card →
          entrance order U A F (theta0 p) k p ≤ theta) ∧
    (∀ (p : ContinuousPath (Vec d)) (O : Set (Vec d)), IsOpen O →
      (∀ i ∈ F, closure (cubeSet (U i)) ⊆ O) →
      ∀ (theta : ℝ≥0∞) (i : ℕ), 1 ≤ i →
        entrance order U A F (theta0 p) i p ≤ theta → theta ≤ ContinuousPath.exitTime O p →
        departure order U A F (theta0 p) i p ≤ ContinuousPath.exitTime O p ∧
        (departure order U A F (theta0 p) i p = ContinuousPath.exitTime O p →
          departure order U A F (theta0 p) i p = ⊤ ∧ ContinuousPath.exitTime O p = ⊤))
    := by
  refine ⟨fun i => ⟨(stopping_induction order U A F hside hloc theta0 htheta0 i).1,
      (stopping_induction order U A F hside hloc theta0 htheta0 i).2.1⟩,
    fun i p => ⟨entrance_le_departure order U A F (theta0 p) p i,
      departure_le_entrance_succ order U A F (theta0 p) p i⟩,
    fun p i hi hfin => ?_, fun p theta _ S hSF _ hvis k hk hkD => ?_,
    fun p O hO hcl theta i hi h1 h2 => ?_⟩
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    exact exists_selected order U A F hside hloc (theta0 p) p n hfin
  · exact entrance_le_of_card order U A hA F hside hloc D hD hdegree (theta0 p) p theta S hSF
      hvis k hk hkD
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    exact departure_le_exitTime order U A F hside hloc (theta0 p) p O hO hcl theta n h1 h2

end
