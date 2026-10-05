
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedPathDiscretizationChain
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedPathDiscretizationWalk

@[expose] public section

/-!
# Weighted path discretization

The statement is the block of
`SubdiffusiveProcess/Section9/WeightedPathDiscretization.lean`.

The statement below is the block verbatim, under
`SubdiffusiveProcess.Providers.Section9`.  Everything is deterministic: no measure, no event
law, no percolation input.

The proof follows the manuscript.

* The `8^d` translates of `r ℤ^d` inside the fine grid `(r/8) ℤ^d`
   give the shift bounds and the decomposition clause
  (`exists_gridShift_decomposition`).
* Intersecting `A`-dilates of cubes with side in `[r,3r]` centred on the fine
  grid have fine indices within `24 A` in each coordinate, so a closed
  neighbourhood in the intersection graph has at most `(48A+1)^d` elements
  (`encard_intersecting_le`).  This is the "finite-degree periodic graph".
* The path is sampled along a uniform time partition of mesh below the modulus
  of continuity at `r/32`, and each sample is rounded to the nearest fine-grid
  point (`exists_sampled_grid_walk`).  The rounding error `r/16` is strictly
  below the half-side `r/8` of every admissible middle quarter, so each sample
  lies in the middle quarter of its cube, and consecutive fine indices differ
  by at most one in each coordinate: this is `section9CrossingSteps d = 1`

* Chronological loop erasure (`exists_injOn_subwalk`: retained occurrences in increasing order, not first-ever
  visits) makes the walk injective while keeping its endpoints, its adjacency
  and its middle-quarter visits.
* A maximal subfamily of pairwise disjoint dilates over the good indices has
  at least `(48A+1)^{-d}` of them (`exists_pairwise_disjoint_selection`), which
  is the dimensional fraction `c(d,A)` of the statement.
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

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

theorem SubdiffusiveProcess.Providers.Section9.weighted_path_discretization (d : ℕ) (_hd : 2 ≤ d) :
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
                    (selected.card : ℝ) := by
  refine ⟨SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps_eq_one d, ?_⟩
  intro A hA
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hDpos : (0 : ℕ) < (48 * A + 1) ^ d := Nat.pow_pos (by omega)
  have hDposR : (0 : ℝ) < (((48 * A + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hDpos
  refine ⟨((((48 * A + 1) ^ d : ℕ) : ℝ))⁻¹, inv_pos.mpr hDposR, ?_⟩
  intro r hr
  refine ⟨?_, fun k => exists_gridShift_decomposition r k, ?_⟩
  · intro a i
    have h8 : (((a i : ℕ) : ℝ)) < 8 := by exact_mod_cast (a i).isLt
    have h0 : (0 : ℝ) ≤ ((a i : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor
    · simp only [gridShift]
      positivity
    · simp only [gridShift]
      nlinarith
  · intro Q hQc hQs
    have hcentre : ∀ (m : Lattice d) (i : Fin d), (Q m).1 i = r / 8 * (m i : ℝ) := by
      intro m i
      simpa [gridCube] using congrFun (hQc m) i
    have hsidepos : ∀ m : Lattice d, (0 : ℝ) < (A : ℝ) * (Q m).2 := by
      intro m
      have := (hQs m).1
      nlinarith
    have hdeg := encard_intersecting_le hr hA Q hQc hQs
    refine ⟨hdeg, ?_⟩
    intro z s R hs hR p a b hab hpa hpb
    obtain ⟨M, k, u, hu0, huM, hmonoU, hstepk, hquarterk, hcube0, hcubeM⟩ :=
      exists_sampled_grid_walk hr Q hQc hQs p a b hab
    obtain ⟨N, q, t, hinj, hadj, hmono, hphi, hq0, hqN, ht0, htN⟩ :=
      exists_injOn_subwalk (fun x y : Lattice d => latticeDist x y ≤ 1)
        (fun (v : Lattice d) (tau : ℝ≥0) => p tau ∈ middleQuarter (Q v)) M k u
        hstepk (hmonoU.monotoneOn _) hquarterk
    refine ⟨N, q, t, hadj, hinj, hmono, ?_, ?_, ?_, ?_, hphi, ?_, ?_⟩
    · exact le_of_eq (ht0.trans hu0).symm
    · exact huM ▸ htN
    · exact hq0 ▸ hcube0
    · exact hqN ▸ hcubeM
    · intro i hi
      refine not_disjoint_centeredAxisCube (hsidepos (q i)) fun j => ?_
      have hb := latticeDist_le_iff.mp (hadj i hi) j
      have hnat : ((q i j - q (i + 1) j).natAbs : ℝ) = |((q i j : ℝ) - (q (i + 1) j : ℝ))| := by
        have := Nat.cast_natAbs (α := ℝ) (q i j - q (i + 1) j)
        push_cast at this
        exact this
      have hz : |((q i j : ℝ) - (q (i + 1) j : ℝ))| ≤ 1 := by
        rw [← hnat]
        exact_mod_cast hb
      have heq : (Q (q i)).1 j - (Q (q (i + 1))).1 j
          = r / 8 * ((q i j : ℝ) - (q (i + 1) j : ℝ)) := by
        rw [hcentre, hcentre]; ring
      rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < r / 8)]
      have h2 := (hQs (q (i + 1))).1
      nlinarith
    · intro good
      obtain ⟨S, hSG, hSpair, hScard⟩ :=
        exists_pairwise_disjoint_selection (D := (48 * A + 1) ^ d)
          (fun l => centeredAxisCube (Q l).1 (A * (Q l).2))
          (fun l => nonempty_centeredAxisCube (hsidepos l)) hdeg hinj
          ((Finset.range (N + 1)).filter (fun i => q i ∈ good))
          (fun i hi => Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
      refine ⟨S, ?_, hSpair, ?_⟩
      · intro i hi
        have hmem := Finset.mem_filter.mp (hSG hi)
        exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem.1), hmem.2⟩
      · rw [inv_mul_le_iff₀ hDposR]
        exact_mod_cast hScard

end
