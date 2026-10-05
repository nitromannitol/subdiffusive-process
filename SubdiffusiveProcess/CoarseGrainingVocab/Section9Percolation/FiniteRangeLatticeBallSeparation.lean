module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolationGeometry

@[expose] public section

/-!
# Separation of lattice balls

The annulus-crossing conclusion requires pairwise disjoint radius-`C` lattice balls, not
merely centers more than `C` apart. This file proves the sufficient `2C` separation and gives
an explicit one-dimensional counterexample to the weaker separation (centers more than `C` apart).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

open Set

noncomputable section

variable {d : ℕ}

/-- Radius-`R` lattice balls are disjoint when one coordinate of their centers is separated
by more than `2R`.

Source: the pairwise-disjoint ball conclusion.
-/
theorem latticeBallSet_disjoint_of_exists_two_mul_lt
    {v w : Lattice d} {R : ℝ}
    (hsep : ∃ i : Fin d, 2 * R < ((|v i - w i| : ℤ) : ℝ)) :
    Disjoint (latticeBallSet v R) (latticeBallSet w R) := by
  rw [Set.disjoint_left]
  intro u huV huW
  obtain ⟨i, hi⟩ := hsep
  have htriInt :
      |v i - w i| ≤ |v i - u i| + |u i - w i| := by
    calc
      |v i - w i| = |(v i - u i) + (u i - w i)| := by congr 1; omega
      _ ≤ |v i - u i| + |u i - w i| := abs_add_le _ _
  have htriReal :
      ((|v i - w i| : ℤ) : ℝ) ≤
        ((|v i - u i| : ℤ) : ℝ) + ((|u i - w i| : ℤ) : ℝ) := by
    exact_mod_cast htriInt
  have hvu : ((|v i - u i| : ℤ) : ℝ) ≤ R := by
    simpa only [abs_sub_comm] using huV i
  have huw : ((|u i - w i| : ℤ) : ℝ) ≤ R := huW i
  have : ((|v i - w i| : ℤ) : ℝ) ≤ 2 * R := by
    calc
      ((|v i - w i| : ℤ) : ℝ) ≤
          ((|v i - u i| : ℤ) : ℝ) + ((|u i - w i| : ℤ) : ℝ) := htriReal
      _ ≤ R + R := add_le_add hvu huw
      _ = 2 * R := by ring
  exact (not_lt_of_ge this) hi

/-- Separation of centers by only `C` does not imply disjointness of radius-`C` balls.

The centers `0` and `3` satisfy the proposed `C=2` center separation, while the lattice point
`1` lies in both closed radius-two balls.

Source: the ball-disjointness conclusion.
-/
theorem exists_center_separated_latticeBalls_not_disjoint :
    ∃ v w : Lattice 1,
      (∃ i : Fin 1, (2 : ℤ) < |v i - w i|) ∧
        ¬Disjoint (latticeBallSet v 2) (latticeBallSet w 2) := by
  let v : Lattice 1 := fun _ ↦ 0
  let w : Lattice 1 := fun _ ↦ 3
  let u : Lattice 1 := fun _ ↦ 1
  refine ⟨v, w, ?_, ?_⟩
  · exact ⟨0, by norm_num [v, w]⟩
  · rw [Set.not_disjoint_iff]
    refine ⟨u, ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      norm_num [latticeBallSet, InLatticeBallReal, u, v]
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      norm_num [latticeBallSet, InLatticeBallReal, u, w]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
