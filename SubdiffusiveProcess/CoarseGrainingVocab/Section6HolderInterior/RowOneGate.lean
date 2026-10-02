import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.RowOneWindows




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The grid centre lies in the domain. -/
theorem rowOne_centre_mem {m n : ℕ} {x y : Vec d}
    (hy : y ∈ truncatedCube d (m : ℤ) (n : ℤ) x) : y ∈ cube d (m : ℤ) :=
  Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) (n : ℤ) x hy

/-- **The gate, in the shape the gated estimate consumes.**  Every window scale
`j ≤ top` around the grid centre is non-touching, because the frozen stopping
hypothesis already puts the base point five scales inside. -/
theorem rowOne_gate {m n top : ℕ} {x y : Vec d}
    (hx : x ∈ cube d ((m : ℤ) - 1)) (hy : y ∈ truncatedCube d (m : ℤ) (n : ℤ) x)
    (hn : (n : ℤ) ≤ (m : ℤ) - 5) (htop : top + 5 ≤ m) :
    ∀ j : ℕ, j ≤ top →
      ¬ BoundaryTouches (truncatedCube d (m : ℤ) (j : ℤ) y) (cube d (m : ℤ)) := by
  intro j hj
  exact interiorGate_of_descendant hx hy hn (by omega)

/-- The stopped controls needed at the base scale follow from the frozen
hypothesis at the larger scale. -/
theorem rowOne_stopping_at_base
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (alpha lambda epsilon : ℝ)
    (step m n ell : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hstop : (Section6Stopping.measurableHolderStoppingScale M alpha lambda
        epsilon step m omega : ℤ) ≤ (m : ℤ) - (n : ℤ))
    (hell : ell ≤ n) :
    (Section6Stopping.measurableHolderStoppingScale M alpha lambda epsilon
      step m omega : ℤ) ≤ (m : ℤ) - (ell : ℤ) := by
  have : (ell : ℤ) ≤ (n : ℤ) := by exact_mod_cast hell
  omega

/-- The base scale is itself five scales inside, so the deep branch's top depth
`m - 5` is admissible above it. -/
theorem rowOne_base_lt_top {m n ell : ℕ}
    (hn : (n : ℤ) ≤ (m : ℤ) - 5) (hell : ell ≤ n)
    (hdeep : 5 < (m : ℝ) - (ell : ℝ)) :
    ell < m - 5 ∧ (m - 5) + 5 ≤ m := by
  have hellZ : (ell : ℤ) ≤ (n : ℤ) := by exact_mod_cast hell
  have hdeepZ : (ell : ℤ) + 5 < (m : ℤ) := by
    have : ((ell : ℝ) + 5) < (m : ℝ) := by linarith
    exact_mod_cast this
  omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
