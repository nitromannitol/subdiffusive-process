module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.InteriorWindows

@[expose] public section

/-!
# The interior gate at every scale below the domain

`Geometry.not_boundaryTouches_of_interior_descendant` gives the gate at scales
*above* the centre's own scale.  The Campanato iteration also needs it at scales
*below*, since its base scale `ell` may be smaller than the scale `n` at which
the grid centre sits inside the frozen base point's window.

Non-touching is monotone downwards in the scale — a smaller window has a smaller
closure — so one lemma covers both directions.  The result,
`interiorGate_of_descendant`, is the form the interior iteration consumes: at an
interior base point, *every* window scale at least five below the domain is
non-touching.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Non-touching passes to smaller windows. -/
theorem not_boundaryTouches_of_le {m j l : ℤ} {x : Vec d} (hjl : j ≤ l)
    (h : ¬ BoundaryTouches (truncatedCube d m l x) (cube d m)) :
    ¬ BoundaryTouches (truncatedCube d m j x) (cube d m) := by
  intro htouch
  apply h
  unfold BoundaryTouches at htouch ⊢
  rw [← Set.nonempty_iff_ne_empty] at htouch ⊢
  obtain ⟨q, hqclosure, hqfrontier⟩ := htouch
  exact ⟨q, closure_mono (truncatedCube_mono d m x hjl) hqclosure, hqfrontier⟩

/-- **The interior gate at every admissible scale.**  If the frozen base point
`x` is one scale inside the domain and the centre `y` sits in its scale-`n`
window, then no window around `y` at any scale at least five below the domain
touches the boundary. -/
theorem interiorGate_of_descendant {m n : ℤ} {x y : Vec d}
    (hx : x ∈ cube d (m - 1)) (hy : y ∈ truncatedCube d m n x) (hn : n ≤ m - 5)
    {j : ℤ} (hj : j ≤ m - 5) :
    ¬ BoundaryTouches (truncatedCube d m j y) (cube d m) := by
  rcases le_total j n with hjn | hnj
  · exact not_boundaryTouches_of_le hjn
      (not_boundaryTouches_of_interior_descendant hx hy le_rfl hn)
  · exact not_boundaryTouches_of_interior_descendant hx hy hnj hj

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
