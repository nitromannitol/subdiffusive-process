module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.InteriorBoundaryGate

@[expose] public section

/-!
# Interior Hölder regularity: the geometric core

The interior re-cut of the cutoff Hölder anchor restricts the
base points to `cube d (m-1)` instead of `cube d m`.  The single
geometric fact behind that restriction is proved once here and reused by every
step of the interior ladder:

> a truncated window `truncatedCube d m n x` whose centre `x` lies one scale
> inside the domain and whose scale is at least five below the domain scale
> never touches `∂ □_m`.

The `top`-window form is already available as
`Section6Holder.not_boundaryTouches_top_of_interior`; the specializations below
are the ones the interior ladder actually consumes, together with the two
indicator rewrites that delete the printed boundary summands.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Base points one scale inside the domain are domain points. -/
theorem mem_cube_of_mem_cube_sub_one {m : ℤ} {x : Vec d}
    (hx : x ∈ cube d (m - 1)) : x ∈ cube d m :=
  cube_subset_cube_of_le (by omega) hx

/-- **The interior gate.**  A window centred one scale inside the domain, at a
scale at least five below the domain scale, never touches the boundary. -/
theorem not_boundaryTouches_of_interior {m n : ℤ} {x : Vec d}
    (hx : x ∈ cube d (m - 1)) (hn : n ≤ m - 5) :
    ¬ BoundaryTouches (truncatedCube d m n x) (cube d m) :=
  Section6Holder.not_boundaryTouches_top_of_interior hx
    (mem_truncatedCube_self n (mem_cube_of_mem_cube_sub_one hx)) le_rfl hn

/-- Descendant windows of an interior base point are interior too. -/
theorem not_boundaryTouches_of_interior_descendant {m n top : ℤ} {x y : Vec d}
    (hx : x ∈ cube d (m - 1)) (hy : y ∈ truncatedCube d m n x)
    (hntop : n ≤ top) (htop : top ≤ m - 5) :
    ¬ BoundaryTouches (truncatedCube d m top y) (cube d m) :=
  Section6Holder.not_boundaryTouches_top_of_interior hx hy hntop htop

/-- The printed `BoundaryTouches` indicator vanishes on the interior branch. -/
theorem boundaryTouches_indicator_eq_zero {m n : ℤ} {x : Vec d} {A : ℝ}
    (hx : x ∈ cube d (m - 1)) (hn : n ≤ m - 5) :
    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then A else 0) = 0 :=
  ite_eq_right (not_boundaryTouches_of_interior hx hn)

/-- The package's own interior indicator, on the interior branch. -/
theorem interior_indicator_eq_zero {m : ℤ} {x : Vec d} {A : ℝ}
    (hx : x ∈ cube d (m - 1)) :
    (if x ∈ cube d (m - 1) then (0 : ℝ) else A) = 0 :=
  ite_eq_left hx

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
