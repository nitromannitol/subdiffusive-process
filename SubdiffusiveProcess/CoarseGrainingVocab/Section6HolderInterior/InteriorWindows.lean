import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellGeometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.Geometry




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Translated cubes are nested in the scale. -/
theorem translatedCube_mono {j l : ℤ} (x : Vec d) (hjl : j ≤ l) :
    translatedCube d j x ⊆ translatedCube d l x := by
  rintro p ⟨y, hy, rfl⟩
  exact ⟨y, cube_subset_cube_of_le hjl hy, rfl⟩



theorem translatedCube_subset_cube_of_interior {m n j : ℤ} {x : Vec d}
    (hx : x ∈ cube d (m - 1)) (hn : n ≤ m - 5) (hjn : j ≤ n) :
    translatedCube d j x ⊆ cube d m :=
  (translatedCube_mono x hjn).trans
    (Section6HarmonicApproximation.translatedCube_subset_domain_of_not_boundaryTouches
      (mem_cube_of_mem_cube_sub_one hx) (not_boundaryTouches_of_interior hx hn))

/-- The same adapter for a descendant centre of an interior base point. -/
theorem translatedCube_subset_cube_of_interior_descendant {m n top j : ℤ}
    {x y : Vec d} (hx : x ∈ cube d (m - 1)) (hy : y ∈ truncatedCube d m n x)
    (hntop : n ≤ top) (htop : top ≤ m - 5) (hjtop : j ≤ top) :
    translatedCube d j y ⊆ cube d m :=
  (translatedCube_mono y hjtop).trans
    (Section6HarmonicApproximation.translatedCube_subset_domain_of_not_boundaryTouches
      (truncatedCube_subset_cube d m n x hy)
      (not_boundaryTouches_of_interior_descendant hx hy hntop htop))



theorem openCubeAtScale_subset_cube_of_interior {m n : ℤ} {x q : Vec d}
    (hx : x ∈ cube d (m - 1)) (hn : n ≤ m - 5)
    (hq : q ∈ truncatedCube d m (n - 1) x) :
    openCubeAtScale q (n - 3) ⊆ cube d m :=
  Section6HarmonicApproximation.openCubeAtScale_predTwo_subset_domain_of_not_boundaryTouches
    (mem_cube_of_mem_cube_sub_one hx) hq (not_boundaryTouches_of_interior hx hn)

/-- Descendant form of the preceding, for the base points the Step-6 cover
actually ranges over: `x` is a descendant of the interior grid centre `z`. -/
theorem openCubeAtScale_subset_cube_of_interior_descendant {m n top : ℤ}
    {z x q : Vec d} (hz : z ∈ cube d (m - 1)) (hx : x ∈ truncatedCube d m n z)
    (hntop : n ≤ top) (htop : top ≤ m - 5)
    (hq : q ∈ truncatedCube d m (top - 1) x) :
    openCubeAtScale q (top - 3) ⊆ cube d m :=
  Section6HarmonicApproximation.openCubeAtScale_predTwo_subset_domain_of_not_boundaryTouches
    (truncatedCube_subset_cube d m n z hx) hq
    (not_boundaryTouches_of_interior_descendant hz hx hntop htop)

/-- There is no boundary cell to price: the hypothesis of the boundary-cell
budget is unsatisfiable at an interior base point. -/
theorem no_boundary_cell_of_interior_descendant {m n top : ℤ}
    {z x q : Vec d} (hz : z ∈ cube d (m - 1)) (hx : x ∈ truncatedCube d m n z)
    (hntop : n ≤ top) (htop : top ≤ m - 5)
    (hq : q ∈ truncatedCube d m (top - 1) x)
    (hpatch : ¬ openCubeAtScale q (top - 3) ⊆ cube d m) : False :=
  hpatch (openCubeAtScale_subset_cube_of_interior_descendant hz hx hntop htop hq)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
