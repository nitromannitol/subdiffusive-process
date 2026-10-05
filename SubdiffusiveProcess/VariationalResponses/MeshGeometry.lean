module

public import SubdiffusiveProcess.Sobolev.HarmonicTriadicMeshH10
public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.Geometry.TriadicResidual
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6MeasurableMaxPrinciple
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeshGluing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}


/-- The closed cube is compact. -/
theorem isCompact_closure_centeredCube (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R) :
    IsCompact (closure (centeredCube z R hR : Set (SpatialCoordinates d))) := by
  exact Bornology.IsBounded.isCompact_closure (centeredCube_isBounded z hR)


/-- `y ↦ ‖∇φ(y)‖` is continuous for a smooth `φ`. -/
theorem continuous_norm_fderiv {φ : SpatialCoordinates d → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous fun y => ‖fderiv ℝ φ y‖ := by
  have h : (1 : WithTop ℕ∞) ≤ ∞ := by
    first
      | exact le_top
      | simp
  exact (hφ.continuous_fderiv (by simp)).norm


/-- A continuous function on a compact set is bounded by its supremum there. -/
theorem le_sSup_image {S : Set (SpatialCoordinates d)} (hS : IsCompact S)
    {g : SpatialCoordinates d → ℝ} (hg : Continuous g) {y : SpatialCoordinates d}
    (hy : y ∈ S) : g y ≤ sSup (g '' S) := by
  have hbdd : BddAbove (g '' S) :=
    IsCompact.bddAbove_image hS hg.continuousOn
  exact le_csSup hbdd (Set.mem_image_of_mem g hy)


/-- The supremum of a nonnegative continuous function on a nonempty compact set is nonnegative. -/
theorem sSup_image_norm_nonneg {S : Set (SpatialCoordinates d)} (hS : IsCompact S)
    (hne : S.Nonempty) {g : SpatialCoordinates d → ℝ} (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) : 0 ≤ sSup (g '' S) := by
  obtain ⟨x, hx⟩ := hne
  have hbdd : BddAbove (g '' S) := hS.bddAbove_image hg.continuousOn
  have hmem : g x ∈ g '' S := Set.mem_image_of_mem g hx
  have hle : g x ≤ sSup (g '' S) := le_csSup hbdd hmem
  linarith [hg0 x]


/-- The closed cube is convex. -/
theorem convex_closure_centeredCube (z : SpatialCoordinates d) {R : ℝ} (hR : 0 < R) :
    Convex ℝ (closure (centeredCube z R hR : Set (SpatialCoordinates d))) := by
  simpa [centeredCube] using! (convex_ball z (R / 2)).closure


/-- The diameter of an odd-grid cell is at most its side length `r/(2m+1)`. -/
theorem dist_le_of_mem_oddGridCell (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (k : OddGridIndex d m) {x y : SpatialCoordinates d}
    (hx : x ∈ (oddGridCell z r hr m k : Set (SpatialCoordinates d)))
    (hy : y ∈ (oddGridCell z r hr m k : Set (SpatialCoordinates d))) :
    dist x y ≤ r / (2 * (m : ℝ) + 1) := by
  have hC : 0 ≤ r / (2 * (m : ℝ) + 1) := by positivity
  refine (dist_pi_le_iff hC).mpr ?_
  intro i
  rw [Real.dist_eq]
  have hx' := (mem_oddGridCell z hr m k x).mp hx
  have hy' := (mem_oddGridCell z hr m k y).mp hy
  obtain ⟨hxlo, hxhi⟩ := hx' i
  obtain ⟨hylo, hyhi⟩ := hy' i
  rw [abs_le]
  constructor <;> linarith


/-- The centre of an odd-grid cell lies in that cell. -/
theorem oddGridCenter_mem_cell (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (k : OddGridIndex d m) :
    oddGridCenter z r m k ∈ (oddGridCell z r hr m k : Set (SpatialCoordinates d)) := by
  rw [mem_oddGridCell]
  intro i
  have hpos : 0 < r / (2 * (m : ℝ) + 1) / 2 := by
    have h1 : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
    exact half_pos (div_pos hr h1)
  dsimp only [oddGridCenter]
  constructor <;> linarith


/-- A closed odd-grid cell lies in the closed parent cube. -/
theorem closure_oddGridCell_subset (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (k : OddGridIndex d m) :
    closure (oddGridCell z r hr m k : Set (SpatialCoordinates d)) ⊆
      closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  exact closure_mono (oddGridCell_subset z hr m k)


/-- The triadic cell side: `r/(2·triadicHalf J+1) = r/3^J`. -/
theorem cell_side_eq (R : ℝ) (J : ℕ) :
    R / (2 * (triadicHalf J : ℝ) + 1) = R / (3 : ℝ) ^ J := by
  rw [triadic_denominator J]


/-- The mean value inequality on a convex set, in absolute-value form. -/
theorem abs_sub_le_mul_dist {φ : SpatialCoordinates d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {S : Set (SpatialCoordinates d)} (hS : Convex ℝ S) {C : ℝ}
    (hC : ∀ x ∈ S, ‖fderiv ℝ φ x‖ ≤ C) {x y : SpatialCoordinates d}
    (hx : x ∈ S) (hy : y ∈ S) : |φ y - φ x| ≤ C * dist y x := by
  have hdiff : ∀ z ∈ S, DifferentiableAt ℝ φ z := fun z _ =>
    (hφ.differentiable (by simp)).differentiableAt
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hC hS hx hy
  rw [Real.norm_eq_abs] at h
  rw [dist_eq_norm]
  exact h


end SubdiffusiveProcess
