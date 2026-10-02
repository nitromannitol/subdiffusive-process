import SubdiffusiveProcess.Geometry.TriadicResidual

/-!
# Parent and child cells in the actual centered triadic grid

The next coordinate label is `3*k+l`, with `l` in `Fin 3`.
Division and remainder recover the parent and local child labels. The
resulting cube is exactly a triadic child of the parent cube.
-/

open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- The middle label obeys the same recursion as the centered triadic grid. -/
theorem triadicHalf_succ (J : ℕ) : triadicHalf (J + 1) = 3 * triadicHalf J + 1 := by
  have h := two_mul_triadicHalf_add_one J
  have h' := two_mul_triadicHalf_add_one (J + 1)
  rw [pow_succ] at h'
  omega

/-- The global label of a local triadic child of a depth-`J` cell. -/
def triadicChild (J : ℕ) (k : OddGridIndex d (triadicHalf J))
    (l : OddGridIndex d 1) : OddGridIndex d (triadicHalf (J + 1)) :=
  fun i => ⟨3 * (k i).val + (l i).val, by
    have hk := (k i).isLt
    have hl := (l i).isLt
    rw [triadicHalf_succ]
    omega⟩

/-- The parent label is coordinatewise integer division by three. -/
def triadicParent (J : ℕ) (k : OddGridIndex d (triadicHalf (J + 1))) :
    OddGridIndex d (triadicHalf J) :=
  fun i => ⟨(k i).val / 3, by
    have hk := (k i).isLt
    have hm := triadicHalf_succ J
    omega⟩

/-- The local child label is the coordinatewise remainder modulo three. -/
def triadicChildLabel (J : ℕ) (k : OddGridIndex d (triadicHalf (J + 1))) :
    OddGridIndex d 1 :=
  fun i => ⟨(k i).val % 3, by omega⟩

/-- Refining a label and then taking its parent recovers the label. -/
theorem triadicParent_child (J : ℕ) (k : OddGridIndex d (triadicHalf J))
    (l : OddGridIndex d 1) : triadicParent J (triadicChild J k l) = k := by
  funext i
  apply Fin.ext
  have hl := (l i).isLt
  change (3 * (k i).val + (l i).val) / 3 = (k i).val
  omega

/-- Refining a label and taking its local remainder recovers that remainder. -/
theorem triadicChildLabel_child (J : ℕ) (k : OddGridIndex d (triadicHalf J))
    (l : OddGridIndex d 1) : triadicChildLabel J (triadicChild J k l) = l := by
  funext i
  apply Fin.ext
  have hl := (l i).isLt
  change (3 * (k i).val + (l i).val) % 3 = (l i).val
  omega

/-- Every fine label has exactly its parent and local remainder decomposition. -/
theorem triadicChild_parent_label (J : ℕ)
    (k : OddGridIndex d (triadicHalf (J + 1))) :
    triadicChild J (triadicParent J k) (triadicChildLabel J k) = k := by
  funext i
  apply Fin.ext
  change 3 * ((k i).val / 3) + (k i).val % 3 = (k i).val
  omega

/-- The next grid side is exactly one third of the parent side. -/
theorem triadic_side_succ (r : ℝ) (J : ℕ) :
    r / (2 * (triadicHalf (J + 1) : ℝ) + 1) =
      (r / (2 * (triadicHalf J : ℝ) + 1)) / 3 := by
  rw [triadicHalf_succ]
  push_cast
  field_simp
  ring

/-- The actual global center equals the center computed inside its parent cell. -/
theorem triadicChild_center (z : SpatialCoordinates d) (r : ℝ) (J : ℕ)
    (k : OddGridIndex d (triadicHalf J)) (l : OddGridIndex d 1) :
    oddGridCenter z r (triadicHalf (J + 1)) (triadicChild J k l) =
      oddGridCenter (oddGridCenter z r (triadicHalf J) k)
        (r / (2 * (triadicHalf J : ℝ) + 1)) 1 l := by
  funext i
  simp only [oddGridCenter, triadicChild, triadicHalf_succ, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  ring

/-- The fine cell is literally a local child cube, not only a subset of one. -/
theorem triadicChild_cell (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (J : ℕ)
    (k : OddGridIndex d (triadicHalf J)) (l : OddGridIndex d 1) :
    oddGridCell z r hr (triadicHalf (J + 1)) (triadicChild J k l) =
      oddGridCell (oddGridCenter z r (triadicHalf J) k)
        (r / (2 * (triadicHalf J : ℝ) + 1)) (div_pos hr (by positivity)) 1 l := by
  unfold oddGridCell
  congr 1
  · exact triadicChild_center z r J k l
  · simpa only [Nat.cast_one, mul_one, show (2 : ℝ) + 1 = 3 by norm_num] using
      triadic_side_succ r J

/-- Every actual fine cell is contained in its actual parent cell. -/
theorem triadicCell_subset_parent (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (J : ℕ) (k : OddGridIndex d (triadicHalf (J + 1))) :
    (oddGridCell z r hr (triadicHalf (J + 1)) k : Set (SpatialCoordinates d)) ⊆
      oddGridCell z r hr (triadicHalf J) (triadicParent J k) := by
  rw [← triadicChild_parent_label J k, triadicChild_cell]
  simpa only [triadicParent_child] using
    oddGridCell_subset (oddGridCenter z r (triadicHalf J) (triadicParent J k))
      (div_pos hr (by positivity)) 1 (triadicChildLabel J k)

/-- The actual children cover their parent up to Lebesgue null sets. -/
theorem triadicChildren_union_ae_eq (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (J : ℕ) (k : OddGridIndex d (triadicHalf J)) :
    (⋃ l : OddGridIndex d 1,
      (oddGridCell z r hr (triadicHalf (J + 1)) (triadicChild J k l) : Set (SpatialCoordinates d)))
      =ᵐ[volume] (oddGridCell z r hr (triadicHalf J) k : Set (SpatialCoordinates d)) := by
  simp_rw [triadicChild_cell]
  exact oddGrid_union_ae_eq _ (div_pos hr (by positivity)) 1

end SubdiffusiveProcess
