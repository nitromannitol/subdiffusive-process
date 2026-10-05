module

public import SubdiffusiveProcess.Geometry.TriadicNesting

@[expose] public section

/-! # Literal descendants of an observation cube

A local depth-`J` label inside a global depth-`N` cube has the global label
`3^J * k + l`. Division and remainder recover both coordinates. The cell
identity relates these labels to actual open cubes in the original grid.
-/
open MeasureTheory Set TopologicalSpace
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- The central label splits into its parent and local central labels. -/
theorem triadicHalf_add (N J : ℕ) :
    triadicHalf (N + J) = 3 ^ J * triadicHalf N + triadicHalf J := by
  have hN := two_mul_triadicHalf_add_one N
  have hJ := two_mul_triadicHalf_add_one J
  have h := two_mul_triadicHalf_add_one (N + J)
  rw [pow_add] at h
  nlinarith

/-- The original-grid label of a local descendant of an observation cell. -/
def triadicDescendant (N J : ℕ) (k : OddGridIndex d (triadicHalf N))
    (l : OddGridIndex d (triadicHalf J)) : OddGridIndex d (triadicHalf (N + J)) :=
  fun i => ⟨3 ^ J * (k i).val + (l i).val, by
    have hk : (k i).val < 3 ^ N := by simpa only [two_mul_triadicHalf_add_one] using (k i).isLt
    have hl : (l i).val < 3 ^ J := by simpa only [two_mul_triadicHalf_add_one] using (l i).isLt
    have hb := Nat.mul_le_mul_left (3 ^ J) (Nat.succ_le_of_lt hk)
    have hsize := two_mul_triadicHalf_add_one (N + J)
    rw [pow_add] at hsize
    nlinarith⟩

/-- The depth-`N` ancestor of a global depth-`N+J` label. -/
def triadicAncestor (N J : ℕ) (k : OddGridIndex d (triadicHalf (N + J))) :
    OddGridIndex d (triadicHalf N) :=
  fun i => ⟨(k i).val / 3 ^ J, by
    have hk : (k i).val < 3 ^ N * 3 ^ J := by
      simpa only [two_mul_triadicHalf_add_one, pow_add] using (k i).isLt
    have h := (Nat.div_lt_iff_lt_mul (show 0 < 3 ^ J by positivity)).mpr hk
    exact h.trans_eq (two_mul_triadicHalf_add_one N).symm⟩

/-- The local label inside the depth-`N` ancestor. -/
def triadicDescendantLabel (N J : ℕ) (k : OddGridIndex d (triadicHalf (N + J))) :
    OddGridIndex d (triadicHalf J) :=
  fun i => ⟨(k i).val % 3 ^ J, by
    exact (Nat.mod_lt _ (show 0 < 3 ^ J by positivity)).trans_eq
      (two_mul_triadicHalf_add_one J).symm⟩

/-- Taking the ancestor of a literal descendant recovers its parent. -/
theorem triadicAncestor_descendant (N J : ℕ) (k : OddGridIndex d (triadicHalf N))
    (l : OddGridIndex d (triadicHalf J)) :
    triadicAncestor N J (triadicDescendant N J k l) = k := by
  funext i
  apply Fin.ext
  change (3 ^ J * (k i).val + (l i).val) / 3 ^ J = (k i).val
  have hl : (l i).val < 3 ^ J := by simpa only [two_mul_triadicHalf_add_one] using (l i).isLt
  rw [Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hl, add_zero]

/-- The remainder of a literal descendant recovers its local label. -/
theorem triadicDescendantLabel_descendant (N J : ℕ)
    (k : OddGridIndex d (triadicHalf N)) (l : OddGridIndex d (triadicHalf J)) :
    triadicDescendantLabel N J (triadicDescendant N J k l) = l := by
  funext i
  apply Fin.ext
  change (3 ^ J * (k i).val + (l i).val) % 3 ^ J = (l i).val
  have hl : (l i).val < 3 ^ J := by simpa only [two_mul_triadicHalf_add_one] using (l i).isLt
  simp [Nat.add_mod, Nat.mod_eq_of_lt hl]

/-- Every original-grid fine label has its actual ancestor/local decomposition. -/
theorem triadicDescendant_ancestor_label (N J : ℕ)
    (k : OddGridIndex d (triadicHalf (N + J))) :
    triadicDescendant N J (triadicAncestor N J k) (triadicDescendantLabel N J k) = k := by
  funext i
  apply Fin.ext
  change 3 ^ J * ((k i).val / 3 ^ J) + (k i).val % 3 ^ J = (k i).val
  simpa only [Nat.mul_comm] using Nat.div_add_mod' (k i).val (3 ^ J)

/-- Descendant labels inside a fixed observation cell are injectively indexed. -/
theorem triadicDescendant_injective (N J : ℕ) (k : OddGridIndex d (triadicHalf N)) :
    Function.Injective (triadicDescendant N J k) := by
  intro l l' h
  have := congrArg (triadicDescendantLabel N J) h
  simpa only [triadicDescendantLabel_descendant] using this

/-- The center computed locally in an observation cell is the original-grid center. -/
theorem triadicDescendant_center (z : SpatialCoordinates d) (r : ℝ) (N J : ℕ)
    (k : OddGridIndex d (triadicHalf N)) (l : OddGridIndex d (triadicHalf J)) :
    oddGridCenter z r (triadicHalf (N + J)) (triadicDescendant N J k l) =
      oddGridCenter (oddGridCenter z r (triadicHalf N) k)
        (r / (2 * (triadicHalf N : ℝ) + 1)) (triadicHalf J) l := by
  funext i
  dsimp only [oddGridCenter, triadicDescendant]
  simp only [triadic_denominator]
  simp only [triadicHalf_add, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  field_simp
  ring

/-- Descendant side lengths agree in the local and original grids. -/
theorem triadic_side_add (r : ℝ) (N J : ℕ) :
    r / (2 * (triadicHalf (N + J) : ℝ) + 1) =
      (r / (2 * (triadicHalf N : ℝ) + 1)) / (2 * (triadicHalf J : ℝ) + 1) := by
  simp only [triadic_denominator, div_div, pow_add]

/-- The actual global descendant cube is exactly the local observation-grid cube. -/
theorem triadicDescendant_cell (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (N J : ℕ) (k : OddGridIndex d (triadicHalf N))
    (l : OddGridIndex d (triadicHalf J)) :
    oddGridCell z r hr (triadicHalf (N + J)) (triadicDescendant N J k l) =
      oddGridCell (oddGridCenter z r (triadicHalf N) k)
        (r / (2 * (triadicHalf N : ℝ) + 1)) (div_pos hr (by positivity)) (triadicHalf J) l := by
  unfold oddGridCell
  congr 1
  · exact triadicDescendant_center z r N J k l
  · exact triadic_side_add r N J

/-- All local descendants lie in their actual observation cube. -/
theorem triadicDescendant_cell_subset (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (N J : ℕ) (k : OddGridIndex d (triadicHalf N))
    (l : OddGridIndex d (triadicHalf J)) :
    (oddGridCell z r hr (triadicHalf (N + J)) (triadicDescendant N J k l) :
      Set (SpatialCoordinates d)) ⊆ oddGridCell z r hr (triadicHalf N) k := by
  rw [triadicDescendant_cell]
  exact oddGridCell_subset _ (div_pos hr (by positivity)) _ _

/-- Fine original-grid cells lie in their literal ancestors. -/
theorem triadicCell_subset_ancestor (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (N J : ℕ) (k : OddGridIndex d (triadicHalf (N + J))) :
    (oddGridCell z r hr (triadicHalf (N + J)) k : Set (SpatialCoordinates d)) ⊆
      oddGridCell z r hr (triadicHalf N) (triadicAncestor N J k) := by
  have h := triadicDescendant_cell_subset z hr N J
    (triadicAncestor N J k) (triadicDescendantLabel N J k)
  simpa only [triadicDescendant_ancestor_label] using h

/-- The actual descendants cover their observation cube up to Lebesgue-null faces. -/
theorem triadicDescendants_union_ae_eq (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (N J : ℕ) (k : OddGridIndex d (triadicHalf N)) :
    (⋃ l : OddGridIndex d (triadicHalf J),
      (oddGridCell z r hr (triadicHalf (N + J)) (triadicDescendant N J k l) :
        Set (SpatialCoordinates d))) =ᵐ[volume]
      (oddGridCell z r hr (triadicHalf N) k : Set (SpatialCoordinates d)) := by
  simp_rw [triadicDescendant_cell]
  exact oddGrid_union_ae_eq _ (div_pos hr (by positivity)) _

end SubdiffusiveProcess
