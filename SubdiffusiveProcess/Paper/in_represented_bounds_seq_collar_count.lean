module

public import SubdiffusiveProcess.Paper.lem_cutoffs_root_uniform

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Finite active-cell set for one smooth collar profile. -/
noncomputable def aux_in_represented_bounds_seq_collar_count_indices
    {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (theta : SpatialCoordinates d → ℝ) : Finset (OddGridIndex d m) := by
  classical
  exact Finset.univ.filter (fun k =>
    (closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∩
      {x : SpatialCoordinates d | 0 < theta x ∧ theta x < 1}).Nonempty)

/-- A fine triadic grid has only a fixed number of boundary labels per coordinate
when the transition region has a fixed multiple of the cell width. -/
theorem aux_in_represented_bounds_seq_collar_count_labels (n b : ℕ) (_hn : 0 < n) :
    (Finset.univ.filter (fun a : Fin n => a.val < b ∨ n ≤ a.val + b)).card ≤ 2 * b := by
  classical
  let L : Finset (Fin n) := Finset.univ.filter (fun a => a.val < b)
  let U : Finset (Fin n) := Finset.univ.filter (fun a => n ≤ a.val + b)
  have hL : L.card ≤ b := by
    calc
      L.card ≤ (Finset.range b).card := by
        apply Finset.card_le_card_of_injOn (fun a : Fin n => a.val)
        · intro a ha
          exact Finset.mem_range.mpr (by simpa [L] using ha)
        · intro a ha c hc hac
          exact Fin.ext hac
      _ = b := Finset.card_range b
  have hU : U.card ≤ b := by
    calc
      U.card ≤ (Finset.range b).card := by
        apply Finset.card_le_card_of_injOn (fun a : Fin n => n - 1 - a.val)
        · intro a ha
          exact Finset.mem_range.mpr (by
            change n - 1 - a.val < b
            have hnear : n ≤ a.val + b := by simpa [U] using ha
            have ha' := a.isLt
            omega)
        · intro a ha c hc hac
          apply Fin.ext
          have ha' := a.isLt
          have hc' := c.isLt
          change n - 1 - a.val = n - 1 - c.val at hac
          omega
      _ = b := Finset.card_range b
  have hUnion : L ∪ U = Finset.univ.filter
      (fun a : Fin n => a.val < b ∨ n ≤ a.val + b) := by
    ext a
    simp [L, U]
  rw [← hUnion]
  exact (Finset.card_union_le L U).trans (by omega)

/-- Active cells of a fine mesh lie in an `O(rho)` collar. The count permits
the mesh width and the collar width to differ by a fixed factor. -/
theorem in_represented_bounds_seq_collar_count
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (h : ℝ) (hh : 0 < h) (hscale : R = (2 * (m : ℝ) + 1) * h)
    (r : ℝ) (hr : 0 < r) (b : ℕ) (hb : 3 * r ≤ (b : ℝ) * h)
    (theta : SpatialCoordinates d → ℝ)
    (hzeroOutside : ∀ x, x ∉ (centeredCube z R hR : Set (SpatialCoordinates d)) → theta x = 0)
    (hone : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * r ≤ Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
        theta x = 1) :
    let I := aux_in_represented_bounds_seq_collar_count_indices z R hR m theta
    (I.card : ℝ) ≤ (d : ℝ) * (2 * (b + 1) : ℝ) * (2 * (m : ℝ) + 1) ^ (d - 1) := by
  classical
  let I := aux_in_represented_bounds_seq_collar_count_indices z R hR m theta
  change (I.card : ℝ) ≤ (d : ℝ) * (2 * (b + 1) : ℝ) * (2 * (m : ℝ) + 1) ^ (d - 1)
  let B : Finset (Fin (2 * m + 1)) := Finset.univ.filter
    (fun a => a.val < b + 1 ∨ 2 * m + 1 ≤ a.val + (b + 1))
  have hB : B.card ≤ 2 * (b + 1) := by
    simpa [B] using
      (aux_in_represented_bounds_seq_collar_count_labels (2 * m + 1) (b + 1) (by omega))
  let I := aux_in_represented_bounds_seq_collar_count_indices z R hR m theta
  have hsub : I ⊆ Finset.univ.filter
      (fun k : OddGridIndex d m => ∃ i : Fin d, k i ∈ B) := by
    intro k hk
    have hk' : k ∈ Finset.univ.filter (fun k =>
        (closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∩
          {x : SpatialCoordinates d | 0 < theta x ∧ theta x < 1}).Nonempty) := by
      simpa [I, aux_in_represented_bounds_seq_collar_count_indices] using hk
    obtain ⟨_, hactive⟩ := Finset.mem_filter.mp hk'
    obtain ⟨x, hxmem⟩ := hactive
    change x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∧
      0 < theta x ∧ theta x < 1 at hxmem
    rcases hxmem with ⟨hxcell, hxpos, hxlt⟩
    have hxQ : x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
      by_contra hx
      have := hzeroOutside x hx
      linarith
    have hdist : Metric.infDist x
        (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) < 3 * r := by
      by_contra hnot
      have := hone x hxQ (le_of_not_gt hnot)
      linarith
    have hfront := aux_cutoffs_cube_frontier_nonempty d (by omega) z R hR
    obtain ⟨y, hyF, hxy⟩ := (Metric.infDist_lt_iff hfront).mp hdist
    obtain ⟨i, hface⟩ := aux_cutoffs_frontier_has_face d z R hR y hyF
    have hxcl : x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) := hxcell
    have hxc := aux_cutoffs_closed_cell_coordinate z R hR m k x hxcl i
    have hxyi : |x i - y i| < 3 * r := by
      have hi := (dist_pi_lt_iff (mul_pos (by norm_num : (0 : ℝ) < 3) hr)).mp hxy i
      simpa only [Real.dist_eq] using hi
    have hcentery : |(z i + ((k i).val - (m : ℝ)) * h) - y i| ≤ 3 * r + h / 2 := by
      have hxc' : |x i - (z i + ((k i).val - (m : ℝ)) * h)| ≤ h / 2 := by
        have heq : R / (2 * (m : ℝ) + 1) = h := by
          rw [hscale]
          field_simp
        simpa [heq] using hxc
      have hsum' : |(z i + ((k i).val - (m : ℝ)) * h) - y i| ≤
          |(z i + ((k i).val - (m : ℝ)) * h) - x i| + |x i - y i| := by
        calc
          _ = |((z i + ((k i).val - (m : ℝ)) * h) - x i) + (x i - y i)| := by
            congr 1 ; ring
          _ ≤ _ := abs_add_le _ _
      calc
        _ ≤ h / 2 + 3 * r := le_trans hsum' (add_le_add (by simpa [abs_sub_comm] using hxc') hxyi.le)
        _ = 3 * r + h / 2 := by ring
    have hface' : y i - z i = R / 2 ∨ y i - z i = -(R / 2) := by
      rcases le_total 0 (y i - z i) with hp | hn
      · left
        simpa [abs_of_nonneg hp] using hface
      · right
        rw [abs_of_nonpos hn] at hface
        linarith
    have hRhalf : R / 2 = ((m : ℝ) + 1 / 2) * h := by
      rw [hscale]
      ring
    have hlabel : (k i).val < b + 1 ∨ 2 * m + 1 ≤ (k i).val + (b + 1) := by
      rcases hface' with hupper | hlower
      · right
        have habs := hcentery
        have hy : y i = z i + R / 2 := by linarith [hupper]
        rw [hy] at habs
        have hk := (abs_le.mp habs).1
        rw [hRhalf] at hk
        have hvb : ((2 * m : ℕ) : ℝ) - (k i).val ≤ (b : ℝ) := by
          push_cast
          nlinarith
        have hn : 2 * m ≤ (k i).val + b := by
          exact_mod_cast (show ((2 * m : ℕ) : ℝ) ≤ (k i).val + b by nlinarith [hvb])
        omega
      · left
        have habs := hcentery
        have hy : y i = z i - R / 2 := by linarith [hlower]
        rw [hy] at habs
        have hk := (abs_le.mp habs).2
        rw [hRhalf] at hk
        have hvb : ((k i).val : ℝ) ≤ (b : ℝ) := by nlinarith
        have hn : (k i).val ≤ b := by exact_mod_cast hvb
        omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ k, i, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ (k i), hlabel⟩
  have hcount := aux_cutoffs_boundary_label_count d (2 * m + 1) B (2 * (b + 1)) hB
  calc
    (I.card : ℝ) ≤ (Finset.univ.filter
        (fun k : OddGridIndex d m => ∃ i : Fin d, k i ∈ B)).card := by
          exact_mod_cast Finset.card_le_card hsub
    _ ≤ (d : ℝ) * (2 * (b + 1) : ℝ) * (2 * (m : ℝ) + 1) ^ (d - 1) := by
      exact_mod_cast hcount

end SubdiffusiveProcess.Paper
