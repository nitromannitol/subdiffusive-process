module

public import SubdiffusiveProcess.Geometry.TriadicResidual
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic

@[expose] public section

open Set Metric Finset
open SubdiffusiveProcess

namespace SubdiffusiveProcess.Paper
attribute [local instance] Classical.propDecidable

/-- Every frontier point of an actual coordinate cube lies on a coordinate face. -/
theorem aux_cutoffs_frontier_has_face (d : ℕ) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (y : SpatialCoordinates d)
    (hy : y ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ i : Fin d, |y i - z i| = R / 2 := by
  have hSphere : dist y z = R / 2 := by
    have h := Metric.frontier_ball_subset_sphere (x := z) (ε := R / 2)
    exact h hy
  obtain ⟨i, hi⟩ := (dist_pi_eq_iff (half_pos hR)).mp hSphere |>.1
  exact ⟨i, by simpa only [Real.dist_eq] using hi⟩

/-- A positive-side coordinate cube in positive dimension has a frontier. -/
theorem aux_cutoffs_cube_frontier_nonempty (d : ℕ) (hd : 1 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    (frontier (centeredCube z R hR : Set (SpatialCoordinates d))).Nonempty := by
  apply nonempty_frontier_iff.mpr
  constructor
  · exact ⟨z, Metric.mem_ball_self (half_pos hR)⟩
  · intro hAll
    let i : Fin d := ⟨0, by omega⟩
    let w : SpatialCoordinates d := fun j => z j + R
    have hw : w ∈ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
      rw [hAll]
      exact Set.mem_univ w
    rw [centeredCube_eq_pi] at hw
    have hi := (Set.mem_pi.mp hw i (Set.mem_univ i)).2
    dsimp [w] at hi
    linarith

/-- Coordinate bounds for a point in the closure of an odd-grid cell. -/
theorem aux_cutoffs_closed_cell_coordinate {d : ℕ} (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (k : OddGridIndex d m)
    (x : SpatialCoordinates d)
    (hx : x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)))
    (i : Fin d) :
    |x i - (z i + ((k i).val - (m : ℝ)) * (R / (2 * (m : ℝ) + 1)))| ≤
      (R / (2 * (m : ℝ) + 1)) / 2 := by
  have hside : 0 ≤ R / (2 * (m : ℝ) + 1) / 2 := by positivity
  have hc : x ∈ Metric.closedBall (oddGridCenter z R m k)
      ((R / (2 * (m : ℝ) + 1)) / 2) := by
    exact Metric.closure_ball_subset_closedBall hx
  have hi := (dist_pi_le_iff hside).mp hc i
  simpa only [Real.dist_eq, oddGridCenter] using hi

/-- A grid interval meeting a point within three mesh widths of either face
has a label in one of the first or last four layers. -/
theorem aux_cutoffs_near_face_label (m : ℕ) (rho R z x y : ℝ)
    (hrho : 0 < rho) (hR : R = (2 * (m : ℝ) + 1) * rho)
    (k : Fin (2 * m + 1))
    (hxcell : |x - (z + ((k.val : ℝ) - (m : ℝ)) * rho)| ≤ rho / 2)
    (hxy : |x - y| < 3 * rho)
    (hface : y - z = R / 2 ∨ y - z = -(R / 2)) :
    k.val < 4 ∨ 2 * m + 1 ≤ k.val + 4 := by
  rcases (abs_le.mp hxcell) with ⟨hxlo, hxhi⟩
  rcases (abs_lt.mp hxy) with ⟨hxylo, hxyhi⟩
  rcases hface with hright | hleft
  · right
    by_contra hnot
    have hk : k.val + 4 < 2 * m + 1 := by omega
    have hkreal : (k.val : ℝ) + 4 ≤ 2 * (m : ℝ) := by exact_mod_cast (by omega : k.val + 4 ≤ 2 * m)
    have hprod : 0 ≤ (2 * (m : ℝ) - (k.val : ℝ) - 4) * rho :=
      mul_nonneg (by linarith) hrho.le
    nlinarith [hprod]
  · left
    by_contra hnot
    have hk : 4 ≤ k.val := by omega
    have hkreal : 4 ≤ (k.val : ℝ) := by exact_mod_cast hk
    have hprod : 0 ≤ ((k.val : ℝ) - 4) * rho :=
      mul_nonneg (by linarith) hrho.le
    nlinarith [hprod]

/-- A boundary-label set of cardinal at most `b` accounts for at most
`d*b*m^(d-1)` grid cells. -/
theorem aux_cutoffs_boundary_label_count
    (d m : ℕ) (B : Finset (Fin m)) (b : ℕ) (hB : B.card ≤ b) :
    (univ.filter (fun k : Fin d → Fin m => ∃ i : Fin d, k i ∈ B)).card ≤
      d * b * m ^ (d - 1) := by
  classical
  let S : Finset (Fin d → Fin m) :=
    univ.filter (fun k => ∃ i : Fin d, k i ∈ B)
  let F : Fin d → Fin m → Finset (Fin d → Fin m) :=
    fun i a => univ.filter (fun k => k i = a)
  have hsub : S ⊆ univ.biUnion (fun i : Fin d => B.biUnion (F i)) := by
    intro k hk
    rcases (mem_filter.mp hk).2 with ⟨i, hi⟩
    apply mem_biUnion.mpr
    refine ⟨i, mem_univ i, ?_⟩
    apply mem_biUnion.mpr
    exact ⟨k i, hi, mem_filter.mpr ⟨mem_univ k, rfl⟩⟩
  have hF (i : Fin d) (a : Fin m) : (F i a).card = m ^ (d - 1) := by
    simpa [F, Fintype.card_fun] using
      (Fintype.card_filter_piFinset_const_eq_of_mem (univ : Finset (Fin m)) i
        (mem_univ a))
  calc
    _ = S.card := rfl
    _ ≤ (univ.biUnion (fun i : Fin d => B.biUnion (F i))).card := card_le_card hsub
    _ ≤ ∑ i : Fin d, (B.biUnion (F i)).card := card_biUnion_le
    _ ≤ ∑ i : Fin d, ∑ a ∈ B, (F i a).card := by
      apply sum_le_sum
      intro i hi
      exact card_biUnion_le
    _ = d * B.card * m ^ (d - 1) := by simp [hF, mul_assoc]
    _ ≤ d * b * m ^ (d - 1) := by gcongr

/-- Every transition cell has some coordinate label in a fixed boundary layer,
provided the root cube has a nonempty frontier. -/
theorem aux_cutoffs_transition_cell_boundary_label {d : ℕ}
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (hscale : R = (2 * (m : ℝ) + 1) * rho)
    (theta : SpatialCoordinates d → ℝ)
    (hone : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho ≤ Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
        theta x = 1)
    (hfront : (frontier (centeredCube z R hR : Set (SpatialCoordinates d))).Nonempty)
    (k : OddGridIndex d m) (x : SpatialCoordinates d)
    (hxcell : x ∈ closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)))
    (htransition : 0 < theta x ∧ theta x < 1) :
    ∃ i : Fin d, (k i).val < 4 ∨ 2 * m + 1 ≤ (k i).val + 4 := by
  let Q := centeredCube z R hR
  have hrootclosure : x ∈ closure (Q : Set (SpatialCoordinates d)) :=
    closure_mono (oddGridCell_subset z hR m k) hxcell
  have hnear : ∃ y ∈ frontier (Q : Set (SpatialCoordinates d)), dist x y < 3 * rho := by
    by_cases hxQ : x ∈ (Q : Set (SpatialCoordinates d))
    · have hdist : Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) < 3 * rho := by
        by_contra hnot
        have hθ : theta x = 1 := hone x hxQ (le_of_not_gt hnot)
        linarith [htransition.2]
      exact (Metric.infDist_lt_iff hfront).mp hdist
    · have hxfront : x ∈ frontier (Q : Set (SpatialCoordinates d)) := by
        change x ∈ closure (Q : Set (SpatialCoordinates d)) \ interior (Q : Set (SpatialCoordinates d))
        exact ⟨hrootclosure, by simpa [Q.isOpen.interior_eq] using hxQ⟩
      exact ⟨x, hxfront, by simpa using (mul_pos (by norm_num : (0 : ℝ) < 3) hrho)⟩
  obtain ⟨y, hyfront, hxy⟩ := hnear
  obtain ⟨i, hface⟩ := aux_cutoffs_frontier_has_face d z R hR y hyfront
  have hface' : y i - z i = R / 2 ∨ y i - z i = -(R / 2) := by
    rcases le_total 0 (y i - z i) with hp | hn
    · left
      simpa [abs_of_nonneg hp] using hface
    · right
      rw [abs_of_nonpos hn] at hface
      linarith
  have hxyi : |x i - y i| < 3 * rho := by
    have hi := (dist_pi_lt_iff (mul_pos (by norm_num : (0 : ℝ) < 3) hrho)).mp hxy i
    simpa only [Real.dist_eq] using hi
  have hside : R / (2 * (m : ℝ) + 1) = rho := by
    rw [hscale]
    field_simp
  have hxc : |x i - (z i + ((k i).val - (m : ℝ)) * rho)| ≤ rho / 2 := by
    simpa only [hside] using aux_cutoffs_closed_cell_coordinate z R hR m k x hxcell i
  exact ⟨i, aux_cutoffs_near_face_label m rho R (z i) (x i) (y i)
    hrho hscale (k i) hxc hxyi hface'⟩

/-- At most eight coordinate labels are within four steps of either end. -/
theorem aux_cutoffs_boundary_labels_card (n : ℕ) (hn : 0 < n) :
    (univ.filter (fun a : Fin n => a.val < 4 ∨ n ≤ a.val + 4)).card ≤ 8 := by
  classical
  let L : Finset (Fin n) := univ.filter (fun a => a.val < 4)
  let U : Finset (Fin n) := univ.filter (fun a => n ≤ a.val + 4)
  have hL : L.card ≤ 4 := by
    calc
      L.card ≤ (Finset.range 4).card := by
        apply Finset.card_le_card_of_injOn (fun a : Fin n => a.val)
        · intro a ha
          have ha' : a.val < 4 := by simpa [L] using ha
          exact Finset.mem_range.mpr ha'
        · intro a ha b hb hab
          exact Fin.ext hab
      _ = 4 := Finset.card_range 4
  have hU : U.card ≤ 4 := by
    calc
      U.card ≤ (Finset.range 4).card := by
        apply Finset.card_le_card_of_injOn (fun a : Fin n => n - 1 - a.val)
        · intro a ha
          have hval := a.isLt
          have hnear : n ≤ a.val + 4 := by simpa [U] using ha
          have hsum : a.val + (n - 1 - a.val) = n - 1 := by omega
          exact Finset.mem_range.mpr (by change n - 1 - a.val < 4; omega)
        · intro a ha b hb hab
          apply Fin.ext
          have ha' := a.isLt
          have hb' := b.isLt
          change n - 1 - a.val = n - 1 - b.val at hab
          have hsum_a : a.val + (n - 1 - a.val) = n - 1 := by omega
          have hsum_b : b.val + (n - 1 - b.val) = n - 1 := by omega
          omega
      _ = 4 := Finset.card_range 4
  have hB : (univ.filter (fun a : Fin n => a.val < 4 ∨ n ≤ a.val + 4)) = L ∪ U := by
    ext a
    simp [L, U]
  rw [hB]
  calc
    (L ∪ U).card ≤ L.card + U.card := Finset.card_union_le L U
    _ ≤ 4 + 4 := add_le_add hL hU
    _ = 8 := by norm_num

/-- The actual transition-cell count is uniform in the mesh and the plateau. -/
theorem aux_cutoffs_uniform_transition_count (d : ℕ) (hd : 1 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (hscale : R = (2 * (m : ℝ) + 1) * rho)
    (theta : SpatialCoordinates d → ℝ)
    (hone : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho ≤ Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
        theta x = 1) :
    (Finset.univ.filter (fun k : OddGridIndex d m =>
      (closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∩
        {x : SpatialCoordinates d | 0 < theta x ∧ theta x < 1}).Nonempty)).card ≤
      d * 8 * (2 * m + 1) ^ (d - 1) := by
  classical
  let B : Finset (Fin (2 * m + 1)) :=
    Finset.univ.filter (fun a => a.val < 4 ∨ 2 * m + 1 ≤ a.val + 4)
  let I : Finset (OddGridIndex d m) :=
    Finset.univ.filter (fun k =>
      (closure (oddGridCell z R hR m k : Set (SpatialCoordinates d)) ∩
        {x : SpatialCoordinates d | 0 < theta x ∧ theta x < 1}).Nonempty)
  have hfront := aux_cutoffs_cube_frontier_nonempty d hd z R hR
  have hsub : I ⊆ Finset.univ.filter (fun k : OddGridIndex d m => ∃ i : Fin d, k i ∈ B) := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    obtain ⟨x, hx⟩ := hk'
    obtain ⟨i, hi⟩ := aux_cutoffs_transition_cell_boundary_label z R hR m rho hrho
      hscale theta hone hfront k x hx.1 hx.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ k, i, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ (k i), hi⟩
  have hB : B.card ≤ 8 := aux_cutoffs_boundary_labels_card (2 * m + 1) (by omega)
  calc
    _ = I.card := rfl
    _ ≤ (Finset.univ.filter (fun k : OddGridIndex d m => ∃ i : Fin d, k i ∈ B)).card :=
      Finset.card_le_card hsub
    _ ≤ d * 8 * (2 * m + 1) ^ (d - 1) :=
      aux_cutoffs_boundary_label_count d (2 * m + 1) B 8 hB

/-- Convert the uniform grid-label count to the paper's physical collar scale. -/
theorem aux_cutoffs_scale_algebra
    (d J Icard : ℕ) (hd : 2 ≤ d) (R rho : ℝ)
    (hR : 0 < R) (hrho : 0 < rho)
    (hscale : rho = R / (3 : ℝ) ^ J)
    (hcount : (Icard : ℝ) ≤ 8 * d * ((3 : ℝ) ^ J) ^ (d - 1)) :
    (Icard : ℝ) ≤ (8 * d * R ^ (d - 1)) * rho ^ (-(d : ℝ) + 1) := by
  have hn : (-(d : ℝ) + 1) = -((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
    ring
  have hpow : rho ^ (-(d : ℝ) + 1) = (rho ^ (d - 1))⁻¹ := by
    rw [hn, Real.rpow_neg (le_of_lt hrho), Real.rpow_natCast]
  have hscale' : rho * (3 : ℝ) ^ J = R := by
    rw [hscale]
    field_simp
  have hpow' : rho ^ (d - 1) * ((3 : ℝ) ^ J) ^ (d - 1) = R ^ (d - 1) := by
    rw [← mul_pow, hscale']
  rw [hpow]
  have hrhopow : rho ^ (d - 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hrho)
  have hident : ((3 : ℝ) ^ J) ^ (d - 1) = R ^ (d - 1) * (rho ^ (d - 1))⁻¹ := by
    apply (eq_div_iff hrhopow).2
    simpa only [div_eq_mul_inv, mul_comm] using hpow'
  calc
    (Icard : ℝ) ≤ 8 * d * ((3 : ℝ) ^ J) ^ (d - 1) := hcount
    _ = 8 * d * R ^ (d - 1) * (rho ^ (d - 1))⁻¹ := by rw [hident]; ring

/-- The physical collar has a mesh-independent transition-cell constant. -/
theorem aux_cutoffs_uniform_transition_cover
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (J : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (theta : SpatialCoordinates d → ℝ)
    (hone : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      3 * rho ≤ Metric.infDist x (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
        theta x = 1)
    (hscale : rho = R / (3 : ℝ) ^ J) :
    (Finset.univ.filter (fun k : OddGridIndex d (triadicHalf J) =>
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
        {x : SpatialCoordinates d | 0 < theta x ∧ theta x < 1}).Nonempty)).card ≤
      (8 * d * R ^ (d - 1)) * rho ^ (-(d : ℝ) + 1) := by
  have hscale' : R = (2 * (triadicHalf J : ℝ) + 1) * rho := by
    calc
      R = (3 : ℝ) ^ J * rho := by rw [hscale]; field_simp
      _ = (2 * (triadicHalf J : ℝ) + 1) * rho := by rw [triadic_denominator]
  have hcount := aux_cutoffs_uniform_transition_count d (by omega : 1 ≤ d)
    z R hR (triadicHalf J) rho hrho hscale' theta hone
  have hcountReal :
      ((Finset.univ.filter (fun k : OddGridIndex d (triadicHalf J) =>
        (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
          {x : SpatialCoordinates d | 0 < theta x ∧ theta x < 1}).Nonempty)).card : ℝ) ≤
        8 * d * ((3 : ℝ) ^ J) ^ (d - 1) := by
    have hNat :
        (Finset.univ.filter (fun k : OddGridIndex d (triadicHalf J) =>
          (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
            {x : SpatialCoordinates d | 0 < theta x ∧ theta x < 1}).Nonempty)).card ≤
          8 * d * (3 ^ J) ^ (d - 1) := by
      calc
        _ ≤ d * 8 * (2 * triadicHalf J + 1) ^ (d - 1) := hcount
        _ = 8 * d * (3 ^ J) ^ (d - 1) := by
          rw [two_mul_triadicHalf_add_one J]
          ring
    exact_mod_cast hNat
  exact aux_cutoffs_scale_algebra d J _ hd R rho hR hrho hscale hcountReal

/-- A single physical collar constant works for every triadic mesh and every
plateau with the specified interior value. This is the quantified form needed
by the cutoff construction. -/
theorem aux_cutoffs_uniform_transition_family
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) :
    ∃ Ccover : ℝ, 0 ≤ Ccover ∧
      ∀ (J : ℕ) (rho : ℝ) (theta : SpatialCoordinates d → ℝ),
        (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
          3 * rho ≤ Metric.infDist x
            (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
            theta x = 1) →
        rho = R / (3 : ℝ) ^ J →
        ∃ I : Finset (OddGridIndex d (triadicHalf J)),
          (∀ k, k ∈ I ↔
            (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
              {x : SpatialCoordinates d | 0 < theta x ∧ theta x < 1}).Nonempty) ∧
          (I.card : ℝ) ≤ Ccover * rho ^ (-(d : ℝ) + 1) := by
  classical
  refine ⟨8 * d * R ^ (d - 1), ?_, ?_⟩
  · positivity
  intro J rho theta hone hscale
  have hrho : 0 < rho := by rw [hscale]; positivity
  let I : Finset (OddGridIndex d (triadicHalf J)) :=
    Finset.univ.filter (fun k =>
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
        {x : SpatialCoordinates d | 0 < theta x ∧ theta x < 1}).Nonempty)
  refine ⟨I, ?_, ?_⟩
  · intro k
    simp [I]
  · exact aux_cutoffs_uniform_transition_cover d hd z R hR J rho hrho theta hone hscale

end SubdiffusiveProcess.Paper
