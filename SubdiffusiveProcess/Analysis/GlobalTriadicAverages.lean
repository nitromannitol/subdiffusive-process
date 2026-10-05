module

public import SubdiffusiveProcess.Geometry.TriadicNesting
public import SubdiffusiveProcess.Analysis.TriadicChildAverages

@[expose] public section

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess

theorem natFloor_div_lt {a h : ℝ} (_hh : 0 < h) {N : ℕ} (hN : N ≠ 0)
    (ha : a / h < (N : ℝ)) : ⌊a / h⌋₊ < N := by
  apply (Nat.floor_lt' hN).mpr
  exact ha

def natFloorFin (a h : ℝ) (N : ℕ) (hh : 0 < h) (hN : N ≠ 0)
    (ha : a / h < (N : ℝ)) : Fin N :=
  ⟨⌊a / h⌋₊, natFloor_div_lt hh hN ha⟩

def natFloorFin_odd (a h : ℝ) (m : ℕ) (hh : 0 < h)
    (ha : a / h < (↑(2 * m + 1) : ℝ)) : Fin (2 * m + 1) :=
  natFloorFin a h (2 * m + 1) hh (by omega) ha

theorem triadic_scaled_coord_lt {d : ℕ} (z x : SpatialCoordinates d) (r h : ℝ)
    (m : ℕ) (hh : 0 < h) (hden : (2 * (m : ℝ) + 1) * h = r)
    (i : Fin d) (hx : x i < z i + r / 2) :
    (x i - (z i - r / 2)) / h < (↑(2 * m + 1) : ℝ) := by
  apply (div_lt_iff₀ hh).mpr
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  nlinarith

def triadicFaceSet {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (m : ℕ) (i : Fin d) (q : Fin (2 * m + 2)) : Set (SpatialCoordinates d) :=
  {x | x i = z i - r / 2 + (q : ℝ) * (r / (2 * (m : ℝ) + 1))}

theorem triadicFaceSet_null {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (_hr : 0 < r)
    (m : ℕ) (ν : Measure (SpatialCoordinates d))
    (hplanes : ∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0)
    (i : Fin d) (q : Fin (2 * m + 2)) : ν (triadicFaceSet z r m i q) = 0 := by
  exact hplanes i (z i - r / 2 + (q : ℝ) * (r / (2 * (m : ℝ) + 1)))

theorem triadicFaceSet_union_null {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (m : ℕ) (ν : Measure (SpatialCoordinates d))
    (hplanes : ∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0) :
    ν (⋃ i : Fin d, ⋃ q : Fin (2 * m + 2), triadicFaceSet z r m i q) = 0 := by
  apply MeasureTheory.measure_iUnion_null
  intro i
  apply MeasureTheory.measure_iUnion_null
  intro q
  exact triadicFaceSet_null z hr m ν hplanes i q

theorem mem_triadicCell_of_mem_cube_of_not_face {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (m : ℕ)
    (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hface : ∀ (i : Fin d) (q : Fin (2 * m + 2)),
      x ∉ triadicFaceSet z r m i q) :
    ∃ k : OddGridIndex d m,
      x ∈ (oddGridCell z r hr m k : Set (SpatialCoordinates d)) := by
  classical
  let h : ℝ := r / (2 * (m : ℝ) + 1)
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hden : (2 * (m : ℝ) + 1) * h = r := by
    dsimp [h]
    exact mul_div_cancel₀ _ (by positivity)
  have hxcoord : ∀ i : Fin d, z i - r / 2 < x i ∧ x i < z i + r / 2 := by
    rw [centeredCube_eq_pi z hr] at hx
    intro i
    exact (by simpa only [mem_pi, mem_univ, mem_Ioo] using hx i (by simp))
  let k : OddGridIndex d m := fun i => natFloorFin_odd
      (x i - (z i - r / 2)) h m hh
      (triadic_scaled_coord_lt z x r h m hh hden i (hxcoord i).2)
  refine ⟨k, ?_⟩
  rw [mem_oddGridCell]
  intro i
  have hq_nonneg : 0 ≤ (⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) := by positivity
  have hy_nonneg : 0 ≤ (x i - (z i - r / 2)) / h := by
    apply (div_nonneg_iff).mpr
    have hxi := hxcoord i
    have hnum : 0 ≤ x i - (z i - r / 2) := by linarith [hxi.1]
    exact Or.inl ⟨hnum, hh.le⟩
  have hq_le : (⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) ≤
      (x i - (z i - r / 2)) / h := by
    exact_mod_cast Nat.floor_le hy_nonneg
  have hq_ne : (⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) ≠
      (x i - (z i - r / 2)) / h := by
    intro heq
    have hN : 2 * m + 1 ≠ 0 := by omega
    have hupper : (x i - (z i - r / 2)) / h < (↑(2 * m + 1) : ℝ) :=
      triadic_scaled_coord_lt z x r h m hh hden i (hxcoord i).2
    have hq : ⌊(x i - (z i - r / 2)) / h⌋₊ < 2 * m + 1 :=
      natFloor_div_lt (a := x i - (z i - r / 2)) (h := h)
        (N := 2 * m + 1) hh hN hupper
    have hqi : ⌊(x i - (z i - r / 2)) / h⌋₊ < 2 * m + 2 := by omega
    apply hface i ⟨⌊(x i - (z i - r / 2)) / h⌋₊, hqi⟩
    change x i = z i - r / 2 + (⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) * h
    have heq' : (x i - (z i - r / 2)) / h =
        (⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) := heq.symm
    have heq'' := (div_eq_iff hh.ne').mp heq'
    linarith
  have hq_lt_real : (⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) <
      (x i - (z i - r / 2)) / h :=
    lt_of_le_of_ne hq_le hq_ne
  have hy_lt : (x i - (z i - r / 2)) / h <
      (⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one ((x i - (z i - r / 2)) / h)
  have hleft : z i + ((⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) - (m : ℝ)) * h - h / 2 =
      z i - r / 2 + (⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) * h := by
    nlinarith [hden]
  have hright : z i + ((⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) - (m : ℝ)) * h + h / 2 =
      z i - r / 2 + ((⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) + 1) * h := by
    nlinarith [hden]
  have hlow : z i - r / 2 + (⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) * h < x i := by
    have := (lt_div_iff₀ hh).mp hq_lt_real
    linarith
  have hupp : x i < z i - r / 2 +
      ((⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) + 1) * h := by
    have := (div_lt_iff₀ hh).mp hy_lt
    linarith
  constructor
  · change z i + ((⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) - (m : ℝ)) *
        (r / (2 * (m : ℝ) + 1)) - (r / (2 * (m : ℝ) + 1)) / 2 < x i
    rw [show r / (2 * (m : ℝ) + 1) = h by rfl, hleft]
    exact hlow
  · change x i < z i + ((⌊(x i - (z i - r / 2)) / h⌋₊ : ℝ) - (m : ℝ)) *
        (r / (2 * (m : ℝ) + 1)) + (r / (2 * (m : ℝ) + 1)) / 2
    rw [show r / (2 * (m : ℝ) + 1) = h by rfl, hright]
    exact hupp

theorem sum_indicator_triadicCell_eq {d : ℕ} (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (m : ℕ) (x : SpatialCoordinates d)
    (a : OddGridIndex d m → ℝ) (k₀ : OddGridIndex d m)
    (hx₀ : x ∈ (oddGridCell z r hr m k₀ : Set (SpatialCoordinates d))) :
    (∑ k : OddGridIndex d m,
      (oddGridCell z r hr m k : Set (SpatialCoordinates d)).indicator
        (fun _ => a k) x) = a k₀ := by
  classical
  rw [Finset.sum_eq_single k₀]
  · simp only [Set.indicator_of_mem hx₀]
  · intro k hk hne
    have hdisj := oddGridCell_pairwiseDisjoint z hr m hne
    have hxk : x ∉ (oddGridCell z r hr m k : Set (SpatialCoordinates d)) := by
      intro hxk
      exact Set.disjoint_left.mp hdisj hxk hx₀
    simp only [Set.indicator_of_notMem hxk]
  · intro h
    exact (h (Finset.mem_univ k₀)).elim

theorem sum_indicator_triadicCell_eq_zero_of_not_mem_root {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (m : ℕ)
    (x : SpatialCoordinates d) (a : OddGridIndex d m → ℝ)
    (hx : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    (∑ k : OddGridIndex d m,
      (oddGridCell z r hr m k : Set (SpatialCoordinates d)).indicator
        (fun _ => a k) x) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k hk
  have hxk : x ∉ (oddGridCell z r hr m k : Set (SpatialCoordinates d)) := by
    intro hxk
    exact hx (oddGridCell_subset z hr m k hxk)
  simp only [Set.indicator_of_notMem hxk]

theorem globalTriadicAverages_sub_eq_increment_ae
    {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) (ν : Measure (SpatialCoordinates d))
    (hplanes : ∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0)
    (f : SpatialCoordinates d → ℝ) :
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  let Δ : SpatialCoordinates d → ℝ := fun x =>
    ∑ j : OddGridIndex d (triadicHalf (n + 1)),
      (oddGridCell z r hr (triadicHalf (n + 1)) j : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
            (oddGridCell z r hr (triadicHalf (n + 1)) j : Set (SpatialCoordinates d)) f -
          averageOn
            (oddGridCell z r hr (triadicHalf n) (triadicParent n j) :
              Set (SpatialCoordinates d)) f) x
  (fun x => E (n + 1) x - E n x) =ᵐ[ν] Δ := by
  dsimp only
  let m : ℕ := triadicHalf (n + 1)
  let B : Set (SpatialCoordinates d) :=
    ⋃ i : Fin d, ⋃ q : Fin (2 * m + 2), triadicFaceSet z r m i q
  have hB : ν B = 0 := by
    dsimp [B, m]
    exact triadicFaceSet_union_null z hr (triadicHalf (n + 1)) ν hplanes
  have hgood : ∀ᵐ x ∂ν, x ∉ B := by
    apply ae_iff.2
    rw [show {x : SpatialCoordinates d | ¬ x ∉ B} = B by
      ext x
      simp]
    exact hB
  filter_upwards [hgood] with x hxB
  have hface : ∀ (i : Fin d) (q : Fin (2 * m + 2)),
      x ∉ triadicFaceSet z r m i q := by
    intro i q hq
    apply hxB
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨q, hq⟩⟩
  by_cases hxroot : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
  · obtain ⟨j, hj⟩ := mem_triadicCell_of_mem_cube_of_not_face
      z hr m x hxroot hface
    have hp : x ∈ (oddGridCell z r hr (triadicHalf n) (triadicParent n j) :
        Set (SpatialCoordinates d)) := by
      exact triadicCell_subset_parent z hr n j hj
    have hfine := sum_indicator_triadicCell_eq z hr
      (triadicHalf (n + 1)) x
      (fun k => averageOn
        (oddGridCell z r hr (triadicHalf (n + 1)) k : Set (SpatialCoordinates d)) f)
      j hj
    have hparent := sum_indicator_triadicCell_eq z hr
      (triadicHalf n) x
      (fun k => averageOn
        (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)) f)
      (triadicParent n j) hp
    have hdelta := sum_indicator_triadicCell_eq z hr
      (triadicHalf (n + 1)) x
      (fun k => averageOn
        (oddGridCell z r hr (triadicHalf (n + 1)) k : Set (SpatialCoordinates d)) f -
        averageOn
          (oddGridCell z r hr (triadicHalf n) (triadicParent n k) :
            Set (SpatialCoordinates d)) f)
      j hj
    rw [hfine, hparent, hdelta]
  · have hfine := sum_indicator_triadicCell_eq_zero_of_not_mem_root z hr
      (triadicHalf (n + 1)) x
      (fun k => averageOn
        (oddGridCell z r hr (triadicHalf (n + 1)) k : Set (SpatialCoordinates d)) f)
      hxroot
    have hparent := sum_indicator_triadicCell_eq_zero_of_not_mem_root z hr
      (triadicHalf n) x
      (fun k => averageOn
        (oddGridCell z r hr (triadicHalf n) k : Set (SpatialCoordinates d)) f)
      hxroot
    have hdelta := sum_indicator_triadicCell_eq_zero_of_not_mem_root z hr
      (triadicHalf (n + 1)) x
      (fun k => averageOn
        (oddGridCell z r hr (triadicHalf (n + 1)) k : Set (SpatialCoordinates d)) f -
        averageOn
          (oddGridCell z r hr (triadicHalf n) (triadicParent n k) :
            Set (SpatialCoordinates d)) f)
      hxroot
    rw [hfine, hparent, hdelta]
    norm_num


end SubdiffusiveProcess
