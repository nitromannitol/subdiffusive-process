import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import Mathlib

/-!
# Half-open triadic cells and covers of the centered cube

`cell d i w` is the half-open cell `∏_a [3^i (w_a - 1/2), 3^i (w_a + 1/2))`.  It agrees almost everywhere with
the translate `cube d i + cellShift d i w` of the open centered cube, so essential suprema over the two agree.
Cells are nested (a scale-`n` cell lies in a unique scale-`i` cell for `n ≤ i`), and the centered cube
`cube d (n + m)` is covered by `3^{m d}` scale-`n` cells.
-/

namespace SubdiffusiveProcess.ConcentrationScales

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- The half-open triadic cell of scale `3^i` and integer index `w`. -/
def cell (d : ℕ) (i : ℤ) (w : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ a, (3 : ℝ) ^ i * ((w a : ℝ) - 1 / 2) ≤ x a ∧ x a < (3 : ℝ) ^ i * ((w a : ℝ) + 1 / 2)}

/-- The open triadic cell of scale `3^i` and integer index `w`. -/
def openCell (d : ℕ) (i : ℤ) (w : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ a, (3 : ℝ) ^ i * ((w a : ℝ) - 1 / 2) < x a ∧ x a < (3 : ℝ) ^ i * ((w a : ℝ) + 1 / 2)}

/-- The centre of the cell `(i, w)`, a point of `3^i ℤ^d`. -/
def cellShift (d : ℕ) (i : ℤ) (w : Fin d → ℤ) : Vec d := fun a => (3 : ℝ) ^ i * (w a : ℝ)

theorem mem_cube_iff {d : ℕ} {i : ℤ} {x : Vec d} :
    x ∈ cube d i ↔ ∀ a, (-(1 / 2 : ℝ)) * (3 : ℝ) ^ i < x a ∧ x a < (1 / 2 : ℝ) * (3 : ℝ) ^ i := by
  unfold cube
  exact Homogenization.mem_openCubeSet_originCube_iff

theorem cell_eq_pi (d : ℕ) (i : ℤ) (w : Fin d → ℤ) :
    cell d i w = Set.pi Set.univ fun a =>
      Set.Ico ((3 : ℝ) ^ i * ((w a : ℝ) - 1 / 2)) ((3 : ℝ) ^ i * ((w a : ℝ) + 1 / 2)) := by
  ext x
  simp [cell, Set.mem_pi]

theorem openCell_eq_pi (d : ℕ) (i : ℤ) (w : Fin d → ℤ) :
    openCell d i w = Set.pi Set.univ fun a =>
      Set.Ioo ((3 : ℝ) ^ i * ((w a : ℝ) - 1 / 2)) ((3 : ℝ) ^ i * ((w a : ℝ) + 1 / 2)) := by
  ext x
  simp [openCell, Set.mem_pi]

theorem measurableSet_cell (d : ℕ) (i : ℤ) (w : Fin d → ℤ) : MeasurableSet (cell d i w) := by
  rw [cell_eq_pi]
  exact MeasurableSet.univ_pi fun a => measurableSet_Ico

theorem measurableSet_openCell (d : ℕ) (i : ℤ) (w : Fin d → ℤ) : MeasurableSet (openCell d i w) := by
  rw [openCell_eq_pi]
  exact MeasurableSet.univ_pi fun a => measurableSet_Ioo

theorem openCell_subset_cell (d : ℕ) (i : ℤ) (w : Fin d → ℤ) : openCell d i w ⊆ cell d i w :=
  fun _ hx a => ⟨(hx a).1.le, (hx a).2⟩

theorem openCell_eq_image (d : ℕ) (i : ℤ) (w : Fin d → ℤ) :
    openCell d i w = (fun x => x + cellShift d i w) '' cube d i := by
  ext x
  constructor
  · intro hx
    refine ⟨x - cellShift d i w, ?_, by simp⟩
    rw [mem_cube_iff]
    intro a
    have h := hx a
    simp only [cellShift, Pi.sub_apply]
    constructor <;> nlinarith [h.1, h.2, zpow_pos (by norm_num : (0 : ℝ) < 3) i]
  · rintro ⟨y, hy, rfl⟩ a
    have h := (mem_cube_iff.mp hy) a
    simp only [cellShift, Pi.add_apply]
    constructor <;> nlinarith [h.1, h.2, zpow_pos (by norm_num : (0 : ℝ) < 3) i]

theorem volume_cell (d : ℕ) (i : ℤ) (w : Fin d → ℤ) :
    volume (cell d i w) = ∏ _a : Fin d, ENNReal.ofReal ((3 : ℝ) ^ i) := by
  rw [cell_eq_pi, Real.volume_pi_Ico]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  ring

theorem volume_openCell (d : ℕ) (i : ℤ) (w : Fin d → ℤ) :
    volume (openCell d i w) = ∏ _a : Fin d, ENNReal.ofReal ((3 : ℝ) ^ i) := by
  rw [openCell_eq_pi, Real.volume_pi_Ioo]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  ring

theorem openCell_ae_eq_cell (d : ℕ) (i : ℤ) (w : Fin d → ℤ) :
    openCell d i w =ᵐ[volume] cell d i w := by
  refine ae_eq_of_subset_of_measure_ge (openCell_subset_cell d i w) ?_
    (measurableSet_openCell d i w).nullMeasurableSet ?_
  · rw [volume_cell, volume_openCell]
  · rw [volume_cell]
    exact (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top).ne

/-- Essential suprema over a cell are essential suprema over the open centered cube of the translated function. -/
theorem essSup_cell_eq (d : ℕ) (i : ℤ) (w : Fin d → ℤ) (f : Vec d → ℝ≥0∞) :
    essSup f (volume.restrict (cell d i w)) =
      essSup (fun x => f (x + cellShift d i w)) (volume.restrict (cube d i)) := by
  have hemb : MeasurableEmbedding (fun x : Vec d => x + cellShift d i w) :=
    measurableEmbedding_addRight _
  have hmp := (measurePreserving_add_right (volume : Measure (Vec d)) (cellShift d i w)).restrict_image_emb
    hemb (cube d i)
  have hmap : (volume.restrict (cube d i)).map (fun x : Vec d => x + cellShift d i w) =
      volume.restrict (cell d i w) := by
    rw [hmp.map_eq, ← openCell_eq_image, Measure.restrict_congr_set (openCell_ae_eq_cell d i w)]
  rw [← hmap]
  exact hemb.essSup_map_measure


theorem int_nest {P w u : ℤ} (hP : Odd P) (h1 : P * (2 * w - 1) ≤ 2 * u)
    (h2 : 2 * u < P * (2 * w + 1)) :
    P * (2 * w - 1) + 1 ≤ 2 * u ∧ 2 * u + 1 ≤ P * (2 * w + 1) := by
  have o1 : Odd (P * (2 * w - 1)) := hP.mul ⟨w - 1, by ring⟩
  have o2 : Odd (P * (2 * w + 1)) := hP.mul ⟨w, by ring⟩
  obtain ⟨q1, hq1⟩ := o1
  obtain ⟨q2, hq2⟩ := o2
  constructor <;> omega

/-- The index of the scale-`i` cell containing the scale-`n` cell of index `u` (for `n ≤ i`). -/
def parentIdx (d : ℕ) (n i : ℤ) (u : Fin d → ℤ) : Fin d → ℤ :=
  fun a => ⌊(3 : ℝ) ^ n * (u a : ℝ) / (3 : ℝ) ^ i + 1 / 2⌋

theorem cell_subset_parent {d : ℕ} {n i : ℤ} (hni : n ≤ i) (u : Fin d → ℤ) :
    cell d n u ⊆ cell d i (parentIdx d n i u) := by
  intro x hx a
  obtain ⟨hlo, hhi⟩ := hx a
  obtain ⟨m, hm⟩ : ∃ m : ℕ, i = n + m := ⟨(i - n).toNat, by omega⟩
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := pow_pos (by norm_num) m
  have hpow : (3 : ℝ) ^ i = (3 : ℝ) ^ n * (3 : ℝ) ^ m := by
    rw [hm, zpow_add₀ (by norm_num), zpow_natCast]
  have hdiv : (3 : ℝ) ^ n * (u a : ℝ) / (3 : ℝ) ^ i = (u a : ℝ) / (3 : ℝ) ^ m := by
    rw [hpow, mul_div_mul_left _ _ h3n.ne']
  obtain ⟨w, hw⟩ : ∃ w : ℤ, parentIdx d n i u a = w := ⟨_, rfl⟩
  have hfl : (w : ℝ) ≤ (u a : ℝ) / (3 : ℝ) ^ m + 1 / 2 := by
    rw [← hw, ← hdiv]; exact Int.floor_le _
  have hfl2 : (u a : ℝ) / (3 : ℝ) ^ m + 1 / 2 < (w : ℝ) + 1 := by
    rw [← hw, ← hdiv]; exact Int.lt_floor_add_one _
  show (3 : ℝ) ^ i * (((parentIdx d n i u a : ℤ) : ℝ) - 1 / 2) ≤ x a ∧
    x a < (3 : ℝ) ^ i * (((parentIdx d n i u a : ℤ) : ℝ) + 1 / 2)
  rw [hw]
  set P : ℤ := (3 : ℤ) ^ m with hP
  have hPR : (P : ℝ) = (3 : ℝ) ^ m := by simp [hP]
  have hPodd : Odd P := Odd.pow (by decide)
  have hPpos : (0 : ℝ) < (P : ℝ) := by rw [hPR]; exact h3m
  have e1 : (P : ℝ) * (2 * w - 1) ≤ 2 * u a := by
    have h := (le_div_iff₀ hPpos).mp
      (by rw [hPR]; linarith : (w : ℝ) - 1 / 2 ≤ (u a : ℝ) / (P : ℝ))
    nlinarith
  have e2 : (2 * u a : ℝ) < (P : ℝ) * (2 * w + 1) := by
    have h := (div_lt_iff₀ hPpos).mp
      (by rw [hPR]; linarith : (u a : ℝ) / (P : ℝ) < (w : ℝ) + 1 / 2)
    nlinarith
  have i1 : P * (2 * w - 1) ≤ 2 * u a := by exact_mod_cast e1
  have i2 : 2 * u a < P * (2 * w + 1) := by exact_mod_cast e2
  obtain ⟨j1, j2⟩ := int_nest hPodd i1 i2
  have r1 : (P : ℝ) * (2 * w - 1) + 1 ≤ 2 * u a := by exact_mod_cast j1
  have r2 : 2 * (u a : ℝ) + 1 ≤ (P : ℝ) * (2 * w + 1) := by exact_mod_cast j2
  rw [hPR] at r1 r2
  rw [hpow]
  constructor
  · nlinarith
  · nlinarith

/-- `K m` is the half-width of the index box: `2 K m + 1 = 3 ^ m`. -/
def boxHalf (m : ℕ) : ℕ := 3 ^ m / 2

theorem two_mul_boxHalf_add_one (m : ℕ) : 2 * boxHalf m + 1 = 3 ^ m :=
  Nat.two_mul_div_two_add_one_of_odd (Odd.pow (by decide))

/-- The box of indices of scale-`n` cells covering `cube d (n + m)`. -/
def idxBox (d m : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(boxHalf m : ℤ)) (boxHalf m : ℤ)

theorem card_idxBox (d m : ℕ) : (idxBox d m).card = (3 ^ m) ^ d := by
  have hcard : (Finset.Icc (-(boxHalf m : ℤ)) (boxHalf m : ℤ)).card = 3 ^ m := by
    rw [Int.card_Icc]
    have := two_mul_boxHalf_add_one m
    omega
  simp [idxBox, Fintype.card_piFinset, hcard]

theorem cube_subset_iUnion_cell (d : ℕ) (n : ℤ) (m : ℕ) :
    cube d (n + m) ⊆ ⋃ u ∈ idxBox d m, cell d n u := by
  intro x hx
  rw [mem_cube_iff] at hx
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hpow : (3 : ℝ) ^ (n + m) = (3 : ℝ) ^ n * (3 : ℝ) ^ m := by
    rw [zpow_add₀ (by norm_num), zpow_natCast]
  have hK : (2 : ℝ) * (boxHalf m : ℝ) + 1 = (3 : ℝ) ^ m := by exact_mod_cast two_mul_boxHalf_add_one m
  simp only [Set.mem_iUnion]
  refine ⟨fun a => ⌊x a / (3 : ℝ) ^ n + 1 / 2⌋, ?_, ?_⟩
  · simp only [idxBox, Fintype.mem_piFinset, Finset.mem_Icc]
    intro a
    obtain ⟨hlo, hhi⟩ := hx a
    rw [hpow] at hlo hhi
    have hy1 : x a / (3 : ℝ) ^ n < (3 : ℝ) ^ m / 2 := by
      rw [div_lt_iff₀ h3n]; nlinarith
    have hy2 : -((3 : ℝ) ^ m / 2) < x a / (3 : ℝ) ^ n := by
      rw [lt_div_iff₀ h3n]; nlinarith
    have hf1 := Int.floor_le (x a / (3 : ℝ) ^ n + 1 / 2)
    have hf2 := Int.lt_floor_add_one (x a / (3 : ℝ) ^ n + 1 / 2)
    constructor
    · have : (-(boxHalf m : ℝ)) - 1 < (⌊x a / (3 : ℝ) ^ n + 1 / 2⌋ : ℝ) := by linarith
      have : -(boxHalf m : ℤ) - 1 < ⌊x a / (3 : ℝ) ^ n + 1 / 2⌋ := by exact_mod_cast this
      omega
    · have : (⌊x a / (3 : ℝ) ^ n + 1 / 2⌋ : ℝ) < (boxHalf m : ℝ) + 1 := by linarith
      have : ⌊x a / (3 : ℝ) ^ n + 1 / 2⌋ < (boxHalf m : ℤ) + 1 := by exact_mod_cast this
      omega
  · intro a
    have hf1 := Int.floor_le (x a / (3 : ℝ) ^ n + 1 / 2)
    have hf2 := Int.lt_floor_add_one (x a / (3 : ℝ) ^ n + 1 / 2)
    have e1 : x a / (3 : ℝ) ^ n * (3 : ℝ) ^ n = x a := div_mul_cancel₀ _ h3n.ne'
    constructor <;> nlinarith

end

end SubdiffusiveProcess.ConcentrationScales
