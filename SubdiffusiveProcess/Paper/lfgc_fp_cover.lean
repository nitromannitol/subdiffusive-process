module

public import SubdiffusiveProcess.Paper.lfgc_fp_bound2
public import SubdiffusiveProcess.Paper.lfgc_fp_det
public import SubdiffusiveProcess.Paper.lfgc_family_cover

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory _root_.SubdiffusiveProcess.Model SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The pad-test bank failure event. -/
def aux_lfgc_fp_cover_fpBad (s : ℝ) (N n : ℕ) {ns : ℕ} (y : Fin ns → Vec d) : Set (BilateralField d) :=
  {omega | ∃ t : Fin ns, ∃ j : ℕ,
    (∃ i ∈ Finset.Icc (n - j) (n + j),
      omega ∈ aux_lfgc_fp_events_bankEv N i (n + 1 + j) (y t) ((3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1))) ∨
    omega ∈ aux_lfgc_fp_events_amajEv N n j (y t) (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8)) ∨
    ∃ l : ℕ, omega ∈ aux_lfgc_fp_events_bankEv N (n + j + l) (n + 1 + j) (y t) (aux_lfgc_fp_bound2_tB s j l)}

/-- Off the failure event all bank bounds hold. -/
theorem lfgc_fp_cover (s : ℝ) (hs : 0 ≤ s) (N n : ℕ) {ns : ℕ} (y : Fin ns → Vec d)
    (omega : BilateralField d) (hω : omega ∉ aux_lfgc_fp_cover_fpBad s N n y) (t : Fin ns) :
    (∀ j : ℕ, ∀ i ∈ Finset.Icc (n - j) (n + j),
      _root_.SubdiffusiveProcess.Paper.aux_prefix_praw_bank i (n + 1 + j) (y t) (aux_lfgc_layer_tail_canonEta N omega) ≤
        (3 : ℝ) ^ (s * (j : ℝ) / 8) / (2 * j + 1)) ∧
    (∀ j : ℕ, _root_.SubdiffusiveProcess.Paper.aux_prefix_praw_Amaj n j (y t) (aux_lfgc_layer_tail_canonEta N omega) ≤
      ENNReal.ofReal (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8))) ∧
    (∀ j : ℕ, _root_.SubdiffusiveProcess.Paper.aux_prefix_praw_Bmaj n j (y t) (aux_lfgc_layer_tail_canonEta N omega) ≤
      ENNReal.ofReal (6 * (3 : ℝ) ^ (s * (j : ℝ) / 8))) := by
  simp only [aux_lfgc_fp_cover_fpBad, Set.mem_ofPred_eq, not_exists, not_or, not_and] at hω
  refine ⟨fun j i hi => ?_, fun j => ?_, fun j => ?_⟩
  · have := (hω t j).1 i hi
    simp only [aux_lfgc_fp_events_bankEv, Set.mem_ofPred_eq, not_lt] at this
    exact this
  · have := (hω t j).2.1
    simp only [aux_lfgc_fp_events_amajEv, Set.mem_ofPred_eq, not_lt] at this
    exact this
  · refine aux_lfgc_fp_det_bmaj_le s hs n j (y t) (aux_lfgc_layer_tail_canonEta N omega) fun l => ?_
    have := (hω t j).2.2 l
    simp only [aux_lfgc_fp_events_bankEv, Set.mem_ofPred_eq, not_lt] at this
    have hlam : 0 ≤ _root_.SubdiffusiveProcess.Paper.aux_psf_lam n j (n + j + l) := (_root_.SubdiffusiveProcess.Paper.aux_psf_lam_pos n j _).le
    rw [← aux_lfgc_fp_bound2_lam_mul_tB s n j l]
    exact mul_le_mul_of_nonneg_left this hlam

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
theorem aux_lfgc_fp_cover_sq_ge_of_le_div {c σ L : ℝ} (hσ : 0 < σ) (hL : 0 < L)
    (h : σ ≤ c / Real.sqrt L) : L ≤ (c / σ) ^ 2 := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have h1 : Real.sqrt L ≤ c / σ := by
    rw [le_div_iff₀ hσ]
    rw [le_div_iff₀ hs] at h
    linarith
  calc L = Real.sqrt L ^ 2 := (Real.sq_sqrt hL.le).symm
    _ ≤ (c / σ) ^ 2 := pow_le_pow_left₀ hs.le h1 2

/-- One window of the pad-test cover. -/
def aux_lfgc_fp_cover_fpWin (s : ℝ) (N n : ℕ) {ns : ℕ} (y : Fin ns → Vec d) (h : ℕ) : Set (BilateralField d) :=
  ⋃ t : Fin ns,
    ((⋃ i ∈ Finset.Icc (n - (h - 1)) (n + (h - 1)),
        aux_lfgc_fp_events_bankEv N i (n + 1 + (h - 1)) (y t)
          ((3 : ℝ) ^ (s * ((h - 1 : ℕ) : ℝ) / 8) / (2 * ((h - 1 : ℕ) : ℝ) + 1))) ∪
      aux_lfgc_fp_events_amajEv N n (h - 1) (y t) (6 * (3 : ℝ) ^ (s * ((h - 1 : ℕ) : ℝ) / 8)) ∪
      ⋃ l ∈ Finset.range h,
        aux_lfgc_fp_events_bankEv N (n + (h - 1 - l) + l) (n + 1 + (h - 1 - l)) (y t) (aux_lfgc_fp_bound2_tB s (h - 1 - l) l))

theorem aux_lfgc_fp_cover_fpBad_subset (s : ℝ) (N n : ℕ) {ns : ℕ} (y : Fin ns → Vec d) :
    aux_lfgc_fp_cover_fpBad s N n y ⊆ ⋃ h : ℕ+, aux_lfgc_fp_cover_fpWin s N n y h := by
  intro omega hω
  obtain ⟨t, j, hcase⟩ := hω
  rcases hcase with ⟨i, hi, hb⟩ | ha | ⟨l, hb⟩
  · refine Set.mem_iUnion.mpr ⟨⟨j + 1, Nat.succ_pos j⟩, Set.mem_iUnion.mpr ⟨t, ?_⟩⟩
    simp only [PNat.mk_coe, Nat.add_sub_cancel]
    exact Or.inl (Or.inl (Set.mem_biUnion hi hb))
  · refine Set.mem_iUnion.mpr ⟨⟨j + 1, Nat.succ_pos j⟩, Set.mem_iUnion.mpr ⟨t, ?_⟩⟩
    simp only [PNat.mk_coe, Nat.add_sub_cancel]
    exact Or.inl (Or.inr ha)
  · refine Set.mem_iUnion.mpr ⟨⟨j + l + 1, Nat.succ_pos _⟩, Set.mem_iUnion.mpr ⟨t, ?_⟩⟩
    simp only [PNat.mk_coe]
    have hj : j + l + 1 - 1 - l = j := by omega
    refine Or.inr (Set.mem_biUnion (x := l) (Finset.mem_range.mpr (show l < j + l + 1 by omega)) ?_)
    rw [hj]
    exact hb

theorem aux_lfgc_fp_cover_measurableSet_fpWin (s : ℝ) (m k : ℕ) {ns : ℕ} (y : Fin ns → Vec d) (h : ℕ+) :
    MeasurableSet[aux_lfgc_family_cover_nodeWin d k h] (aux_lfgc_fp_cover_fpWin s (m + k) (m + 1) y h) := by
  have hh := h.pos
  refine MeasurableSet.iUnion fun t => ?_
  refine MeasurableSet.union (MeasurableSet.union ?_ ?_) ?_
  · refine MeasurableSet.biUnion (Set.to_countable _) fun i hi => ?_
    refine aux_lfgc_fp_events_measurableSet_bankEv _ _ _ _ _ _ ?_
    have hi' := Finset.mem_Icc.mp hi
    simp only [Set.mem_Icc]
    constructor <;> push_cast <;> omega
  · refine aux_lfgc_fp_events_measurableSet_amajEv _ _ _ _ _ _ fun i hi => ?_
    have hi' := Finset.mem_Icc.mp hi
    simp only [Set.mem_Icc]
    constructor <;> push_cast <;> omega
  · refine MeasurableSet.biUnion (Set.to_countable _) fun l hl => ?_
    refine aux_lfgc_fp_events_measurableSet_bankEv _ _ _ _ _ _ ?_
    have hl' := Finset.mem_range.mp hl
    simp only [Set.mem_Icc]
    constructor <;> push_cast <;> omega

end SubdiffusiveProcess.Paper
