module

public import SubdiffusiveProcess.Paper.lfgc_p_trunc

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Layer footprints of the truncated scores

The truncated bad score `aux_lfgc_p_trunc_ztr … n y L` and the truncated drift score `aux_lfgc_p_trunc_dtr … n y L` depend on a
potential sample only through its layers `0, …, n + L`: the response atoms at cutoff `l` only
see the layers `0, …, l` (through the cutoff coefficient `a_l`), the field and product
truncations only see the layers up to `n + L`, and the drift head only the layers up to `n`.
-/

open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess
  Homogenization.Book
open scoped ENNReal BigOperators

namespace Paper
variable {d : ℕ}

/-- The cutoff coefficient family depends on the sample only through the coefficient. -/
theorem aux_lfgc_p_trunc_dep_aCutoffFamily_congr (M : GMCModel d) (L : ℕ) {ω ω' : PotentialSample d}
    (h : aCutoff M L ω = aCutoff M L ω') : aCutoffFamily M L ω = aCutoffFamily M L ω' := by
  have key : ∀ (a a' : Vec d → ℝ), a = a' →
      ∀ (p : ∀ U : Ch02.Domain d, Nonempty (ScalarCoeffOnData U a))
        (p' : ∀ U : Ch02.Domain d, Nonempty (ScalarCoeffOnData U a')),
      (⟨fun Q => Classical.choice (p (Ch02.cubeDomain Q))⟩ :
          ScalarTriadicCoeffData a).toTriadicCoeffFamily =
        (⟨fun Q => Classical.choice (p' (Ch02.cubeDomain Q))⟩ :
          ScalarTriadicCoeffData a').toTriadicCoeffFamily := by
    intro a a' ha p p'
    subst ha
    rfl
  exact key _ _ h (fun U => exists_aCutoffCoeffOnData M L ω U)
    (fun U => exists_aCutoffCoeffOnData M L ω' U)

theorem aux_lfgc_p_trunc_dep_aCutoff_translate_congr (M : GMCModel d) (L : ℕ) (x : Vec d) {g g' : PotentialSample d}
    (h : ∀ k ≤ L, g k = g' k) :
    aCutoff M L (translatePotentialSample x g) = aCutoff M L (translatePotentialSample x g') := by
  funext y
  unfold aCutoff translatePotentialSample
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]

/-- A response atom at cutoff `l` only sees the layers `0, …, l`. -/
theorem aux_lfgc_p_trunc_dep_jval_congr (M : GMCModel d) (l : ℕ) (x : Vec d) {g g' : PotentialSample d}
    (h : ∀ k ≤ l, g k = g' k) : Paper.aux_psf_Jval M l g x = Paper.aux_psf_Jval M l g' x := by
  unfold Paper.aux_psf_Jval section6Response
  rw [aux_lfgc_p_trunc_dep_aCutoffFamily_congr M l (aux_lfgc_p_trunc_dep_aCutoff_translate_congr M l x h)]

theorem aux_lfgc_p_trunc_dep_field_term_congr (s : ℝ) (n : ℕ) (y : Vec d) (j : ℕ) {g g' : PotentialSample d}
    (h : ∀ i ∈ Finset.Icc (n - j) (n + j), g i = g' i) :
    Paper.aux_lem_band_piece_field_term s n y g j =
      Paper.aux_lem_band_piece_field_term s n y g' j := by
  unfold Paper.aux_lem_band_piece_field_term
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i hi]

theorem aux_lfgc_p_trunc_dep_ftr_congr (s : ℝ) (n : ℕ) (y : Vec d) (L : ℕ) {g g' : PotentialSample d}
    (h : ∀ i ≤ n + L, g i = g' i) : aux_lfgc_p_trunc_ftr s n y L g = aux_lfgc_p_trunc_ftr s n y L g' := by
  have hT : ∀ j, j ≤ L → Paper.aux_lem_band_piece_field_term s n y g j =
      Paper.aux_lem_band_piece_field_term s n y g' j := fun j hj =>
    aux_lfgc_p_trunc_dep_field_term_congr s n y j fun i hi => h i (by have := (Finset.mem_Icc.mp hi).2; omega)
  unfold aux_lfgc_p_trunc_ftr
  congr 1
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, hT j hj⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, (hT j hj).symm⟩

theorem aux_lfgc_p_trunc_dep_pj_congr (n : ℕ) (y : Vec d) (L j : ℕ) (hj : j ≤ L) {g g' : PotentialSample d}
    (h : ∀ i ≤ n + L, g i = g' i) :
    Paper.aux_lem_band_piece_product_Pj d n y g L j =
      Paper.aux_lem_band_piece_product_Pj d n y g' L j := by
  have hA : ∀ x : Vec d, (∏ i ∈ Finset.Icc (n - j) (n + j), ENNReal.ofReal (Real.exp |g i x|)) =
      ∏ i ∈ Finset.Icc (n - j) (n + j), ENNReal.ofReal (Real.exp |g' i x|) := fun x =>
    Finset.prod_congr rfl fun i hi => by
      rw [h i (by have := (Finset.mem_Icc.mp hi).2; omega)]
  have hB : ∀ x : Vec d, (∏ i ∈ Finset.Icc (n + j) (n + L),
      ENNReal.ofReal (Real.exp (4 * |g i x - g i y|))) =
      ∏ i ∈ Finset.Icc (n + j) (n + L), ENNReal.ofReal (Real.exp (4 * |g' i x - g' i y|)) :=
    fun x => Finset.prod_congr rfl fun i hi => by
      rw [h i (Finset.mem_Icc.mp hi).2]
  unfold Paper.aux_lem_band_piece_product_Pj
  simp only [hA, hB]

theorem aux_lfgc_p_trunc_dep_pcand_congr (s : ℝ) (n : ℕ) (y : Vec d) (L : ℕ) {g g' : PotentialSample d}
    (h : ∀ i ≤ n + L, g i = g' i) :
    Paper.aux_lem_band_piece_product_trunc_Pcand d s n y g L =
      Paper.aux_lem_band_piece_product_trunc_Pcand d s n y g' L := by
  unfold Paper.aux_lem_band_piece_product_trunc_Pcand
  congr 1
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, by rw [aux_lfgc_p_trunc_dep_pj_congr n y L j hj h]⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, by rw [aux_lfgc_p_trunc_dep_pj_congr n y L j hj h]⟩

theorem aux_lfgc_p_trunc_dep_rfull_congr (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) {g g' : PotentialSample d}
    (h : ∀ i ≤ n, g i = g' i) : aux_lfgc_p_trunc_rfull M s n y g = aux_lfgc_p_trunc_rfull M s n y g' := by
  unfold aux_lfgc_p_trunc_rfull
  congr 1
  ext v
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, l, hj, hl, x, hx1, hx2, rfl⟩
    exact ⟨j, l, hj, hl, x, hx1, hx2, by rw [aux_lfgc_p_trunc_dep_jval_congr M l x fun k hk => h k (by omega)]⟩
  · rintro ⟨j, l, hj, hl, x, hx1, hx2, rfl⟩
    exact ⟨j, l, hj, hl, x, hx1, hx2, by rw [aux_lfgc_p_trunc_dep_jval_congr M l x fun k hk => h k (by omega)]⟩

theorem aux_lfgc_p_trunc_dep_dhead_congr (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) {g g' : PotentialSample d}
    (h : ∀ i ≤ n, g i = g' i) : aux_lfgc_p_trunc_dhead M s n y g = aux_lfgc_p_trunc_dhead M s n y g' := by
  have h1 : sSup {v : ℝ≥0∞ | ∃ j l : ℕ, j ≤ n ∧ l ≤ n ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid l (x - y) ∧ x - y ∈ cube d (j : ℤ) \ cube d ((j : ℤ) - 1) ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((n : ℝ) - (l : ℝ)))) *
        (min (Paper.aux_psf_Jval M l g x) 1) ^ (1 / 2 : ℝ)} =
      sSup {v : ℝ≥0∞ | ∃ j l : ℕ, j ≤ n ∧ l ≤ n ∧ l + 2 ≤ j ∧ ∃ x : Vec d,
      OnTriadicGrid l (x - y) ∧ x - y ∈ cube d (j : ℤ) \ cube d ((j : ℤ) - 1) ∧
      v = ENNReal.ofReal ((3 : ℝ) ^ (-(s / 2) * ((n : ℝ) - (l : ℝ)))) *
        (min (Paper.aux_psf_Jval M l g' x) 1) ^ (1 / 2 : ℝ)} := by
    congr 1
    ext v
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, l, hj, hl, hlj, x, hx1, hx2, rfl⟩
      exact ⟨j, l, hj, hl, hlj, x, hx1, hx2, by rw [aux_lfgc_p_trunc_dep_jval_congr M l x fun k hk => h k (by omega)]⟩
    · rintro ⟨j, l, hj, hl, hlj, x, hx1, hx2, rfl⟩
      exact ⟨j, l, hj, hl, hlj, x, hx1, hx2, by rw [aux_lfgc_p_trunc_dep_jval_congr M l x fun k hk => h k (by omega)]⟩
  have h2 : ∀ j x, shellBlock n j g x = shellBlock n j g' x := fun j x => by
    unfold shellBlock
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [h i (Finset.mem_Icc.mp hi).2]
  have h3 : g 0 = g' 0 := h 0 (Nat.zero_le n)
  unfold aux_lfgc_p_trunc_dhead
  rw [h1, h3]
  simp only [h2]

theorem aux_lfgc_p_trunc_dep_dtail_congr (n : ℕ) (y : Vec d) (j : ℕ) {g g' : PotentialSample d} (h : g j = g' j) :
    aux_lfgc_p_trunc_dtail n y g j = aux_lfgc_p_trunc_dtail n y g' j := by
  unfold aux_lfgc_p_trunc_dtail
  rw [h]

theorem lfgc_p_trunc_dep (M : GMCModel d) (s eps : ℝ) (n : ℕ) (y : Vec d) (L : ℕ)
    {g g' : PotentialSample d} (h : ∀ i ≤ n + L, g i = g' i) :
    aux_lfgc_p_trunc_ztr M s eps n y L g = aux_lfgc_p_trunc_ztr M s eps n y L g' := by
  unfold aux_lfgc_p_trunc_ztr
  rw [aux_lfgc_p_trunc_dep_ftr_congr s n y L h, aux_lfgc_p_trunc_dep_pcand_congr s n y L h,
    aux_lfgc_p_trunc_dep_rfull_congr M s n y fun i hi => h i (by omega)]

theorem aux_lfgc_p_trunc_dep_dtr_congr (M : GMCModel d) (s : ℝ) (n : ℕ) (y : Vec d) (L : ℕ)
    {g g' : PotentialSample d} (h : ∀ i ≤ n + L, g i = g' i) :
    aux_lfgc_p_trunc_dtr M s n y L g = aux_lfgc_p_trunc_dtr M s n y L g' := by
  unfold aux_lfgc_p_trunc_dtr
  rw [aux_lfgc_p_trunc_dep_dhead_congr M s n y fun i hi => h i (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  exact aux_lfgc_p_trunc_dep_dtail_congr n y j (h j (by have := Finset.mem_range.mp hj; omega))

end Paper
