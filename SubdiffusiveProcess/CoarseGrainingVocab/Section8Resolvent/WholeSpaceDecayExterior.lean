module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayGraph
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The extended nonnegative `L²` mass of `u` on `s`. -/
def wholeSpaceL2Mass (u : Vec d → ℝ) (s : Set (Vec d)) : ℝ≥0∞ :=
  ∫⁻ x in s, ENNReal.ofReal (u x ^ 2) ∂volume

/-- An ordinary squared integral is the real value of `wholeSpaceL2Mass` for
an `L²` function. -/
theorem integral_sq_eq_toReal_wholeSpaceL2Mass {u : Vec d → ℝ}
    (hu : MemLp u 2 volume) (s : Set (Vec d)) :
    ∫ x in s, u x ^ 2 ∂volume = (wholeSpaceL2Mass u s).toReal := by
  have hsq : Integrable (fun x ↦ u x ^ 2) volume := hu.integrable_sq
  have hnonneg : 0 ≤ᵐ[volume.restrict s] fun x ↦ u x ^ 2 :=
    Filter.Eventually.of_forall fun x ↦ sq_nonneg (u x)
  simpa only [wholeSpaceL2Mass] using
    (integral_eq_lintegral_of_nonneg_ae hnonneg hsq.integrableOn.aestronglyMeasurable)

/-- Sum a geometric family of finite graph shells covering an exterior set.

`count j` is the number of enumerated cells in graph shell `j`.  The cover is
written with the shifted shells `n + k`, which is exactly the output supplied
by a graph-distance lower bound. -/
theorem wholeSpaceL2Mass_exterior_le_geometric
    (u : Vec d → ℝ) (count : ℕ → ℕ)
    (cell : (j : ℕ) → Fin (count j) → Set (Vec d))
    (exterior : Set (Vec d)) (n : ℕ) {A q : ℝ}
    (hcover : exterior ⊆
      ⋃ p : Σ k : ℕ, Fin (count (n + k)), cell (n + p.1) p.2)
    (hshell : ∀ j,
      ∑ i : Fin (count j), wholeSpaceL2Mass u (cell j i) ≤
        ENNReal.ofReal A * ENNReal.ofReal q ^ j) :
    wholeSpaceL2Mass u exterior ≤
      ENNReal.ofReal A * ENNReal.ofReal q ^ n *
        (1 - ENNReal.ofReal q)⁻¹ := by
  let shiftedCell : (Σ k : ℕ, Fin (count (n + k))) → Set (Vec d) :=
    fun p ↦ cell (n + p.1) p.2
  have hrestrict : volume.restrict exterior ≤
      volume.restrict (⋃ p, shiftedCell p) :=
    Measure.restrict_mono hcover le_rfl
  calc
    wholeSpaceL2Mass u exterior ≤
        wholeSpaceL2Mass u (⋃ p, shiftedCell p) := by
      exact lintegral_mono' hrestrict le_rfl
    _ ≤ ∑' p, wholeSpaceL2Mass u (shiftedCell p) := by
      exact lintegral_iUnion_le shiftedCell (fun x ↦ ENNReal.ofReal (u x ^ 2))
    _ = ∑' k, ∑' i : Fin (count (n + k)),
          wholeSpaceL2Mass u (cell (n + k) i) := by
      exact ENNReal.tsum_sigma' _
    _ ≤ ∑' k, ENNReal.ofReal A * ENNReal.ofReal q ^ (n + k) := by
      exact ENNReal.tsum_le_tsum fun k ↦ by
        simpa only [tsum_fintype] using hshell (n + k)
    _ = ENNReal.ofReal A * ENNReal.ofReal q ^ n *
          (1 - ENNReal.ofReal q)⁻¹ := by
      simp_rw [pow_add, mul_assoc]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- Real-valued form of `wholeSpaceL2Mass_exterior_le_geometric`. -/
theorem integral_sq_exterior_le_geometric
    {u : Vec d → ℝ} (hu : MemLp u 2 volume) (count : ℕ → ℕ)
    (cell : (j : ℕ) → Fin (count j) → Set (Vec d))
    (exterior : Set (Vec d)) (n : ℕ) {A q : ℝ}
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hqOne : q < 1)
    (hcover : exterior ⊆
      ⋃ p : Σ k : ℕ, Fin (count (n + k)), cell (n + p.1) p.2)
    (hshell : ∀ j,
      ∑ i : Fin (count j), wholeSpaceL2Mass u (cell j i) ≤
        ENNReal.ofReal A * ENNReal.ofReal q ^ j) :
    ∫ x in exterior, u x ^ 2 ∂volume ≤
      A * q ^ n * (1 - q)⁻¹ := by
  let bound : ℝ≥0∞ := ENNReal.ofReal A * ENNReal.ofReal q ^ n *
    (1 - ENNReal.ofReal q)⁻¹
  have hqENN : ENNReal.ofReal q < 1 := ENNReal.ofReal_lt_one.mpr hqOne
  have hboundTop : bound ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
    · exact ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hqENN).ne'
  have hmass := wholeSpaceL2Mass_exterior_le_geometric
    u count cell exterior n hcover hshell
  have hreal := ENNReal.toReal_mono hboundTop hmass
  rw [integral_sq_eq_toReal_wholeSpaceL2Mass hu]
  calc
    (wholeSpaceL2Mass u exterior).toReal ≤ bound.toReal := hreal
    _ = A * q ^ n * (1 - q)⁻¹ := by
      have hqENNle : ENNReal.ofReal q ≤ 1 := hqENN.le
      simp only [bound, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
        ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq]
      rw [ENNReal.toReal_sub_of_le hqENNle (by simp)]
      simp only [ENNReal.toReal_one, ENNReal.toReal_ofReal hq]

/-- Version of `integral_sq_exterior_le_geometric` whose shell hypothesis is
stated with ordinary real integrals.  `L²` integrability supplies the finiteness
needed to move the finite shell sums through `ENNReal.ofReal`. -/
theorem integral_sq_exterior_le_geometric_of_real_shell
    {u : Vec d → ℝ} (hu : MemLp u 2 volume) (count : ℕ → ℕ)
    (cell : (j : ℕ) → Fin (count j) → Set (Vec d))
    (exterior : Set (Vec d)) (n : ℕ) {A q : ℝ}
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hqOne : q < 1)
    (hcover : exterior ⊆
      ⋃ p : Σ k : ℕ, Fin (count (n + k)), cell (n + p.1) p.2)
    (hshell : ∀ j,
      ∑ i : Fin (count j), ∫ x in cell j i, u x ^ 2 ∂volume ≤
        A * q ^ j) :
    ∫ x in exterior, u x ^ 2 ∂volume ≤
      A * q ^ n * (1 - q)⁻¹ := by
  apply integral_sq_exterior_le_geometric hu count cell exterior n hA hq hqOne
    hcover
  intro j
  calc
    ∑ i : Fin (count j), wholeSpaceL2Mass u (cell j i) =
        ∑ i : Fin (count j), ENNReal.ofReal
          (∫ x in cell j i, u x ^ 2 ∂volume) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hfinite : wholeSpaceL2Mass u (cell j i) ≠ ⊤ := by
        exact (hu.integrable_sq.integrableOn.setLIntegral_lt_top).ne
      rw [integral_sq_eq_toReal_wholeSpaceL2Mass hu]
      exact (ENNReal.ofReal_toReal hfinite).symm
    _ = ENNReal.ofReal
        (∑ i : Fin (count j), ∫ x in cell j i, u x ^ 2 ∂volume) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _hi
      exact integral_nonneg fun x ↦ sq_nonneg (u x)
    _ ≤ ENNReal.ofReal (A * q ^ j) :=
      ENNReal.ofReal_mono (hshell j)
    _ = ENNReal.ofReal A * ENNReal.ofReal q ^ j := by
      rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_pow hq]

/-- A geometric power at the ceiling of a nonnegative real number has the
corresponding exponential decay. -/
theorem pow_natCeil_le_exp_log {q x : ℝ} (hq : 0 < q) (hqOne : q < 1) :
    q ^ ⌈x⌉₊ ≤ Real.exp (Real.log q * x) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (Nat.le_ceil x) (Real.log_neg hq hqOne).le

/-- Exponential version of the exterior shell estimate.  The prefactor
`(1-q)⁻¹` is the exact cost of summing all shells beyond the graph-distance
threshold. -/
theorem integral_sq_exterior_le_exp
    {u : Vec d → ℝ} (hu : MemLp u 2 volume) (count : ℕ → ℕ)
    (cell : (j : ℕ) → Fin (count j) → Set (Vec d))
    (exterior : Set (Vec d)) {A q rate : ℝ}
    (hA : 0 ≤ A) (hq : 0 < q) (hqOne : q < 1)
    (hcover : exterior ⊆
      ⋃ p : Σ k : ℕ, Fin (count (⌈rate⌉₊ + k)),
        cell (⌈rate⌉₊ + p.1) p.2)
    (hshell : ∀ j,
      ∑ i : Fin (count j), wholeSpaceL2Mass u (cell j i) ≤
        ENNReal.ofReal A * ENNReal.ofReal q ^ j) :
    ∫ x in exterior, u x ^ 2 ∂volume ≤
      A * (1 - q)⁻¹ * Real.exp (Real.log q * rate) := by
  have hgeom := integral_sq_exterior_le_geometric hu count cell exterior
    ⌈rate⌉₊ hA hq.le hqOne hcover hshell
  have hpow := pow_natCeil_le_exp_log (x := rate) hq hqOne
  have hinv : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hqOne.le)
  calc
    ∫ x in exterior, u x ^ 2 ∂volume ≤
        A * q ^ ⌈rate⌉₊ * (1 - q)⁻¹ := hgeom
    _ ≤ A * Real.exp (Real.log q * rate) * (1 - q)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hA) hinv
    _ = A * (1 - q)⁻¹ * Real.exp (Real.log q * rate) := by ring

/-- Real-shell form of the exponential exterior estimate. -/
theorem integral_sq_exterior_le_exp_of_real_shell
    {u : Vec d → ℝ} (hu : MemLp u 2 volume) (count : ℕ → ℕ)
    (cell : (j : ℕ) → Fin (count j) → Set (Vec d))
    (exterior : Set (Vec d)) {A q rate : ℝ}
    (hA : 0 ≤ A) (hq : 0 < q) (hqOne : q < 1)
    (hcover : exterior ⊆
      ⋃ p : Σ k : ℕ, Fin (count (⌈rate⌉₊ + k)),
        cell (⌈rate⌉₊ + p.1) p.2)
    (hshell : ∀ j,
      ∑ i : Fin (count j), ∫ x in cell j i, u x ^ 2 ∂volume ≤
        A * q ^ j) :
    ∫ x in exterior, u x ^ 2 ∂volume ≤
      A * (1 - q)⁻¹ * Real.exp (Real.log q * rate) := by
  have hgeom := integral_sq_exterior_le_geometric_of_real_shell hu count cell
    exterior ⌈rate⌉₊ hA hq.le hqOne hcover hshell
  have hpow := pow_natCeil_le_exp_log (x := rate) hq hqOne
  have hinv : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hqOne.le)
  calc
    ∫ x in exterior, u x ^ 2 ∂volume ≤
        A * q ^ ⌈rate⌉₊ * (1 - q)⁻¹ := hgeom
    _ ≤ A * Real.exp (Real.log q * rate) * (1 - q)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hA) hinv
    _ = A * (1 - q)⁻¹ * Real.exp (Real.log q * rate) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
