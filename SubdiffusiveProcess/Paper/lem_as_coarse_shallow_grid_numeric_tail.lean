module

public import Mathlib
public import Homogenization.Book.Ch02.MultiscaleEllipticity

@[expose] public section

open MeasureTheory Set Filter
open Homogenization
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper


private theorem aux_poly_geom_tsum
    (C a : ℝ) (_hC : 0 ≤ C) (ha : 0 < a) :
    (∑' N : ℕ, ENNReal.ofReal
      (C * ((N : ℝ) + 1) * (3 : ℝ) ^ (-a * (N : ℝ)))) ≠ ⊤ := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hbase_pos : 0 < (3 : ℝ) ^ (-a) := Real.rpow_pos_of_pos h3 (-a)
  have hbase_lt : (3 : ℝ) ^ (-a) < 1 := by
    rw [Real.rpow_def_of_pos h3, ← Real.exp_zero, Real.exp_lt_exp]
    nlinarith [mul_pos ha hlog3]
  have hbase_norm : ‖(3 : ℝ) ^ (-a)‖ < 1 := by
    rw [Real.norm_of_nonneg hbase_pos.le]
    exact hbase_lt
  have hrpow (n : ℕ) :
      (3 : ℝ) ^ (-a * (n : ℝ)) = ((3 : ℝ) ^ (-a)) ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_mul (x := 3) (y := -a) (z := (n : ℝ)) (by norm_num)
  have hpoly : Summable (fun n : ℕ => (n : ℝ) * ((3 : ℝ) ^ (-a)) ^ n) := by
    simpa using
      (summable_pow_mul_geometric_of_norm_lt_one (r := (3 : ℝ) ^ (-a)) 1 hbase_norm)
  have hgeom : Summable (fun n : ℕ => ((3 : ℝ) ^ (-a)) ^ n) :=
    summable_geometric_of_lt_one hbase_pos.le hbase_lt
  have hsum : Summable (fun n : ℕ =>
      C * ((n : ℝ) * ((3 : ℝ) ^ (-a)) ^ n) + C * ((3 : ℝ) ^ (-a)) ^ n) :=
    (hpoly.mul_left C).add (hgeom.mul_left C)
  have hf : Summable (fun n : ℕ =>
      C * ((n : ℝ) + 1) * (3 : ℝ) ^ (-a * (n : ℝ))) := by
    refine hsum.congr (fun n => ?_)
    rw [hrpow n]
    ring
  exact Summable.tsum_ofReal_ne_top hf


/-- The exact retained response-bank test set at one depth: one test for each
descendant, infrared convention, and one of the four bank branches. -/
def aux_lem_as_coarse_shallow_grid_numeric_tail_level (d k : ℕ) :
    Finset (((ℕ × TriadicCube d) × Bool) × Fin 4) :=
  ((({k} : Finset ℕ).product
      (descendantsAtScale (originCube d 0) (-(k : ℤ)))).product
      (Finset.univ : Finset Bool)).product (Finset.univ : Finset (Fin 4))

/-- Retained tests through depth `K`, including both infrared conventions. -/
def aux_lem_as_coarse_shallow_grid_numeric_tail_grid (d K : ℕ) :
    Finset (((ℕ × TriadicCube d) × Bool) × Fin 4) :=
  (Finset.range (K + 1)).biUnion (aux_lem_as_coarse_shallow_grid_numeric_tail_level d)

theorem aux_lem_as_coarse_shallow_grid_numeric_tail_level_card (d k : ℕ) :
    (aux_lem_as_coarse_shallow_grid_numeric_tail_level d k).card = 8 * (3 ^ d) ^ k := by
  have hdepth :
      (descendantsAtScale (originCube d 0) (-(k : ℤ))).card =
        (3 ^ d) ^ k := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d 0)
      (by simp [originCube])]
    convert descendantsAtDepth_card (originCube d 0) k using 1; simp [originCube]
  simp [aux_lem_as_coarse_shallow_grid_numeric_tail_level, hdepth]
  omega

theorem aux_lem_as_coarse_shallow_grid_numeric_tail_grid_card (d K : ℕ) :
    (aux_lem_as_coarse_shallow_grid_numeric_tail_grid d K).card ≤ (K + 1) * (8 * (3 ^ d) ^ K) := by
  calc
    (aux_lem_as_coarse_shallow_grid_numeric_tail_grid d K).card ≤
        ∑ k ∈ Finset.range (K + 1), (aux_lem_as_coarse_shallow_grid_numeric_tail_level d k).card := by
          simpa [aux_lem_as_coarse_shallow_grid_numeric_tail_grid] using
            (Finset.card_biUnion_le (s := Finset.range (K + 1))
              (t := aux_lem_as_coarse_shallow_grid_numeric_tail_level d))
    _ ≤ ∑ k ∈ Finset.range (K + 1), 8 * (3 ^ d) ^ K := by
      apply Finset.sum_le_sum
      intro k hk
      rw [aux_lem_as_coarse_shallow_grid_numeric_tail_level_card]
      have hkK : k ≤ K := by
        have hk' := Finset.mem_range.mp hk
        omega
      exact Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by positivity : 0 < 3 ^ d) hkK)
    _ = (K + 1) * (8 * (3 ^ d) ^ K) := by simp

/-- The paper's strict choice of `theta` leaves positive exponential slack
after paying for every retained depth and descendant. -/
theorem aux_lem_as_coarse_shallow_grid_numeric_tail_rate_margin (d : ℕ) (theta c : ℝ)
    (hθ : 0 ≤ theta)
    (hsmall : (d : ℝ) * theta < c * (1 - theta) / 2) :
    0 < c * (1 - theta) - (d : ℝ) * theta ∧
    0 < c * (1 - theta) / 2 := by
  constructor <;> nlinarith

/-- The extra factor from summing over all shallow depths is harmless. -/
theorem aux_lem_as_coarse_shallow_grid_numeric_tail_linear_geometric (q : ℝ≥0) (hq : q < 1) :
    (∑' N : ℕ, ((N + 1 : ℕ) : ℝ≥0∞) * (q : ℝ≥0∞) ^ N) ≠ ∞ := by
  have hs₁ : Summable (fun N : ℕ => (N : ℝ≥0) * q ^ N) := by
    rw [← NNReal.summable_coe]
    simpa using (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by simpa using hq))
  have hs₀ : Summable (fun N : ℕ => q ^ N) := by
    exact NNReal.summable_geometric hq
  have hs : Summable (fun N : ℕ => ((N + 1 : ℕ) : ℝ≥0) * q ^ N) := by
    convert hs₁.add hs₀ using 1
    ext N
    push_cast
    ring
  have hcoe := ENNReal.tsum_coe_eq hs.hasSum
  convert hcoe.symm ▸ (ENNReal.coe_ne_top (r := ∑' N : ℕ,
      ((N + 1 : ℕ) : ℝ≥0) * q ^ N)) using 1
  simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_natCast]

theorem aux_lem_as_coarse_shallow_grid_numeric_tail_real_pointwise
    (d N K : ℕ) (theta c Ce : ℝ)
    (_hθ : 0 ≤ theta) (hθ1 : theta < 1) (hc : 0 < c) (hCe : 0 ≤ Ce)
    (hK : (K : ℝ) ≤ theta * (N : ℝ)) :
    Ce * ((aux_lem_as_coarse_shallow_grid_numeric_tail_grid d K).card : ℝ) *
      (3 : ℝ) ^ (-c * ((N : ℝ) - K)) ≤
      8 * Ce * ((N : ℝ) + 1) *
        (3 : ℝ) ^ (-(c * (1 - theta) - (d : ℝ) * theta) * N) := by
  have hKN : K ≤ N := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hKNR : (K : ℝ) ≤ N := by nlinarith
    exact_mod_cast hKNR
  have hcard := aux_lem_as_coarse_shallow_grid_numeric_tail_grid_card d K
  have hpowcast : (((3 ^ d) ^ K : ℕ) : ℝ) =
      (3 : ℝ) ^ ((d : ℝ) * K) := by
    rw [← pow_mul]
    norm_cast
  have hcardR : ((aux_lem_as_coarse_shallow_grid_numeric_tail_grid d K).card : ℝ) ≤
      ((K : ℝ) + 1) * (8 * (3 : ℝ) ^ ((d : ℝ) * K)) := by
    have hcard' : ((aux_lem_as_coarse_shallow_grid_numeric_tail_grid d K).card : ℝ) ≤
        (((K + 1) * (8 * (3 ^ d) ^ K) : ℕ) : ℝ) := by exact_mod_cast hcard
    calc
      ((aux_lem_as_coarse_shallow_grid_numeric_tail_grid d K).card : ℝ) ≤
          (((K + 1) * (8 * (3 ^ d) ^ K) : ℕ) : ℝ) := hcard'
      _ = ((K : ℝ) + 1) * (8 * (3 : ℝ) ^ ((d : ℝ) * K)) := by
        push_cast
        rw [← pow_mul]
        norm_cast
  have hK1 : (K : ℝ) + 1 ≤ N + 1 := by exact_mod_cast Nat.add_le_add_right hKN 1
  have hexp : (d : ℝ) * K - c * ((N : ℝ) - K) ≤
      -(c * (1 - theta) - (d : ℝ) * theta) * N := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hpow : (3 : ℝ) ^ ((d : ℝ) * K) *
      (3 : ℝ) ^ (-c * ((N : ℝ) - K)) ≤
      (3 : ℝ) ^ (-(c * (1 - theta) - (d : ℝ) * theta) * N) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simpa [sub_eq_add_neg] using hexp)
  have hp1 : 0 ≤ (3 : ℝ) ^ (-c * ((N : ℝ) - K)) := by positivity
  have hp2 : 0 ≤ (3 : ℝ) ^ ((d : ℝ) * K) := by positivity
  calc
    Ce * ((aux_lem_as_coarse_shallow_grid_numeric_tail_grid d K).card : ℝ) *
        (3 : ℝ) ^ (-c * ((N : ℝ) - K)) ≤
        Ce * (((K : ℝ) + 1) * (8 * (3 : ℝ) ^ ((d : ℝ) * K))) *
          (3 : ℝ) ^ (-c * ((N : ℝ) - K)) := by gcongr
    _ = 8 * Ce * ((K : ℝ) + 1) *
        ((3 : ℝ) ^ ((d : ℝ) * K) *
          (3 : ℝ) ^ (-c * ((N : ℝ) - K))) := by ring
    _ ≤ 8 * Ce * ((N : ℝ) + 1) *
        ((3 : ℝ) ^ ((d : ℝ) * K) *
          (3 : ℝ) ^ (-c * ((N : ℝ) - K))) := by gcongr
    _ ≤ 8 * Ce * ((N : ℝ) + 1) *
        (3 : ℝ) ^ (-(c * (1 - theta) - (d : ℝ) * theta) * N) := by
          gcongr

/-- Exact retained bank union tail is summable once the retained-depth
fraction satisfies the paper's rate inequality. No summability assumption
is supplied by the caller. -/
theorem aux_lem_as_coarse_shallow_grid_numeric_tail_actual_grid_tail_summable
    (d : ℕ) (theta c Ce : ℝ)
    (hθ : 0 ≤ theta) (hθ1 : theta < 1) (hc : 0 < c) (hCe : 0 ≤ Ce)
    (hsmall : (d : ℝ) * theta < c * (1 - theta) / 2)
    (K : ℕ → ℕ) (hK : ∀ N, (K N : ℝ) ≤ theta * (N : ℝ)) :
    (∑' N : ℕ, ENNReal.ofReal
      (Ce * ((aux_lem_as_coarse_shallow_grid_numeric_tail_grid d (K N)).card : ℝ) *
        (3 : ℝ) ^ (-c * ((N : ℝ) - K N)))) ≠ ∞ := by
  let a : ℝ := c * (1 - theta) - (d : ℝ) * theta
  have ha : 0 < a := (aux_lem_as_coarse_shallow_grid_numeric_tail_rate_margin d theta c hθ hsmall).1
  have hsum := aux_poly_geom_tsum (8 * Ce) a (by positivity) ha
  have hle : ∀ N : ℕ,
      ENNReal.ofReal
          (Ce * ((aux_lem_as_coarse_shallow_grid_numeric_tail_grid d (K N)).card : ℝ) *
            (3 : ℝ) ^ (-c * ((N : ℝ) - K N))) ≤
      ENNReal.ofReal
          (8 * Ce * ((N : ℝ) + 1) * (3 : ℝ) ^ (-a * N)) := by
    intro N
    exact ENNReal.ofReal_le_ofReal
      (aux_lem_as_coarse_shallow_grid_numeric_tail_real_pointwise d N (K N) theta c Ce hθ hθ1 hc hCe (hK N))
  exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hle)

theorem lem_as_coarse_shallow_grid_numeric_tail
    (d : ℕ) (theta c Ce : ℝ)
    (hθ : 0 ≤ theta) (hθ1 : theta < 1) (hc : 0 < c) (hCe : 0 ≤ Ce)
    (hsmall : (d : ℝ) * theta < c * (1 - theta) / 2) :
    (∑' N : ℕ, ENNReal.ofReal
      (Ce * ((aux_lem_as_coarse_shallow_grid_numeric_tail_grid d ⌊theta * (N : ℝ)⌋₊).card : ℝ) *
        (3 : ℝ) ^ (-c * ((N : ℝ) - ⌊theta * (N : ℝ)⌋₊)))) ≠ ∞ := by
  apply aux_lem_as_coarse_shallow_grid_numeric_tail_actual_grid_tail_summable d theta c Ce hθ hθ1 hc hCe hsmall
    (fun N => ⌊theta * (N : ℝ)⌋₊)
  intro N
  exact Nat.floor_le (mul_nonneg hθ (Nat.cast_nonneg N))

/-- A summable uniform one-cell failure estimate gives one event on which
every cell in each sufficiently deep finite grid is good.  The numerical
summability assumption is the place where the response-bank decay must beat
the number of retained cubes. -/
theorem aux_lem_as_coarse_shallow_grid_numeric_tail_finite_grid_eventual
    {Ω α : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : ℕ → Finset α)
    (bad : ℕ → α → Set Ω) (b : ℕ → ℝ≥0∞)
    (hcell : ∀ N i, i ∈ G N → P (bad N i) ≤ b N)
    (hsum : (∑' N : ℕ, (G N).card * b N) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ᶠ N in atTop, ∀ i ∈ G N, ω ∉ bad N i := by
  let badGrid : ℕ → Set Ω := fun N => ⋃ i ∈ G N, bad N i
  have hbound : ∀ N, P (badGrid N) ≤ (G N).card * b N := by
    intro N
    calc
      P (badGrid N) ≤ ∑ i ∈ G N, P (bad N i) := by
        simpa [badGrid] using measure_biUnion_finset_le (G N) (bad N)
      _ ≤ ∑ i ∈ G N, b N := Finset.sum_le_sum (fun i hi => hcell N i hi)
      _ = (G N).card * b N := by simp
  have hsumGrid : (∑' N : ℕ, P (badGrid N)) ≠ ∞ := by
    exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hbound)
  have hbc := ae_eventually_notMem (μ := P) hsumGrid
  filter_upwards [hbc] with ω hω
  exact hω.mono (fun N hN i hi hmem => hN (mem_iUnion₂.mpr ⟨i, hi, hmem⟩))

/-- The geometric form used after the grid cardinality and shifted-bank
comparison rates have been combined. -/
theorem aux_lem_as_coarse_shallow_grid_numeric_tail_finite_grid_geometric
    {Ω α : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : ℕ → Finset α)
    (bad : ℕ → α → Set Ω) (b : ℕ → ℝ≥0∞)
    (hcell : ∀ N i, i ∈ G N → P (bad N i) ≤ b N)
    (C q : ℝ≥0∞) (hC : C < ∞) (hq : q < 1)
    (hgeom : ∀ N, (G N).card * b N ≤ C * q ^ N) :
    ∀ᵐ ω ∂P, ∀ᶠ N in atTop, ∀ i ∈ G N, ω ∉ bad N i := by
  apply aux_lem_as_coarse_shallow_grid_numeric_tail_finite_grid_eventual P G bad b hcell
  have hsum : (∑' N : ℕ, (G N).card * b N) ≤ C * (1 - q)⁻¹ := by
    calc
      (∑' N : ℕ, (G N).card * b N) ≤ ∑' N : ℕ, C * q ^ N :=
        ENNReal.tsum_le_tsum hgeom
      _ = C * (1 - q)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hqsum : (1 - q)⁻¹ < ∞ := by
    simpa only [ENNReal.tsum_geometric] using
      (tsum_geometric_lt_top.mpr hq)
  exact ne_top_of_le_ne_top (ne_of_lt (ENNReal.mul_lt_top hC hqsum)) hsum

/-- The paper's retained grid is eventually good simultaneously, provided
the response construction supplies its stated uniform one-cell tail. The
summability needed for Borel--Cantelli is proved above, not assumed here. -/
theorem aux_lem_as_coarse_shallow_grid_numeric_tail_actual_grid_eventual
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (d : ℕ) (theta c Ce : ℝ)
    (hθ : 0 ≤ theta) (hθ1 : theta < 1) (hc : 0 < c) (hCe : 0 ≤ Ce)
    (hsmall : (d : ℝ) * theta < c * (1 - theta) / 2)
    (bad : ℕ → (((ℕ × TriadicCube d) × Bool) × Fin 4) → Set Ω)
    (hcell : ∀ (N : ℕ) i,
      i ∈ aux_lem_as_coarse_shallow_grid_numeric_tail_grid d ⌊theta * (N : ℝ)⌋₊ →
      P (bad N i) ≤ ENNReal.ofReal
        (Ce * (3 : ℝ) ^ (-c * ((N : ℝ) - ⌊theta * (N : ℝ)⌋₊)))) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      ∀ i ∈ aux_lem_as_coarse_shallow_grid_numeric_tail_grid d ⌊theta * (N : ℝ)⌋₊,
        ω ∉ bad N i := by
  let G : ℕ → Finset (((ℕ × TriadicCube d) × Bool) × Fin 4) :=
    fun N => aux_lem_as_coarse_shallow_grid_numeric_tail_grid d ⌊theta * (N : ℝ)⌋₊
  let b : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal
    (Ce * (3 : ℝ) ^ (-c * ((N : ℝ) - ⌊theta * (N : ℝ)⌋₊)))
  apply aux_lem_as_coarse_shallow_grid_numeric_tail_finite_grid_eventual P G bad b
  · exact hcell
  · have hsum := lem_as_coarse_shallow_grid_numeric_tail d theta c Ce hθ hθ1 hc hCe hsmall
    convert hsum using 1
    congr 1
    funext N
    dsimp [G, b]
    rw [← ENNReal.ofReal_natCast
      (aux_lem_as_coarse_shallow_grid_numeric_tail_grid d ⌊theta * (N : ℝ)⌋₊).card,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring

/-- Merge the finitely many bank-branch tail estimates at one fixed model
into one positive coefficient, rate, and starting depth. -/
theorem aux_lem_as_coarse_shallow_grid_numeric_tail_finite_bank_common_rate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (bad : Fin n → ℕ → Set Ω)
    (hbranch : ∀ i : Fin n, ∃ C c : ℝ, ∃ N0 : ℕ,
      0 < C ∧ 0 < c ∧
      ∀ N : ℕ, N0 ≤ N →
        P (bad i N) ≤ ENNReal.ofReal
          (C * (3 : ℝ) ^ (-c * (N : ℝ)))) :
    ∃ C c : ℝ, ∃ N0 : ℕ,
      0 < C ∧ 0 < c ∧
      ∀ i : Fin n, ∀ N : ℕ, N0 ≤ N →
        P (bad i N) ≤ ENNReal.ofReal
          (C * (3 : ℝ) ^ (-c * (N : ℝ))) := by
  by_cases hn : Nonempty (Fin n)
  · let s : Finset (Fin n) := Finset.univ
    have hs : s.Nonempty := by
      rcases hn with ⟨i⟩
      exact ⟨i, Finset.mem_univ i⟩
    choose C_i c_i N0_i hC_i hc_i h_bound_i using hbranch
    set C := s.sup' hs C_i with hC_def
    set c := s.inf' hs c_i with hc_def
    set N0 := s.sup' hs N0_i with hN0_def
    have hC_pos : 0 < C := by
      rw [hC_def]
      refine ((Finset.lt_sup'_iff hs).mpr ?_)
      rcases hn with ⟨i⟩
      exact ⟨i, Finset.mem_univ i, hC_i i⟩
    have hc_pos : 0 < c := by
      rw [hc_def]
      refine ((Finset.lt_inf'_iff hs).mpr ?_)
      intro i hi
      exact hc_i i
    have hN0_bound : ∀ i, N0_i i ≤ N0 := by
      intro i
      rw [hN0_def]
      exact Finset.le_sup' N0_i (Finset.mem_univ i)
    have hC_bound : ∀ i, C_i i ≤ C := by
      intro i
      rw [hC_def]
      exact Finset.le_sup' C_i (Finset.mem_univ i)
    have hc_bound : ∀ i, c ≤ c_i i := by
      intro i
      rw [hc_def]
      exact Finset.inf'_le c_i (Finset.mem_univ i)
    refine ⟨C, c, N0, hC_pos, hc_pos, ?_⟩
    intro i N hN
    have hN_i : N0_i i ≤ N := le_trans (hN0_bound i) hN
    have h_indiv := h_bound_i i N hN_i
    refine le_trans h_indiv ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h_nonneg_pow : 0 ≤ (3 : ℝ) ^ (-c_i i * (N : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have h_base : 1 ≤ (3 : ℝ) := by norm_num
    have h_exp : -c_i i * (N : ℝ) ≤ -c * (N : ℝ) := by
      have hc_le : c ≤ c_i i := hc_bound i
      have hN_nonneg : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
      nlinarith
    have h_pow_le : (3 : ℝ) ^ (-c_i i * (N : ℝ)) ≤ (3 : ℝ) ^ (-c * (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le h_base h_exp
    have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
    calc
      C_i i * ((3 : ℝ) ^ (-c_i i * (N : ℝ))) ≤
          C * ((3 : ℝ) ^ (-c_i i * (N : ℝ))) :=
        mul_le_mul_of_nonneg_right (hC_bound i) h_nonneg_pow
      _ ≤ C * ((3 : ℝ) ^ (-c * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left h_pow_le hC_nonneg
  · have hn0 : n = 0 := by
      by_contra! h
      have hpos : 0 < n := Nat.pos_of_ne_zero h
      exact hn ⟨Fin.mk 0 hpos⟩
    subst hn0
    refine ⟨1, 1, 0, by norm_num, by norm_num, ?_⟩
    intro i
    exact Fin.elim0 i

end SubdiffusiveProcess.Paper
