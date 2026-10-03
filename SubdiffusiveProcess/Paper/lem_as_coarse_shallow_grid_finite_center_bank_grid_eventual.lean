module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_actual_bank_grid_eventual

@[expose] public section

open MeasureTheory Set Filter
open SubdiffusiveProcess Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-! ## F. Borel–Cantelli for the real bank tail on a translated centre family -/

theorem aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_poly_geom_tsum
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

/-- Retained tests at one physical depth: one per centre, bank branch and
coordinate. -/
def aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_level {d : ℕ} (cen : ℕ → Finset (SpatialCoordinates d)) (n : ℕ) :
    Finset (((ℕ × SpatialCoordinates d) × Bool) × Fin d) :=
  ((({n} : Finset ℕ) ×ˢ cen n) ×ˢ (Finset.univ : Finset Bool)) ×ˢ
    (Finset.univ : Finset (Fin d))

/-- Retained tests through depth `K`. -/
def aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid {d : ℕ} (cen : ℕ → Finset (SpatialCoordinates d)) (K : ℕ) :
    Finset (((ℕ × SpatialCoordinates d) × Bool) × Fin d) :=
  (Finset.range (K + 1)).biUnion (aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_level cen)

theorem aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_card {d : ℕ} (cen : ℕ → Finset (SpatialCoordinates d)) (Cc : ℝ)
    (hcard : ∀ n : ℕ, ((cen n).card : ℝ) ≤ Cc * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)))
    (K : ℕ) :
    ((aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid cen K).card : ℝ) ≤
      ((K : ℝ) + 1) * ((2 * (d : ℝ)) * Cc * (3 : ℝ) ^ ((d : ℝ) * (K : ℝ))) := by
  have hlev : ∀ n, ((aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_level cen n).card : ℝ) = 2 * (d : ℝ) * (cen n).card := by
    intro n
    simp only [aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_level, Finset.card_product, Finset.card_singleton, one_mul,
      Finset.card_univ, Fintype.card_bool, Fintype.card_fin]
    push_cast
    ring
  calc ((aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid cen K).card : ℝ) ≤
        ((∑ n ∈ Finset.range (K + 1), (aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_level cen n).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ n ∈ Finset.range (K + 1), ((aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_level cen n).card : ℝ) := by
        push_cast; rfl
    _ ≤ ∑ n ∈ Finset.range (K + 1),
          (2 * (d : ℝ)) * Cc * (3 : ℝ) ^ ((d : ℝ) * (K : ℝ)) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [hlev n]
        have hnK : (n : ℝ) ≤ K := by
          have := Finset.mem_range.mp hn
          exact_mod_cast Nat.le_of_lt_succ this
        have hpow : (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) ≤ (3 : ℝ) ^ ((d : ℝ) * (K : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_left hnK (Nat.cast_nonneg d))
        have hCc : 0 ≤ Cc := by
          have h0 := hcard 0
          simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at h0
          exact (Nat.cast_nonneg _).trans h0
        calc 2 * (d : ℝ) * ((cen n).card : ℝ) ≤
            2 * (d : ℝ) * (Cc * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ))) :=
              mul_le_mul_of_nonneg_left (hcard n) (by positivity)
          _ ≤ 2 * (d : ℝ) * (Cc * (3 : ℝ) ^ ((d : ℝ) * (K : ℝ))) := by
              gcongr
          _ = (2 * (d : ℝ)) * Cc * (3 : ℝ) ^ ((d : ℝ) * (K : ℝ)) := by ring
    _ = ((K : ℝ) + 1) * ((2 * (d : ℝ)) * Cc * (3 : ℝ) ^ ((d : ℝ) * (K : ℝ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_real_pointwise {d : ℕ} (cen : ℕ → Finset (SpatialCoordinates d))
    (Cc : ℝ)
    (hcard : ∀ n : ℕ, ((cen n).card : ℝ) ≤ Cc * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)))
    (N K : ℕ) (theta c Ce : ℝ)
    (_hθ : 0 ≤ theta) (hθ1 : theta < 1) (hc : 0 < c) (hCe : 0 ≤ Ce)
    (hK : (K : ℝ) ≤ theta * (N : ℝ)) :
    Ce * ((aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid cen K).card : ℝ) *
      (3 : ℝ) ^ (-c * ((N : ℝ) - K)) ≤
      (2 * (d : ℝ)) * Cc * Ce * ((N : ℝ) + 1) *
        (3 : ℝ) ^ (-(c * (1 - theta) - (d : ℝ) * theta) * N) := by
  have hCc : 0 ≤ Cc := by
    have h0 := hcard 0
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at h0
    exact (Nat.cast_nonneg _).trans h0
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hKN : (K : ℝ) ≤ N := by nlinarith
  have hcardR := aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_card cen Cc hcard K
  have hK1 : (K : ℝ) + 1 ≤ N + 1 := by linarith
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
    Ce * ((aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid cen K).card : ℝ) *
        (3 : ℝ) ^ (-c * ((N : ℝ) - K)) ≤
        Ce * (((K : ℝ) + 1) * ((2 * (d : ℝ)) * Cc * (3 : ℝ) ^ ((d : ℝ) * K))) *
          (3 : ℝ) ^ (-c * ((N : ℝ) - K)) := by gcongr
    _ = (2 * (d : ℝ)) * Cc * Ce * ((K : ℝ) + 1) *
        ((3 : ℝ) ^ ((d : ℝ) * K) *
          (3 : ℝ) ^ (-c * ((N : ℝ) - K))) := by ring
    _ ≤ (2 * (d : ℝ)) * Cc * Ce * ((N : ℝ) + 1) *
        ((3 : ℝ) ^ ((d : ℝ) * K) *
          (3 : ℝ) ^ (-c * ((N : ℝ) - K))) := by gcongr
    _ ≤ (2 * (d : ℝ)) * Cc * Ce * ((N : ℝ) + 1) *
        (3 : ℝ) ^ (-(c * (1 - theta) - (d : ℝ) * theta) * N) := by
          gcongr

theorem aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_summable {d : ℕ} (cen : ℕ → Finset (SpatialCoordinates d))
    (Cc : ℝ)
    (hcard : ∀ n : ℕ, ((cen n).card : ℝ) ≤ Cc * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)))
    (theta c Ce : ℝ)
    (hθ : 0 ≤ theta) (hθ1 : theta < 1) (hc : 0 < c) (hCe : 0 ≤ Ce)
    (hsmall : (d : ℝ) * theta < c * (1 - theta) / 2) :
    (∑' N : ℕ, ENNReal.ofReal
      (Ce * ((aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid cen ⌊theta * (N : ℝ)⌋₊).card : ℝ) *
        (3 : ℝ) ^ (-c * ((N : ℝ) - ⌊theta * (N : ℝ)⌋₊)))) ≠ ∞ := by
  have hCc : 0 ≤ Cc := by
    have h0 := hcard 0
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at h0
    exact (Nat.cast_nonneg _).trans h0
  let a : ℝ := c * (1 - theta) - (d : ℝ) * theta
  have ha : 0 < a := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    dsimp [a]; nlinarith
  have hsum := aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_poly_geom_tsum ((2 * (d : ℝ)) * Cc * Ce) a (by positivity) ha
  have hle : ∀ N : ℕ,
      ENNReal.ofReal
          (Ce * ((aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid cen ⌊theta * (N : ℝ)⌋₊).card : ℝ) *
            (3 : ℝ) ^ (-c * ((N : ℝ) - ⌊theta * (N : ℝ)⌋₊))) ≤
      ENNReal.ofReal
          ((2 * (d : ℝ)) * Cc * Ce * ((N : ℝ) + 1) * (3 : ℝ) ^ (-a * N)) := by
    intro N
    exact ENNReal.ofReal_le_ofReal
      (aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_real_pointwise cen Cc hcard N _ theta c Ce hθ hθ1 hc hCe
        (Nat.floor_le (mul_nonneg hθ (Nat.cast_nonneg N))))
  exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hle)

/-- **Translated retained-bank Borel–Cantelli.** For any deterministic centre
family `cen n` of size `≤ Cc 3^{dn}`, the real finite-bank tail of every
retained shifted coordinate `Θ_{n,y}ω`, `y ∈ cen n`, `n ≤ ⌊θ N⌋`, is eventually
good almost surely. Only the scale-shift law (valid at arbitrary centres) and
the unit-bank tail are used; `Cc` may depend on the root. -/
theorem lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Z : Bool → Fin d → BilateralField d → ℝ)
    (theta Cgeom Ce ce eps : ℝ) (Ne : ℕ)
    (hθ : 0 ≤ theta) (hθ1 : theta < 1)
    (hCe : 0 < Ce) (hce : 0 < ce)
    (hsmall : (d : ℝ) * theta < ce * (1 - theta) / 2)
    (htail : ∀ (b : Bool) (i : Fin d) (n : ℕ), Ne ≤ n →
      (chaosSampleLaw M).toMeasure
        {om | Cgeom * eps * Z b i om +
          Ce * (3 : ℝ) ^ (-(ce * (n : ℝ))) <
          |aux_matched_affine_finite_response M (Pi.single i 1) b n om - Z b i om|} ≤
        ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * (n : ℝ)))))
    (cen : ℕ → Finset (SpatialCoordinates d)) (Cc : ℝ)
    (hcard : ∀ n : ℕ, ((cen n).card : ℝ) ≤ Cc * (3 : ℝ) ^ ((d : ℝ) * (n : ℝ))) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ᶠ N : ℕ in atTop,
      ∀ (n : ℕ), n ≤ ⌊theta * (N : ℝ)⌋₊ →
      ∀ y ∈ cen n, ∀ (b : Bool) (i : Fin d),
        ¬(Cgeom * eps *
            Z b i (aux_lem_as_coarse_shallow_grid_scaleShift n y om) +
          Ce * (3 : ℝ) ^ (-(ce * ((N - n : ℕ) : ℝ))) <
          |aux_matched_affine_finite_response M (Pi.single i 1) b (N - n)
              (aux_lem_as_coarse_shallow_grid_scaleShift n y om) -
           Z b i (aux_lem_as_coarse_shallow_grid_scaleShift n y om)|) := by
  let K : ℕ → ℕ := fun N => ⌊theta * (N : ℝ)⌋₊
  let G : ℕ → Finset (((ℕ × SpatialCoordinates d) × Bool) × Fin d) :=
    fun N => aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid cen (K N)
  let bad : ℕ → (((ℕ × SpatialCoordinates d) × Bool) × Fin d) → Set (BilateralField d) :=
    fun N u =>
      {om | Cgeom * eps *
          Z u.1.2 u.2 (aux_lem_as_coarse_shallow_grid_scaleShift u.1.1.1 u.1.1.2 om) +
        Ce * (3 : ℝ) ^ (-(ce * ((N - u.1.1.1 : ℕ) : ℝ))) <
        |aux_matched_affine_finite_response M (Pi.single u.2 1) u.1.2 (N - u.1.1.1)
            (aux_lem_as_coarse_shallow_grid_scaleShift u.1.1.1 u.1.1.2 om) -
         Z u.1.2 u.2 (aux_lem_as_coarse_shallow_grid_scaleShift u.1.1.1 u.1.1.2 om)|}
  have hcut : ∀ᶠ N : ℕ in atTop, K N + Ne ≤ N := by
    have hmargin : 0 < 1 - theta := by linarith
    have hE : ∀ᶠ N : ℕ in atTop,
        (Ne : ℝ) ≤ (1 - theta) * (N : ℝ) :=
      (Tendsto.const_mul_atTop hmargin tendsto_natCast_atTop_atTop).eventually_ge_atTop _
    filter_upwards [hE] with N hN
    have hK : (K N : ℝ) ≤ theta * (N : ℝ) :=
      Nat.floor_le (mul_nonneg hθ (Nat.cast_nonneg N))
    have hKN : ((K N + Ne : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hKN
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hcut
  have hcell : ∀ N, N0 ≤ N → ∀ u ∈ G N,
      (chaosSampleLaw M).toMeasure (bad N u) ≤
        ENNReal.ofReal (Ce * (3 : ℝ) ^
          (-ce * ((N : ℝ) - K N))) := by
    intro N hN u hu
    obtain ⟨⟨⟨n, y⟩, b⟩, i⟩ := u
    have hn : n ≤ K N := by
      obtain ⟨j, hj, hlev⟩ := Finset.mem_biUnion.mp hu
      have hnj : n = j := Finset.mem_singleton.mp
        (Finset.mem_product.mp
          (Finset.mem_product.mp
            (Finset.mem_product.mp hlev).1).1).1
      rw [hnj]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hrem : Ne ≤ N - n := by
      have := hN0 N hN
      omega
    let S : Set (BilateralField d) :=
      {om | Cgeom * eps * Z b i om +
        Ce * (3 : ℝ) ^ (-(ce * ((N - n : ℕ) : ℝ))) <
        |aux_matched_affine_finite_response M (Pi.single i 1) b (N - n) om - Z b i om|}
    have hroot : (chaosSampleLaw M).toMeasure S ≤
        ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * ((N - n : ℕ) : ℝ)))) :=
      htail b i (N - n) hrem
    have hshift : (chaosSampleLaw M).toMeasure (bad N ⟨⟨⟨n, y⟩, b⟩, i⟩) ≤
        ENNReal.ofReal (Ce * (3 : ℝ) ^ (-(ce * ((N - n : ℕ) : ℝ)))) :=
      (aux_lem_as_coarse_shallow_grid_scaleShift_prob_le M n y S).trans hroot
    have hpow : (3 : ℝ) ^ (-(ce * ((N - n : ℕ) : ℝ))) ≤
        (3 : ℝ) ^ (-ce * ((N : ℝ) - K N)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hcutN := hN0 N hN
      have hnN : n ≤ N := by omega
      rw [Nat.cast_sub hnN]
      have : (n : ℝ) ≤ K N := by exact_mod_cast hn
      nlinarith
    exact hshift.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hCe.le))
  have hsum : (∑' N : ℕ, (G N).card *
      ENNReal.ofReal (Ce * (3 : ℝ) ^ (-ce * ((N : ℝ) - K N)))) ≠ ∞ := by
    have hs := aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_summable cen Cc hcard theta ce Ce hθ hθ1 hce hCe.le hsmall
    convert hs using 1
    congr 1
    funext N
    dsimp [G, K]
    rw [← ENNReal.ofReal_natCast
      (aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid cen ⌊theta * (N : ℝ)⌋₊).card,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  let G' : ℕ → Finset (((ℕ × SpatialCoordinates d) × Bool) × Fin d) :=
    fun N => if N0 ≤ N then G N else ∅
  have hsum' : (∑' N : ℕ, (G' N).card *
      ENNReal.ofReal (Ce * (3 : ℝ) ^ (-ce * ((N : ℝ) - K N)))) ≠ ∞ := by
    apply ne_top_of_le_ne_top hsum
    apply ENNReal.tsum_le_tsum
    intro N
    gcongr
    by_cases hN : N0 ≤ N
    · simp [G', hN]
    · simp [G', hN]
  have hbc := aux_lem_as_coarse_shallow_grid_numeric_tail_finite_grid_eventual
    (chaosSampleLaw M).toMeasure G' bad
    (fun N => ENNReal.ofReal (Ce * (3 : ℝ) ^ (-ce * ((N : ℝ) - K N))))
    (by
      intro N u hu
      by_cases hN : N0 ≤ N
      · exact hcell N hN u (by simpa [G', hN] using hu)
      · simp [G', hN] at hu)
    hsum'
  filter_upwards [hbc] with om hom
  filter_upwards [hom, Filter.eventually_ge_atTop N0] with N hGrid hN
  intro n hn y hy b i
  have hu : (⟨⟨⟨n, y⟩, b⟩, i⟩ : (((ℕ × SpatialCoordinates d) × Bool) × Fin d)) ∈ G N := by
    apply Finset.mem_biUnion.mpr
    refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), ?_⟩
    simp [aux_lem_as_coarse_shallow_grid_finite_center_bank_grid_eventual_grid_level, hy]
  exact hGrid _ (by simpa [G', hN] using hu)

end Paper



