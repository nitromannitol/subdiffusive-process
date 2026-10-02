import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Paper.prop_folded_iteration
import SubdiffusiveProcess.Paper.lem_primitive
import SubdiffusiveProcess.Paper.rem_resolved_strata
import SubdiffusiveProcess.Paper.lane4_regularity_mesh_statistic
import SubdiffusiveProcess.Paper.lane4_reference_mesh_statistic


set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators

namespace Paper


/-- Sup-metric balls are the open coordinate cubes of `rem_resolved_strata`. -/
theorem aux_lane4_two_mesh_energy_bound_ball_eq {d : ℕ} (hd : 1 ≤ d)
    (c : SpatialCoordinates d) (ρ : ℝ) :
    Metric.ball c ρ = {y : SpatialCoordinates d | ∀ i : Fin d, |y i - c i| < ρ} := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [ball_pi' c ρ]
  ext y
  simp [Real.dist_eq]

theorem aux_lane4_two_mesh_energy_bound_mem_cube {d : ℕ} {y : SpatialCoordinates d}
    (hy : ∀ i : Fin d, 0 < y i ∧ y i < 1) :
    y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) := by
  show y ∈ ((centeredCube (fun _ => (1 / 2 : ℝ)) 1 one_pos : Opens (SpatialCoordinates d)) :
    Set (SpatialCoordinates d))
  rw [centeredCube_eq_pi (fun _ => (1 / 2 : ℝ)) one_pos]
  intro i _
  simp only [Set.mem_Ioo]
  constructor <;> linarith [(hy i).1, (hy i).2]

/-- The triadic depth `n` of a radius `r ≤ 1`. -/
theorem aux_lane4_two_mesh_energy_bound_scale {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ n : ℕ, (3 : ℝ) ^ (-(n : ℤ)) ≤ r ∧ r < 3 * (3 : ℝ) ^ (-(n : ℤ)) := by
  obtain ⟨z, hz1, hz2⟩ := exists_mem_Ico_zpow hr (show (1 : ℝ) < 3 by norm_num)
  have hz0 : z ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have : (3 : ℝ) ^ (1 : ℤ) ≤ (3 : ℝ) ^ z := zpow_le_zpow_right₀ (by norm_num) (by omega)
    norm_num at this
    linarith
  have hk : (-(((-z).toNat : ℕ) : ℤ)) = z := by omega
  refine ⟨(-z).toNat, ?_, ?_⟩
  · rw [hk]; exact hz1
  · rw [hk]
    have : (3 : ℝ) ^ (z + 1) = 3 * (3 : ℝ) ^ z := by
      rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]; ring
    rw [← this]; exact hz2

theorem aux_lane4_two_mesh_energy_bound_scale_pow {r eta : ℝ} (hr : 0 < r) (heta : 0 < eta)
    (n : ℕ) (hn : r < 3 * (3 : ℝ) ^ (-(n : ℤ))) :
    (3 : ℝ) ^ (eta * (n : ℝ)) ≤ 3 ^ eta * r ^ (-eta) := by
  have hpos : 0 < (3 : ℝ) ^ n := by positivity
  have h3n : (3 : ℝ) ^ (-(n : ℤ)) = ((3 : ℝ) ^ n)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hlt : (3 : ℝ) ^ n * r < 3 := by
    have := mul_lt_mul_of_pos_left hn hpos
    rwa [h3n, mul_comm (3 : ℝ) ((3 : ℝ) ^ n)⁻¹, ← mul_assoc, mul_inv_cancel₀ hpos.ne',
      one_mul] at this
  have hle : (3 : ℝ) ^ n ≤ 3 / r := by
    rw [le_div_iff₀ hr]; exact hlt.le
  calc (3 : ℝ) ^ (eta * (n : ℝ)) = ((3 : ℝ) ^ n) ^ eta := by
        rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
    _ ≤ (3 / r) ^ eta := Real.rpow_le_rpow hpos.le hle heta.le
    _ = 3 ^ eta * r ^ (-eta) := by
        rw [Real.div_rpow (by norm_num) hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]

/-- A neighbouring point of the target mesh of side `3^{-L}`, strictly inside the cube. -/
theorem aux_lane4_two_mesh_energy_bound_grid {d : ℕ} (L : ℕ) (hL : 1 ≤ L)
    (x : SpatialCoordinates d) (hx : ∀ i, 0 < x i ∧ x i < 1) :
    ∃ g : Fin d → Fin (3 ^ L + 1), ∀ i : Fin d,
      0 < ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) ∧
      ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) < 1 ∧
      |x i - ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(L : ℤ))| < (3 : ℝ) ^ (-(L : ℤ)) := by
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = (3 : ℝ) ^ (-(L : ℤ)) := ⟨_, rfl⟩
  rw [← hh]
  have hpos : 0 < h := by rw [hh]; exact zpow_pos (by norm_num) _
  have hprod : ((3 ^ L : ℕ) : ℝ) * h = 1 := by
    rw [hh, zpow_neg, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    exact mul_inv_cancel₀ (by positivity)
  have hL3 : 3 ≤ 3 ^ L := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have hk : ∀ i, max 1 ⌊x i / h⌋₊ < 3 ^ L := by
    intro i
    apply max_lt (by omega)
    rw [Nat.floor_lt (div_nonneg (hx i).1.le hpos.le), div_lt_iff₀ hpos, hprod]
    exact (hx i).2
  refine ⟨fun i => ⟨max 1 ⌊x i / h⌋₊, by have := hk i; omega⟩, fun i => ?_⟩
  have hki := hk i
  have hk1 : (1 : ℝ) ≤ ((max 1 ⌊x i / h⌋₊ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
  have hkL : ((max 1 ⌊x i / h⌋₊ : ℕ) : ℝ) + 1 ≤ ((3 ^ L : ℕ) : ℝ) := by exact_mod_cast hki
  show 0 < ((max 1 ⌊x i / h⌋₊ : ℕ) : ℝ) * h ∧ ((max 1 ⌊x i / h⌋₊ : ℕ) : ℝ) * h < 1 ∧
    |x i - ((max 1 ⌊x i / h⌋₊ : ℕ) : ℝ) * h| < h
  refine ⟨by positivity, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right hkL hpos.le
    rw [hprod, add_mul, one_mul] at this
    linarith
  · have hlt := Nat.lt_floor_add_one (x i / h)
    rw [div_lt_iff₀ hpos] at hlt
    rcases le_total 1 ⌊x i / h⌋₊ with h1 | h1
    · rw [max_eq_right h1]
      have hfl := Nat.floor_le (div_nonneg (hx i).1.le hpos.le)
      rw [le_div_iff₀ hpos] at hfl
      rw [abs_lt]; constructor <;> nlinarith
    · rw [max_eq_left h1]
      have h1' : (⌊x i / h⌋₊ : ℝ) ≤ 1 := by exact_mod_cast h1
      have : x i < 2 * h := by nlinarith
      rw [abs_lt]; constructor <;> push_cast <;> linarith [(hx i).1]

/-- A half-triadic radius below `1/2` is a root radius `3^{-k}/2`, with depth bounded by
any scale it exceeds. -/
theorem aux_lane4_two_mesh_energy_bound_depth {ρ : ℝ}
    (hρ : ρ ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2)) (hρ1 : ρ < 1 / 2) :
    ∃ k : ℕ, ρ = (3 : ℝ) ^ (-(k : ℤ)) / 2 ∧
      ∀ n : ℕ, (3 : ℝ) ^ (-(n : ℤ)) / 2 < ρ → k < n := by
  obtain ⟨z, rfl⟩ := hρ
  have hz : z < 0 := by
    by_contra hcon
    push_neg at hcon
    have : (1 : ℝ) ≤ 3 ^ z := one_le_zpow₀ (by norm_num) hcon
    linarith
  have hk : (-(((-z).toNat : ℕ) : ℤ)) = z := by omega
  refine ⟨(-z).toNat, by rw [hk], ?_⟩
  intro n hn
  have h1 : (3 : ℝ) ^ (-(n : ℤ)) < 3 ^ z := by linarith
  have h2 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h1
  omega

/-- The activation order of a finite boundary chain is an initial-segment permutation. -/
theorem aux_lane4_two_mesh_energy_bound_perm {d : ℕ} (hd : 1 ≤ d) (m : ℕ) (hm : m ≤ d)
    (I : ℕ → Finset (Fin d)) (hI0 : I 0 = ∅)
    (hstep : ∀ j : ℕ, j < m → ∃ i : Fin d, i ∉ I j ∧ I (j + 1) = insert i (I j)) :
    ∃ σ : Equiv.Perm (Fin d), ∀ j : ℕ, j ≤ m →
      Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j) = I j := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  choose! a ha using hstep
  have hmem : ∀ j : ℕ, j ≤ m → ∀ i : Fin d, i ∈ I j ↔ ∃ l, l < j ∧ a l = i := by
    intro j
    induction j with
    | zero => intro _ i; simp [hI0]
    | succ j ih =>
      intro hj i
      rw [(ha j (by omega)).2, Finset.mem_insert, ih (by omega)]
      constructor
      · rintro (rfl | ⟨l, hl, rfl⟩)
        · exact ⟨j, by omega, rfl⟩
        · exact ⟨l, by omega, rfl⟩
      · rintro ⟨l, hl, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
        · exact Or.inr ⟨l, hl, rfl⟩
        · exact Or.inl rfl
  have key : ∀ l l', l < l' → l' < m → a l ≠ a l' := by
    intro l l' hll' hl' heq
    exact (ha l' hl').1 ((hmem l' hl'.le (a l')).2 ⟨l, hll', heq⟩)
  have hinj : ∀ l l', l < m → l' < m → a l = a l' → l = l' := by
    intro l l' hl hl' heq
    rcases lt_trichotomy l l' with h | h | h
    · exact absurd heq (key l l' h hl')
    · exact h
    · exact absurd heq.symm (key l' l h hl)
  let e : {l : Fin d // l.val < m} → {i : Fin d // i ∈ I m} := fun l =>
    ⟨a l.val, (hmem m le_rfl _).2 ⟨l.val, l.2, rfl⟩⟩
  have hbij : Function.Bijective e := by
    constructor
    · rintro ⟨l, hl⟩ ⟨l', hl'⟩ heq
      have : a l.val = a l'.val := congrArg Subtype.val heq
      exact Subtype.ext (Fin.ext (hinj _ _ hl hl' this))
    · rintro ⟨i, hi⟩
      obtain ⟨l, hl, rfl⟩ := (hmem m le_rfl i).1 hi
      exact ⟨⟨⟨l, by omega⟩, hl⟩, rfl⟩
  refine ⟨(Equiv.ofBijective e hbij).extendSubtype, fun j hj => ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨l, rfl⟩ : ∃ l, (Equiv.ofBijective e hbij).extendSubtype l = i :=
    ⟨_, Equiv.apply_symm_apply _ i⟩
  rw [Equiv.symm_apply_apply]
  by_cases hl : l.val < m
  · have hσl : (Equiv.ofBijective e hbij).extendSubtype l = a l.val := by
      rw [Equiv.extendSubtype_apply_of_mem _ l hl]
      rfl
    rw [hσl, hmem j hj]
    constructor
    · intro h; exact ⟨l.val, h, rfl⟩
    · rintro ⟨l', hl', heq⟩
      have := hinj l' l.val (by omega) hl heq
      omega
  · have hσl := Equiv.extendSubtype_not_mem (Equiv.ofBijective e hbij) l hl
    constructor
    · intro h; omega
    · intro h
      exfalso; apply hσl
      obtain ⟨l', hl', heq⟩ := (hmem j hj _).1 h
      exact (hmem m le_rfl _).2 ⟨l', by omega, heq⟩

/-- The mesh average of a positive continuous weight is positive. -/
theorem aux_lane4_two_mesh_energy_bound_avg_pos {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (hf : Continuous f) (C : ℝ) (hC : 0 < C) (z : SpatialCoordinates d) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < (volume.real (Metric.ball z ρ))⁻¹ * ∫ x in Metric.ball z ρ, C * Real.exp (f x) := by
  have hball : 0 < volume (Metric.ball z ρ) := Metric.measure_ball_pos volume z hρ
  have hvol : 0 < volume.real (Metric.ball z ρ) :=
    ENNReal.toReal_pos hball.ne' measure_ball_lt_top.ne
  have hint : IntegrableOn (fun x => Real.exp (f x)) (Metric.ball z ρ) volume :=
    ((hf.rexp).continuousOn.integrableOn_compact (isCompact_closedBall z ρ)).mono_set
      Metric.ball_subset_closedBall
  haveI : NeZero (volume.restrict (Metric.ball z ρ)) :=
    ⟨by rw [Ne, Measure.restrict_eq_zero]; exact hball.ne'⟩
  have hexp := integral_exp_pos (μ := volume.restrict (Metric.ball z ρ)) hint
  rw [integral_const_mul]
  exact mul_pos (inv_pos.mpr hvol) (mul_pos hC hexp)

/-- The literal original reference weight `b_k(z)` is positive. -/
theorem aux_lane4_two_mesh_energy_bound_bpos {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N k : ℕ) (z : SpatialCoordinates d) :
    0 < (volume.real (Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2)))⁻¹ *
      ∫ x in Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2),
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp ((H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
            (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
  refine aux_lane4_two_mesh_energy_bound_avg_pos
    (fun x => (H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
      (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ?_ _
    (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)) z
    (by positivity)
  exact ((H omega).continuous.add
    (continuous_finset_sum (Finset.range k) fun (j : ℕ) _ =>
      (omega (-((j : ℕ) : ℤ))).continuous)).sub continuous_const

/-- Each source term is controlled by the original reference bound; at most `d+1` terms. -/
theorem aux_lane4_two_mesh_energy_bound_source {d : ℕ} (N : ℕ) (etas t0 V : ℝ)
    (hexp : 0 < (d : ℝ) + 2 - t0 - etas) (hV0 : 0 ≤ V)
    (b : ℕ → SpatialCoordinates d → ℝ) (hbpos : ∀ k z, 0 < b k z)
    (hV : ∀ k : ℕ, k ≤ N → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
        b k z + (b k z)⁻¹ ≤ V * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ (-etas))
    (S : Finset ℕ) (hcard : S.card ≤ d + 1) (kd : ℕ → ℕ) (z : ℕ → SpatialCoordinates d)
    (Rj : ℕ → ℝ)
    (hS : ∀ j ∈ S, kd j ≤ N ∧ Rj j = (3 : ℝ) ^ (-((kd j : ℤ))) / 2 ∧
      ∀ i, 0 ≤ z j i ∧ z j i ≤ 1) :
    ∑ j ∈ S, (b (kd j) (z j))⁻¹ * Rj j ^ ((d : ℝ) + 2 - t0) ≤ ((d : ℝ) + 1) * V := by
  have hterm : ∀ j ∈ S, (b (kd j) (z j))⁻¹ * Rj j ^ ((d : ℝ) + 2 - t0) ≤ V := by
    intro j hj
    obtain ⟨hk, hR, hz⟩ := hS j hj
    have hRpos : 0 < Rj j := by rw [hR]; positivity
    have hR1 : Rj j ≤ 1 := by
      rw [hR]
      have : (3 : ℝ) ^ (-((kd j : ℤ))) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
      linarith
    have hb := hbpos (kd j) (z j)
    have hinv : (b (kd j) (z j))⁻¹ ≤ V * Rj j ^ (-etas) := by
      have := hV (kd j) hk (z j) hz
      rw [← hR] at this
      linarith
    calc (b (kd j) (z j))⁻¹ * Rj j ^ ((d : ℝ) + 2 - t0)
        ≤ V * Rj j ^ (-etas) * Rj j ^ ((d : ℝ) + 2 - t0) :=
          mul_le_mul_of_nonneg_right hinv (Real.rpow_nonneg hRpos.le _)
      _ = V * Rj j ^ ((d : ℝ) + 2 - t0 - etas) := by
          rw [mul_assoc, ← Real.rpow_add hRpos]; congr 2; ring
      _ ≤ V * 1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one hRpos.le hR1 hexp.le) hV0
      _ = V := mul_one V
  calc ∑ j ∈ S, (b (kd j) (z j))⁻¹ * Rj j ^ ((d : ℝ) + 2 - t0) ≤ ∑ _j ∈ S, V :=
        Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * V := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((d : ℝ) + 1) * V :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hV0

/-- The first-mesh statistic, read at the encoded catalogue entry, controls the chain's
product of step constants; unused slots are padded by nonnegative allowances. -/
theorem aux_lane4_two_mesh_energy_bound_catalogue {d : ℕ} (J n : ℕ) (Cstep c eta U : ℝ)
    (hCstep : 1 ≤ Cstep) (hc : 0 ≤ c)
    (B : SpatialCoordinates d → Finset (Fin d) → ℕ → ℝ) (hB : ∀ y I k, 0 ≤ B y I k)
    (g : Fin d → Fin (3 ^ (n + J) + 1)) (σ : Equiv.Perm (Fin d))
    (y : SpatialCoordinates d)
    (hy : y = fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ))))
    (hU : ∀ dep : Fin (d + 1) → Fin (n + J + 1),
        (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
          B (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ))))
            (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val)) ≤ U)
    (m : ℕ) (hmd : m ≤ d) (I : ℕ → Finset (Fin d))
    (hσ : ∀ j : ℕ, j ≤ m → Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j) = I j)
    (kd : ℕ → ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range (m + 1))
    (hkd : ∀ j ∈ S, kd j ≤ n + J) :
    Cstep ^ (d + 1) * Real.exp (c * ∑ j ∈ S, B y (I j) (kd j)) ≤
      U * (3 : ℝ) ^ (eta * (n : ℝ)) := by
  subst hy
  obtain ⟨y, hy⟩ : ∃ y : SpatialCoordinates d,
      y = fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ))) := ⟨_, rfl⟩
  rw [← hy] at hU ⊢
  have h1 := hU (fun j => ⟨min (kd j.val) (n + J), Nat.lt_succ_of_le (min_le_right _ _)⟩)
  let f : ℕ → ℝ := fun l =>
    B y (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < l)) (min (kd l) (n + J))
  have hsum : (∑ j : Fin (d + 1), B y
      (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val))
        (min (kd j.val) (n + J))) = ∑ l ∈ Finset.range (d + 1), f l :=
    Fin.sum_univ_eq_sum_range f (d + 1)
  have hle : ∑ j ∈ S, B y (I j) (kd j) ≤ ∑ l ∈ Finset.range (d + 1), f l := by
    calc ∑ j ∈ S, B y (I j) (kd j) = ∑ j ∈ S, f j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hS hj))
          simp only [f, hσ j hjm, min_eq_left (hkd j hj)]
      _ ≤ ∑ l ∈ Finset.range (d + 1), f l := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · refine hS.trans fun l hl => ?_
            simp only [Finset.mem_range] at hl ⊢
            omega
          · intro l _ _; exact hB _ _ _
  have hZ : Cstep ^ (d + 1) * Real.exp (c * ∑ j ∈ S, B y (I j) (kd j)) ≤
      Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1), B y
        (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val))
          (min (kd j.val) (n + J))) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hc
    rw [hsum]; exact hle
  have h3 : 0 < (3 : ℝ) ^ (eta * (n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (3 : ℝ) ^ (-eta * (n : ℝ)) * (3 : ℝ) ^ (eta * (n : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  calc Cstep ^ (d + 1) * Real.exp (c * ∑ j ∈ S, B y (I j) (kd j))
      ≤ Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1), B y
        (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val))
          (min (kd j.val) (n + J))) := hZ
    _ = (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1), B y
        (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val))
          (min (kd j.val) (n + J)))) * (3 : ℝ) ^ (eta * (n : ℝ)) := by
        rw [mul_comm ((3 : ℝ) ^ (-eta * (n : ℝ))), mul_assoc, hinv, mul_one]
    _ ≤ U * (3 : ℝ) ^ (eta * (n : ℝ)) := mul_le_mul_of_nonneg_right h1 h3.le

theorem aux_lane4_two_mesh_energy_bound_U_ge {d : ℕ} (J : ℕ) (Cstep c eta U : ℝ)
    (hCstep : 1 ≤ Cstep) (hc : 0 ≤ c)
    (B : SpatialCoordinates d → Finset (Fin d) → ℕ → ℝ) (hB : ∀ y I k, 0 ≤ B y I k)
    (hU : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + J) + 1))
        (dep : Fin (d + 1) → Fin (n + J + 1)) (σ : Equiv.Perm (Fin d)),
        (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
          B (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ))))
            (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val)) ≤ U) :
    1 ≤ U := by
  have h := hU 0 (fun _ => 0) (fun _ => 0) 1
  have h0 : (3 : ℝ) ^ (-eta * ((0 : ℕ) : ℝ)) = 1 := by simp
  rw [h0, one_mul] at h
  have hC : 1 ≤ Cstep ^ (d + 1) := one_le_pow₀ hCstep
  have hE : 1 ≤ Real.exp (c * ∑ j : Fin (d + 1),
      B (fun i => (((fun _ => (0 : Fin (3 ^ (0 + J) + 1))) i : ℕ) : ℝ) *
        (3 : ℝ) ^ (-(((0 + J : ℕ) : ℤ))))
        (Finset.univ.filter (fun i : Fin d => ((1 : Equiv.Perm (Fin d)).symm i).val < j.val))
          ((fun _ => (0 : Fin (0 + J + 1))) j).val) :=
    Real.one_le_exp (mul_nonneg hc (Finset.sum_nonneg fun j _ => hB _ _ _))
  have := one_le_mul_of_one_le_of_one_le hC hE
  linarith

theorem aux_lane4_two_mesh_energy_bound_V_nonneg {d : ℕ} (N : ℕ) (etas V : ℝ)
    (b : ℕ → SpatialCoordinates d → ℝ) (hbpos : ∀ k z, 0 < b k z)
    (hV : ∀ k : ℕ, k ≤ N → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
        b k z + (b k z)⁻¹ ≤ V * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ (-etas)) :
    0 ≤ V := by
  have h := hV 0 (Nat.zero_le _) 0 (fun _ => ⟨le_rfl, zero_le_one⟩)
  have hb := hbpos 0 0
  have hpos : 0 < ((3 : ℝ) ^ (-(((0 : ℕ) : ℤ))) / 2) ^ (-etas) :=
    Real.rpow_pos_of_pos (by positivity) _
  by_contra hcon
  push_neg at hcon
  have h1 : V * ((3 : ℝ) ^ (-(((0 : ℕ) : ℤ))) / 2) ^ (-etas) < 0 := mul_neg_of_neg_of_pos hcon hpos
  have h2 : 0 < b 0 0 + (b 0 0)⁻¹ := by positivity
  linarith

theorem aux_lane4_two_mesh_energy_bound_smono {d : ℕ} (m : ℕ) (I : ℕ → Finset (Fin d))
    (s R : ℕ → ℝ) (used : ℕ → Bool) (Lstar : ℝ) (hL : 1 ≤ Lstar) (delta : Fin d → ℝ)
    (hdelta : ∀ i, 0 < delta i) (hs : ∀ j, j ≤ m → 0 < s j)
    (h8 : ∀ j, j ≤ m → used j = true → 8 * s j < R j)
    (htU : ∀ j : ℕ, j < m → used j = true →
      ∃ i : Fin d, I (j + 1) = insert i (I j) ∧ Lstar * R j + delta i ≤ s (j + 1))
    (htN : ∀ j : ℕ, j < m → used j = false →
      ∃ i : Fin d, I (j + 1) = insert i (I j) ∧ s j + delta i ≤ s (j + 1)) :
    ∀ j, j ≤ m → s 0 ≤ s j := by
  have hstep : ∀ j, j < m → s j ≤ s (j + 1) := by
    intro j hj
    cases hu : used j
    · obtain ⟨i, -, hle⟩ := htN j hj hu
      linarith [hdelta i]
    · obtain ⟨i, -, hle⟩ := htU j hj hu
      have h1 := h8 j hj.le hu
      have h2 := hs j hj.le
      have : R j ≤ Lstar * R j := le_mul_of_one_le_left (by linarith) hL
      linarith [hdelta i]
  intro j
  induction j with
  | zero => intro _; exact le_rfl
  | succ j ih => intro hj; exact (ih (by omega)).trans (hstep j (by omega))

/-- Final scale conversion: `3^{ηn} ≲ r^{-η}`, `r' ≤ 2r`, source sum `≤ (d+1)V`. -/
theorem aux_lane4_two_mesh_energy_bound_final (t0 eta Rstar dd : ℝ) (hdd : 0 ≤ dd)
    (ht0 : 0 < t0) (hRstar : 0 < Rstar)
    (K1 Cs ex Estart E U V Kf S r r' T : ℝ)
    (hK1 : 0 ≤ K1) (hP : 0 ≤ Cs * ex) (hE : 0 ≤ E) (hV : 0 ≤ V)
    (hr : 0 < r) (hr' : 0 < r') (hr'r : r' ≤ 2 * r)
    (hTpos : 0 < T) (hT : T ≤ 3 ^ eta * r ^ (-eta)) (hPU : Cs * ex ≤ U * T)
    (hS : S ≤ (dd + 1) * V)
    (hmain : Estart ≤ K1 * Cs * ex * r' ^ t0 * (Rstar ^ (-t0) * E + Kf ^ 2 * S)) :
    Estart ≤ (K1 * 3 ^ eta * 2 ^ t0 * (Rstar ^ (-t0) + dd + 1)) * U * r ^ (t0 - eta) *
      (E + V * Kf ^ 2) := by
  have hRt : 0 < Rstar ^ (-t0) := Real.rpow_pos_of_pos hRstar _
  have hW : Rstar ^ (-t0) * E + Kf ^ 2 * S ≤ (Rstar ^ (-t0) + dd + 1) * (E + V * Kf ^ 2) := by
    have h1 : Kf ^ 2 * S ≤ Kf ^ 2 * ((dd + 1) * V) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    have hA : 0 ≤ Rstar ^ (-t0) * (V * Kf ^ 2) := by positivity
    have hB : 0 ≤ (dd + 1) * E := by positivity
    have heq : (Rstar ^ (-t0) + dd + 1) * (E + V * Kf ^ 2) =
        Rstar ^ (-t0) * E + Rstar ^ (-t0) * (V * Kf ^ 2) + (dd + 1) * E +
          Kf ^ 2 * ((dd + 1) * V) := by ring
    rw [heq]; linarith
  have hW2 : 0 ≤ (Rstar ^ (-t0) + dd + 1) * (E + V * Kf ^ 2) := by positivity
  have hU : 0 ≤ U := by
    by_contra hcon
    push_neg at hcon
    have := mul_neg_of_neg_of_pos hcon hTpos
    linarith
  have hr't : r' ^ t0 ≤ 2 ^ t0 * r ^ t0 := by
    rw [← Real.mul_rpow (by norm_num) hr.le]
    exact Real.rpow_le_rpow hr'.le hr'r ht0.le
  have hr't0 : 0 ≤ r' ^ t0 := Real.rpow_nonneg hr'.le _
  have hrpow : r ^ (-eta) * r ^ t0 = r ^ (t0 - eta) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  calc Estart ≤ K1 * Cs * ex * r' ^ t0 * (Rstar ^ (-t0) * E + Kf ^ 2 * S) := hmain
    _ ≤ K1 * (Cs * ex) * r' ^ t0 * ((Rstar ^ (-t0) + dd + 1) * (E + V * Kf ^ 2)) := by
        rw [← mul_assoc K1 Cs ex]
        exact mul_le_mul_of_nonneg_left hW
          (by rw [mul_assoc K1 Cs ex]; exact mul_nonneg (mul_nonneg hK1 hP) hr't0)
    _ ≤ K1 * (U * T) * r' ^ t0 * ((Rstar ^ (-t0) + dd + 1) * (E + V * Kf ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ hW2
        apply mul_le_mul_of_nonneg_right _ hr't0
        exact mul_le_mul_of_nonneg_left hPU hK1
    _ = K1 * U * (T * r' ^ t0) * ((Rstar ^ (-t0) + dd + 1) * (E + V * Kf ^ 2)) := by ring
    _ ≤ K1 * U * ((3 ^ eta * r ^ (-eta)) * (2 ^ t0 * r ^ t0)) *
        ((Rstar ^ (-t0) + dd + 1) * (E + V * Kf ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ hW2
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK1 hU)
        exact mul_le_mul hT hr't hr't0 (by positivity)
    _ = (K1 * 3 ^ eta * 2 ^ t0 * (Rstar ^ (-t0) + dd + 1)) * U * (r ^ (-eta) * r ^ t0) *
        (E + V * Kf ^ 2) := by ring
    _ = _ := by rw [hrpow]

/-- Radii above `1/2` are handled by the global energy. -/
theorem aux_lane4_two_mesh_energy_bound_large (d : ℕ) (t0 eta : ℝ) (hp : 0 < t0 - eta)
    (hpd : t0 - eta ≤ d) (Cg : ℝ) (hCg : 2 ^ d ≤ Cg) (r : ℝ) (hr : 1 / 2 < r)
    (U V Kf Eb E : ℝ) (hU : 1 ≤ U) (hV : 0 ≤ V) (hE : 0 ≤ E) (hEb : Eb ≤ E) :
    Eb ≤ Cg * U * r ^ (t0 - eta) * (E + V * Kf ^ 2) := by
  have h1 : (1 / 2 : ℝ) ^ (t0 - eta) ≤ r ^ (t0 - eta) :=
    Real.rpow_le_rpow (by norm_num) hr.le hp.le
  have h2 : (1 / 2 : ℝ) ^ ((d : ℕ) : ℝ) ≤ (1 / 2 : ℝ) ^ (t0 - eta) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hpd
  have h3 : (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ ((d : ℕ) : ℝ) = 1 := by
    rw [Real.rpow_natCast, ← mul_pow]; norm_num
  have h2d : (0 : ℝ) < 2 ^ d := by positivity
  have hCr : 1 ≤ Cg * r ^ (t0 - eta) := by
    rw [← h3]
    exact mul_le_mul hCg (h2.trans h1) (by positivity) (by linarith)
  have hX : E ≤ E + V * Kf ^ 2 := by have := mul_nonneg hV (sq_nonneg Kf); linarith
  have hCU : 1 ≤ Cg * U * r ^ (t0 - eta) := by
    calc (1 : ℝ) ≤ Cg * r ^ (t0 - eta) := hCr
      _ ≤ Cg * r ^ (t0 - eta) * U := le_mul_of_one_le_right (by linarith) hU
      _ = Cg * U * r ^ (t0 - eta) := by ring
  calc Eb ≤ E := hEb
    _ ≤ E + V * Kf ^ 2 := hX
    _ ≤ Cg * U * r ^ (t0 - eta) * (E + V * Kf ^ 2) :=
        le_mul_of_one_le_left (by linarith) hCU

/-- The boundary-stratum chain of the frozen `rem_resolved_strata`, at a base point `y`. -/
theorem aux_lane4_two_mesh_energy_bound_chain (d : ℕ) (hd : 2 ≤ d) (Lstar t0 : ℝ)
    (hLstar : 10 ≤ Lstar) (ht0 : 0 < t0) (ht0d : t0 < (d : ℝ))
    (Rstar : ℝ) (hRstar : 0 < Rstar) (hRsmall : Rstar < 1 / (100 * Lstar))
    (hRhalf : ∃ k : ℤ, Rstar = (3 : ℝ) ^ k / 2)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (y : SpatialCoordinates d) (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (r : ℝ) (hr : eps ≤ r) (hr1 : r ≤ 1) :
    ∃ (m : ℕ) (I : ℕ → Finset (Fin d)) (s R : ℕ → ℝ) (used : ℕ → Bool),
      m ≤ d ∧ I 0 = ∅ ∧ r / 2 ≤ s 0 ∧ s 0 < 3 * (r / 2) ∧
      (∀ j : ℕ, j ≤ m →
        s j ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) ∧ 0 < s j ∧ eps / 2 ≤ s j) ∧
      (∀ j : ℕ, j ≤ m → used j = true →
        R j ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) ∧ 8 * s j < R j ∧ R j ≤ Rstar ∧
          ∀ i : Fin d, i ∉ I j → 4 * Lstar * R j ≤ min (y i) (1 - y i)) ∧
      (∀ j : ℕ, j < m → used j = true → s (j + 1) ≤ 3 * (1 + 100 * Lstar) * R j) ∧
      (∀ j : ℕ, j < m → used j = false → s (j + 1) ≤ 3 * (1 + 100 * Lstar) * s j) ∧
      (∀ j : ℕ, j < m → used j = true →
        ∃ i : Fin d, I (j + 1) = insert i (I j) ∧
          Lstar * R j + min (y i) (1 - y i) ≤ s (j + 1)) ∧
      (∀ j : ℕ, j < m → used j = false →
        ∃ i : Fin d, I (j + 1) = insert i (I j) ∧ s j + min (y i) (1 - y i) ≤ s (j + 1)) ∧
      (∀ j : ℕ, j < m → ∃ i : Fin d, i ∉ I j ∧ I (j + 1) = insert i (I j)) ∧
      (s m ≥ Rstar / 24 ∨ (used m = true ∧ R m = Rstar)) ∧
      (used m = true → s m < Rstar / 24) := by
  have hrem := rem_resolved_strata d hd Lstar t0 hLstar ht0 ht0d
  rcases hrem with ⟨Cg, -, h1, -⟩
  have h2 := h1 1 0 le_rfl le_rfl Rstar hRstar hRsmall hRhalf eps heps heps1 y hy r hr hr1
  extract_lets half delta face center cube nextFaceDistance cap near at h2
  rcases h2 with ⟨m, I, s, R, used, h3⟩
  extract_lets J at h3
  rcases h3 with ⟨⟨hmd, hI0, hs0⟩, hQ, -, hU, hS, hT, -, -, -, -⟩
  have hyI : ∀ i, 0 < y i ∧ y i < 1 := aux_rem_resolved_strata_mem_cube hy
  have hdelta : ∀ i, 0 < delta i := fun i => lt_min (hyI i).1 (sub_pos.mpr (hyI i).2)
  have hr0 : 0 < r / 2 := by linarith
  have hs : ∀ j : ℕ, j ≤ m → 0 < s j := fun j hj => (hQ j hj).2.1
  have htrans := aux_rem_resolved_strata_transitions d Lstar Rstar half delta nextFaceDistance
    cap near m I s R used hU hS
  have hnext : ∀ j : ℕ, j < m →
      (used j = true → s (j + 1) ≤ 3 * (1 + 100 * Lstar) * R j) ∧
        (used j = false → s (j + 1) ≤ 3 * (1 + 100 * Lstar) * s j) :=
    fun j hj => aux_rem_resolved_strata_next d Lstar Rstar hLstar hRhalf half rfl delta hdelta
      nextFaceDistance cap rfl near (I j) (I (j + 1)) (s j) (R j) (s (j + 1)) (used j)
      (hs j hj.le) (hU j hj.le) (hS j hj)
  refine ⟨m, I, s, R, used, hmd, hI0, hs0.1.2, aux_rem_resolved_strata_least_lt hr0 hs0, hQ,
    ?_, fun j hj => (hnext j hj).1, fun j hj => (hnext j hj).2, htrans.1, htrans.2, ?_, hT, ?_⟩
  · intro j hj hu
    obtain ⟨hgr, h8, hRle, hclear⟩ := (hU j hj).2.1 hu
    exact ⟨hgr.1.1, h8, hRle, hclear⟩
  · intro j hj
    rcases (hS j hj).2 with ⟨_, i, hi, _, hins, _⟩ | ⟨_, _, _, i, hi, _, hins, _⟩
    · exact ⟨i, hi, hins⟩
    · exact ⟨i, hi, hins⟩
  · intro hu
    exact ((hU m le_rfl).1.mp hu).1

/-- Energy composition along the chain based at the mesh point `y`, via the proved
composition helper of `rem_resolved_strata`. -/
theorem aux_lane4_two_mesh_energy_bound_energy (d : ℕ) (hd : 1 ≤ d) (Lstar Rstar t0 : ℝ)
    (hRstar : 0 < Rstar) (ht0 : 0 < t0) (Cstep c Kf : ℝ) (hCstep : 1 ≤ Cstep) (hc : 0 ≤ c)
    (energy : Set (SpatialCoordinates d) → ℝ)
    (hmono : ∀ A A' : Set (SpatialCoordinates d), A ⊆ A' → energy A ≤ energy A')
    (hnn : ∀ A, 0 ≤ energy A)
    (y : SpatialCoordinates d) (hy : ∀ i, 0 < y i ∧ y i < 1)
    (m : ℕ) (hmd : m ≤ d) (I : ℕ → Finset (Fin d)) (s R : ℕ → ℝ) (used : ℕ → Bool)
    (Bv bv : ℕ → ℝ) (r : ℝ) (hr : 0 < r) (hI0 : I 0 = ∅) (hs0 : r / 2 ≤ s 0)
    (hs0' : s 0 < 3 * (r / 2))
    (hs : ∀ j : ℕ, j ≤ m → 0 < s j)
    (hR : ∀ j : ℕ, j ≤ m → used j = true → 0 < R j)
    (hB : ∀ j : ℕ, j ≤ m → used j = true → 0 ≤ Bv j)
    (hb : ∀ j : ℕ, j ≤ m → used j = true → 0 < bv j)
    (hnU : ∀ j : ℕ, j < m → used j = true → s (j + 1) ≤ 3 * (1 + 100 * Lstar) * R j)
    (hnN : ∀ j : ℕ, j < m → used j = false → s (j + 1) ≤ 3 * (1 + 100 * Lstar) * s j)
    (htU : ∀ j : ℕ, j < m → used j = true →
      ∃ i : Fin d, I (j + 1) = insert i (I j) ∧ Lstar * R j + min (y i) (1 - y i) ≤ s (j + 1))
    (htN : ∀ j : ℕ, j < m → used j = false →
      ∃ i : Fin d, I (j + 1) = insert i (I j) ∧ s j + min (y i) (1 - y i) ≤ s (j + 1))
    (hT : s m ≥ Rstar / 24 ∨ (used m = true ∧ R m = Rstar))
    (hUm : used m = true → s m < Rstar / 24)
    (hK1 : 1 ≤ 3 * (1 + 100 * Lstar))
    (hstepU : ∀ j : ℕ, j ≤ m → used j = true →
      energy (Metric.ball (fun i => if i ∈ I j then (if y i ≤ 1 / 2 then (0 : ℝ) else 1)
          else y i) (s j)) ≤
        Cstep * Real.exp (c * Bv j) * (s j / R j) ^ t0 *
          (energy (Metric.ball (fun i => if i ∈ I j then (if y i ≤ 1 / 2 then (0 : ℝ) else 1)
              else y i) (Lstar * R j)) +
            (bv j)⁻¹ * Kf ^ 2 * R j ^ ((d : ℝ) + 2)))
    (x : SpatialCoordinates d) (ρ : ℝ) (hxρ : ∀ i, |x i - y i| + ρ ≤ r / 2) :
    energy (Metric.ball x ρ) ≤ (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * Cstep ^ (d + 1) *
      Real.exp (c * ∑ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true), Bv j) *
      r ^ t0 *
      (Rstar ^ (-t0) * energy Set.univ + Kf ^ 2 *
        ∑ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true),
          (bv j)⁻¹ * (R j) ^ ((d : ℝ) + 2 - t0)) := by
  have hball := aux_lane4_two_mesh_energy_bound_ball_eq hd
  exact aux_rem_resolved_strata_energy_chain d m hmd s R used
    (fun j => energy (Metric.ball (fun i => if i ∈ I j then (if y i ≤ 1 / 2 then (0 : ℝ) else 1)
      else y i) (s j)))
    (fun j => energy (Metric.ball (fun i => if i ∈ I j then (if y i ≤ 1 / 2 then (0 : ℝ) else 1)
      else y i) (Lstar * R j)))
    Bv bv (3 * (1 + 100 * Lstar)) r Rstar t0 Cstep c Kf (energy Set.univ)
    (energy (Metric.ball x ρ))
    hK1 hr hRstar ht0 hCstep hc (hnn _) hs0' hs hR hB hb (fun j _ => hnn _) hnU hnN hstepU
    (fun j hj hu => by
      obtain ⟨i, hins, hle⟩ := htU j hj hu
      apply hmono
      rw [hball, hball, hins]
      exact aux_rem_resolved_strata_cube_insert y hy (I j) i _ _ hle)
    (fun _ => hmono _ _ (Set.subset_univ _))
    (fun j hj hu => by
      obtain ⟨i, hins, hle⟩ := htN j hj hu
      apply hmono
      rw [hball, hball, hins]
      exact aux_rem_resolved_strata_cube_insert y hy (I j) i _ _ hle)
    (fun _ => hmono _ _ (Set.subset_univ _))
    hT hUm
    (by
      apply hmono
      rw [hball, hball, hI0]
      intro z hz k
      simp only [Finset.notMem_empty, if_false]
      have h1 := hz k
      have h2 := hxρ k
      calc |z k - y k| ≤ |z k - x k| + |x k - y k| := abs_sub_le _ _ _
        _ < ρ + |x k - y k| := by linarith
        _ ≤ r / 2 := by linarith
        _ ≤ s 0 := hs0)

/-- Main branch `r ≤ 1/2`: shifted target-mesh point, boundary chain, catalogue, reference
bound, and scale conversion. -/
theorem aux_lane4_two_mesh_energy_bound_main (d : ℕ) (hd : 2 ≤ d)
    (Lstar Rstar t0 eta etas : ℝ)
    (hLstar : 10 ≤ Lstar) (hRstar_pos : 0 < Rstar) (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (hRstar_mem : Rstar ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (ht0_low : (d : ℝ) - 1 < t0) (ht0_high : t0 < (d : ℝ))
    (heta_pos : 0 < eta) (hetas_lt : etas < (d : ℝ) + 2 - t0)
    (J : ℕ) (hJ : 1 ≤ J) (Cstep c : ℝ) (hCstep : 1 ≤ Cstep) (hc : 0 ≤ c)
    (N : ℕ) (Kf : ℝ)
    (energy : Set (SpatialCoordinates d) → ℝ)
    (hmono : ∀ A A' : Set (SpatialCoordinates d), A ⊆ A' → energy A ≤ energy A')
    (hnn : ∀ A, 0 ≤ energy A)
    (b : ℕ → SpatialCoordinates d → ℝ) (hbpos : ∀ k z, 0 < b k z)
    (B : SpatialCoordinates d → Finset (Fin d) → ℕ → ℝ) (hB : ∀ y I k, 0 ≤ B y I k)
    (hstep : ∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ),
      s ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) → (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s →
      k ≤ N → 8 * s < (3 : ℝ) ^ (-((k : ℤ))) / 2 → (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar →
      (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i)) →
      energy (Metric.ball (fun i => if i ∈ I then (if y i ≤ 1 / 2 then (0 : ℝ) else 1)
          else y i) s) ≤
        Cstep * Real.exp (c * B y I k) * (s / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (energy (Metric.ball (fun i => if i ∈ I then (if y i ≤ 1 / 2 then (0 : ℝ) else 1)
              else y i) (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (b k (fun i => if i ∈ I then (if y i ≤ 1 / 2 then (0 : ℝ) else 1) else y i))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)))
    (U : ℝ)
    (hU : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + J) + 1))
        (dep : Fin (d + 1) → Fin (n + J + 1)) (σ : Equiv.Perm (Fin d)),
        (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
          B (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ))))
            (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val)) ≤ U)
    (V : ℝ)
    (hV : ∀ k : ℕ, k ≤ N → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
        b k z + (b k z)⁻¹ ≤ V * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ (-etas))
    (hV0 : 0 ≤ V)
    (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (r : ℝ) (hr : (3 : ℝ) ^ (-(N : ℤ)) ≤ r) (hr2 : r ≤ 1 / 2) :
    energy (Metric.ball x (r / 2)) ≤
      ((36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
        (Rstar ^ (-t0) + (d : ℝ) + 1)) * U * r ^ (t0 - eta) * (energy Set.univ + V * Kf ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have ht0 : 0 < t0 := by linarith
  have hL0 : 0 < Lstar := by linarith
  have heps : 0 < (3 : ℝ) ^ (-(N : ℤ)) := zpow_pos (by norm_num) _
  have heps1 : (3 : ℝ) ^ (-(N : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hr0 : 0 < r := lt_of_lt_of_le heps hr
  obtain ⟨n, hn1, hn2⟩ := aux_lane4_two_mesh_energy_bound_scale hr0 (by linarith)
  have hxc := aux_rem_resolved_strata_mem_cube hx
  obtain ⟨g, hg⟩ := aux_lane4_two_mesh_energy_bound_grid (n + J) (by omega) x hxc
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ))) := ⟨_, rfl⟩
  have hhpos : 0 < h := by rw [hh]; exact zpow_pos (by norm_num) _
  have hhr : 3 * h ≤ r := by
    have h1 : (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ))) ≤ (3 : ℝ) ^ (-((n : ℤ) + 1)) :=
      zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
    have h2 : (3 : ℝ) ^ (-((n : ℤ) + 1)) * 3 = (3 : ℝ) ^ (-(n : ℤ)) := by
      rw [neg_add, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), mul_assoc,
        show (3 : ℝ) ^ (-1 : ℤ) * 3 = 1 by norm_num, mul_one]
    rw [hh]; linarith
  obtain ⟨y, hy⟩ : ∃ y : SpatialCoordinates d,
      y = fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ))) := ⟨_, rfl⟩
  have hyc : ∀ i, 0 < y i ∧ y i < 1 := fun i => by rw [hy]; exact ⟨(hg i).1, (hg i).2.1⟩
  have hxy : ∀ i, |x i - y i| < h := fun i => by rw [hy, hh]; exact (hg i).2.2
  have hyQ := aux_lane4_two_mesh_energy_bound_mem_cube hyc
  obtain ⟨r', hr'⟩ : ∃ r' : ℝ, r' = r + 2 * h := ⟨_, rfl⟩
  have hr'1 : r' ≤ 1 := by linarith
  have hr'r : r' ≤ 2 * r := by linarith
  have hr'0 : 0 < r' := by linarith
  have hepsr' : (3 : ℝ) ^ (-(N : ℤ)) ≤ r' := by linarith
  have hRhalf : ∃ k : ℤ, Rstar = (3 : ℝ) ^ k / 2 := by
    obtain ⟨k, hk⟩ := hRstar_mem; exact ⟨k, hk.symm⟩
  have hch := aux_lane4_two_mesh_energy_bound_chain d hd Lstar t0 hLstar ht0 ht0_high Rstar
    hRstar_pos hRstar_lt hRhalf _ heps heps1 y hyQ r' hepsr' hr'1
  rcases hch with ⟨m, I, s, R, used, hmd, hI0, hs0, hs0', hQ, hUsed, hnU, hnN, htU, htN, hins,
    hT, hUm⟩
  have hsmono := aux_lane4_two_mesh_energy_bound_smono m I s R used Lstar (by linarith)
    (fun i => min (y i) (1 - y i)) (fun i => lt_min (hyc i).1 (sub_pos.mpr (hyc i).2))
    (fun j hj => (hQ j hj).2.1) (fun j hj hu => (hUsed j hj hu).2.1) htU htN
  have hRlt : Rstar < 1 / 2 := by
    have : 1 / (100 * Lstar) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hdep : ∀ j : ℕ, ∃ k : ℕ, j ≤ m → used j = true →
      R j = (3 : ℝ) ^ (-(k : ℤ)) / 2 ∧ k < n ∧ k < N := by
    intro j
    by_cases hj : j ≤ m ∧ used j = true
    · obtain ⟨hRh, h8, hRle, -⟩ := hUsed j hj.1 hj.2
      obtain ⟨k, hk, hkn⟩ := aux_lane4_two_mesh_energy_bound_depth hRh (by linarith)
      refine ⟨k, fun _ _ => ⟨hk, hkn n ?_, hkn N ?_⟩⟩
      · have h1 := hsmono j hj.1
        linarith
      · have h1 := (hQ j hj.1).2.2
        linarith
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose kd hkd using hdep
  obtain ⟨σ, hσ⟩ := aux_lane4_two_mesh_energy_bound_perm hd1 m hmd I hI0 hins
  have hRpos : ∀ j : ℕ, j ≤ m → used j = true → 0 < R j := fun j hj hu => by
    rw [(hkd j hj hu).1]; positivity
  have hE := aux_lane4_two_mesh_energy_bound_energy d hd1 Lstar Rstar t0 hRstar_pos ht0 Cstep c
    Kf hCstep hc energy hmono hnn y hyc m hmd I s R used (fun j => B y (I j) (kd j))
    (fun j => b (kd j) (fun i => if i ∈ I j then (if y i ≤ 1 / 2 then (0 : ℝ) else 1) else y i))
    r' hr'0 hI0 hs0 hs0' (fun j hj => (hQ j hj).2.1) hRpos (fun j _ _ => hB _ _ _)
    (fun j _ _ => hbpos _ _) hnU hnN htU htN hT hUm (by linarith)
    (fun j hj hu => by
      have hk := hkd j hj hu
      obtain ⟨hRh, h8, hRle, hclear⟩ := hUsed j hj hu
      rw [hk.1] at h8 hRle hclear
      have hst := hstep y hyQ (I j) (s j) (kd j) (hQ j hj).1 (hQ j hj).2.2 (hQ j hj).2.1
        hk.2.2.le h8 hRle hclear
      rw [← hk.1] at hst
      exact hst)
    x (r / 2) (fun i => by have := hxy i; linarith)
  have hScard : ((Finset.range (m + 1)).filter (fun j => used j = true)).card ≤ d + 1 :=
    (Finset.card_filter_le _ _).trans (by simp; omega)
  have hmemS : ∀ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true),
      j ≤ m ∧ used j = true := fun j hj => by
    have hj' := Finset.mem_filter.mp hj
    exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hj'.1), hj'.2⟩
  have hcat := aux_lane4_two_mesh_energy_bound_catalogue J n Cstep c eta U hCstep hc B hB g σ y hy
    (fun dep => hU n g dep σ) m hmd I hσ kd _ (Finset.filter_subset _ _)
    (fun j hj => by
      have := (hkd j (hmemS j hj).1 (hmemS j hj).2).2.1
      omega)
  have hsrc := aux_lane4_two_mesh_energy_bound_source N etas t0 V (by linarith) hV0 b hbpos hV _
    hScard kd (fun j i => if i ∈ I j then (if y i ≤ 1 / 2 then (0 : ℝ) else 1) else y i) R
    (fun j hj => by
      have hk := hkd j (hmemS j hj).1 (hmemS j hj).2
      refine ⟨hk.2.2.le, hk.1, fun i => ?_⟩
      show 0 ≤ (if i ∈ I j then (if y i ≤ 1 / 2 then (0 : ℝ) else 1) else y i) ∧
        (if i ∈ I j then (if y i ≤ 1 / 2 then (0 : ℝ) else 1) else y i) ≤ 1
      split_ifs
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨zero_le_one, le_rfl⟩
      · exact ⟨(hyc i).1.le, (hyc i).2.le⟩)
  have hT3 := aux_lane4_two_mesh_energy_bound_scale_pow hr0 heta_pos n hn2
  have hK1 : 0 ≤ (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 :=
    Real.rpow_nonneg (by have : 0 ≤ 3 * (1 + 100 * Lstar) := by linarith
                         positivity) _
  have hP : 0 ≤ Cstep ^ (d + 1) *
      Real.exp (c * ∑ j ∈ (Finset.range (m + 1)).filter (fun j => used j = true),
        B y (I j) (kd j)) :=
    mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le
  exact aux_lane4_two_mesh_energy_bound_final t0 eta Rstar d (Nat.cast_nonneg d) ht0 hRstar_pos
    _ _ _ _ _ U V Kf _ r r' _ hK1 hP (hnn _) hV0 hr0 hr'0 hr'r
    (Real.rpow_pos_of_pos (by norm_num) _) hT3 hcat hsrc hE

/-- Deterministic core with the frozen constant, for abstract energy and data. -/
theorem aux_lane4_two_mesh_energy_bound_core (d : ℕ) (hd : 2 ≤ d)
    (Lstar Rstar t0 eta etas : ℝ)
    (hLstar : 10 ≤ Lstar) (hRstar_pos : 0 < Rstar) (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (hRstar_mem : Rstar ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (ht0_low : (d : ℝ) - 1 < t0) (ht0_high : t0 < (d : ℝ))
    (heta_pos : 0 < eta) (heta_lt : eta < t0 - ((d : ℝ) - 1))
    (hetas_lt : etas < (d : ℝ) + 2 - t0)
    (J : ℕ) (hJ : 1 ≤ J) (Cstep c : ℝ) (hCstep : 1 ≤ Cstep) (hc : 0 ≤ c)
    (N : ℕ) (Kf : ℝ)
    (energy : Set (SpatialCoordinates d) → ℝ)
    (hmono : ∀ A A' : Set (SpatialCoordinates d), A ⊆ A' → energy A ≤ energy A')
    (hnn : ∀ A, 0 ≤ energy A)
    (b : ℕ → SpatialCoordinates d → ℝ) (hbpos : ∀ k z, 0 < b k z)
    (B : SpatialCoordinates d → Finset (Fin d) → ℕ → ℝ) (hB : ∀ y I k, 0 ≤ B y I k)
    (hstep : ∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ),
      s ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) → (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s →
      k ≤ N → 8 * s < (3 : ℝ) ^ (-((k : ℤ))) / 2 → (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar →
      (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i)) →
      energy (Metric.ball (fun i => if i ∈ I then (if y i ≤ 1 / 2 then (0 : ℝ) else 1)
          else y i) s) ≤
        Cstep * Real.exp (c * B y I k) * (s / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (energy (Metric.ball (fun i => if i ∈ I then (if y i ≤ 1 / 2 then (0 : ℝ) else 1)
              else y i) (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (b k (fun i => if i ∈ I then (if y i ≤ 1 / 2 then (0 : ℝ) else 1) else y i))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)))
    (U : ℝ)
    (hU : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + J) + 1))
        (dep : Fin (d + 1) → Fin (n + J + 1)) (σ : Equiv.Perm (Fin d)),
        (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
          B (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ))))
            (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val)) ≤ U)
    (V : ℝ)
    (hV : ∀ k : ℕ, k ≤ N → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
        b k z + (b k z)⁻¹ ≤ V * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ (-etas))
    (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (r : ℝ) (hr : (3 : ℝ) ^ (-(N : ℤ)) ≤ r) :
    energy (Metric.ball x (r / 2)) ≤
      (2 ^ d + (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
        (Rstar ^ (-t0) + (d : ℝ) + 1)) * U * r ^ (t0 - eta) * (energy Set.univ + V * Kf ^ 2) := by
  have hU1 := aux_lane4_two_mesh_energy_bound_U_ge J Cstep c eta U hCstep hc B hB hU
  have hV0 := aux_lane4_two_mesh_energy_bound_V_nonneg N etas V b hbpos hV
  have hEnn := hnn Set.univ
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hK1 : 0 ≤ (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
      (Rstar ^ (-t0) + (d : ℝ) + 1) := by
    have h36 : 0 ≤ (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 :=
      Real.rpow_nonneg (by have : 0 ≤ 3 * (1 + 100 * Lstar) := by linarith
                           positivity) _
    have hR : 0 ≤ Rstar ^ (-t0) := (Real.rpow_pos_of_pos hRstar_pos _).le
    have h3 : 0 ≤ (3 : ℝ) ^ eta := (Real.rpow_pos_of_pos (by norm_num) _).le
    have h2 : 0 ≤ (2 : ℝ) ^ t0 := (Real.rpow_pos_of_pos (by norm_num) _).le
    have : 0 ≤ Rstar ^ (-t0) + (d : ℝ) + 1 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg h36 h3) h2) this
  by_cases hr2 : r ≤ 1 / 2
  · have hmain := aux_lane4_two_mesh_energy_bound_main d hd Lstar Rstar t0 eta etas hLstar
      hRstar_pos hRstar_lt hRstar_mem ht0_low ht0_high heta_pos hetas_lt J hJ Cstep c hCstep hc
      N Kf energy hmono hnn b hbpos B hB hstep U hU V hV hV0 x hx r hr hr2
    have hr0 : 0 < r := lt_of_lt_of_le (zpow_pos (by norm_num) _) hr
    have hX : 0 ≤ U * r ^ (t0 - eta) * (energy Set.univ + V * Kf ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hr0.le _))
        (add_nonneg hEnn (mul_nonneg hV0 (sq_nonneg _)))
    have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
    calc energy (Metric.ball x (r / 2))
        ≤ ((36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
          (Rstar ^ (-t0) + (d : ℝ) + 1)) * U * r ^ (t0 - eta) *
            (energy Set.univ + V * Kf ^ 2) := hmain
      _ = ((36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
          (Rstar ^ (-t0) + (d : ℝ) + 1)) * (U * r ^ (t0 - eta) *
            (energy Set.univ + V * Kf ^ 2)) := by ring
      _ ≤ (2 ^ d + (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
          (Rstar ^ (-t0) + (d : ℝ) + 1)) * (U * r ^ (t0 - eta) *
            (energy Set.univ + V * Kf ^ 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) hX
      _ = _ := by ring
  · push_neg at hr2
    exact aux_lane4_two_mesh_energy_bound_large d t0 eta (by linarith) (by linarith) _
      (le_add_of_nonneg_right hK1) r hr2 U V Kf _ _ hU1 hV0 hEnn
      (hmono _ _ (Set.subset_univ _))

theorem aux_lane4_two_mesh_energy_bound_Cpos (d : ℕ) (Lstar Rstar t0 eta : ℝ)
    (hLstar : 10 ≤ Lstar) (hRstar : 0 < Rstar) :
    0 < 2 ^ d + (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
      (Rstar ^ (-t0) + (d : ℝ) + 1) := by
  have h36 : 0 ≤ (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 :=
    Real.rpow_nonneg (by have : 0 ≤ 3 * (1 + 100 * Lstar) := by linarith
                         positivity) _
  have hR : 0 ≤ Rstar ^ (-t0) := (Real.rpow_pos_of_pos hRstar _).le
  have h3 : 0 ≤ (3 : ℝ) ^ eta := (Real.rpow_pos_of_pos (by norm_num) _).le
  have h2 : 0 ≤ (2 : ℝ) ^ t0 := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hd : 0 ≤ Rstar ^ (-t0) + (d : ℝ) + 1 := by positivity
  exact add_pos_of_pos_of_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (mul_nonneg h36 h3) h2) hd)




theorem lane4_two_mesh_energy_bound
    (d : ℕ) (hd : 2 ≤ d)
    (Lstar Rstar t0 eta etas : ℝ)
    (hLstar : 10 ≤ Lstar)
    (hRstar_pos : 0 < Rstar)
    (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (hRstar_mem : Rstar ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (ht0_low : (d : ℝ) - 1 < t0)
    (ht0_high : t0 < (d : ℝ))
    (heta_pos : 0 < eta)
    (heta_lt : eta < t0 - ((d : ℝ) - 1))
    (hetas_pos : 0 < etas)
    (hetas_lt : etas < (d : ℝ) + 2 - t0) :
    ∃ J0 : ℕ, 1 ≤ J0 ∧ ∃ Cgeom : ℝ, 0 < Cgeom ∧
      ∀ J : ℕ, J0 ≤ J → ∀ Cstep c : ℝ, 1 ≤ Cstep → 0 ≤ c →
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)],
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      ∀ (N : ℕ) (omega : BilateralField d)
        (u : weakSobolevGraph (unitNeumannCube d)) (Kf : ℝ), 0 ≤ Kf →
      let Q : Opens (SpatialCoordinates d) := unitNeumannCube d;
      let a := cutoffPositiveCoefficient M H omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos;
      let eps : ℝ := (3 : ℝ) ^ (-(N : ℤ));
      let half : Set ℝ := Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2);
      let R : ℕ → ℝ := fun k => (3 : ℝ) ^ (-((k : ℤ))) / 2;
      let energy : Set (SpatialCoordinates d) → ℝ := fun A =>
        ∫ y in A ∩ (Q : Set (SpatialCoordinates d)),
          a.val y * ∑ i : Fin d,
            (((sobolevGradient (u : SobolevData Q)) i : SpatialCoordinates d → ℝ) y) ^ 2;
      let face : SpatialCoordinates d → Fin d → ℝ :=
        fun y i => if y i ≤ 1 / 2 then 0 else 1;
      let delta : SpatialCoordinates d → Fin d → ℝ :=
        fun y i => min (y i) (1 - y i);
      let center : SpatialCoordinates d → Finset (Fin d) → SpatialCoordinates d :=
        fun y I i => if i ∈ I then face y i else y i;
      let cube : SpatialCoordinates d → Finset (Fin d) → ℝ → Set (SpatialCoordinates d) :=
        fun y I s => Metric.ball (center y I) s;
      let e : SpatialCoordinates d → Finset (Fin d) → ℝ → ℝ :=
        fun y I s => energy (cube y I s);
      let G : ℕ → SpatialCoordinates d → ℝ := fun k x =>
        H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x;
      let spoint : ℕ → SpatialCoordinates d → ℝ := fun k x =>
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (G k x - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P);
      let b : ℕ → SpatialCoordinates d → ℝ := fun k z =>
        (volume.real (Metric.ball z (R k)))⁻¹ * ∫ x in Metric.ball z (R k), spoint k x;
      let Cat : ℕ → Type := fun n =>
        (Fin d → Fin (3 ^ (n + J) + 1)) ×
          ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d));
      let ygrid : (n : ℕ) → Cat n → SpatialCoordinates d := fun n pi i =>
        ((pi.1 i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ)));
      let active : (n : ℕ) → Cat n → Fin (d + 1) → Finset (Fin d) := fun n pi j =>
        Finset.univ.filter (fun i : Fin d => (pi.2.2.symm i).val < j.val);
      let rootDepth : (n : ℕ) → Cat n → Fin (d + 1) → ℕ := fun n pi j => (pi.2.1 j).val;
      ∀ (B : SpatialCoordinates d → Finset (Fin d) → ℕ → ℝ),
      (∀ (y : SpatialCoordinates d) (I : Finset (Fin d)) (k : ℕ), 0 ≤ B y I k) →
      (∀ (y : SpatialCoordinates d), y ∈ (Q : Set (SpatialCoordinates d)) →
        ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ),
        s ∈ half → eps / 2 ≤ s → 0 < s → k ≤ N → 8 * s < R k → R k ≤ Rstar →
        (∀ i, i ∉ I → 4 * Lstar * R k ≤ delta y i) →
        e y I s ≤ Cstep * Real.exp (c * B y I k) * (s / R k) ^ t0 *
          (e y I (Lstar * R k) +
            (b k (center y I))⁻¹ * Kf ^ 2 * (R k) ^ ((d : ℝ) + 2))) →
      let Z : (n : ℕ) → Cat n → ℝ := fun n pi =>
        Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
          B (ygrid n pi) (active n pi j) (rootDepth n pi j));
      ∀ (U : ℝ),
      IsLUB {v : ℝ | ∃ n : ℕ, ∃ pi : Cat n,
        v = (3 : ℝ) ^ (-eta * (n : ℝ)) * Z n pi} U →
      ∀ (V : ℝ),
      (∀ k : ℕ, k ≤ N → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
        b k z + (b k z)⁻¹ ≤ V * (R k) ^ (-etas)) →
      ∀ (x : SpatialCoordinates d), x ∈ (Q : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, eps ≤ r →
        energy (Metric.ball x (r / 2)) ≤
          Cgeom * U * r ^ (t0 - eta) * (energy Set.univ + V * Kf ^ 2) := by
  refine ⟨1, le_rfl, 2 ^ d + (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
      (Rstar ^ (-t0) + (d : ℝ) + 1),
    aux_lane4_two_mesh_energy_bound_Cpos d Lstar Rstar t0 eta hLstar hRstar_pos, ?_⟩
  intro J hJ Cstep c hCstep hc M _ _ H N omega u Kf hKf Q a eps half R energy face delta center
    cube e G spoint b Cat ygrid active rootDepth B hB hstep Z U hU V hV x hx r hr
  exact aux_lane4_two_mesh_energy_bound_core d hd Lstar Rstar t0 eta etas hLstar hRstar_pos
    hRstar_lt hRstar_mem ht0_low ht0_high heta_pos heta_lt hetas_lt J hJ Cstep c hCstep hc N Kf
    energy (fun A A' h => aux_rem_resolved_strata_energy_mono a u h)
    (fun A => aux_rem_resolved_strata_energy_nonneg a u A)
    b (fun k z => aux_lane4_two_mesh_energy_bound_bpos M H omega N k z) B hB hstep U
    (fun n g dep σ => hU.1 ⟨n, (g, (dep, σ)), rfl⟩) V hV x hx r hr

end Paper
