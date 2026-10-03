module

public import SubdiffusiveProcess.Lane4.Carriers
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace Paper

lemma aux_lane4_regularity_mesh_statistic_card_bound (d J : ℕ) :
    ∃ Ccount Cd : ℝ, 1 ≤ Ccount ∧ 0 < Cd ∧
      (∀ n : ℕ,
        (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
          ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ≤
        Ccount * ((n : ℝ) + Ccount) ^ Cd * (3 : ℝ) ^ ((d : ℝ) * n)) ∧
      Cd = (d + 1 : ℕ) := by
  let m : ℕ := d + 1
  let Ccount : ℝ :=
    (2 * (3 : ℝ) ^ J) ^ d * ((J + 1 : ℝ) ^ m) * (Nat.factorial d : ℝ)
  refine ⟨Ccount, (m : ℝ), ?_, by
    dsimp [m]
    exact_mod_cast (Nat.zero_lt_succ d), ?_, by dsimp [m]⟩
  · have h3 : 1 ≤ (3 : ℝ) ^ J := one_le_pow₀ (by norm_num)
    have hbase : 1 ≤ 2 * (3 : ℝ) ^ J := by nlinarith
    have hpow : 1 ≤ (2 * (3 : ℝ) ^ J) ^ d := one_le_pow₀ hbase
    have hJ0 : (0 : ℝ) ≤ (J : ℝ) := by positivity
    have hJ : 1 ≤ (J + 1 : ℝ) := by linarith
    have hJpow : 1 ≤ (J + 1 : ℝ) ^ m := one_le_pow₀ hJ
    have hfac : 1 ≤ (Nat.factorial d : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero d))
    dsimp [Ccount]
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ (2 * (3 : ℝ) ^ J) ^ d * ((J + 1 : ℝ) ^ m) *
          (Nat.factorial d : ℝ) := by gcongr
  · intro n
    let A : ℝ := (3 : ℝ) ^ (n + J) + 1
    let D : ℝ := (n + J + 1 : ℕ)
    have h3nJ : (1 : ℝ) ≤ (3 : ℝ) ^ (n + J) := one_le_pow₀ (by norm_num)
    have hfirst : A ≤ (2 * (3 : ℝ) ^ J) * (3 : ℝ) ^ n := by
      dsimp [A]
      rw [pow_add]
      have hprod : (1 : ℝ) ≤ (3 : ℝ) ^ n * (3 : ℝ) ^ J := by
        have hn : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        have hJ' : (1 : ℝ) ≤ (3 : ℝ) ^ J := one_le_pow₀ (by norm_num)
        nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hJ')]
      nlinarith
    have hfirstpow : A ^ d ≤
        (2 * (3 : ℝ) ^ J) ^ d * (3 : ℝ) ^ (d * n) := by
      calc
        A ^ d ≤ ((2 * (3 : ℝ) ^ J) * (3 : ℝ) ^ n) ^ d := by gcongr
        _ = (2 * (3 : ℝ) ^ J) ^ d * (3 : ℝ) ^ (d * n) := by
          rw [mul_pow, ← pow_mul]
          congr 2
          rw [Nat.mul_comm]
    have hsecond : D ≤ (J + 1 : ℝ) * ((n : ℝ) + Ccount) := by
      have hC : (1 : ℝ) ≤ Ccount := by
        dsimp [Ccount]
        have h3 : 1 ≤ (3 : ℝ) ^ J := one_le_pow₀ (by norm_num)
        have hbase : 1 ≤ 2 * (3 : ℝ) ^ J := by nlinarith
        have hpow : 1 ≤ (2 * (3 : ℝ) ^ J) ^ d := one_le_pow₀ hbase
        have hJ0 : (0 : ℝ) ≤ (J : ℝ) := by positivity
        have hJ : 1 ≤ (J + 1 : ℝ) := by linarith
        have hJpow : 1 ≤ (J + 1 : ℝ) ^ m := one_le_pow₀ hJ
        have hfac : 1 ≤ (Nat.factorial d : ℝ) := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero d))
        calc
          (1 : ℝ) = 1 * 1 * 1 := by ring
          _ ≤ (2 * (3 : ℝ) ^ J) ^ d * ((J + 1 : ℝ) ^ m) *
              (Nat.factorial d : ℝ) := by gcongr
      dsimp [D]
      have hnat' : (n : ℝ) + J + 1 ≤ (J + 1 : ℝ) * ((n : ℝ) + 1) := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        have hJ : (0 : ℝ) ≤ (J : ℝ) := by positivity
        nlinarith [mul_nonneg hn hJ]
      have hC' : (n : ℝ) + 1 ≤ (n : ℝ) + Ccount := by linarith
      calc
        (n + J + 1 : ℕ) = (n : ℝ) + J + 1 := by norm_num
        _ ≤ (J + 1 : ℝ) * ((n : ℝ) + 1) := hnat'
        _ ≤ (J + 1 : ℝ) * ((n : ℝ) + Ccount) :=
          mul_le_mul_of_nonneg_left hC' (by positivity)
    have hsecondpow : D ^ m ≤ (J + 1 : ℝ) ^ m * ((n : ℝ) + Ccount) ^ m := by
      dsimp [D] at hsecond ⊢
      calc
        (n + J + 1 : ℕ) ^ m ≤
            ((J + 1 : ℝ) * ((n : ℝ) + Ccount)) ^ m :=
          pow_le_pow_left₀ (by positivity) hsecond m
        _ = (J + 1 : ℝ) ^ m * ((n : ℝ) + Ccount) ^ m := by rw [mul_pow]
    have hcard :
        (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
          ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) =
          A ^ d * (D ^ m * (Nat.factorial d : ℝ)) := by
      simp [A, D, m, Fintype.card_perm]
    rw [hcard]
    have hpoly_rpow : ((n : ℝ) + Ccount) ^ (m : ℝ) =
        ((n : ℝ) + Ccount) ^ m := Real.rpow_natCast _ m
    rw [hpoly_rpow]
    calc
      A ^ d * (D ^ m * (Nat.factorial d : ℝ)) ≤
          ((2 * (3 : ℝ) ^ J) ^ d * (3 : ℝ) ^ (d * n)) *
            ((J + 1 : ℝ) ^ m * ((n : ℝ) + Ccount) ^ m) *
              (Nat.factorial d : ℝ) := by
        calc
          A ^ d * (D ^ m * (Nat.factorial d : ℝ)) ≤
              ((2 * (3 : ℝ) ^ J) ^ d * (3 : ℝ) ^ (d * n)) *
                (D ^ m * (Nat.factorial d : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hfirstpow (by positivity)
          _ ≤ ((2 * (3 : ℝ) ^ J) ^ d * (3 : ℝ) ^ (d * n)) *
              ((J + 1 : ℝ) ^ m * ((n : ℝ) + Ccount) ^ m *
                (Nat.factorial d : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hsecondpow (by positivity)
          _ = _ := by ring
      _ = Ccount * ((n : ℝ) + Ccount) ^ m *
          (3 : ℝ) ^ ((d : ℝ) * n) := by
        dsimp [Ccount, m]
        have h3 : (3 : ℝ) ^ ((d : ℝ) * (n : ℝ)) = (3 : ℝ) ^ (d * n) := by
          rw [show (d : ℝ) * (n : ℝ) = ((d * n : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
        rw [h3]
        ring

lemma aux_lane4_regularity_mesh_statistic_product_moment {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (d : ℕ) (q K c : ℝ) (hq1 : 1 ≤ q) (hK : 1 ≤ K)
    (B : Fin (d + 1) → Ω → ℝ)
    (hmem : ∀ i, MemLp (fun ω => Real.exp (c * B i ω))
      (ENNReal.ofReal (((d : ℝ) + 1) * q)) P)
    (hnorm : ∀ i, eLpNorm (fun ω => Real.exp (c * B i ω))
      (ENNReal.ofReal (((d : ℝ) + 1) * q)) P ≤ ENNReal.ofReal K) :
    MemLp (fun ω => Real.exp (c * ∑ i : Fin (d + 1), B i ω))
      (ENNReal.ofReal q) P ∧
      eLpNorm (fun ω => Real.exp (c * ∑ i : Fin (d + 1), B i ω))
        (ENNReal.ofReal q) P ≤ ENNReal.ofReal (((d : ℝ) + 1) * K) ^ (d + 1 : ℝ) := by
  let x : Fin (d + 1) → Ω → ℝ := fun i ω => Real.exp (c * B i ω)
  let S : Ω → ℝ := fun ω => ∑ i : Fin (d + 1), x i ω
  let R : ℝ≥0∞ := ENNReal.ofReal (((d : ℝ) + 1) * q)
  have hR1 : (1 : ℝ≥0∞) ≤ R := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hd : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have hq : (0 : ℝ) ≤ q := by linarith
    nlinarith [mul_nonneg hd (sub_nonneg.mpr hq1)]
  have hxm : ∀ i, MemLp (x i) R P := by
    intro i
    simpa [x, R] using! hmem i
  have hnormx : ∀ i, eLpNorm (x i) R P ≤ ENNReal.ofReal K := by
    intro i
    simpa [x, R] using! hnorm i
  have hsum : MemLp S R P := by
    change MemLp (fun ω => ∑ i : Fin (d + 1), x i ω) R P
    exact memLp_finset_sum (p := R) (μ := P)
      (Finset.univ : Finset (Fin (d + 1))) (fun i hi => hxm i)
  have hsum_norm : eLpNorm S R P ≤ ENNReal.ofReal (((d : ℝ) + 1) * K) := by
    calc
      eLpNorm S R P ≤ ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))), eLpNorm (x i) R P := by
        rw [show S = ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))), x i by
          funext ω
          simp [S]]
        exact eLpNorm_sum_le (p := R) (μ := P)
          (f := fun i : Fin (d + 1) => x i) (s := Finset.univ)
          hR1
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))), ENNReal.ofReal K := by
        apply Finset.sum_le_sum
        intro i hi
        exact hnormx i
      _ = ENNReal.ofReal (((d : ℝ) + 1) * K) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        calc
          (d + 1) • ENNReal.ofReal K =
              ((d + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal K := by
            rw [nsmul_eq_mul]
          _ = ENNReal.ofReal (((d + 1 : ℕ) : ℝ) * K) := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (d + 1 : ℕ))]
            simp only [ENNReal.ofReal_natCast]
          _ = ENNReal.ofReal (((d : ℝ) + 1) * K) := by
            congr 2
            norm_num [Nat.cast_add]
  have hS_nonneg : ∀ ω, 0 ≤ S ω := by
    intro ω
    dsimp [S, x]
    exact Finset.sum_nonneg fun i hi => (Real.exp_pos _).le
  let M : ℝ≥0∞ := (d + 1 : ℕ)
  have hpow0 := hsum.norm_rpow_div M
  have hMpos : (0 : ℝ) < (d + 1 : ℝ) := by positivity
  have hdiv : R / M = ENNReal.ofReal q := by
    dsimp [R, M]
    rw [← ENNReal.ofReal_natCast]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1)]
    have hcast : (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) := by norm_num
    rw [hcast]
    rw [mul_comm]
    rw [ENNReal.mul_div_cancel_right]
    · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    · simp
  have hpow : MemLp (fun ω => S ω ^ (d + 1)) (ENNReal.ofReal q) P := by
    rw [← hdiv]
    convert hpow0 using 1
    · funext ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hS_nonneg ω)]
      have hM : M.toReal = (d + 1 : ℝ) := by
        change ((d + 1 : ℕ) : ℝ≥0∞).toReal = _
        rw [ENNReal.toReal_natCast]
        norm_num
      rw [hM]
      have he : (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) := by norm_num
      rw [he]
      rw [Real.rpow_natCast]
  have hpow_norm : eLpNorm (fun ω => S ω ^ (d + 1))
      (ENNReal.ofReal q) P ≤ ENNReal.ofReal (((d : ℝ) + 1) * K) ^ (d + 1 : ℝ) := by
    have hnorm_rpow := eLpNorm_norm_rpow S (m0 := ‹MeasurableSpace Ω›)
      (μ := P) (p := ENNReal.ofReal q) (q := (d + 1 : ℝ)) hsum.aestronglyMeasurable (by exact hMpos)
    have hscale : ENNReal.ofReal q * ENNReal.ofReal (d + 1 : ℝ) = R := by
      calc
        ENNReal.ofReal q * ENNReal.ofReal (d + 1 : ℝ) =
            ENNReal.ofReal (q * (d + 1 : ℝ)) := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ q)]
        _ = ENNReal.ofReal (((d : ℝ) + 1) * q) := by
          congr 1
          ring
        _ = R := by rfl
    have hnorm_rpow' :
        eLpNorm (fun ω => S ω ^ (d + 1 : ℝ)) (ENNReal.ofReal q) P =
          eLpNorm S (ENNReal.ofReal q * ENNReal.ofReal (d + 1 : ℝ)) P ^
            (d + 1 : ℝ) := by
      calc
        eLpNorm (fun ω => S ω ^ (d + 1 : ℝ)) (ENNReal.ofReal q) P =
            eLpNorm (fun ω => ‖S ω‖ ^ (d + 1 : ℝ)) (ENNReal.ofReal q) P := by
          apply eLpNorm_congr_ae
          filter_upwards [] with ω
          rw [Real.norm_eq_abs, abs_of_nonneg (hS_nonneg ω)]
        _ = _ := hnorm_rpow
    have hnat :
        eLpNorm (fun ω => S ω ^ (d + 1)) (ENNReal.ofReal q) P =
          eLpNorm (fun ω => S ω ^ (d + 1 : ℝ)) (ENNReal.ofReal q) P := by
      apply eLpNorm_congr_ae
      filter_upwards [] with ω
      have he : (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) := by norm_num
      rw [he, Real.rpow_natCast]
    calc
      eLpNorm (fun ω => S ω ^ (d + 1)) (ENNReal.ofReal q) P =
          eLpNorm (fun ω => S ω ^ (d + 1 : ℝ)) (ENNReal.ofReal q) P := hnat
      _ = eLpNorm S R P ^ (d + 1 : ℝ) := by rw [hnorm_rpow', hscale]
      _ ≤ ENNReal.ofReal (((d : ℝ) + 1) * K) ^ (d + 1 : ℝ) := by
        gcongr
  have hprod_ae : AEStronglyMeasurable
      (fun ω => ∏ i : Fin (d + 1), x i ω) P := by
    simpa using!
      (Finset.aestronglyMeasurable_fun_prod (μ := P)
        (Finset.univ : Finset (Fin (d + 1))) (fun i hi => (hxm i).aestronglyMeasurable))
  have hprod_le : ∀ ω, (∏ i : Fin (d + 1), x i ω) ≤ (S ω) ^ (d + 1) := by
    intro ω
    have hle : ∀ i : Fin (d + 1), x i ω ≤ S ω := by
      intro i
      change Real.exp (c * B i ω) ≤
        ∑ j : Fin (d + 1), Real.exp (c * B j ω)
      exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin (d + 1))))
        (f := fun j => Real.exp (c * B j ω))
        (fun j hj => (Real.exp_pos (c * B j ω)).le) (Finset.mem_univ i)
    calc
      (∏ i : Fin (d + 1), x i ω) ≤ ∏ i : Fin (d + 1), S ω := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (Real.exp_pos _).le
        · intro i hi
          exact hle i
      _ = (S ω) ^ (d + 1) := by simp
  have hprod_le_norm : ∀ ω,
      ‖∏ i : Fin (d + 1), x i ω‖ ≤ ‖(S ω) ^ (d + 1)‖ := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hprod_le ω
    · exact Finset.prod_nonneg fun i hi => (Real.exp_pos _).le
  have hprod_mem : MemLp (fun ω => ∏ i : Fin (d + 1), x i ω)
      (ENNReal.ofReal q) P :=
    MemLp.of_le hpow hprod_ae
      (Filter.Eventually.of_forall fun ω => hprod_le_norm ω)
  have heq : (fun ω => Real.exp (c * ∑ i : Fin (d + 1), B i ω)) =
      (fun ω => ∏ i : Fin (d + 1), x i ω) := by
    funext ω
    dsimp [x]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  rw [heq]
  exact ⟨hprod_mem,
    (eLpNorm_mono_ae hprod_ae (Filter.Eventually.of_forall fun ω => hprod_le_norm ω)).trans hpow_norm⟩

lemma aux_lane4_regularity_mesh_statistic_summable_cardinality
    (k : ℕ → ℕ) (d b : ℕ) (C q eta : ℝ)
    (hC : 0 ≤ C) (hq : 1 ≤ q) (hgap : (d : ℝ) < q * eta)
    (hcard : ∀ n : ℕ, (k n : ℝ) ≤
      C * ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ ((d : ℝ) * n)) :
    Summable (fun n : ℕ =>
      (3 : ℝ) ^ (-eta * n) * (k n : ℝ) ^ (1 / q)) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hexp_nonneg : 0 ≤ 1 / q := by positivity
  have hexp_le : 1 / q ≤ 1 := by
    rw [div_le_one hqpos]
    exact hq
  let r : ℝ := (3 : ℝ) ^ ((d : ℝ) / q - eta)
  have hrpos : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrexponent : (d : ℝ) / q - eta < 0 := by
    apply sub_neg.mpr
    exact (div_lt_iff₀ hqpos).2 (by simpa [mul_comm] using! hgap)
  have hrlt : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hrexponent
  have hrsum : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ b) * r ^ n) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ b * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one b
        (by simpa [abs_of_pos hrpos] using! hrlt)
    have hshift := (hbase.comp_injective Nat.succ_injective).mul_left r⁻¹
    refine hshift.congr (fun n => ?_)
    simp only [Function.comp_apply, Nat.cast_succ]
    rw [pow_succ]
    field_simp [hrpos.ne']
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_
    (hrsum.mul_left (C ^ (1 / q)))
  intro n
  have hk_nonneg : 0 ≤ (k n : ℝ) := Nat.cast_nonneg _
  have hn_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
  have hn_one : 1 ≤ (n : ℝ) + 1 := by
    linarith only [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hpoly_one : 1 ≤ ((n : ℝ) + 1) ^ b := one_le_pow₀ hn_one
  have hkpow := Real.rpow_le_rpow hk_nonneg (hcard n) hexp_nonneg
  calc
    (3 : ℝ) ^ (-eta * n) * (k n : ℝ) ^ (1 / q)
        ≤ (3 : ℝ) ^ (-eta * n) *
            (C * (((n : ℝ) + 1) ^ b) * (3 : ℝ) ^ ((d : ℝ) * n)) ^ (1 / q) :=
      mul_le_mul_of_nonneg_left hkpow (Real.rpow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ (-eta * n) *
          (C ^ (1 / q) * ((((n : ℝ) + 1) ^ b) ^ (1 / q)) *
            (((3 : ℝ) ^ ((d : ℝ) * n)) ^ (1 / q))) := by
          rw [Real.mul_rpow (mul_nonneg hC (pow_nonneg hn_nonneg _))
            (Real.rpow_nonneg (by norm_num) _),
            Real.mul_rpow hC (pow_nonneg hn_nonneg _)]
    _ ≤ (3 : ℝ) ^ (-eta * n) *
          (C ^ (1 / q) * (((n : ℝ) + 1) ^ b) *
            (((3 : ℝ) ^ ((d : ℝ) * n)) ^ (1 / q))) := by
          gcongr
          exact Real.rpow_le_self_of_one_le hpoly_one hexp_le
    _ = C ^ (1 / q) * (((n : ℝ) + 1) ^ b * r ^ n) := by
          have hgeom : (3 : ℝ) ^ (-eta * n) *
              (((3 : ℝ) ^ ((d : ℝ) * n)) ^ (1 / q)) = r ^ n := by
            dsimp [r]
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
              ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
            congr 1
            field_simp [hqpos.ne']
            ring
          rw [← hgeom]
          ring

lemma aux_lane4_regularity_mesh_statistic_finite_bank
    {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) {q : ℝ≥0∞} (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (F : ι → Ω → ℝ) (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (K : ℝ≥0∞) (hK : ∀ i, eLpNorm (F i) q μ ≤ K) :
    eLpNorm (fun ω => ‖fun i : ι => F i ω‖) q μ ≤
      (Fintype.card ι : ℝ≥0∞) ^ (1 / q.toReal) * K := by
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le hq)
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt (by
    exact (aemeasurable_pi_lambda (fun i => (hF i).aemeasurable)).aestronglyMeasurable.norm)]
  calc
    (∫⁻ ω, ‖‖fun i : ι => F i ω‖‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal)
        ≤ (∫⁻ ω, ∑ i : ι, ‖F i ω‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal) := by
          gcongr with ω
          obtain ⟨i, hi, hsup⟩ :=
            Finset.exists_mem_eq_sup (Finset.univ : Finset ι)
              Finset.univ_nonempty (fun i : ι => ‖F i ω‖₊)
          rw [enorm_eq_nnnorm, Real.nnnorm_of_nonneg (norm_nonneg _)]
          change ((↑(Finset.univ.sup fun i : ι => ‖F i ω‖₊) : ℝ≥0∞) ^ q.toReal) ≤ _
          rw [hsup]
          exact Finset.single_le_sum
            (fun j _ => show (0 : ℝ≥0∞) ≤ ‖F j ω‖ₑ ^ q.toReal from bot_le)
            (Finset.mem_univ i)
    _ = (∑ i : ι, ∫⁻ ω, ‖F i ω‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal) := by
          congr 1
          exact lintegral_finset_sum' Finset.univ fun i hi =>
            (hF i).enorm.pow_const q.toReal
    _ ≤ ((Fintype.card ι : ℝ≥0∞) * K ^ q.toReal) ^ (1 / q.toReal) := by
          apply ENNReal.rpow_le_rpow
          · calc
              ∑ i : ι, ∫⁻ ω, ‖F i ω‖ₑ ^ q.toReal ∂μ
                  = ∑ i : ι, eLpNorm (F i) q μ ^ q.toReal := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt (hF i),
                        ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hqr.ne',
                        ENNReal.rpow_one]
              _ ≤ ∑ _i : ι, K ^ q.toReal := Finset.sum_le_sum fun i hi =>
                    ENNReal.rpow_le_rpow (hK i) hqr.le
              _ = (Fintype.card ι : ℝ≥0∞) * K ^ q.toReal := by simp [mul_comm]
          · exact (one_div_pos.mpr hqr).le
    _ = (Fintype.card ι : ℝ≥0∞) ^ (1 / q.toReal) * K := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hqr).le,
            ← ENNReal.rpow_mul, one_div, mul_inv_cancel₀ hqr.ne', ENNReal.rpow_one]

lemma aux_lane4_regularity_mesh_statistic_countable_dominator
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, MemLp (F n) p μ)
    (hs : Summable (fun n => (eLpNorm (F n) p μ).toReal)) :
    ∃ W : Ω → ℝ, MemLp W p μ ∧
      (∀ᵐ ω ∂μ, 0 ≤ W ω ∧ ∀ n : ℕ, |F n ω| ≤ W ω) ∧
      eLpNorm W p μ ≤ ∑' n : ℕ, eLpNorm (F n) p μ := by
  let W : Ω → ℝ := fun ω => ∑' n, ‖F n ω‖
  have hInt : ∀ n, Integrable (F n) μ := fun n => (hF n).integrable hp
  have hInt_le : ∀ n, ∫ ω, ‖F n ω‖ ∂μ ≤ (eLpNorm (F n) p μ).toReal := by
    intro n
    calc
      ∫ ω, ‖F n ω‖ ∂μ = (eLpNorm (F n) 1 μ).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm (hF n).aestronglyMeasurable, integral_norm_eq_lintegral_enorm (hF n).aestronglyMeasurable]
      _ ≤ (eLpNorm (F n) p μ).toReal := ENNReal.toReal_mono (hF n).ne
        (eLpNorm_le_eLpNorm_of_exponent_le hp)
  have hsInt : Summable (fun n => ∫ ω, ‖F n ω‖ ∂μ) :=
    Summable.of_nonneg_of_le
      (fun n => integral_nonneg (fun ω => norm_nonneg (F n ω))) hInt_le hs
  have hPoint : ∀ᵐ ω ∂μ, Summable (fun n => ‖F n ω‖) := by
    have hmeas : ∀ n, AEMeasurable (fun ω => ‖F n ω‖ₑ) μ :=
      fun n => (hF n).enorm.aestronglyMeasurable.aemeasurable
    have hterm : ∀ n, (∫⁻ ω, ‖F n ω‖ₑ ∂μ) ≤
        ENNReal.ofReal (eLpNorm (F n) p μ).toReal := by
      intro n
      calc
        (∫⁻ ω, ‖F n ω‖ₑ ∂μ) = eLpNorm (F n) 1 μ :=
          (eLpNorm_one_eq_lintegral_enorm (hF n).aestronglyMeasurable).symm
        _ ≤ eLpNorm (F n) p μ :=
          eLpNorm_le_eLpNorm_of_exponent_le hp
        _ = ENNReal.ofReal (eLpNorm (F n) p μ).toReal :=
          (ENNReal.ofReal_toReal (hF n).ne).symm
    have htotal : (∫⁻ ω, ∑' n, ‖F n ω‖ₑ ∂μ) < ∞ := by
      rw [lintegral_tsum hmeas]
      refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => ENNReal.toReal_nonneg) hs]
      exact ENNReal.ofReal_lt_top
    have htop : ∀ᵐ ω ∂μ, (∑' n, ‖F n ω‖ₑ) < ∞ :=
      ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) htotal.ne
    filter_upwards [htop] with ω hω
    have hreal : Summable (fun n => (‖F n ω‖₊ : ℝ)) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
      exact hω.ne
    simpa only [coe_nnnorm] using! hreal

  let S : ℕ → Ω → ℝ := fun n => ∑ i ∈ Finset.range n, fun ω => ‖F i ω‖
  have hBound : ∀ n, eLpNorm (S n) p μ ≤
      ∑' i, eLpNorm (F i) p μ := by
    intro n
    calc
      eLpNorm (S n) p μ ≤
          ∑ i ∈ Finset.range n, eLpNorm (fun ω => ‖F i ω‖) p μ :=
        eLpNorm_sum_le hp
      _ = ∑ i ∈ Finset.range n, eLpNorm (F i) p μ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact eLpNorm_norm (p := p) (F i) (hF i).aestronglyMeasurable
      _ ≤ ∑' i, eLpNorm (F i) p μ := ENNReal.sum_le_tsum _
  have hTendsto : ∀ᵐ ω ∂μ,
      Tendsto (fun n => S n ω) atTop (𝓝 (W ω)) := by
    filter_upwards [hPoint] with ω hω
    simpa only [S, Finset.sum_apply] using! hω.hasSum.tendsto_sum_nat
  have hWmeas : AEStronglyMeasurable W μ := aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (memLp_finset_sum' (Finset.range n) fun i hi => (hF i).norm).aestronglyMeasurable) hTendsto
  have hWnorm : eLpNorm W p μ ≤ ∑' i, eLpNorm (F i) p μ :=
    Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hBound)
      (fun n => (memLp_finset_sum' (Finset.range n) fun i hi => (hF i).norm).aestronglyMeasurable) hWmeas hTendsto
  have hsum_norms : (∑' i, eLpNorm (F i) p μ) ≠ ∞ := by
    have heq : (fun i => eLpNorm (F i) p μ) =
        fun i => ENNReal.ofReal (eLpNorm (F i) p μ).toReal := by
      funext n
      exact (ENNReal.ofReal_toReal (hF n).ne).symm
    rw [heq, ← ENNReal.ofReal_tsum_of_nonneg (fun n => ENNReal.toReal_nonneg) hs]
    exact ENNReal.ofReal_ne_top
  have hW : MemLp W p μ := hWnorm.trans_lt (lt_top_iff_ne_top.2 hsum_norms)
  refine ⟨W, hW, ?_, hWnorm⟩
  filter_upwards [hPoint] with ω hω
  constructor
  · exact tsum_nonneg fun n => norm_nonneg _
  · intro n
    simpa only [Real.norm_eq_abs] using! hω.le_tsum n
      (fun j hj => norm_nonneg (F j ω))

lemma aux_lane4_regularity_mesh_statistic_envelope
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ι : ℕ → Type} [∀ n, Fintype (ι n)]
    (hinhab : ∀ n, Nonempty (ι n)) (d b : ℕ) (C eta : ℝ) (hC : 0 ≤ C)
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) (hqt : q ≠ ∞)
    (hgap : (d : ℝ) < q.toReal * eta)
    (hcard : ∀ n : ℕ, (Fintype.card (ι n) : ℝ) ≤
      C * ((n : ℝ) + 1) ^ b * (3 : ℝ) ^ ((d : ℝ) * n))
    (Z : ∀ n, ι n → Ω → ℝ)
    (hZ : ∀ n i, AEStronglyMeasurable (Z n i) μ)
    (K : ℝ≥0∞) (hKt : K ≠ ∞)
    (hK : ∀ n i, eLpNorm (Z n i) q μ ≤ K) :
    ∃ W : Ω → ℝ, MemLp W p μ ∧
      (∀ᵐ ω ∂μ, 0 ≤ W ω ∧ ∀ n i, |Z n i ω| ≤
        W ω * (3 : ℝ) ^ (eta * n)) ∧
      eLpNorm W p μ ≤
        (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * n)) *
          (Fintype.card (ι n) : ℝ≥0∞) ^ (1 / q.toReal)) * K := by
  classical
  have hp_t : p ≠ ∞ := fun h => hqt (top_unique (h ▸ hpq))
  have hq1 : 1 ≤ q.toReal := by
    rw [← ENNReal.toReal_one, ENNReal.toReal_le_toReal (by simp) hqt]
    exact hp.trans hpq
  have hsum_real : Summable (fun n : ℕ =>
      (3 : ℝ) ^ (-eta * n) * (Fintype.card (ι n) : ℝ) ^ (1 / q.toReal)) :=
    aux_lane4_regularity_mesh_statistic_summable_cardinality
      (fun n => Fintype.card (ι n)) d b C q.toReal eta hC hq1 hgap hcard
  let B : ℕ → Ω → ℝ := fun n ω => ‖fun i : ι n => Z n i ω‖
  let F : ℕ → Ω → ℝ := fun n ω => (3 : ℝ) ^ (-eta * n) * B n ω
  have hBmeas : ∀ n, AEStronglyMeasurable (B n) μ := by
    intro n
    have hv : AEStronglyMeasurable (fun ω => fun i : ι n => Z n i ω) μ := by
      have heq : (fun ω => fun i : ι n => Z n i ω) =
          fun ω => ∑ i : ι n, (Z n i ω) •
            (Pi.single i (1 : ℝ) : ι n → ℝ) := by
        funext ω
        exact pi_eq_sum_univ' (fun i : ι n => Z n i ω)
      rw [heq]
      apply Finset.aestronglyMeasurable_fun_sum Finset.univ
      intro i _
      have hc : AEStronglyMeasurable
          (fun _ : Ω => (Pi.single i (1 : ℝ) : ι n → ℝ)) μ :=
        stronglyMeasurable_const.aestronglyMeasurable
      exact (hZ n i).smul hc
    exact hv.norm
  have hBq : ∀ n, eLpNorm (B n) q μ ≤
      (Fintype.card (ι n) : ℝ≥0∞) ^ (1 / q.toReal) * K := by
    intro n
    letI : Nonempty (ι n) := hinhab n
    exact aux_lane4_regularity_mesh_statistic_finite_bank μ
      (hp.trans hpq) hqt (Z n) (hZ n) K (hK n)
  have hBmemq : ∀ n, MemLp (B n) q μ := by
    intro n
    refine (hBq n).trans_lt ?_
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by finiteness))
      (lt_top_iff_ne_top.2 hKt)
  have hFmem : ∀ n, MemLp (F n) p μ := by
    intro n
    exact ((hBmemq n).mono_exponent hpq).const_mul ((3 : ℝ) ^ (-eta * n))
  have hFnorm : ∀ n, eLpNorm (F n) p μ ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-eta * n)) *
        ((Fintype.card (ι n) : ℝ≥0∞) ^ (1 / q.toReal) * K) := by
    intro n
    rw [show F n = ((3 : ℝ) ^ (-eta * n)) • B n by funext ω; simp [F]]
    rw [eLpNorm_const_smul]
    rw [Real.enorm_of_nonneg (Real.rpow_nonneg (by norm_num) _)]
    exact mul_le_mul_of_nonneg_left ((eLpNorm_le_eLpNorm_of_exponent_le hpq).trans
      (hBq n)) (by positivity)
  have hsum_norm : Summable (fun n => (eLpNorm (F n) p μ).toReal) := by
    have hmajor : ∀ n, (eLpNorm (F n) p μ).toReal ≤
        ((3 : ℝ) ^ (-eta * n) * (Fintype.card (ι n) : ℝ) ^
          (1 / q.toReal)) * K.toReal := by
      intro n
      calc
        (eLpNorm (F n) p μ).toReal ≤
            (ENNReal.ofReal ((3 : ℝ) ^ (-eta * n)) *
              ((Fintype.card (ι n) : ℝ≥0∞) ^ (1 / q.toReal) * K)).toReal :=
          (ENNReal.toReal_le_toReal (hFmem n).ne
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (ENNReal.mul_ne_top
                (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by finiteness)) hKt))).2
            (hFnorm n)
        _ = ((3 : ℝ) ^ (-eta * n) * (Fintype.card (ι n) : ℝ) ^
              (1 / q.toReal)) * K.toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num) _)]
          have hk : ((Fintype.card (ι n) : ℝ≥0∞) ^ (1 / q.toReal)).toReal =
              (Fintype.card (ι n) : ℝ) ^ (1 / q.toReal) := by
            rw [← ENNReal.toReal_rpow]
            norm_cast
          rw [hk]
          ring
    exact Summable.of_nonneg_of_le (fun n => ENNReal.toReal_nonneg) hmajor
      (hsum_real.mul_right K.toReal)
  obtain ⟨W, hW, hdom, hWnorm⟩ :=
    aux_lane4_regularity_mesh_statistic_countable_dominator μ hp hp_t F hFmem hsum_norm
  refine ⟨W, hW, ?_, ?_⟩
  · filter_upwards [hdom] with ω hω
    refine ⟨hω.1, fun n i => ?_⟩
    have hi : |Z n i ω| ≤ B n ω := by
      change |Z n i ω| ≤ ‖fun j : ι n => Z n j ω‖
      rw [Pi.norm_def]
      change ‖Z n i ω‖ ≤ ↑(Finset.univ.sup fun b : ι n => ‖Z n b ω‖₊)
      exact_mod_cast Finset.le_sup (f := fun j : ι n => ‖Z n j ω‖₊)
        (Finset.mem_univ i)
    have ha : 0 < (3 : ℝ) ^ (-eta * n) := Real.rpow_pos_of_pos (by norm_num) _
    apply (mul_le_mul_iff_of_pos_left ha).1
    calc
      (3 : ℝ) ^ (-eta * n) * |Z n i ω| ≤ F n ω := by
        simpa [F] using! mul_le_mul_of_nonneg_left hi ha.le
      _ ≤ W ω := (le_abs_self (F n ω)).trans (hω.2 n)
      _ = (3 : ℝ) ^ (-eta * n) * (W ω * (3 : ℝ) ^ (eta * n)) := by
        calc
          W ω = W ω * ((3 : ℝ) ^ (-eta * n) * (3 : ℝ) ^ (eta * n)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
            simp
          _ = (3 : ℝ) ^ (-eta * n) * (W ω * (3 : ℝ) ^ (eta * n)) := by ring
  · calc
      eLpNorm W p μ ≤ ∑' n : ℕ, eLpNorm (F n) p μ := hWnorm
      _ ≤ ∑' n : ℕ, (ENNReal.ofReal ((3 : ℝ) ^ (-eta * n)) *
          (Fintype.card (ι n) : ℝ≥0∞) ^ (1 / q.toReal)) * K :=
        ENNReal.tsum_le_tsum fun n => by simpa [mul_assoc] using! hFnorm n
      _ = (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * n)) *
          (Fintype.card (ι n) : ℝ≥0∞) ^ (1 / q.toReal)) * K := ENNReal.tsum_mul_right



theorem lane4_regularity_mesh_statistic (d J : ℕ) (hJ : 1 ≤ J) :
    let Cat : ℕ → Type := fun n =>
      (Fin d → Fin (3 ^ (n + J) + 1)) ×
        ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))
    ∃ Ccount Cd : ℝ, 1 ≤ Ccount ∧ 0 < Cd ∧
      (∀ n : ℕ, (Nat.card (Cat n) : ℝ) ≤
        Ccount * ((n : ℝ) + Ccount) ^ Cd * (3 : ℝ) ^ ((d : ℝ) * n)) ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
        ∀ p q eta : ℝ, 1 ≤ p → p ≤ q → 0 < eta → (d : ℝ) < q * eta →
        ∀ Cstep c K : ℝ, 1 ≤ Cstep → 0 ≤ c → 1 ≤ K →
        ∀ B : (N : ℕ) → (n : ℕ) → Cat n → Fin (d + 1) → Ω → ℝ,
          (∀ N n pi i ω, 0 ≤ B N n pi i ω) →
          (∀ N n pi i, MemLp (fun ω => Real.exp (c * B N n pi i ω))
            (ENNReal.ofReal (((d : ℝ) + 1) * q)) P) →
          (∀ N n pi i, eLpNorm (fun ω => Real.exp (c * B N n pi i ω))
            (ENNReal.ofReal (((d : ℝ) + 1) * q)) P ≤ ENNReal.ofReal K) →
          let Z := fun N n (pi : Cat n) ω =>
            Cstep ^ (d + 1) * Real.exp (c * ∑ i : Fin (d + 1), B N n pi i ω)
          ∃ (U : ℕ → Ω → ℝ) (Cp : ℝ), 0 ≤ Cp ∧
            (∀ N, Measurable (U N)) ∧
            (∀ N ω, 0 ≤ U N ω) ∧
            (∀ N, MemLp (U N) (ENNReal.ofReal p) P) ∧
            (∀ N, eLpNorm (U N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
            (∀ᵐ ω ∂P, ∀ N,
              IsLUB {v : ℝ | ∃ n : ℕ, ∃ pi : Cat n,
                v = (3 : ℝ) ^ (-eta * (n : ℝ)) * Z N n pi ω} (U N ω))) := by
  dsimp
  obtain ⟨Ccount, Cd, hCcount, hCd, hcard, hCdEq⟩ :=
    aux_lane4_regularity_mesh_statistic_card_bound d J
  refine ⟨Ccount, Cd, hCcount, hCd, ?_, ?_⟩
  · exact hcard
  · intro Ω _ P _ p q eta hp hpq heta hgap Cstep c K hCstep hc hK B
      hBnonneg hBmem hBnorm
    have hp0 : 0 ≤ p := by linarith
    have hq0 : 0 ≤ q := by linarith
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (hp.trans hpq)
    have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hpqE : ENNReal.ofReal p ≤ ENNReal.ofReal q :=
      ENNReal.ofReal_le_ofReal hpq
    have hqtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
    have hqgap : (d : ℝ) < (ENNReal.ofReal q).toReal * eta := by
      simpa [ENNReal.toReal_ofReal hq0] using! hgap
    let Cenv : ℝ := Ccount * (Ccount + 1) ^ (d + 1 : ℕ)
    have hCenv : 0 ≤ Cenv := by
      dsimp [Cenv]
      positivity
    have hcard_env : ∀ n : ℕ, (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
          ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ≤
        Cenv * ((n : ℝ) + 1) ^ (d + 1 : ℕ) *
          (3 : ℝ) ^ ((d : ℝ) * n) := by
      intro n
      calc
        _ ≤ Ccount * ((n : ℝ) + Ccount) ^ Cd *
            (3 : ℝ) ^ ((d : ℝ) * n) := hcard n
        _ ≤ Cenv * ((n : ℝ) + 1) ^ (d + 1 : ℕ) *
            (3 : ℝ) ^ ((d : ℝ) * n) := by
          have hn : (n : ℝ) + Ccount ≤ (Ccount + 1) * ((n : ℝ) + 1) := by
            nlinarith [hCcount]
          have hCd' : ((n : ℝ) + Ccount) ^ Cd =
              ((n : ℝ) + Ccount) ^ (d + 1 : ℕ) := by
            rw [hCdEq]
            exact Real.rpow_natCast _ _
          rw [hCd']
          have hpow := pow_le_pow_left₀ (by positivity) hn (d + 1)
          calc
            Ccount * ((n : ℝ) + Ccount) ^ (d + 1 : ℕ) *
                (3 : ℝ) ^ ((d : ℝ) * n) ≤
                Ccount * ((Ccount + 1) * ((n : ℝ) + 1)) ^ (d + 1 : ℕ) *
                  (3 : ℝ) ^ ((d : ℝ) * n) := by
                    gcongr
            _ = Cenv * ((n : ℝ) + 1) ^ (d + 1 : ℕ) *
                (3 : ℝ) ^ ((d : ℝ) * n) := by
                  dsimp [Cenv]
                  rw [mul_pow]
                  ring
    have hinhab : ∀ n : ℕ,
        Nonempty ((Fin d → Fin (3 ^ (n + J) + 1)) ×
          ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) := by
      intro n
      have hgrid : 0 < 3 ^ (n + J) + 1 := by positivity
      have hroot : 0 < n + J + 1 := by positivity
      exact ⟨(fun _ => ⟨0, hgrid⟩,
        (fun _ => ⟨0, hroot⟩, Equiv.refl _))⟩
    let KZ : ℝ≥0∞ := ENNReal.ofReal (Cstep ^ (d + 1)) *
      ENNReal.ofReal (((d : ℝ) + 1) * K) ^ (d + 1 : ℝ)
    have hKZtop : KZ ≠ ∞ := by
      dsimp [KZ]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by finiteness))
    have hZmem : ∀ N n pi, MemLp
        (fun ω => Cstep ^ (d + 1) * Real.exp (c *
          ∑ i : Fin (d + 1), B N n pi i ω)) (ENNReal.ofReal q) P := by
      intro N n pi
      have hprod := aux_lane4_regularity_mesh_statistic_product_moment P d q K c
        (by linarith) hK (fun i ω => B N n pi i ω)
        (fun i => by simpa using! hBmem N n pi i)
        (fun i => by simpa using! hBnorm N n pi i)
      exact hprod.1.const_mul (Cstep ^ (d + 1))
    have henv : ∀ N : ℕ, ∃ W : Ω → ℝ, MemLp W (ENNReal.ofReal p) P ∧
        (∀ᵐ ω ∂P, 0 ≤ W ω ∧ ∀ n pi,
          |(Cstep ^ (d + 1) * Real.exp (c *
            ∑ i : Fin (d + 1), B N n pi i ω))| ≤
            W ω * (3 : ℝ) ^ (eta * n)) ∧
        eLpNorm W (ENNReal.ofReal p) P ≤
          (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * n)) *
          (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
              ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
                (1 / (ENNReal.ofReal q).toReal)) * KZ := by
      intro N
      have hZae : ∀ n pi, AEStronglyMeasurable
          (fun ω => Cstep ^ (d + 1) * Real.exp (c *
            ∑ i : Fin (d + 1), B N n pi i ω)) P := by
        intro n pi
        exact (hZmem N n pi).aestronglyMeasurable
      have hZnorm : ∀ n pi, eLpNorm
          (fun ω => Cstep ^ (d + 1) * Real.exp (c *
            ∑ i : Fin (d + 1), B N n pi i ω)) (ENNReal.ofReal q) P ≤ KZ := by
        intro n pi
        dsimp [KZ]
        rw [show (fun ω => Cstep ^ (d + 1) *
          Real.exp (c * ∑ i : Fin (d + 1), B N n pi i ω)) =
            (Cstep ^ (d + 1)) •
              (fun ω => Real.exp (c * ∑ i : Fin (d + 1), B N n pi i ω)) by
          funext ω; simp [smul_eq_mul]]
        rw [eLpNorm_const_smul]
        rw [Real.enorm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (aux_lane4_regularity_mesh_statistic_product_moment P d q K c
          (by linarith) hK (fun i ω => B N n pi i ω)
          (fun i => by simpa using! hBmem N n pi i)
          (fun i => by simpa using! hBnorm N n pi i)).2 (by positivity)
      have hgen := aux_lane4_regularity_mesh_statistic_envelope P
        (ι := fun n => (Fin d → Fin (3 ^ (n + J) + 1)) ×
          ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d)))
        hinhab d (d + 1) Cenv eta hCenv hpE hpqE hqtop hqgap
        (by simpa only [Nat.card_eq_fintype_card] using! hcard_env)
        (fun n pi ω => Cstep ^ (d + 1) * Real.exp (c *
          ∑ i : Fin (d + 1), B N n pi i ω))
        hZae KZ hKZtop hZnorm
      simpa only [Nat.card_eq_fintype_card] using! hgen
    choose W hW hWdom hWbound using henv
    let I : Type := Σ n : ℕ,
      (Fin d → Fin (3 ^ (n + J) + 1)) ×
        ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))
    let f : ℕ → I → Ω → ℝ := fun N z ω =>
      (3 : ℝ) ^ (-(eta * (z.1 : ℝ))) *
        (Cstep ^ (d + 1) * Real.exp (c *
          ∑ i : Fin (d + 1), B N z.1 z.2 i ω))
    have hfmem : ∀ N z, MemLp (f N z) (ENNReal.ofReal p) P := by
      intro N z
      rcases z with ⟨n, pi⟩
      dsimp [f]
      exact (hZmem N n pi).mono_exponent hpqE |>.const_mul
        ((3 : ℝ) ^ (-(eta * (n : ℝ))))
    have hfmeas : ∀ N z, AEMeasurable (f N z) P := by
      intro N z
      exact (hfmem N z).aestronglyMeasurable.aemeasurable
    let V : ℕ → Ω → ℝ := fun N ω => ⨆ z : I, f N z ω
    have hVae : ∀ N, AEMeasurable (V N) P := by
      intro N
      apply AEMeasurable.iSup (hfmeas N)
    let U : ℕ → Ω → ℝ := fun N ω =>
      max 0 ((hVae N).mk (V N) ω)
    let Rbound : ℝ≥0∞ :=
      (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ))) *
        (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
          ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
            (1 / (ENNReal.ofReal q).toReal)) * KZ
    let Cp : ℝ := Rbound.toReal
    let z0 : I := ⟨0, Classical.choice (hinhab 0)⟩
    letI : Nonempty I := ⟨z0⟩
    have hf_nonneg : ∀ N z ω, 0 ≤ f N z ω := by
      intro N z ω
      dsimp [f]
      positivity
    have hVmk : ∀ᵐ ω ∂P, ∀ N, (hVae N).mk (V N) ω = V N ω := by
      rw [ae_all_iff]
      intro N
      exact (hVae N).ae_eq_mk.symm
    have hWdom_all : ∀ᵐ ω ∂P, ∀ N n pi,
        |Cstep ^ (d + 1) * Real.exp (c *
          ∑ i : Fin (d + 1), B N n pi i ω)| ≤
          W N ω * (3 : ℝ) ^ (eta * n) := by
      rw [ae_all_iff]
      intro N
      exact (hWdom N).mono (fun ω hω n pi => hω.2 n pi)
    have hWnonneg_all : ∀ᵐ ω ∂P, ∀ N, 0 ≤ W N ω := by
      rw [ae_all_iff]
      intro N
      exact (hWdom N).mono (fun ω hω => hω.1)
    have hupper : ∀ᵐ ω ∂P, ∀ N z, f N z ω ≤ W N ω := by
      filter_upwards [hWdom_all] with ω hω N z
      rcases z with ⟨n, pi⟩
      have hz := hω N n pi
      have ha : 0 < (3 : ℝ) ^ (-(eta * (n : ℝ))) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hznonneg : 0 ≤ Cstep ^ (d + 1) * Real.exp
          (c * ∑ i : Fin (d + 1), B N n pi i ω) := by positivity
      calc
        f N ⟨n, pi⟩ ω = (3 : ℝ) ^ (-(eta * (n : ℝ))) *
            |Cstep ^ (d + 1) * Real.exp (c *
              ∑ i : Fin (d + 1), B N n pi i ω)| := by
                simp [f, abs_of_nonneg hznonneg]
        _ ≤ (3 : ℝ) ^ (-(eta * (n : ℝ))) *
            (W N ω * (3 : ℝ) ^ (eta * (n : ℝ))) :=
              mul_le_mul_of_nonneg_left hz ha.le
        _ = W N ω := by
          calc
            (3 : ℝ) ^ (-(eta * (n : ℝ))) *
                (W N ω * (3 : ℝ) ^ (eta * (n : ℝ))) =
              W N ω * ((3 : ℝ) ^ (-(eta * (n : ℝ))) *
                (3 : ℝ) ^ (eta * (n : ℝ))) := by ring
            _ = W N ω := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
              simp
    have hVupper : ∀ᵐ ω ∂P, ∀ N, V N ω ≤ W N ω := by
      filter_upwards [hupper] with ω hω N
      exact ciSup_le (fun z => hω N z)
    have hV_nonneg_ae : ∀ᵐ ω ∂P, ∀ N, 0 ≤ V N ω := by
      filter_upwards [hupper] with ω hω N
      have hBdd : BddAbove (Set.range (fun z : I => f N z ω)) := by
        refine ⟨W N ω, ?_⟩
        rintro _ ⟨z, rfl⟩
        exact hω N z
      exact (hf_nonneg N z0 ω).trans (le_ciSup hBdd z0)
    have hUeq : ∀ᵐ ω ∂P, ∀ N, U N ω = V N ω := by
      filter_upwards [hVmk, hV_nonneg_ae] with ω hω hnonneg N
      dsimp [U]
      rw [hω N]
      exact max_eq_right (hnonneg N)
    have hUdom : ∀ᵐ ω ∂P, ∀ N, ‖U N ω‖ ≤ ‖W N ω‖ := by
      filter_upwards [hUeq, hVupper, hWnonneg_all, hV_nonneg_ae] with
        ω hEq hVup hWnonneg hVnonneg N
      rw [hEq N]
      rw [Real.norm_eq_abs, abs_of_nonneg (hVnonneg N)]
      rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg N)]
      exact hVup N
    have hrealR : Summable (fun n : ℕ =>
        (3 : ℝ) ^ (-eta * (n : ℝ)) *
          (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
            ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ^
            (1 / q)) :=
      aux_lane4_regularity_mesh_statistic_summable_cardinality
        (fun n => Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
          ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))))
        d (d + 1) Cenv q eta hCenv (by linarith) hgap hcard_env
    have hRbound : Rbound ≠ ∞ := by
      have hterm : ∀ n : ℕ,
          ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ))) *
              (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
                ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
                (1 / (ENNReal.ofReal q).toReal) =
            ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ)) *
              (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
                ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ^
                (1 / q)) := by
        intro n
        have hpowtop :
            (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
              ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
                (1 / (ENNReal.ofReal q).toReal) ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg (by positivity) (by finiteness)
        have hpowreal :
            ((Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
              ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
                (1 / (ENNReal.ofReal q).toReal)).toReal =
              (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
                ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ^ (1 / q) := by
          rw [← ENNReal.toReal_rpow]
          norm_cast
          simp [ENNReal.toReal_ofReal hq0]
        rw [← ENNReal.ofReal_toReal hpowtop, hpowreal]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      dsimp [Rbound]
      rw [show (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ))) *
          (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
            ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
              (1 / (ENNReal.ofReal q).toReal)) =
          ∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ)) *
            (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
              ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ^
                (1 / q)) by
            apply tsum_congr
            exact hterm]
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hrealR]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKZtop
    refine ⟨U, Cp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [Cp]
      exact ENNReal.toReal_nonneg
    · intro N
      dsimp [U]
      exact Measurable.max measurable_const (hVae N).measurable_mk
    · intro N ω
      dsimp [U]
      exact le_max_left _ _
    · intro N
      apply MemLp.of_le (hW N)
        ((Measurable.max measurable_const (hVae N).measurable_mk).aestronglyMeasurable)
      exact hUdom.mono (fun ω hω => hω N)
    · intro N
      calc
        eLpNorm (U N) (ENNReal.ofReal p) P ≤
            eLpNorm (W N) (ENNReal.ofReal p) P :=
          eLpNorm_mono_ae ((Measurable.max measurable_const (hVae N).measurable_mk).aestronglyMeasurable) (hUdom.mono (fun ω hω => hω N))
        _ ≤ Rbound := hWbound N
        _ = ENNReal.ofReal Cp := by
          dsimp [Cp]
          exact (ENNReal.ofReal_toReal hRbound).symm
    · filter_upwards [hUeq, hVupper, hupper] with ω hEq hVup hpoint N
      have hBdd : BddAbove (Set.range (fun z : I => f N z ω)) := by
        refine ⟨W N ω, ?_⟩
        rintro _ ⟨z, rfl⟩
        exact hpoint N z
      have hL : IsLUB (Set.range (fun z : I => f N z ω)) (V N ω) :=
        isLUB_ciSup hBdd
      have hset :
          {v : ℝ | ∃ n : ℕ, ∃ pi,
            v = (3 : ℝ) ^ (-eta * (n : ℝ)) *
              (Cstep ^ (d + 1) * Real.exp (c *
                ∑ i : Fin (d + 1), B N n pi i ω))} =
            Set.range (fun z : I => f N z ω) := by
        ext v
        constructor
        · rintro ⟨n, pi, rfl⟩
          refine ⟨⟨n, pi⟩, ?_⟩
          dsimp [f]
          ring
        · rintro ⟨z, rfl⟩
          rcases z with ⟨n, pi⟩
          refine ⟨n, pi, ?_⟩
          dsimp [f]
          ring
      rw [hset, hEq N]
      simpa [V] using! hL

end Paper
