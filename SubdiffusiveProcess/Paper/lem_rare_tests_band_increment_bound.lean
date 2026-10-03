module

public import SubdiffusiveProcess.Lane3.BandFiltration
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

namespace Paper

lemma aux_lem_rare_tests_band_increment_bound_markov
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 1 ≤ p) (f g : α → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (ε : ℝ) (hε : 0 < ε) :
    μ {x | ε ≤ f x - g x} ≤
      (ENNReal.ofReal ε)⁻¹ ^ p *
        (eLpNorm f (ENNReal.ofReal p) μ + eLpNorm g (ENNReal.ofReal p) μ) ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by positivity
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hε0 : ENNReal.ofReal ε ≠ 0 := by positivity
  have hεtop : ENNReal.ofReal ε ≠ ∞ := ENNReal.ofReal_ne_top
  have hsub : {x | ε ≤ f x - g x} ⊆
      {x | ENNReal.ofReal ε ≤ ‖(f - g) x‖ₑ} := by
    intro x hx
    change ε ≤ f x - g x at hx
    change ENNReal.ofReal ε ≤ ‖f x - g x‖ₑ
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hx.trans (le_abs_self _))
  have hmark :=
    meas_ge_le_mul_pow_eLpNorm_enorm μ (f := f - g) hp0 hptop
      hε0 (fun h => (hεtop h).elim)
  calc
    μ {x | ε ≤ f x - g x} ≤ μ {x | ENNReal.ofReal ε ≤ ‖(f - g) x‖ₑ} :=
      measure_mono hsub
    _ ≤ (ENNReal.ofReal ε)⁻¹ ^ (ENNReal.ofReal p).toReal *
          eLpNorm (f - g) (ENNReal.ofReal p) μ ^ (ENNReal.ofReal p).toReal := hmark
    _ ≤ (ENNReal.ofReal ε)⁻¹ ^ p *
          (eLpNorm f (ENNReal.ofReal p) μ + eLpNorm g (ENNReal.ofReal p) μ) ^ p := by
      have hp_nonneg : 0 ≤ p := by linarith
      rw [ENNReal.toReal_ofReal hp_nonneg]
      gcongr
      exact eLpNorm_sub_le (by simpa using ENNReal.ofReal_le_ofReal hp)

lemma aux_lem_rare_tests_band_increment_bound_linear
    (p L B a r O : ℝ) (hp : 0 ≤ p) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hhalf : 2 * O ≤ a * r * (p * L))
    (hmargin : 4 * B ≤ a * p * L) :
    O - a * r * (p * L) ≤ -(B * (2 * r)) := by
  have hbscale : 4 * B * r ≤ a * p * L * r := by
    exact mul_le_mul_of_nonneg_right hmargin hr
  have hO : O ≤ (a * r * (p * L)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hhalf
  have hBr : 2 * B * r ≤ (a * r * (p * L)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    convert hbscale using 1 <;> ring
  linarith

lemma aux_lem_rare_tests_band_increment_bound_expand
    (p x y z L : ℝ) :
    p * ((x + y - z) * L) = p * ((x + y) * L) - z * (p * L) := by
  rw [sub_mul, mul_sub]
  congr 1
  ac_rfl

lemma aux_lem_rare_tests_band_increment_bound_linear_exp
    (p L B a r x : ℝ) (hp : 0 ≤ p) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hhalf : 2 * (p * (x * L)) ≤ a * r * (p * L))
    (hmargin : 4 * B ≤ a * p * L) :
    p * ((x - a * r) * L) ≤ -(B * (2 * r)) := by
  have hsimple : p * (x * L) - a * r * (p * L) ≤ -(B * (2 * r)) :=
    aux_lem_rare_tests_band_increment_bound_linear p L B a r (p * (x * L))
      hp hL hr hhalf hmargin
  calc
    p * ((x - a * r) * L) = p * (x * L) - a * r * (p * L) := by
      rw [sub_mul, mul_sub]
      congr 1
      ac_rfl
    _ ≤ _ := hsimple

lemma aux_lem_rare_tests_band_increment_bound_pow_three (n : ℕ) :
    (n : ℝ) ≤ (3 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ (3 : ℝ) ^ n :=
        one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num)
      norm_num at *
      nlinarith

lemma aux_lem_rare_tests_band_increment_bound_dyadic_linear (k : ℕ) :
    (k : ℝ) + 4 ≤ 4 * (2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have hone : 1 ≤ (2 : ℝ) ^ k :=
        one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)
      norm_num at *
      nlinarith

lemma aux_lem_rare_tests_band_increment_bound_absorption_inner
    (Cstar a p B : ℝ) (N Hinc : ℕ) (hCstar : 0 < Cstar) (ha : 0 < a)
    (hp : 1 ≤ p) (hCpow : 2 * Cstar ≤ (3 : ℝ) ^ N)
    (hHinc : 2 * ((N : ℝ) + 4) / a < Hinc)
    (hmargin4 : 4 * B < a * p * Real.log 3) :
    ∀ H0 : ℕ, Hinc ≤ H0 →
      ∀ ell : ℕ, 1 ≤ ell →
        (((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ ^ p) *
            (2 * Cstar *
              (3 : ℝ) ^
                (-(a * ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)))) ^ p ≤
          Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  intro H0 hH0 ell hell
  let q : ℝ := ((2 ^ (ell - 1) : ℕ) : ℝ)
  let r : ℝ := ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hq_one : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (one_le_pow₀ (show 1 ≤ (2 : ℕ) by norm_num))
  have hell_sub : (ell : ℝ) + 3 = ((ell - 1 : ℕ) : ℝ) + 4 := by
    have hnat : ell = (ell - 1) + 1 := by omega
    rw [hnat]
    push_cast
    ring
  have hover : (ell : ℝ) + 3 + N ≤ ((N : ℝ) + 4) * q := by
    have hindex : (ell : ℝ) + 3 ≤ 4 * q := by
      rw [hell_sub]
      simpa [q] using aux_lem_rare_tests_band_increment_bound_dyadic_linear (ell - 1)
    have hNq : (N : ℝ) ≤ (N : ℝ) * q := by
      have := mul_le_mul_of_nonneg_left hq_one (Nat.cast_nonneg N)
      simpa [mul_comm] using this
    dsimp [q] at hindex hNq ⊢
    nlinarith
  have hell_step : ell = (ell - 1) + 1 := by omega
  have hdouble : ((2 ^ ell * H0 : ℕ) : ℝ) = 2 * r := by
    have hpow : 2 ^ ell = 2 * 2 ^ (ell - 1) := by
      rw [hell_step, pow_succ]
      exact Nat.mul_comm _ _
    dsimp [r]
    rw [hpow]
    push_cast
    ring
  have hH0real : (Hinc : ℝ) ≤ H0 := by exact_mod_cast hH0
  have hKlt : 2 * ((N : ℝ) + 4) / a < (H0 : ℝ) :=
    hHinc.trans_le hH0real
  have hKmul : 2 * ((N : ℝ) + 4) < (H0 : ℝ) * a :=
    (div_lt_iff₀ ha).mp hKlt
  have hKle : 2 * ((N : ℝ) + 4) ≤ a * (H0 : ℝ) := by
    nlinarith
  have hscale : 2 * ((N : ℝ) + 4) * q ≤ a * r := by
    have hmul := mul_le_mul_of_nonneg_right hKle hq_pos.le
    dsimp [q, r] at hmul ⊢
    push_cast at hmul ⊢
    convert hmul using 1 <;> ring
  have heps_inv :
      ((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ =
        (2 : ℝ) ^ ((ell : ℤ) + 3 : ℤ) := by
    rw [← zpow_neg]
    congr 1
    ring
  have heps_nat :
      (2 : ℝ) ^ ((ell : ℤ) + 3 : ℤ) = (2 : ℝ) ^ (ell + 3) := by
    rw [show (ell : ℤ) + 3 = ((ell + 3 : ℕ) : ℤ) by omega, zpow_natCast]
  have heps_le :
      ((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ ≤ (3 : ℝ) ^ (ell + 3) := by
    rw [heps_inv, heps_nat]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hthree_nonneg : 0 ≤ (3 : ℝ) ^ (-(a * r)) := by positivity
  have hCscale :
      2 * Cstar * (3 : ℝ) ^ (-(a * r)) ≤
        (3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r)) := by
    exact mul_le_mul_of_nonneg_right hCpow hthree_nonneg
  have hbase :
      ((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ *
          (2 * Cstar * (3 : ℝ) ^ (-(a * r))) ≤
        (3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r))) := by
    calc
      _ ≤ (3 : ℝ) ^ (ell + 3) *
          (2 * Cstar * (3 : ℝ) ^ (-(a * r))) := by
            gcongr
      _ ≤ _ := by gcongr
  have hbase_rpow :
      (((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ *
          (2 * Cstar * (3 : ℝ) ^ (-(a * r))) ) ^ p ≤
        ((3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r)))) ^ p := by
    exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hlogR :
      Real.log ((3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r)))) =
        (((ell : ℝ) + 3) + N - a * r) * Real.log 3 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
    push_cast
    ring
  have hp_nonneg : 0 ≤ p := by linarith
  have hscale_mul :
      2 * (((N : ℝ) + 4) * q * (p * Real.log 3)) ≤
        a * r * (p * Real.log 3) := by
    have := mul_le_mul_of_nonneg_right hscale (mul_nonneg hp_nonneg hlog3.le)
    convert this using 1 <;> ring
  have hover_mul :
      p * (((ell : ℝ) + 3 + N) * Real.log 3) ≤
        ((N : ℝ) + 4) * q * (p * Real.log 3) := by
    have := mul_le_mul_of_nonneg_right hover (mul_nonneg hp_nonneg hlog3.le)
    convert this using 1 <;> ring
  have hlog_bound :
      p * ((((ell : ℝ) + 3) + N - a * r) * Real.log 3) ≤ -(B * (2 * r)) := by
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      exact_mod_cast (Nat.zero_le (2 ^ (ell - 1) * H0))
    have hhalf :
        2 * (p * ((((ell : ℝ) + 3) + N) * Real.log 3)) ≤
          a * r * (p * Real.log 3) := by
      calc
        _ ≤ 2 * (((N : ℝ) + 4) * q * (p * Real.log 3)) :=
          mul_le_mul_of_nonneg_left hover_mul (by norm_num : (0 : ℝ) ≤ 2)
        _ ≤ _ := hscale_mul
    exact aux_lem_rare_tests_band_increment_bound_linear_exp p (Real.log 3) B a r
      (((ell : ℝ) + 3) + N) hp_nonneg hlog3.le hr_nonneg hhalf hmargin4.le
  have hRpos :
      0 < (3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r))) := by positivity
  have hRpow :
      ((3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r)))) ^ p ≤
        Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))) := by
    rw [Real.rpow_def_of_pos hRpos, hlogR, hdouble]
    apply Real.exp_le_exp.mpr
    calc
      _ = p * ((((ell : ℝ) + 3 + N - a * r) * Real.log 3)) :=
        mul_comm _ _
      _ ≤ _ := hlog_bound
  calc
    (((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ ^ p) *
          (2 * Cstar * (3 : ℝ) ^ (-(a *
            ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)))) ^ p =
        (((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ *
          (2 * Cstar * (3 : ℝ) ^ (-(a * r))) ) ^ p := by
            dsimp [r]
            calc
              _ = ((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ ^ p *
                  ((2 * Cstar) ^ p *
                    ((3 : ℝ) ^ (-(a *
                      ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)))) ^ p) := by
                rw [Real.mul_rpow (by positivity) (by positivity)]
              _ = ((((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ *
                    (2 * Cstar)) ^ p) *
                    ((3 : ℝ) ^ (-(a *
                      ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)))) ^ p := by
                calc
                  _ = ((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ ^ p *
                      ((2 * Cstar) ^ p) *
                      ((3 : ℝ) ^ (-(a *
                        ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)))) ^ p := by ring
                  _ = _ := by
                    congr 1
                    exact (Real.mul_rpow (by positivity) (by positivity)).symm
              _ = (((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ *
                    (2 * Cstar *
                      (3 : ℝ) ^ (-(a *
                        ((2 ^ (ell - 1) * H0 : ℕ) : ℝ))))) ^ p := by
                calc
                  _ = ((((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ *
                      (2 * Cstar)) *
                      (3 : ℝ) ^ (-(a *
                        ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)))) ^ p := by
                    symm
                    exact Real.mul_rpow (by positivity) (by positivity)
                  _ = _ := by congr 1 <;> ring
    _ ≤ ((3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r)))) ^ p := hbase_rpow
    _ ≤ Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))) := hRpow

lemma aux_lem_rare_tests_band_increment_bound_absorption
    (Cstar a p Cgeom B : ℝ) (hCstar : 0 < Cstar) (ha : 0 < a)
    (hp : 1 ≤ p) (hCgeom : 4 ≤ Cgeom) (hB : 0 < B)
    (hmargin : Cgeom * B < a * p * Real.log 3) :
    ∃ Hinc : ℕ, 0 < Hinc ∧
      ∀ H0 : ℕ, Hinc ≤ H0 →
        ∀ ell : ℕ, 1 ≤ ell →
          (((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ ^ p) *
              (2 * Cstar *
                (3 : ℝ) ^
                  (-(a * ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)))) ^ p ≤
            Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * Cstar)
  have hCpow : 2 * Cstar ≤ (3 : ℝ) ^ N :=
    (le_of_lt hN).trans
      (aux_lem_rare_tests_band_increment_bound_pow_three N)
  obtain ⟨Hinc, hHinc⟩ :=
    exists_nat_gt (2 * ((N : ℝ) + 4) / a)
  have hHinc_pos : 0 < Hinc := by
    have : (0 : ℝ) < Hinc := by
      have hpos : 0 < 2 * ((N : ℝ) + 4) / a := by positivity
      exact hpos.trans hHinc
    exact_mod_cast this
  have hmargin4 : 4 * B < a * p * Real.log 3 := by
    have hfour : 4 * B ≤ Cgeom * B := by nlinarith
    exact hfour.trans_lt hmargin
  refine ⟨Hinc, hHinc_pos, ?_⟩
  exact aux_lem_rare_tests_band_increment_bound_absorption_inner Cstar a p B N Hinc
    hCstar ha hp hCpow hHinc hmargin4
  /-
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * Cstar)
  have hpow_three : ∀ n : ℕ, (n : ℝ) ≤ (3 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [pow_succ]
        have hone : 1 ≤ (3 : ℝ) ^ n :=
          one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num)
        norm_num at *
        nlinarith
  have hCpow : 2 * Cstar ≤ (3 : ℝ) ^ N :=
    (le_of_lt hN).trans (hpow_three N)
  obtain ⟨Hinc, hHinc⟩ :=
    exists_nat_gt (2 * ((N : ℝ) + 4) / a)
  have hHinc_pos : 0 < Hinc := by
    have : (0 : ℝ) < Hinc := by
      have hpos : 0 < 2 * ((N : ℝ) + 4) / a := by positivity
      exact hpos.trans hHinc
    exact_mod_cast this
  refine ⟨Hinc, hHinc_pos, ?_⟩
  intro H0 hH0 ell hell
  let q : ℝ := ((2 ^ (ell - 1) : ℕ) : ℝ)
  let r : ℝ := ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)
  have hq_pos : 0 < q := by
    dsimp [q]
    positivity
  have hq_one : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (one_le_pow₀ (show 1 ≤ (2 : ℕ) by norm_num))
  have hlin : ∀ k : ℕ, (k : ℝ) + 4 ≤ 4 * (2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        have hone : 1 ≤ (2 : ℝ) ^ k :=
          one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)
        norm_num at *
        nlinarith
  have hell_sub : (ell : ℝ) + 3 = ((ell - 1 : ℕ) : ℝ) + 4 := by
    have hnat : ell = (ell - 1) + 1 := by omega
    rw [hnat]
    push_cast
    ring
  have hover : (ell : ℝ) + 3 + N ≤ ((N : ℝ) + 4) * q := by
    have hindex : (ell : ℝ) + 3 ≤ 4 * q := by
      rw [hell_sub]
      simpa [q] using hlin (ell - 1)
    have hNq : (N : ℝ) ≤ (N : ℝ) * q := by
      have := mul_le_mul_of_nonneg_left hq_one (Nat.cast_nonneg N)
      simpa [mul_comm] using this
    dsimp [q] at hindex hNq ⊢
    nlinarith
  have hell_step : ell = (ell - 1) + 1 := by omega
  have hdouble : ((2 ^ ell * H0 : ℕ) : ℝ) = 2 * r := by
    have hpow : 2 ^ ell = 2 * 2 ^ (ell - 1) := by
      rw [hell_step, pow_succ]
      exact Nat.mul_comm _ _
    dsimp [r]
    rw [hpow]
    push_cast
    ring
  have hH0real : (Hinc : ℝ) ≤ H0 := by exact_mod_cast hH0
  have hKlt : 2 * ((N : ℝ) + 4) / a < (H0 : ℝ) :=
    hHinc.trans_le hH0real
  have hKmul : 2 * ((N : ℝ) + 4) < (H0 : ℝ) * a :=
    (div_lt_iff₀ ha).mp hKlt
  have hKle : 2 * ((N : ℝ) + 4) ≤ a * (H0 : ℝ) := by
    nlinarith
  have hscale : 2 * ((N : ℝ) + 4) * q ≤ a * r := by
    have hmul := mul_le_mul_of_nonneg_right hKle hq_pos.le
    dsimp [q, r] at hmul ⊢
    push_cast at hmul ⊢
    convert hmul using 1 <;> ring
  have heps_inv :
      ((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ =
        (2 : ℝ) ^ ((ell : ℤ) + 3 : ℤ) := by
    rw [← zpow_neg]
    congr 1
    ring
  have heps_nat :
      (2 : ℝ) ^ ((ell : ℤ) + 3 : ℤ) = (2 : ℝ) ^ (ell + 3) := by
    rw [show (ell : ℤ) + 3 = ((ell + 3 : ℕ) : ℤ) by omega, zpow_natCast]
  have heps_le :
      ((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ ≤ (3 : ℝ) ^ (ell + 3) := by
    rw [heps_inv, heps_nat]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hthree_nonneg : 0 ≤ (3 : ℝ) ^ (-(a * r)) := by positivity
  have hCscale :
      2 * Cstar * (3 : ℝ) ^ (-(a * r)) ≤
        (3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r)) := by
    exact mul_le_mul_of_nonneg_right hCpow hthree_nonneg
  have hbase :
      ((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ *
          (2 * Cstar * (3 : ℝ) ^ (-(a * r))) ≤
        (3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r))) := by
    calc
      _ ≤ (3 : ℝ) ^ (ell + 3) *
          (2 * Cstar * (3 : ℝ) ^ (-(a * r))) := by
            gcongr
      _ ≤ _ := by gcongr
  have hbase_rpow :
      (((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ *
          (2 * Cstar * (3 : ℝ) ^ (-(a * r))) ) ^ p ≤
        ((3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r)))) ^ p := by
    exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hlogR :
      Real.log ((3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r)))) =
        (((ell : ℝ) + 3) + N - a * r) * Real.log 3 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
    push_cast
    ring
  have hmargin4 : 4 * B < a * p * Real.log 3 := by
    have hfour : 4 * B ≤ Cgeom * B := by nlinarith
    exact hfour.trans_lt hmargin
  have hmargin2 : 2 * B < (a * p * Real.log 3) / 2 := by
    nlinarith
  have hp_nonneg : 0 ≤ p := by linarith
  have hscale_mul :
      2 * (((N : ℝ) + 4) * q * (p * Real.log 3)) ≤
        a * r * (p * Real.log 3) := by
    have := mul_le_mul_of_nonneg_right hscale (mul_nonneg hp_nonneg hlog3.le)
    convert this using 1 <;> ring
  have hover_mul :
      p * (((ell : ℝ) + 3 + N) * Real.log 3) ≤
        ((N : ℝ) + 4) * q * (p * Real.log 3) := by
    have := mul_le_mul_of_nonneg_right hover (mul_nonneg hp_nonneg hlog3.le)
    convert this using 1 <;> ring
  have hlog_bound :
      p * ((((ell : ℝ) + 3) + N - a * r) * Real.log 3) ≤ -(B * (2 * r)) := by
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      exact_mod_cast (Nat.zero_le (2 ^ (ell - 1) * H0))
    have hhalf :
        2 * (p * ((((ell : ℝ) + 3) + N) * Real.log 3)) ≤
          a * r * (p * Real.log 3) := by
      calc
        _ ≤ 2 * (((N : ℝ) + 4) * q * (p * Real.log 3)) :=
          mul_le_mul_of_nonneg_left hover_mul (by norm_num : (0 : ℝ) ≤ 2)
        _ ≤ _ := hscale_mul
    exact aux_lem_rare_tests_band_increment_bound_linear_exp p (Real.log 3) B a r
      (((ell : ℝ) + 3) + N) hp_nonneg hlog3.le hr_nonneg hhalf hmargin4.le
  have hRpos :
      0 < (3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r))) := by positivity
  have hRpow :
      ((3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r)))) ^ p ≤
        Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))) := by
    rw [Real.rpow_def_of_pos hRpos, hlogR, hdouble]
    apply Real.exp_le_exp.mpr
    calc
      _ = p * ((((ell : ℝ) + 3 + N - a * r) * Real.log 3)) :=
        mul_comm _ _
      _ ≤ _ := hlog_bound
  calc
    (((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ ^ p) *
          (2 * Cstar * (3 : ℝ) ^ (-(a *
            ((2 ^ (ell - 1) * H0 : ℕ) : ℝ)))) ^ p =
        (((2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ))⁻¹ *
          (2 * Cstar * (3 : ℝ) ^ (-(a * r))) ) ^ p := by
            dsimp [r]
            rw [Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ ((3 : ℝ) ^ (ell + 3) *
          ((3 : ℝ) ^ N * (3 : ℝ) ^ (-(a * r)))) ^ p := hbase_rpow
    _ ≤ Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))) := hRpow
  -/

lemma aux_lem_rare_tests_band_increment_bound_ennreal_product
    (ε U p : ℝ) (hε : 0 < ε) (hU : 0 < U) (hp : 0 ≤ p) :
    (ENNReal.ofReal ε)⁻¹ ^ p * (ENNReal.ofReal U) ^ p =
      ENNReal.ofReal ((ε⁻¹ * U) ^ p) := by
  rw [← ENNReal.ofReal_inv_of_pos hε]
  rw [ENNReal.ofReal_rpow_of_pos (by positivity),
    ENNReal.ofReal_rpow_of_pos hU]
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [Real.mul_rpow (by positivity) (by positivity)]



theorem lem_rare_tests_band_increment_bound :
    ∀ (d : ℕ) (hd : 1 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
      (center : ℤ)
      (X : ℕ → BilateralField d → ℝ)
      (Cstar a p : ℝ) (hCstar : 0 < Cstar) (ha : 0 < a) (hp : 1 ≤ p),
      (let Bsym : ℕ → MeasurableSpace (BilateralField d) := fun H =>
          MeasurableSpace.comap
            ((Set.Icc (center - (H : ℤ)) (center + (H : ℤ))).restrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (H : ℤ)) (center + (H : ℤ))) →
                C(SpatialCoordinates d, ℝ)));
      (∀ m H : ℕ,
          eLpNorm (fun ω => X m ω - (P[X m | Bsym H]) ω)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cstar * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
        ∀ Cgeom B : ℝ, 4 ≤ Cgeom → 0 < B →
          Cgeom * B < a * p * Real.log 3 →
          ∃ Hinc : ℕ, 0 < Hinc ∧
            ∀ H0 : ℕ, Hinc ≤ H0 →
              ∀ (m ell : ℕ), 1 ≤ ell →
                P {ω |
                    2 ^ (-(ell : ℤ) - 3 : ℤ) ≤
                      (P[X m | Bsym (2 ^ ell * H0)]) ω -
                        (P[X m | Bsym (2 ^ (ell - 1) * H0)]) ω} ≤
                  ENNReal.ofReal
                    (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))))) := by
  intro d hd _ _ P _ center X Cstar a p hCstar ha hp
  dsimp
  intro hband Cgeom B hCgeom hB hmargin
  obtain ⟨Hinc, hHinc, habs⟩ :=
    aux_lem_rare_tests_band_increment_bound_absorption Cstar a p Cgeom B
      hCstar ha hp hCgeom hB hmargin
  refine ⟨Hinc, hHinc, ?_⟩
  intro H0 hH0 m ell hell
  let Hsmall : ℕ := 2 ^ (ell - 1) * H0
  let Hlarge : ℕ := 2 ^ ell * H0
  let ε : ℝ := (2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hlevels : Hsmall ≤ Hlarge := by
    dsimp [Hsmall, Hlarge]
    exact Nat.mul_le_mul_right H0
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hlevel_real : (Hsmall : ℝ) ≤ Hlarge := by exact_mod_cast hlevels
  have hdecay :
      Cstar * (3 : ℝ) ^ (-(a * (Hlarge : ℝ))) ≤
        Cstar * (3 : ℝ) ^ (-(a * (Hsmall : ℝ))) := by
    apply mul_le_mul_of_nonneg_left ?_ hCstar.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  by_cases hXm : Integrable (X m) P
  · have hf : AEStronglyMeasurable
        (fun ω => X m ω -
          (P[X m |
            MeasurableSpace.comap
              ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
              (inferInstance : MeasurableSpace
                ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                  C(SpatialCoordinates d, ℝ)))]) ω) P := by
      apply hXm.aestronglyMeasurable.sub
      exact (integrable_condExp (m :=
        MeasurableSpace.comap
          ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
              C(SpatialCoordinates d, ℝ)))) (μ := P) (f := X m)).aestronglyMeasurable
    have hg : AEStronglyMeasurable
        (fun ω => X m ω -
          (P[X m |
            MeasurableSpace.comap
              ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
              (inferInstance : MeasurableSpace
                ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                  C(SpatialCoordinates d, ℝ)))]) ω) P := by
      apply hXm.aestronglyMeasurable.sub
      exact (integrable_condExp (m :=
        MeasurableSpace.comap
          ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
              C(SpatialCoordinates d, ℝ)))) (μ := P) (f := X m)).aestronglyMeasurable
    have hmark := aux_lem_rare_tests_band_increment_bound_markov p hp
      (fun ω => X m ω -
        (P[X m |
          MeasurableSpace.comap
            ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                C(SpatialCoordinates d, ℝ)))]) ω)
      (fun ω => X m ω -
        (P[X m |
          MeasurableSpace.comap
            ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
            (inferInstance : MeasurableSpace
              ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                C(SpatialCoordinates d, ℝ)))]) ω)
      hf hg ε hε
    have hevent :
        {ω : BilateralField d | ε ≤
            (X m ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω) -
            (X m ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω)} =
          {ω : BilateralField d |
            ε ≤
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω} := by
      ext ω
      simp only [mem_setOf_eq]
      congr 1
      ring
    rw [hevent] at hmark
    let U : ℝ := 2 * Cstar * (3 : ℝ) ^ (-(a * (Hsmall : ℝ)))
    have hU : 0 < U := by
      dsimp [U]
      positivity
    have hnorm :
        eLpNorm (fun ω => X m ω -
            (P[X m |
              MeasurableSpace.comap
                ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
                (inferInstance : MeasurableSpace
                  ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                    C(SpatialCoordinates d, ℝ)))]) ω)
            (ENNReal.ofReal p) P +
          eLpNorm (fun ω => X m ω -
            (P[X m |
              MeasurableSpace.comap
                ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
                (inferInstance : MeasurableSpace
                  ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                    C(SpatialCoordinates d, ℝ)))]) ω)
            (ENNReal.ofReal p) P ≤ ENNReal.ofReal U := by
      calc
        _ ≤ ENNReal.ofReal
              (Cstar * (3 : ℝ) ^ (-(a * (Hsmall : ℝ)))) +
            ENNReal.ofReal
              (Cstar * (3 : ℝ) ^ (-(a * (Hlarge : ℝ)))) :=
          add_le_add (hband m Hsmall) (hband m Hlarge)
        _ ≤ ENNReal.ofReal
              (Cstar * (3 : ℝ) ^ (-(a * (Hsmall : ℝ)))) +
            ENNReal.ofReal
              (Cstar * (3 : ℝ) ^ (-(a * (Hsmall : ℝ)))) := by
          gcongr
        _ = ENNReal.ofReal U := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          dsimp [U]
          ring
    have hmark_bound :
        P {ω : BilateralField d |
            ε ≤
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω} ≤
          (ENNReal.ofReal ε)⁻¹ ^ p * (ENNReal.ofReal U) ^ p := by
      calc
        _ ≤ (ENNReal.ofReal ε)⁻¹ ^ p *
            (eLpNorm (fun ω => X m ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω)
              (ENNReal.ofReal p) P +
              eLpNorm (fun ω => X m ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω)
              (ENNReal.ofReal p) P) ^ p := hmark
        _ ≤ _ := by gcongr
    have hmark_real :
        P {ω : BilateralField d |
            ε ≤
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω} ≤
          ENNReal.ofReal ((ε⁻¹ * U) ^ p) := by
      calc
        _ ≤ (ENNReal.ofReal ε)⁻¹ ^ p * (ENNReal.ofReal U) ^ p := hmark_bound
        _ = _ :=
          aux_lem_rare_tests_band_increment_bound_ennreal_product ε U p hε hU
            (by linarith)
    have habs_real : ε⁻¹ ^ p * U ^ p ≤
        Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))) := by
      simpa [ε, U, Hsmall, Hlarge] using habs H0 hH0 ell hell
    have hreal : (ε⁻¹ * U) ^ p ≤
        Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ))) := by
      calc
        _ = ε⁻¹ ^ p * U ^ p :=
          Real.mul_rpow (by positivity) (by positivity)
        _ ≤ _ := habs_real
    have hfinal :
        P {ω : BilateralField d |
            ε ≤
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω -
              (P[X m |
                MeasurableSpace.comap
                  ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
                  (inferInstance : MeasurableSpace
                    ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
                      C(SpatialCoordinates d, ℝ)))]) ω} ≤
          ENNReal.ofReal
            (Real.exp (-(B * ((2 ^ ell * H0 : ℕ) : ℝ)))) := by
      exact hmark_real.trans (ENNReal.ofReal_le_ofReal hreal)
    simpa [ε, Hsmall, Hlarge] using hfinal
  · have hsmall_zero := condExp_of_not_integrable (m :=
        MeasurableSpace.comap
          ((Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))).restrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (center - (Hsmall : ℤ)) (center + (Hsmall : ℤ))) →
              C(SpatialCoordinates d, ℝ)))) hXm
    have hlarge_zero := condExp_of_not_integrable (m :=
        MeasurableSpace.comap
          ((Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))).restrict)
          (inferInstance : MeasurableSpace
            ((i : Set.Icc (center - (Hlarge : ℤ)) (center + (Hlarge : ℤ))) →
              C(SpatialCoordinates d, ℝ)))) hXm
    dsimp [Hsmall, Hlarge] at hsmall_zero hlarge_zero
    rw [hlarge_zero, hsmall_zero]
    simp only [Pi.zero_apply, sub_self]
    have : {ω : BilateralField d |
        (2 : ℝ) ^ (-(ell : ℤ) - 3 : ℤ) ≤ (0 : ℝ)} = ∅ := by
      ext ω
      simp only [mem_setOf_eq, not_le, mem_empty_iff_false, iff_false]
      positivity
    rw [this, measure_empty]
    exact bot_le

end Paper
