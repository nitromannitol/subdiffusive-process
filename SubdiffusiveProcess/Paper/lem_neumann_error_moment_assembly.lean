module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



theorem lem_neumann_error_moment_assembly :
  ∀ (p Bcoerc Bresponse Cload : ℝ),
    1 ≤ p → 0 ≤ Bcoerc → 0 ≤ Bresponse → 0 < Cload →
    ∃ Cerr Cunif : ℝ, 0 < Cerr ∧ 0 < Cunif ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
    ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
    ∀ (K Y V D : Ω → ℝ),
      (∀ x, 0 ≤ K x) → (∀ x, 0 ≤ Y x) →
      (∀ x, 0 ≤ V x) →
      (∀ x, |D x| ≤
        Cload * eps ^ (1 / 4 : ℝ) * Real.sqrt (K x) * Real.sqrt (Y x) +
          Cload ^ 2 * eps ^ (1 / 2 : ℝ) * K x) →
      (∀ x, V x ≤ 2 * Y x + 2 * Cload ^ 2 * eps ^ (1 / 2 : ℝ) * K x) →
      AEStronglyMeasurable D μ → AEStronglyMeasurable V μ →
      MemLp K (ENNReal.ofReal (4 * p)) μ →
      eLpNorm K (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal Bcoerc →
      MemLp Y (ENNReal.ofReal (4 * p)) μ →
      eLpNorm Y (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal Bresponse →
      eLpNorm D (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) ∧
      eLpNorm V (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Cunif
    := by
  intro p Bcoerc Bresponse Cload hp hBcoerc hBresponse hCload
  let Cerr : ℝ := Cload * (Bcoerc + Bresponse) + Cload ^ 2 * Bcoerc + 1
  let Cunif : ℝ := 2 * Bresponse + 2 * Cload ^ 2 * Bcoerc + 1
  refine ⟨Cerr, Cunif, ?_, ?_, ?_⟩
  · dsimp [Cerr]
    nlinarith [sq_nonneg Cload]
  · dsimp [Cunif]
    nlinarith [sq_nonneg Cload]
  intro Ω _ μ _ eps heps heps8 K Y V D hK hY hV hD hVle hDmeas hVmeas
    hKmem hKbound hYmem hYbound
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpq : ENNReal.ofReal p ≤ ENNReal.ofReal (4 * p) := by
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have hpone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hKp : eLpNorm K (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Bcoerc :=
    (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans hKbound
  have hYp : eLpNorm Y (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Bresponse :=
    (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans hYbound
  have heps_le_one : eps ≤ 1 := by linarith
  have hepsq_pos : 0 < eps ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos heps _
  have hepsq_nonneg : 0 ≤ eps ^ (1 / 4 : ℝ) := hepsq_pos.le
  have hepsh_le_q : eps ^ (1 / 2 : ℝ) ≤ eps ^ (1 / 4 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge heps heps_le_one (by norm_num)
  have hepsh_le_one : eps ^ (1 / 2 : ℝ) ≤ 1 := by
    exact Real.rpow_le_one heps.le heps_le_one (by norm_num)
  let a : ℝ := Cload * eps ^ (1 / 4 : ℝ) / 2
  let b : ℝ := Cload ^ 2 * eps ^ (1 / 4 : ℝ)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hDpoint : ∀ x, |D x| ≤ a * (K x + Y x) + b * K x := by
    intro x
    have hsqrt : Real.sqrt (K x) * Real.sqrt (Y x) ≤ (K x + Y x) / 2 := by
      have hKsq : (Real.sqrt (K x)) ^ 2 = K x := Real.sq_sqrt (hK x)
      have hYsq : (Real.sqrt (Y x)) ^ 2 = Y x := Real.sq_sqrt (hY x)
      nlinarith [sq_nonneg (Real.sqrt (K x) - Real.sqrt (Y x))]
    have hfirst : Cload * eps ^ (1 / 4 : ℝ) * Real.sqrt (K x) * Real.sqrt (Y x) ≤
        a * (K x + Y x) := by
      dsimp [a]
      have hcoef : 0 ≤ Cload * eps ^ (1 / 4 : ℝ) :=
        mul_nonneg hCload.le (Real.rpow_nonneg heps.le _)
      nlinarith [mul_le_mul_of_nonneg_left hsqrt hcoef]
    have hsecond : Cload ^ 2 * eps ^ (1 / 2 : ℝ) * K x ≤ b * K x := by
      dsimp [b]
      have hKnonneg := hK x
      have hcoef : 0 ≤ Cload ^ 2 := sq_nonneg Cload
      simpa [mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hepsh_le_q hKnonneg) hcoef)
    exact (hD x).trans (add_le_add hfirst hsecond)
  have hVpoint : ∀ x, V x ≤ 2 * Y x + (2 * Cload ^ 2) * K x := by
    intro x
    have hcoef : 0 ≤ 2 * Cload ^ 2 := by positivity
    have hsecond : 2 * Cload ^ 2 * eps ^ (1 / 2 : ℝ) * K x ≤
        (2 * Cload ^ 2) * K x := by
      calc
        2 * Cload ^ 2 * eps ^ (1 / 2 : ℝ) * K x =
            (2 * Cload ^ 2) * (eps ^ (1 / 2 : ℝ) * K x) := by ring
        _ ≤ (2 * Cload ^ 2) * K x := by
          simpa using (mul_le_mul_of_nonneg_left
            (show eps ^ (1 / 2 : ℝ) * K x ≤ K x by
              simpa using mul_le_mul_of_nonneg_right hepsh_le_one (hK x)) hcoef)
    exact (hVle x).trans (add_le_add (le_refl _) hsecond)
  have hKY : AEStronglyMeasurable (K + Y) μ :=
    hKmem.aestronglyMeasurable.add hYmem.aestronglyMeasurable
  have hDnorm : eLpNorm D (ENNReal.ofReal p) μ ≤
      eLpNorm (a • (K + Y) + b • K) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono_real hDmeas
    intro x
    rw [Real.norm_eq_abs]
    simpa [a, b, smul_eq_mul, Pi.add_apply, mul_add, add_assoc, add_left_comm,
      add_comm] using hDpoint x
  have hVnorm : eLpNorm V (ENNReal.ofReal p) μ ≤
      eLpNorm ((2 : ℝ) • Y + (2 * Cload ^ 2) • K) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono_real hVmeas
    intro x
    have hVnonneg : 0 ≤ V x := hV x
    rw [Real.norm_eq_abs, abs_of_nonneg hVnonneg]
    simpa [smul_eq_mul, Pi.add_apply] using hVpoint x
  have hDtarget : eLpNorm (a • (K + Y) + b • K) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal a * (eLpNorm K (ENNReal.ofReal p) μ +
        eLpNorm Y (ENNReal.ofReal p) μ) +
        ENNReal.ofReal b * eLpNorm K (ENNReal.ofReal p) μ := by
    have hsum := eLpNorm_add_le (μ := μ) (f := a • (K + Y)) (g := b • K) hpone
    have hscalea := eLpNorm_const_smul_le (p := ENNReal.ofReal p) (μ := μ)
      (c := a) (f := K + Y)
    have hscaleb := eLpNorm_const_smul_le (p := ENNReal.ofReal p) (μ := μ)
      (c := b) (f := K)
    have hKYnorm := eLpNorm_add_le (μ := μ) (f := K) (g := Y) hpone
    calc
      eLpNorm (a • (K + Y) + b • K) (ENNReal.ofReal p) μ ≤
          eLpNorm (a • (K + Y)) (ENNReal.ofReal p) μ +
            eLpNorm (b • K) (ENNReal.ofReal p) μ := hsum
      _ ≤ ‖a‖ₑ * eLpNorm (K + Y) (ENNReal.ofReal p) μ +
            ‖b‖ₑ * eLpNorm K (ENNReal.ofReal p) μ :=
        add_le_add hscalea hscaleb
      _ ≤ ENNReal.ofReal a * (eLpNorm K (ENNReal.ofReal p) μ +
            eLpNorm Y (ENNReal.ofReal p) μ) +
            ENNReal.ofReal b * eLpNorm K (ENNReal.ofReal p) μ := by
        rw [Real.enorm_eq_ofReal ha, Real.enorm_eq_ofReal hb]
        gcongr
  have hVtarget : eLpNorm ((2 : ℝ) • Y + (2 * Cload ^ 2) • K)
      (ENNReal.ofReal p) μ ≤
      2 * eLpNorm Y (ENNReal.ofReal p) μ +
        ENNReal.ofReal (2 * Cload ^ 2) * eLpNorm K (ENNReal.ofReal p) μ := by
    have hsum := eLpNorm_add_le (μ := μ)
      (f := (2 : ℝ) • Y) (g := (2 * Cload ^ 2) • K) hpone
    have hscaleY := eLpNorm_const_smul_le (p := ENNReal.ofReal p) (μ := μ)
      (c := (2 : ℝ)) (f := Y)
    have hscaleK := eLpNorm_const_smul_le (p := ENNReal.ofReal p) (μ := μ)
      (c := (2 * Cload ^ 2 : ℝ)) (f := K)
    calc
      eLpNorm ((2 : ℝ) • Y + (2 * Cload ^ 2) • K) (ENNReal.ofReal p) μ ≤
          eLpNorm ((2 : ℝ) • Y) (ENNReal.ofReal p) μ +
            eLpNorm ((2 * Cload ^ 2) • K) (ENNReal.ofReal p) μ := hsum
      _ ≤ ‖(2 : ℝ)‖ₑ * eLpNorm Y (ENNReal.ofReal p) μ +
            ‖(2 * Cload ^ 2 : ℝ)‖ₑ * eLpNorm K (ENNReal.ofReal p) μ :=
        add_le_add hscaleY hscaleK
      _ ≤ 2 * eLpNorm Y (ENNReal.ofReal p) μ +
            ENNReal.ofReal (2 * Cload ^ 2) * eLpNorm K (ENNReal.ofReal p) μ := by
        rw [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2),
          Real.enorm_eq_ofReal (by positivity)]
        norm_num
  constructor
  · calc
      eLpNorm D (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal a * (eLpNorm K (ENNReal.ofReal p) μ +
            eLpNorm Y (ENNReal.ofReal p) μ) +
            ENNReal.ofReal b * eLpNorm K (ENNReal.ofReal p) μ :=
        hDnorm.trans hDtarget
      _ ≤ ENNReal.ofReal a * (ENNReal.ofReal Bcoerc + ENNReal.ofReal Bresponse) +
            ENNReal.ofReal b * ENNReal.ofReal Bcoerc := by
        gcongr
      _ ≤ ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) := by
        rw [← ENNReal.ofReal_add hBcoerc hBresponse,
          ← ENNReal.ofReal_mul ha,
          ← ENNReal.ofReal_mul hb]
        rw [← ENNReal.ofReal_add (mul_nonneg ha (add_nonneg hBcoerc hBresponse))
          (mul_nonneg hb hBcoerc)]
        apply ENNReal.ofReal_le_ofReal
        dsimp [a, b, Cerr]
        have hsum_nonneg : 0 ≤ Bcoerc + Bresponse := add_nonneg hBcoerc hBresponse
        have hterm_nonneg : 0 ≤ Cload * (Bcoerc + Bresponse) :=
          mul_nonneg hCload.le hsum_nonneg
        have hsq_nonneg : 0 ≤ Cload ^ 2 * Bcoerc := mul_nonneg (sq_nonneg Cload) hBcoerc
        nlinarith [mul_nonneg hepsq_nonneg hsum_nonneg,
          mul_nonneg hepsq_nonneg hsq_nonneg]
  · calc
      eLpNorm V (ENNReal.ofReal p) μ ≤
          2 * eLpNorm Y (ENNReal.ofReal p) μ +
            ENNReal.ofReal (2 * Cload ^ 2) * eLpNorm K (ENNReal.ofReal p) μ :=
        hVnorm.trans hVtarget
      _ ≤ 2 * ENNReal.ofReal Bresponse +
            ENNReal.ofReal (2 * Cload ^ 2) * ENNReal.ofReal Bcoerc := by
        gcongr
      _ ≤ ENNReal.ofReal Cunif := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Cload ^ 2)]
        rw [← ENNReal.ofReal_add
          (mul_nonneg (by positivity : (0 : ℝ) ≤ 2) hBresponse)
          (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Cload ^ 2) hBcoerc)]
        apply ENNReal.ofReal_le_ofReal
        dsimp [Cunif]
        rw [mul_assoc]
        nlinarith [mul_nonneg (sq_nonneg Cload) hBcoerc]

end SubdiffusiveProcess.Paper
