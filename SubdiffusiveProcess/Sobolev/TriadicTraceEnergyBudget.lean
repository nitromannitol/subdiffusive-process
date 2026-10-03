module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! This file proves a deterministic scalar envelope for a linear trace factor and its quadratic energy cost. It does not assert any probabilistic or PDE estimate. -/
noncomputable section
namespace SubdiffusiveProcess

private lemma aux_triadic_trace_exponential_factor
    (Kp t tau budget : ℝ) (hKp : 0 ≤ Kp) (ht : 0 ≤ t)
    (hτ : tau ≤ 1) (hbudget : budget ≤ t) :
    Kp * Real.exp ((tau + 2 * budget) / 2) + 1 ≤
      (Kp * Real.exp ((1 : ℝ) / 2) + 1) * Real.exp t := by
  have harg : (tau + 2 * budget) / 2 ≤ (1 : ℝ) / 2 + t := by
    linarith only [hτ, hbudget]
  have hexp : Real.exp ((tau + 2 * budget) / 2) ≤
      Real.exp ((1 : ℝ) / 2) * Real.exp t := by
    calc
      Real.exp ((tau + 2 * budget) / 2) ≤ Real.exp ((1 : ℝ) / 2 + t) :=
        (Real.exp_le_exp).2 harg
      _ = Real.exp ((1 : ℝ) / 2) * Real.exp t := Real.exp_add _ _
  have htExp : 1 ≤ Real.exp t := by
    have h := (Real.exp_le_exp).2 ht
    simpa only [Real.exp_zero] using h
  calc
    Kp * Real.exp ((tau + 2 * budget) / 2) + 1 ≤
        Kp * (Real.exp ((1 : ℝ) / 2) * Real.exp t) + Real.exp t :=
      add_le_add (mul_le_mul_of_nonneg_left hexp hKp) htExp
    _ = (Kp * Real.exp ((1 : ℝ) / 2) + 1) * Real.exp t := by ring

private lemma aux_triadic_trace_factor_bound
    (Cbase Kp t tau budget : ℝ) (hBase : 0 ≤ Cbase) (hKp : 0 ≤ Kp)
    (ht : 0 ≤ t) (hτ : tau ≤ 1) (hbudget : budget ≤ t) :
    Cbase * (Kp * Real.exp ((tau + 2 * budget) / 2) + 1) ≤
      (Cbase * (Kp * Real.exp ((1 : ℝ) / 2) + 1)) * Real.exp t := by
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (aux_triadic_trace_exponential_factor Kp t tau budget hKp ht hτ hbudget) hBase

private lemma aux_triadic_exp_envelope
    (A C rate t : ℝ) (hAmp : A ≤ C) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hrate : rate ≤ C * Real.log 3) :
    A * Real.exp (rate * t) ≤ C * (3 : ℝ) ^ (C * t) := by
  have hexpArg : rate * t ≤ Real.log 3 * (C * t) := by
    calc
      rate * t ≤ (C * Real.log 3) * t := mul_le_mul_of_nonneg_right hrate ht
      _ = Real.log 3 * (C * t) := by ring
  have hexp : Real.exp (rate * t) ≤ (3 : ℝ) ^ (C * t) := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (3 : ℝ)) (C * t)]
    exact (Real.exp_le_exp).2 hexpArg
  calc
    A * Real.exp (rate * t) ≤ C * Real.exp (rate * t) :=
      mul_le_mul_of_nonneg_right hAmp (Real.exp_pos _).le
    _ ≤ C * (3 : ℝ) ^ (C * t) := mul_le_mul_of_nonneg_left hexp hC

private lemma aux_triadic_energy_squaring
    (Ce D M b K t : ℝ) (hCe : 0 ≤ Ce) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hK0 : 0 ≤ K) (hK : K ≤ M * Real.exp (b * t)) :
    2 * Ce * (D * K) ^ 2 ≤
      (2 * Ce * (D * M) ^ 2) * Real.exp ((2 * b) * t) := by
  have hDK : D * K ≤ D * (M * Real.exp (b * t)) :=
    mul_le_mul_of_nonneg_left hK hD
  have hDK0 : 0 ≤ D * K := mul_nonneg hD hK0
  have hDKupper0 : 0 ≤ D * (M * Real.exp (b * t)) :=
    mul_nonneg hD (mul_nonneg hM (Real.exp_pos _).le)
  have hSq : (D * K) ^ 2 ≤ (D * (M * Real.exp (b * t))) ^ 2 := by
    have hmul := mul_le_mul hDK hDK hDK0 hDKupper0
    simpa only [pow_two] using hmul
  calc
    2 * Ce * (D * K) ^ 2 ≤ 2 * Ce * (D * (M * Real.exp (b * t))) ^ 2 :=
      mul_le_mul_of_nonneg_left hSq (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hCe)
    _ = 2 * Ce * (D * M) ^ 2 *
        (Real.exp (b * t) * Real.exp (b * t)) := by ring
    _ = 2 * Ce * (D * M) ^ 2 * Real.exp ((b * t) + (b * t)) := by
      rw [← Real.exp_add]
    _ = (2 * Ce * (D * M) ^ 2) * Real.exp ((2 * b) * t) := by
      rw [show (b * t) + (b * t) = (2 * b) * t by ring]

/-- One deterministic triadic envelope bounds both the linear trace constant and its quadratic energy cost. -/
theorem exists_triadic_trace_energy_budget
    (Cbase Kp Ce D Cmin : ℝ) (hBase : 0 ≤ Cbase) (hKp : 0 ≤ Kp)
    (hCe : 0 ≤ Ce) (hD : 0 ≤ D) :
    ∃ Cbound : ℝ, 1 ≤ Cbound ∧ Cbase ≤ Cbound ∧ Cmin ≤ Cbound ∧
      ∀ (t tau budget : ℝ), 0 ≤ t → tau ≤ 1 → budget ≤ t →
      let K : ℝ := Cbase * (Kp * Real.exp ((tau + 2 * budget) / 2) + 1) *
        (3 : ℝ) ^ (Cbase * t)
      K ≤ Cbound * (3 : ℝ) ^ (Cbound * t) ∧
        2 * Ce * (D * K) ^ 2 ≤ Cbound * (3 : ℝ) ^ (Cbound * t) := by
  let M : ℝ := Cbase * (Kp * Real.exp ((1 : ℝ) / 2) + 1)
  let b : ℝ := 1 + Cbase * Real.log 3
  let Q : ℝ := 2 * Ce * (D * M) ^ 2
  let C₁ : ℝ := max (max 1 Cbase) Cmin
  let C₂ : ℝ := max (max M Q) ((2 * b) / Real.log 3)
  let Cbound : ℝ := max C₁ C₂
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg hBase (add_nonneg (mul_nonneg hKp (Real.exp_pos _).le) (by norm_num))
  have hb0 : 0 ≤ b := by
    have hprod : 0 ≤ Cbase * Real.log 3 := mul_nonneg hBase hlog3.le
    dsimp [b]
    linarith only [hprod]
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hCe) (sq_nonneg (D * M))
  have hOne : 1 ≤ Cbound := by
    exact le_trans (le_max_left 1 Cbase)
      (le_trans (le_max_left (max 1 Cbase) Cmin) (le_max_left C₁ C₂))
  have hBaseBound : Cbase ≤ Cbound := by
    exact le_trans (le_max_right 1 Cbase)
      (le_trans (le_max_left (max 1 Cbase) Cmin) (le_max_left C₁ C₂))
  have hMinBound : Cmin ≤ Cbound := by
    exact le_trans (le_max_right (max 1 Cbase) Cmin) (le_max_left C₁ C₂)
  have hMBound : M ≤ Cbound := by
    exact le_trans (le_max_left M Q)
      (le_trans (le_max_left (max M Q) ((2 * b) / Real.log 3)) (le_max_right C₁ C₂))
  have hQBound : Q ≤ Cbound := by
    exact le_trans (le_max_right M Q)
      (le_trans (le_max_left (max M Q) ((2 * b) / Real.log 3)) (le_max_right C₁ C₂))
  have hRateBound : (2 * b) / Real.log 3 ≤ Cbound := by
    exact le_trans (le_max_right (max M Q) ((2 * b) / Real.log 3)) (le_max_right C₁ C₂)
  have hRateTwice : 2 * b ≤ Cbound * Real.log 3 :=
    (div_le_iff₀ hlog3).mp hRateBound
  have hRateOnce : b ≤ Cbound * Real.log 3 := by
    linarith only [hb0, hRateTwice]
  have hCbound0 : 0 ≤ Cbound := le_trans (by norm_num : (0 : ℝ) ≤ 1) hOne
  refine ⟨Cbound, hOne, hBaseBound, hMinBound, ?_⟩
  intro t tau budget ht hτ hbudget
  have hFactor := aux_triadic_trace_factor_bound Cbase Kp t tau budget hBase hKp ht hτ hbudget
  have hPow0 : 0 ≤ (3 : ℝ) ^ (Cbase * t) := Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hKraw : Cbase * (Kp * Real.exp ((tau + 2 * budget) / 2) + 1) *
      (3 : ℝ) ^ (Cbase * t) ≤ M * Real.exp (b * t) := by
    calc
      Cbase * (Kp * Real.exp ((tau + 2 * budget) / 2) + 1) *
          (3 : ℝ) ^ (Cbase * t) ≤
        (Cbase * (Kp * Real.exp ((1 : ℝ) / 2) + 1)) * Real.exp t *
          (3 : ℝ) ^ (Cbase * t) := mul_le_mul_of_nonneg_right hFactor hPow0
      _ = M * Real.exp (b * t) := by
        rw [Real.rpow_def_of_pos (by norm_num : 0 < (3 : ℝ)) (Cbase * t)]
        calc
          Cbase * (Kp * Real.exp ((1 : ℝ) / 2) + 1) * Real.exp t *
              Real.exp (Real.log 3 * (Cbase * t)) =
              Cbase * (Kp * Real.exp ((1 : ℝ) / 2) + 1) *
                (Real.exp t * Real.exp (Real.log 3 * (Cbase * t))) := by ring
          _ = Cbase * (Kp * Real.exp ((1 : ℝ) / 2) + 1) *
              Real.exp ((1 + Cbase * Real.log 3) * t) := by
            rw [← Real.exp_add]
            rw [show t + Real.log 3 * (Cbase * t) =
              (1 + Cbase * Real.log 3) * t by ring]
          _ = M * Real.exp (b * t) := by rfl
  have hK0 : 0 ≤ Cbase * (Kp * Real.exp ((tau + 2 * budget) / 2) + 1) *
      (3 : ℝ) ^ (Cbase * t) := by
    have hBracket0 : 0 ≤ Kp * Real.exp ((tau + 2 * budget) / 2) + 1 :=
      add_nonneg (mul_nonneg hKp (Real.exp_pos _).le) (by norm_num)
    exact mul_nonneg (mul_nonneg hBase hBracket0) hPow0
  have hEnergyRaw := aux_triadic_energy_squaring Ce D M b
    (Cbase * (Kp * Real.exp ((tau + 2 * budget) / 2) + 1) * (3 : ℝ) ^ (Cbase * t))
    t hCe hD hM0 hK0 hKraw
  have hLinearEnvelope := aux_triadic_exp_envelope M Cbound b t hMBound hCbound0 ht hRateOnce
  have hEnergyEnvelope := aux_triadic_exp_envelope Q Cbound (2 * b) t hQBound hCbound0 ht hRateTwice
  constructor
  · change Cbase * (Kp * Real.exp ((tau + 2 * budget) / 2) + 1) *
      (3 : ℝ) ^ (Cbase * t) ≤ Cbound * (3 : ℝ) ^ (Cbound * t)
    exact hKraw.trans hLinearEnvelope
  · change 2 * Ce *
      (D * (Cbase * (Kp * Real.exp ((tau + 2 * budget) / 2) + 1) *
        (3 : ℝ) ^ (Cbase * t))) ^ 2 ≤ Cbound * (3 : ℝ) ^ (Cbound * t)
    exact hEnergyRaw.trans hEnergyEnvelope
end SubdiffusiveProcess
