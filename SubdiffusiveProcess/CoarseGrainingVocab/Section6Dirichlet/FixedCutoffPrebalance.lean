module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FixedCutoffParameters
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedPrebalance

@[expose] public section

/-!
# Substitution in the fixed-cutoff Dirichlet prebalance

This file is the deterministic part of the substitution following
`e.fixed.cutoff.response.algebraic`.  It consumes pointwise response and
energy-envelope bounds, and returns the quarter-exponent appearing in the
manuscript.  No probabilistic construction of those envelopes is assumed.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

noncomputable section

/-- The response-decay weight in `e.fixed.cutoff.response.algebraic`. -/
def fixedCutoffDirichletResponseWeight (theta : ℝ) (N : ℕ) : ℝ :=
  Real.rpow 3 (-theta * (N : ℝ) / 2)

/-- The compensating weight in the energy supremum `Ŷ`. -/
def fixedCutoffDirichletEnergyWeight (theta : ℝ) (N : ℕ) : ℝ :=
  Real.rpow 3 (fixedCutoffDirichletEpsilon theta * (N : ℝ))

/-- The final algebraic-decay weight. -/
def fixedCutoffDirichletTargetWeight (theta : ℝ) (N : ℕ) : ℝ :=
  Real.rpow 3 (-theta * (N : ℝ) / 4)

theorem fixedCutoffDirichletResponseWeight_le_one
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    fixedCutoffDirichletResponseWeight theta N ≤ 1 := by
  unfold fixedCutoffDirichletResponseWeight
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  have hN : 0 ≤ theta * (N : ℝ) := mul_nonneg htheta (Nat.cast_nonneg N)
  linarith

theorem one_le_fixedCutoffDirichletEnergyWeight
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    1 ≤ fixedCutoffDirichletEnergyWeight theta N := by
  unfold fixedCutoffDirichletEnergyWeight fixedCutoffDirichletEpsilon
  apply Real.one_le_rpow (by norm_num)
  exact mul_nonneg (div_nonneg htheta (by norm_num)) (Nat.cast_nonneg N)

private theorem fixedCutoffDirichlet_growth_energy_power_identity
    (theta : ℝ) (N : ℕ) :
    Real.rpow 3
          (fixedCutoffDirichletS1 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
        fixedCutoffDirichletResponseWeight theta N *
        fixedCutoffDirichletEnergyWeight theta N =
      Real.rpow 3
        (fixedCutoffDirichletS1 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ) -
          theta * (N : ℝ) / 2 +
          fixedCutoffDirichletEpsilon theta * (N : ℝ)) := by
  change (3 : ℝ) ^
          (fixedCutoffDirichletS1 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
        (3 : ℝ) ^ (-theta * (N : ℝ) / 2) *
        (3 : ℝ) ^ (fixedCutoffDirichletEpsilon theta * (N : ℝ)) =
      (3 : ℝ) ^
        (fixedCutoffDirichletS1 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ) -
          theta * (N : ℝ) / 2 +
          fixedCutoffDirichletEpsilon theta * (N : ℝ))
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

theorem fixedCutoffDirichlet_growth_energy_term_le
    {theta W Yhat E Y : ℝ} (N : ℕ)
    (htheta : 0 ≤ theta) (hW : 0 ≤ W) (hYhat : 0 ≤ Yhat)
    (hY : 0 ≤ Y)
    (hResponse : E ≤ W * fixedCutoffDirichletResponseWeight theta N)
    (hEnergy : Y ≤ Yhat * fixedCutoffDirichletEnergyWeight theta N) :
    Real.rpow 3
          (fixedCutoffDirichletS1 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ)) * E * Y ≤
      Real.rpow 3 fixedCutoffDirichletS1 * W * Yhat *
        fixedCutoffDirichletTargetWeight theta N := by
  have hA : 0 ≤ Real.rpow 3
      (fixedCutoffDirichletS1 *
        (fixedCutoffDirichletBalanceScale theta N : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hR : 0 ≤ fixedCutoffDirichletResponseWeight theta N :=
    Real.rpow_nonneg (by norm_num) _
  have hG : 0 ≤ fixedCutoffDirichletEnergyWeight theta N :=
    Real.rpow_nonneg (by norm_num) _
  calc
    Real.rpow 3
          (fixedCutoffDirichletS1 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ)) * E * Y ≤
        Real.rpow 3
            (fixedCutoffDirichletS1 *
              (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
          (W * fixedCutoffDirichletResponseWeight theta N) *
          (Yhat * fixedCutoffDirichletEnergyWeight theta N) := by
      gcongr
    _ = W * Yhat *
        Real.rpow 3
          (fixedCutoffDirichletS1 *
              (fixedCutoffDirichletBalanceScale theta N : ℝ) -
            theta * (N : ℝ) / 2 +
            fixedCutoffDirichletEpsilon theta * (N : ℝ)) := by
      rw [← fixedCutoffDirichlet_growth_energy_power_identity theta N]
      ring
    _ ≤ W * Yhat *
        (Real.rpow 3 fixedCutoffDirichletS1 *
          Real.rpow 3 (-theta * (N : ℝ) / 4)) := by
      gcongr
      exact fixedCutoffDirichlet_growth_energy_power_le N htheta
    _ = Real.rpow 3 fixedCutoffDirichletS1 * W * Yhat *
        fixedCutoffDirichletTargetWeight theta N := by
      unfold fixedCutoffDirichletTargetWeight
      ring

theorem fixedCutoffDirichlet_decay_term_le
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    Real.rpow 3
        (-fixedCutoffDirichletS2 *
          (fixedCutoffDirichletBalanceScale theta N : ℝ)) ≤
      Real.rpow 3 fixedCutoffDirichletS2 *
        fixedCutoffDirichletTargetWeight theta N := by
  simpa [fixedCutoffDirichletTargetWeight] using
    fixedCutoffDirichlet_decay_power_le N htheta

theorem fixedCutoffDirichlet_squared_response_term_le
    {theta W E : ℝ} (N : ℕ)
    (htheta : 0 ≤ theta) (hE : 0 ≤ E)
    (hResponse : E ≤ W * fixedCutoffDirichletResponseWeight theta N) :
    Real.rpow 3
          (-fixedCutoffDirichletS2 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
        (Real.rpow 3
            (fixedCutoffDirichletS1 *
              (fixedCutoffDirichletBalanceScale theta N : ℝ)) * E ^ (2 : ℕ)) ≤
      W ^ (2 : ℕ) * fixedCutoffDirichletTargetWeight theta N := by
  have hR : 0 ≤ fixedCutoffDirichletResponseWeight theta N :=
    Real.rpow_nonneg (by norm_num) _
  have hER : E ^ (2 : ℕ) ≤
      (W * fixedCutoffDirichletResponseWeight theta N) ^ (2 : ℕ) := by
    nlinarith
  have hA : 0 ≤ Real.rpow 3
      (fixedCutoffDirichletS1 *
        (fixedCutoffDirichletBalanceScale theta N : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hB : 0 ≤ Real.rpow 3
      (-fixedCutoffDirichletS2 *
        (fixedCutoffDirichletBalanceScale theta N : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    Real.rpow 3
          (-fixedCutoffDirichletS2 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
        (Real.rpow 3
            (fixedCutoffDirichletS1 *
              (fixedCutoffDirichletBalanceScale theta N : ℝ)) * E ^ (2 : ℕ)) ≤
        Real.rpow 3
            (-fixedCutoffDirichletS2 *
              (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
          (Real.rpow 3
              (fixedCutoffDirichletS1 *
                (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
            (W * fixedCutoffDirichletResponseWeight theta N) ^ (2 : ℕ)) := by
      gcongr
    _ = W ^ (2 : ℕ) *
        (Real.rpow 3
            (-fixedCutoffDirichletS2 *
              (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
          (Real.rpow 3
              (fixedCutoffDirichletS1 *
                (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
            fixedCutoffDirichletResponseWeight theta N ^ (2 : ℕ))) := by
      ring
    _ ≤ W ^ (2 : ℕ) * fixedCutoffDirichletTargetWeight theta N := by
      gcongr
      simpa [fixedCutoffDirichletResponseWeight,
        fixedCutoffDirichletTargetWeight] using
        fixedCutoffDirichlet_squared_branch_power_le N htheta

/-- Complete deterministic substitution in `e.Dirichlet.prebalance`.  The
constant is universal; every random dependence is confined to `W` and
`Yhat`. -/
theorem fixedCutoffDirichlet_prebalanceCore_le
    {theta W Yhat E1 E2 Y : ℝ} (N : ℕ)
    (htheta : 0 ≤ theta) (hW : 0 ≤ W) (hYhat : 0 ≤ Yhat)
    (hE2 : 0 ≤ E2) (hY : 0 ≤ Y)
    (hResponseOne :
      E1 ≤ W * fixedCutoffDirichletResponseWeight theta N)
    (hResponseTwo :
      E2 ≤ W * fixedCutoffDirichletResponseWeight theta N)
    (hEnergy :
      Y ≤ Yhat * fixedCutoffDirichletEnergyWeight theta N) :
    dirichletPrebalanceCore fixedCutoffDirichletS1 fixedCutoffDirichletS2
        (fixedCutoffDirichletBalanceScale theta N) E1 E2 Y ≤
      (Real.rpow 3 fixedCutoffDirichletS1 +
          Real.rpow 3 fixedCutoffDirichletS2 + 1) *
        (1 + W) ^ (2 : ℕ) * (1 + Yhat) *
        fixedCutoffDirichletTargetWeight theta N := by
  let T := fixedCutoffDirichletTargetWeight theta N
  let P := (1 + W) ^ (2 : ℕ) * (1 + Yhat) * T
  have hT : 0 ≤ T := Real.rpow_nonneg (by norm_num) _
  have hWone : 0 ≤ 1 + W := by positivity
  have hYone : 0 ≤ 1 + Yhat := by positivity
  have hWle : W ≤ (1 + W) ^ (2 : ℕ) := by nlinarith [sq_nonneg W]
  have hWsqle : W ^ (2 : ℕ) ≤ (1 + W) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg W]
  have honeW : 1 ≤ (1 + W) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg W]
  have hYle : Yhat ≤ 1 + Yhat := by linarith
  have honeY : 1 ≤ 1 + Yhat := by linarith
  have hWY : W * Yhat ≤ (1 + W) ^ (2 : ℕ) * (1 + Yhat) :=
    mul_le_mul hWle hYle hYhat (sq_nonneg (1 + W))
  have hWfactor : (1 + W) ^ (2 : ℕ) ≤
      (1 + W) ^ (2 : ℕ) * (1 + Yhat) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left honeY (sq_nonneg (1 + W))
  have hOne : 1 ≤ (1 + W) ^ (2 : ℕ) * (1 + Yhat) :=
    honeW.trans hWfactor
  have hWsq : W ^ (2 : ℕ) ≤
      (1 + W) ^ (2 : ℕ) * (1 + Yhat) := by
    exact hWsqle.trans hWfactor
  have hFirstRaw := fixedCutoffDirichlet_growth_energy_term_le N
    htheta hW hYhat hY hResponseOne hEnergy
  have hFirst :
      Real.rpow 3
            (fixedCutoffDirichletS1 *
              (fixedCutoffDirichletBalanceScale theta N : ℝ)) * E1 * Y ≤
        Real.rpow 3 fixedCutoffDirichletS1 * P := by
    calc
      _ ≤ Real.rpow 3 fixedCutoffDirichletS1 * W * Yhat * T := hFirstRaw
      _ = Real.rpow 3 fixedCutoffDirichletS1 * (W * Yhat) * T := by ring
      _ ≤ Real.rpow 3 fixedCutoffDirichletS1 *
          ((1 + W) ^ (2 : ℕ) * (1 + Yhat)) * T := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hWY
            (Real.rpow_nonneg (by norm_num) _)) hT
      _ = Real.rpow 3 fixedCutoffDirichletS1 * P := by
        dsimp only [P]
        ring
  have hDecayRaw := fixedCutoffDirichlet_decay_term_le N htheta
  have hDecay :
      Real.rpow 3
          (-fixedCutoffDirichletS2 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ)) ≤
        Real.rpow 3 fixedCutoffDirichletS2 * P := by
    calc
      _ ≤ Real.rpow 3 fixedCutoffDirichletS2 * T := hDecayRaw
      _ = Real.rpow 3 fixedCutoffDirichletS2 * 1 * T := by ring
      _ ≤ Real.rpow 3 fixedCutoffDirichletS2 *
          ((1 + W) ^ (2 : ℕ) * (1 + Yhat)) * T := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hOne
            (Real.rpow_nonneg (by norm_num) _)) hT
      _ = Real.rpow 3 fixedCutoffDirichletS2 * P := by
        dsimp only [P]
        ring
  have hSquaredRaw := fixedCutoffDirichlet_squared_response_term_le N
    htheta hE2 hResponseTwo
  have hSquared :
      Real.rpow 3
            (-fixedCutoffDirichletS2 *
              (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
          (Real.rpow 3
              (fixedCutoffDirichletS1 *
                (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
            E2 ^ (2 : ℕ)) ≤ P := by
    calc
      _ ≤ W ^ (2 : ℕ) * T := hSquaredRaw
      _ ≤ ((1 + W) ^ (2 : ℕ) * (1 + Yhat)) * T := by
        gcongr
      _ = P := by rfl
  unfold dirichletPrebalanceCore
  dsimp only [P] at hFirst hDecay hSquared ⊢
  nlinarith

/-- In the GMC implementation the energy envelope is `1 + 2 E₂`.  Thus the
same response prefactor controls it, and no separate infinite supremum over
outer scales is needed. -/
theorem fixedCutoffDirichlet_responseEnvelope_le
    {theta W E2 : ℝ} (N : ℕ)
    (htheta : 0 ≤ theta) (hW : 0 ≤ W)
    (hResponseTwo :
      E2 ≤ W * fixedCutoffDirichletResponseWeight theta N) :
    1 + 2 * E2 ≤
      (1 + 2 * W) * fixedCutoffDirichletEnergyWeight theta N := by
  have hR := fixedCutoffDirichletResponseWeight_le_one N htheta
  have hWR : W * fixedCutoffDirichletResponseWeight theta N ≤ W := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hR hW
  have hplain : 1 + 2 * E2 ≤ 1 + 2 * W := by
    linarith [hResponseTwo.trans hWR]
  have hbase : 0 ≤ 1 + 2 * W := by positivity
  exact hplain.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_fixedCutoffDirichletEnergyWeight N htheta) hbase)



theorem fixedCutoffDirichlet_prebalanceCore_le_of_response
    {theta W E1 E2 : ℝ} (N : ℕ)
    (htheta : 0 ≤ theta) (hW : 0 ≤ W) (hE2 : 0 ≤ E2)
    (hResponseOne :
      E1 ≤ W * fixedCutoffDirichletResponseWeight theta N)
    (hResponseTwo :
      E2 ≤ W * fixedCutoffDirichletResponseWeight theta N) :
    dirichletPrebalanceCore fixedCutoffDirichletS1 fixedCutoffDirichletS2
        (fixedCutoffDirichletBalanceScale theta N) E1 E2 (1 + 2 * E2) ≤
      (Real.rpow 3 fixedCutoffDirichletS1 +
          Real.rpow 3 fixedCutoffDirichletS2 + 1) *
        (1 + W) ^ (2 : ℕ) * (2 + 2 * W) *
        fixedCutoffDirichletTargetWeight theta N := by
  have hY : 0 ≤ 1 + 2 * E2 := by positivity
  have hYhat : 0 ≤ 1 + 2 * W := by positivity
  convert fixedCutoffDirichlet_prebalanceCore_le N htheta hW hYhat hE2 hY
      hResponseOne hResponseTwo
      (fixedCutoffDirichlet_responseEnvelope_le N htheta hW hResponseTwo) using 1
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
