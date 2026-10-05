module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyScaleTransfer

@[expose] public section

/-!
# Exponential bookkeeping for row 2's two legs

Every prefactor row 2 accumulates — the Campanato exponential, the two
coefficient-ratio exponentials and the two window-volume prices — is of the
shape `exp (c + p * lambda * (gap + 1))`, which is exactly the shape
`Section6Holder.exists_holderExponentialAbsorption` converts into a fraction of
the frozen gap gain `3^{(1-alpha)(m-n)}`.

This module collects the three pieces of bookkeeping that conversion needs: the
multiplicative combinator, the conversion of a triadic window price into
exponential form, and the abstract form of the oscillation leg (family estimate
times the Step-6 square root of the coefficient average).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

/-- Products of nonnegative factors add exponents. -/
theorem mul_le_exp_add {X Y a b : ℝ} (hY0 : 0 ≤ Y)
    (hX : X ≤ Real.exp a) (hY : Y ≤ Real.exp b) : X * Y ≤ Real.exp (a + b) := by
  rw [Real.exp_add]
  exact mul_le_mul hX hY hY0 (Real.exp_nonneg a)

/-- Weakening an exponential bound: a larger constant and a larger rate. -/
theorem le_exp_mono {X c c' p p' w : ℝ} (hw : 0 ≤ w)
    (hX : X ≤ Real.exp (c + p * w)) (hc : c ≤ c') (hp : p ≤ p') :
    X ≤ Real.exp (c' + p' * w) := by
  refine hX.trans (Real.exp_le_exp.mpr ?_)
  have : p * w ≤ p' * w := mul_le_mul_of_nonneg_right hp hw
  linarith

/-- A triadic power in exponential form. -/
theorem zpow_three_le_exp {j : ℤ} {t : ℝ} (h : (j : ℝ) * Real.log 3 ≤ t) :
    (3 : ℝ) ^ j ≤ Real.exp t := by
  have heq : (3 : ℝ) ^ j = Real.exp ((j : ℝ) * Real.log 3) := by
    rw [← Real.rpow_intCast (3 : ℝ) j,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  rw [heq]
  exact Real.exp_le_exp.mpr h

/-- **The window-volume price in exponential form.** -/
theorem scaleTransferPrice_le_exp (d : ℕ) {j : ℤ} {t : ℝ} (hj : -2 ≤ j)
    (h : ((j : ℝ) + 2) * (d : ℝ) * Real.log 3 ≤ t) :
    scaleTransferPrice d j ≤ Real.exp t := by
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ (j + 2) := by
    have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
      (show (0 : ℤ) ≤ j + 2 by omega)
    simpa using this
  have hY : (1 : ℝ) ≤ ((3 : ℝ) ^ (j + 2)) ^ d := one_le_pow₀ h3
  have hsq : Real.sqrt (((3 : ℝ) ^ (j + 2)) ^ d) ≤ ((3 : ℝ) ^ (j + 2)) ^ d := by
    have hmul : ((3 : ℝ) ^ (j + 2)) ^ d ≤
        ((3 : ℝ) ^ (j + 2)) ^ d * ((3 : ℝ) ^ (j + 2)) ^ d := by
      nlinarith [hY]
    have := Real.sqrt_le_sqrt hmul
    rwa [Real.sqrt_mul_self (by linarith : (0 : ℝ) ≤ ((3 : ℝ) ^ (j + 2)) ^ d)]
      at this
  have heq : ((3 : ℝ) ^ (j + 2)) ^ d = (3 : ℝ) ^ ((j + 2) * (d : ℤ)) := by
    rw [← zpow_natCast ((3 : ℝ) ^ (j + 2)) d, ← zpow_mul]
  rw [scaleTransferPrice]
  refine hsq.trans ?_
  rw [heq]
  refine zpow_three_le_exp ?_
  push_cast
  linarith [h]

/-- **The oscillation leg, as arithmetic.**  The composed family estimate
`hfam` is multiplied by the nonnegative square root `S` of the Step-6
coefficient average; the top window goes to the global energy `Eg` and the
family's defect budget to the datum `Da`. -/
theorem rowTwo_oscLeg_arith {price E1 S OscX OscTop D Ktop Kdat Eg Da : ℝ}
    {gate top : ℤ} (hprice : 0 ≤ price) (hE1 : 0 ≤ E1) (hS : 0 ≤ S)
    (hfam : (3 : ℝ) ^ (-gate) * OscX ≤
      price * (E1 * ((3 : ℝ) ^ (-top) * OscTop + D)))
    (htop : S * ((3 : ℝ) ^ (-top) * OscTop) ≤ Ktop * Eg)
    (hD : S * D ≤ Kdat * Da)
    (hKtop : 0 ≤ Ktop) (hKdat : 0 ≤ Kdat) (hEg : 0 ≤ Eg) (hDa : 0 ≤ Da) :
    S * ((3 : ℝ) ^ (-gate) * OscX) ≤
      price * E1 * ((Ktop + Kdat) * (Eg + Da)) := by
  have hpe : 0 ≤ price * E1 := mul_nonneg hprice hE1
  have hstep1 : S * ((3 : ℝ) ^ (-gate) * OscX) ≤
      price * E1 * (S * ((3 : ℝ) ^ (-top) * OscTop) + S * D) := by
    have := mul_le_mul_of_nonneg_left hfam hS
    calc S * ((3 : ℝ) ^ (-gate) * OscX)
        ≤ S * (price * (E1 * ((3 : ℝ) ^ (-top) * OscTop + D))) := this
      _ = price * E1 * (S * ((3 : ℝ) ^ (-top) * OscTop) + S * D) := by ring
  refine hstep1.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hpe
  have h1 : Ktop * Eg ≤ (Ktop + Kdat) * Eg :=
    mul_le_mul_of_nonneg_right (by linarith) hEg
  have h2 : Kdat * Da ≤ (Ktop + Kdat) * Da :=
    mul_le_mul_of_nonneg_right (by linarith) hDa
  calc S * ((3 : ℝ) ^ (-top) * OscTop) + S * D ≤ Ktop * Eg + Kdat * Da :=
        add_le_add htop hD
    _ ≤ (Ktop + Kdat) * Eg + (Ktop + Kdat) * Da := add_le_add h1 h2
    _ = (Ktop + Kdat) * (Eg + Da) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
