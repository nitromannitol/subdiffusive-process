module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.BalancedOrders
public import Mathlib.Algebra.Order.Floor.Semifield

@[expose] public section

/-!
# Fixed-cutoff Dirichlet parameters

This file records the deterministic parameter choices in the proof of
`t.fixed.cutoff.Dirichlet.algebraic`.  The probabilistic fixed-cutoff response
estimate is deliberately not assumed here: once such an estimate is supplied,
these lemmas perform the integer-scale balance without exposing that external
input in downstream theorem statements.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open Homogenization
open Homogenization.Book.Ch03.ABK26

noncomputable section

/-- The lower response order used in the fixed-cutoff proof. -/
def fixedCutoffDirichletS1 : ℝ := 1 / 2

/-- The negative-norm order used in the fixed-cutoff proof. -/
def fixedCutoffDirichletS : ℝ := 5 / 8

/-- The upper datum order used in the fixed-cutoff proof. -/
def fixedCutoffDirichletS2 : ℝ := 3 / 4

/-- The small exponent used to make the energy envelope summable. -/
def fixedCutoffDirichletEpsilon (theta : ℝ) : ℝ := theta / 100

/-- The unrounded intermediate scale in the fixed-cutoff balance. -/
def fixedCutoffDirichletBalanceArgument (theta : ℝ) (N : ℕ) : ℝ :=
  theta * (N : ℝ) /
    (2 * (fixedCutoffDirichletS1 + fixedCutoffDirichletS2))

/-- The literal integer intermediate scale from the manuscript. -/
def fixedCutoffDirichletBalanceScale (theta : ℝ) (N : ℕ) : ℕ :=
  max 1 ⌊fixedCutoffDirichletBalanceArgument theta N⌋₊

theorem fixedCutoffDirichlet_parameter_orders :
    0 < fixedCutoffDirichletS1 ∧
      fixedCutoffDirichletS1 < fixedCutoffDirichletS ∧
      fixedCutoffDirichletS < fixedCutoffDirichletS2 ∧
      fixedCutoffDirichletS2 < 1 := by
  unfold fixedCutoffDirichletS1 fixedCutoffDirichletS fixedCutoffDirichletS2
  norm_num

/-- The fixed lower response order as a `FractionalOrder`. -/
def fixedCutoffDirichletS1Order : FractionalOrder :=
  ⟨fixedCutoffDirichletS1,
    fixedCutoffDirichlet_parameter_orders.1,
    fixedCutoffDirichlet_parameter_orders.2.1.trans
      (fixedCutoffDirichlet_parameter_orders.2.2.1.trans
        fixedCutoffDirichlet_parameter_orders.2.2.2)⟩

/-- The fixed negative-norm order as a `FractionalOrder`. -/
def fixedCutoffDirichletSOrder : FractionalOrder :=
  ⟨fixedCutoffDirichletS,
    fixedCutoffDirichlet_parameter_orders.1.trans
      fixedCutoffDirichlet_parameter_orders.2.1,
    fixedCutoffDirichlet_parameter_orders.2.2.1.trans
      fixedCutoffDirichlet_parameter_orders.2.2.2⟩

/-- The fixed upper datum order as a `FractionalOrder`. -/
def fixedCutoffDirichletS2Order : FractionalOrder :=
  ⟨fixedCutoffDirichletS2,
    fixedCutoffDirichlet_parameter_orders.1.trans
      (fixedCutoffDirichlet_parameter_orders.2.1.trans
        fixedCutoffDirichlet_parameter_orders.2.2.1),
    fixedCutoffDirichlet_parameter_orders.2.2.2⟩

@[simp] theorem fixedCutoffDirichletS1Order_coe :
    (fixedCutoffDirichletS1Order : ℝ) = fixedCutoffDirichletS1 := rfl

@[simp] theorem fixedCutoffDirichletSOrder_coe :
    (fixedCutoffDirichletSOrder : ℝ) = fixedCutoffDirichletS := rfl

@[simp] theorem fixedCutoffDirichletS2Order_coe :
    (fixedCutoffDirichletS2Order : ℝ) = fixedCutoffDirichletS2 := rfl

theorem fixedCutoffDirichletS1Order_lt_fixedCutoffDirichletSOrder :
    (fixedCutoffDirichletS1Order : ℝ) <
      (fixedCutoffDirichletSOrder : ℝ) :=
  fixedCutoffDirichlet_parameter_orders.2.1

theorem fixedCutoffDirichletSOrder_lt_fixedCutoffDirichletS2Order :
    (fixedCutoffDirichletSOrder : ℝ) <
      (fixedCutoffDirichletS2Order : ℝ) :=
  fixedCutoffDirichlet_parameter_orders.2.2.1

theorem fixedCutoffDirichletBalanceScale_pos (theta : ℝ) (N : ℕ) :
    0 < fixedCutoffDirichletBalanceScale theta N := by
  simp [fixedCutoffDirichletBalanceScale]

theorem fixedCutoffDirichletBalanceArgument_nonneg {theta : ℝ} (N : ℕ)
    (htheta : 0 ≤ theta) :
    0 ≤ fixedCutoffDirichletBalanceArgument theta N := by
  unfold fixedCutoffDirichletBalanceArgument fixedCutoffDirichletS1
    fixedCutoffDirichletS2
  positivity

@[simp] theorem fixedCutoffDirichletBalanceArgument_eq
    (theta : ℝ) (N : ℕ) :
    fixedCutoffDirichletBalanceArgument theta N =
      (2 / 5 : ℝ) * theta * (N : ℝ) := by
  unfold fixedCutoffDirichletBalanceArgument fixedCutoffDirichletS1
    fixedCutoffDirichletS2
  ring

theorem fixedCutoffDirichletBalanceScale_le_argument_add_one
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    (fixedCutoffDirichletBalanceScale theta N : ℝ) ≤
      fixedCutoffDirichletBalanceArgument theta N + 1 := by
  have harg : 0 ≤ fixedCutoffDirichletBalanceArgument theta N :=
    fixedCutoffDirichletBalanceArgument_nonneg N htheta
  have hfloor : (⌊fixedCutoffDirichletBalanceArgument theta N⌋₊ : ℝ) ≤
      fixedCutoffDirichletBalanceArgument theta N :=
    Nat.floor_le harg
  rw [fixedCutoffDirichletBalanceScale, Nat.cast_max]
  apply max_le
  · norm_num
    simpa using harg
  · exact hfloor.trans (le_add_of_nonneg_right (by norm_num))

theorem fixedCutoffDirichletBalanceArgument_lt_scale_add_one
    (theta : ℝ) (N : ℕ) :
    fixedCutoffDirichletBalanceArgument theta N <
      (fixedCutoffDirichletBalanceScale theta N : ℝ) + 1 := by
  have hfloor := Nat.lt_floor_add_one
    (fixedCutoffDirichletBalanceArgument theta N)
  have hle : ⌊fixedCutoffDirichletBalanceArgument theta N⌋₊ ≤
      fixedCutoffDirichletBalanceScale theta N := by
    exact Nat.le_max_right _ _
  have hleReal : (⌊fixedCutoffDirichletBalanceArgument theta N⌋₊ : ℝ) ≤
      (fixedCutoffDirichletBalanceScale theta N : ℝ) := by
    exact_mod_cast hle
  linarith

/-- The growing response branch retains at least a quarter of the input
algebraic exponent after the integer balance. -/
theorem fixedCutoffDirichlet_growth_exponent_le
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    fixedCutoffDirichletS1 *
          (fixedCutoffDirichletBalanceScale theta N : ℝ) -
        theta * (N : ℝ) / 2 ≤
      -theta * (N : ℝ) / 4 + fixedCutoffDirichletS1 := by
  have hk := fixedCutoffDirichletBalanceScale_le_argument_add_one N htheta
  rw [fixedCutoffDirichletBalanceArgument_eq] at hk
  unfold fixedCutoffDirichletS1
  have hN : 0 ≤ theta * (N : ℝ) := mul_nonneg htheta (Nat.cast_nonneg N)
  nlinarith

/-- The energy-envelope weight `theta / 100` still leaves the printed
quarter-exponent after balancing. -/
theorem fixedCutoffDirichlet_growth_energy_exponent_le
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    fixedCutoffDirichletS1 *
          (fixedCutoffDirichletBalanceScale theta N : ℝ) -
        theta * (N : ℝ) / 2 +
        fixedCutoffDirichletEpsilon theta * (N : ℝ) ≤
      -theta * (N : ℝ) / 4 + fixedCutoffDirichletS1 := by
  have hk := fixedCutoffDirichletBalanceScale_le_argument_add_one N htheta
  rw [fixedCutoffDirichletBalanceArgument_eq] at hk
  unfold fixedCutoffDirichletS1 fixedCutoffDirichletEpsilon
  have hN : 0 ≤ theta * (N : ℝ) := mul_nonneg htheta (Nat.cast_nonneg N)
  nlinarith

/-- The decaying branch retains at least a quarter of the input algebraic
exponent after the integer balance. -/
theorem fixedCutoffDirichlet_decay_exponent_le
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    -fixedCutoffDirichletS2 *
        (fixedCutoffDirichletBalanceScale theta N : ℝ) ≤
      -theta * (N : ℝ) / 4 + fixedCutoffDirichletS2 := by
  have hk := fixedCutoffDirichletBalanceArgument_lt_scale_add_one theta N
  rw [fixedCutoffDirichletBalanceArgument_eq] at hk
  unfold fixedCutoffDirichletS2
  have hN : 0 ≤ theta * (N : ℝ) := mul_nonneg htheta (Nat.cast_nonneg N)
  nlinarith

/-- The response-squared branch has more decay than the quarter-exponent
required in the final theorem. -/
theorem fixedCutoffDirichlet_squared_exponent_le
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    (fixedCutoffDirichletS1 - fixedCutoffDirichletS2) *
          (fixedCutoffDirichletBalanceScale theta N : ℝ) -
        theta * (N : ℝ) ≤
      -theta * (N : ℝ) / 4 := by
  have hk : (0 : ℝ) ≤ fixedCutoffDirichletBalanceScale theta N := by
    positivity
  have hN : 0 ≤ theta * (N : ℝ) := mul_nonneg htheta (Nat.cast_nonneg N)
  unfold fixedCutoffDirichletS1 fixedCutoffDirichletS2
  nlinarith

theorem fixedCutoffDirichlet_growth_power_le
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    Real.rpow 3
          (fixedCutoffDirichletS1 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
        Real.rpow 3 (-theta * (N : ℝ) / 2) ≤
      Real.rpow 3 fixedCutoffDirichletS1 *
        Real.rpow 3 (-theta * (N : ℝ) / 4) := by
  change (3 : ℝ) ^
        (fixedCutoffDirichletS1 *
          (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
      (3 : ℝ) ^ (-theta * (N : ℝ) / 2) ≤
    (3 : ℝ) ^ fixedCutoffDirichletS1 *
      (3 : ℝ) ^ (-theta * (N : ℝ) / 4)
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (by
      convert fixedCutoffDirichlet_growth_exponent_le N htheta using 1 <;> ring)

theorem fixedCutoffDirichlet_growth_energy_power_le
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    Real.rpow 3
        (fixedCutoffDirichletS1 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ) -
          theta * (N : ℝ) / 2 +
          fixedCutoffDirichletEpsilon theta * (N : ℝ)) ≤
      Real.rpow 3 fixedCutoffDirichletS1 *
        Real.rpow 3 (-theta * (N : ℝ) / 4) := by
  change (3 : ℝ) ^
      (fixedCutoffDirichletS1 *
          (fixedCutoffDirichletBalanceScale theta N : ℝ) -
        theta * (N : ℝ) / 2 +
        fixedCutoffDirichletEpsilon theta * (N : ℝ)) ≤
    (3 : ℝ) ^ fixedCutoffDirichletS1 *
      (3 : ℝ) ^ (-theta * (N : ℝ) / 4)
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (by
      simpa [add_comm] using
        fixedCutoffDirichlet_growth_energy_exponent_le N htheta)

theorem fixedCutoffDirichlet_decay_power_le
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    Real.rpow 3
        (-fixedCutoffDirichletS2 *
          (fixedCutoffDirichletBalanceScale theta N : ℝ)) ≤
      Real.rpow 3 fixedCutoffDirichletS2 *
        Real.rpow 3 (-theta * (N : ℝ) / 4) := by
  change (3 : ℝ) ^
      (-fixedCutoffDirichletS2 *
        (fixedCutoffDirichletBalanceScale theta N : ℝ)) ≤
    (3 : ℝ) ^ fixedCutoffDirichletS2 *
      (3 : ℝ) ^ (-theta * (N : ℝ) / 4)
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (by
      simpa [add_comm] using
        fixedCutoffDirichlet_decay_exponent_le N htheta)

theorem fixedCutoffDirichlet_squared_power_le
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    Real.rpow 3
        ((fixedCutoffDirichletS1 - fixedCutoffDirichletS2) *
            (fixedCutoffDirichletBalanceScale theta N : ℝ) -
          theta * (N : ℝ)) ≤
      Real.rpow 3 (-theta * (N : ℝ) / 4) := by
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (fixedCutoffDirichlet_squared_exponent_le N htheta)

theorem fixedCutoffDirichlet_squared_branch_power_le
    {theta : ℝ} (N : ℕ) (htheta : 0 ≤ theta) :
    Real.rpow 3
          (-fixedCutoffDirichletS2 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
        (Real.rpow 3
            (fixedCutoffDirichletS1 *
              (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
          Real.rpow 3 (-theta * (N : ℝ) / 2) ^ (2 : ℕ)) ≤
      Real.rpow 3 (-theta * (N : ℝ) / 4) := by
  change (3 : ℝ) ^
        (-fixedCutoffDirichletS2 *
          (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
      ((3 : ℝ) ^
          (fixedCutoffDirichletS1 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ)) *
        ((3 : ℝ) ^ (-theta * (N : ℝ) / 2)) ^ (2 : ℕ)) ≤
    (3 : ℝ) ^ (-theta * (N : ℝ) / 4)
  rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hexponent :
      -fixedCutoffDirichletS2 *
            (fixedCutoffDirichletBalanceScale theta N : ℝ) +
          (fixedCutoffDirichletS1 *
              (fixedCutoffDirichletBalanceScale theta N : ℝ) +
            (-theta * (N : ℝ) / 2 + -theta * (N : ℝ) / 2)) =
        (fixedCutoffDirichletS1 - fixedCutoffDirichletS2) *
            (fixedCutoffDirichletBalanceScale theta N : ℝ) -
          theta * (N : ℝ) := by
    ring
  rw [hexponent]
  exact fixedCutoffDirichlet_squared_power_le N htheta

theorem fixedCutoffDirichletTargetWeight_eq_gap
    {theta : ℝ} {L N : ℕ} (hLN : L ≤ N) :
    Real.rpow 3 (-theta * ((N - L : ℕ) : ℝ) / 4) =
      Real.rpow 3 (-(theta / 4) * ((N : ℝ) - (L : ℝ))) := by
  congr 1
  rw [Nat.cast_sub hLN]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
