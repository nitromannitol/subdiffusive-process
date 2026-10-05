module

public import SubdiffusiveProcess.Model.TauSq
public import SubdiffusiveProcess.Model.GMCModel

@[expose] public section

/-!
# The walk-dimension exponents `beta_0`, `beta_-`, `beta_+`

For a
sufficiently large `C_0(d) < ∞`,

    beta_0 := 2 + 2 tau^2 / (d log 3)

    beta_- := d_w                                              if d = 2
              max {2 + eta_sub, beta_0 - C_0 delta^3 |log delta|}   if d >= 3

    beta_+ := d_w                                              if d = 2
              beta_0 + C_0 delta^3 |log delta|                 if d >= 3

and in `d = 2` the walk dimension is `d_w = 2 + tau^2 / log 3` exactly, with
`eta_sub = tau^2 / log 3` (`SubdiffusiveProcess/MainTheorems.lean`, Theorem A).

These exponents are what the two off-diagonal heat-kernel bounds of Section 10
 are stated
in terms of these exponents. `C_0` is left as an explicit parameter rather than fixed, exactly as the
source leaves it ("for a sufficiently large `C_0(d)`"); a statement that needs it large
must quantify it.

The companion object `Phi_F`  is defined, as
`SubdiffusiveProcess.Frozen.Section7.intrinsicOffDiagonalRate`.
-/

set_option autoImplicit false

open _root_.SubdiffusiveProcess.Model

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Exponents

variable {d : ℕ}

/-- The exact two-dimensional walk dimension, `d_w = 2 + tau^2 / log 3`. -/
def walkDimensionTwo (M : GMCModel d) : ℝ :=
  2 + tauSq M.P / Real.log 3

/-- The subdiffusivity exponent, `eta_sub = tau^2 / log 3` in `d = 2`. -/
def etaSubTwo (M : GMCModel d) : ℝ :=
  tauSq M.P / Real.log 3

/-- `beta_0 = 2 + 2 tau^2 / (d log 3)`. -/
def betaZero (M : GMCModel d) : ℝ :=
  2 + 2 * tauSq M.P / ((d : ℝ) * Real.log 3)

/-- `beta_-`, the lower walk-dimension exponent. -/
def betaMinus (C0 : ℝ) (M : GMCModel d) (etaSub : ℝ) : ℝ :=
  if d = 2 then walkDimensionTwo M
  else max (2 + etaSub) (betaZero M - C0 * M.delta ^ 3 * |Real.log M.delta|)

/-- `beta_+`, the upper walk-dimension exponent. -/
def betaPlus (C0 : ℝ) (M : GMCModel d) : ℝ :=
  if d = 2 then walkDimensionTwo M
  else betaZero M + C0 * M.delta ^ 3 * |Real.log M.delta|

@[simp] theorem betaMinus_two (C0 : ℝ) (M : GMCModel 2) (etaSub : ℝ) :
    betaMinus C0 M etaSub = walkDimensionTwo M := by
  simp [betaMinus]

@[simp] theorem betaPlus_two (C0 : ℝ) (M : GMCModel 2) :
    betaPlus C0 M = walkDimensionTwo M := by
  simp [betaPlus]

/-- In two dimensions the two exponents coincide, which is the exact `d = 2` statement
of Theorem A. -/
theorem betaMinus_eq_betaPlus_two (C0 : ℝ) (M : GMCModel 2) (etaSub : ℝ) :
    betaMinus C0 M etaSub = betaPlus C0 M := by
  simp

/-- In two dimensions the walk dimension is `2 + eta_sub`. -/
theorem walkDimensionTwo_eq (M : GMCModel d) :
    walkDimensionTwo M = 2 + etaSubTwo M := rfl

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Exponents
