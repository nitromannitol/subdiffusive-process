import SubdiffusiveProcess.Frozen.Assumptions.TauSq
import SubdiffusiveProcess.Frozen.Assumptions.GMCModel




set_option autoImplicit false

open SubdiffusiveProcess.Frozen.Assumptions

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
