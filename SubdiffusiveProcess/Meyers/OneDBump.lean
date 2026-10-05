module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.ContDiff.Basic

@[expose] public section

/-! One-dimensional bump/antiderivative test functions for the `d = 1` case of the Meyers glue. -/

open MeasureTheory Set Filter Topology

noncomputable section

namespace SubdiffusiveProcess.Meyers

/-- the bump `s ↦ φ.normed (y - s)` centred at `y` -/
def bumpAt (φ : ContDiffBump (0 : ℝ)) (y : ℝ) : ℝ → ℝ := fun s => φ.normed volume (y - s)

theorem contDiff_bumpAt (φ : ContDiffBump (0 : ℝ)) (y : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (bumpAt φ y) :=
  (φ.contDiff_normed (μ := volume) (n := ⊤)).comp (contDiff_const.sub contDiff_id)

theorem bumpAt_nonneg (φ : ContDiffBump (0 : ℝ)) (y s : ℝ) : 0 ≤ bumpAt φ y s :=
  φ.nonneg_normed _

theorem integral_bumpAt (φ : ContDiffBump (0 : ℝ)) (y : ℝ) : ∫ s, bumpAt φ y s = 1 := by
  have := integral_sub_left_eq_self (fun t => φ.normed volume t) volume y
  simpa [bumpAt] using this.trans φ.integral_normed

theorem support_bumpAt_subset (φ : ContDiffBump (0 : ℝ)) (y : ℝ) :
    Function.support (bumpAt φ y) ⊆ Ioo (y - φ.rOut) (y + φ.rOut) := by
  intro s hs
  have h1 : y - s ∈ Function.support (φ.normed volume) := hs
  rw [φ.support_normed_eq] at h1
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at h1
  constructor <;> linarith [h1.1, h1.2]

theorem bumpAt_le (φ : ContDiffBump (0 : ℝ)) (y s : ℝ) : bumpAt φ y s ≤ 1 / (2 * φ.rIn) := by
  have h := φ.normed_le_div_measure_closedBall_rIn (μ := volume) (y - s)
  rw [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal (by have := φ.rIn_pos; positivity)] at h
  have e : φ.rIn + φ.rIn = 2 * φ.rIn := by ring
  simpa [bumpAt, e] using h

theorem hasCompactSupport_bumpAt (φ : ContDiffBump (0 : ℝ)) (y : ℝ) :
    HasCompactSupport (bumpAt φ y) := by
  have hsub : tsupport (bumpAt φ y) ⊆ Icc (y - φ.rOut) (y + φ.rOut) :=
    closure_minimal (fun s hs => Ioo_subset_Icc_self (support_bumpAt_subset φ y hs)) isClosed_Icc
  exact (isCompact_Icc).of_isClosed_subset isClosed_closure hsub

theorem integrable_bumpAt (φ : ContDiffBump (0 : ℝ)) (y : ℝ) : Integrable (bumpAt φ y) :=
  (contDiff_bumpAt φ y).continuous.integrable_of_hasCompactSupport (hasCompactSupport_bumpAt φ y)

end SubdiffusiveProcess.Meyers
