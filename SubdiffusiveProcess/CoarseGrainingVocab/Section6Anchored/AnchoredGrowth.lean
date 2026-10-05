module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.AnchoredGrowthCore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.Convergence

@[expose] public section

/-!
# The anchored growth clauses

This is `step .5` and `step .6` of the printed proof of
`l.finite.cutoff.coefficient.convergence` (`l.finite.cutoff.coefficient.convergence`):

> Choose `δ₀(d)` small, absorb the square-root term into an arbitrarily small
> linear slope, and exponentiate.

Concretely, the deterministic core of `AnchoredGrowthCore.lean` produces, at the
dyadic index `n = dyadicIndex x` of a point (so that `2 + ‖x‖ ≤ 2ⁿ`),

* `|log ã_L(x)| ≤ C(d) δ (n+1) + C₁ + C₂ (G₁+G₂) √(n+1) / 2`,
* `|∇ log ã_L(x)| ≤ C₂ G₁ √(n+1)`, and the same for the `C^{1,1}` seminorm.

The absorption is the arithmetic–geometric inequality
`E √T ≤ ε T + E²/(4ε)` at the *deterministic* threshold `ε = log 2 / 4`; the
random `E` is thereby moved into the additive constant, leaving the slope
`C(d) δ + ε ≤ log 2 / 2` whenever `δ ≤ δ₀(d) = log 2 / (4 C(d))`.  A further
`ε` pays for the polynomial prefactor `2 + d C₂ G₁ √T` through `T ≤ ε⁻¹ e^{εT}`,
so the total slope is at most `3 log 2 / 4` and the exponentiated bound has the
deterministic exponent `κ = 3/4`.

The `√(log(2+‖x‖))` form of the frozen conclusion comes from
`GeometricSqrt.sqrt_dyadicIndex_succ_le`.

The random constant is the *measurable* `anchoredComega`, built from the two
countable-supremum envelopes of `MeasurableEnvelope.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Filter MeasureTheory Topology
open Homogenization Homogenization.IndependentSums
open _root_.SubdiffusiveProcess.Model
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Euclidean readouts of the stored derivative -/

theorem euclideanNorm_le_dim_mul_norm (u : Vec d) :
    euclideanNorm u ≤ (d : ℝ) * ‖u‖ := by
  simpa only [euclideanNorm_eq_norm_ofVec] using HilbertVec.norm_ofVec_le_mul_norm u

theorem euclideanNorm_shellGradient_le (g : PotentialField d) (x : Vec d) :
    euclideanNorm (shellGradient g x) ≤
      (d : ℝ) * ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ := by
  refine (euclideanNorm_le_dim_mul_norm (shellGradient g x)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
  rw [shellGradient_eq_gradOfCLM]
  exact norm_gradOfCLM_le _

/-! ## The deterministic constants -/

/-- The absorption threshold: a quarter of `log 2`, chosen so that two copies of
it plus the value slope stay below `3 log 2 / 4`. -/
def absorbEps : ℝ := Real.log 2 / 4

theorem absorbEps_pos : 0 < absorbEps := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [absorbEps]
  linarith

/-- The deterministic exponent of the polynomial growth clause. -/
def anchoredKappa : ℝ := 3 / 4

theorem anchoredKappa_mem : anchoredKappa ∈ Set.Ioo (0 : ℝ) 1 := by
  rw [anchoredKappa]
  constructor <;> norm_num

/-- The deterministic smallness threshold `δ₀(d)` of the printed statement. -/
def anchoredDelta0 (d : ℕ) : ℝ := Real.log 2 / (4 * valueMaximalSlope d)

theorem anchoredDelta0_pos (d : ℕ) : 0 < anchoredDelta0 d := by
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hslope := valueMaximalSlope_pos d
  rw [anchoredDelta0]
  positivity

theorem valueMaximalSlope_mul_delta_le {M : GMCModel d}
    (hdelta : M.delta ≤ anchoredDelta0 d) :
    valueMaximalSlope d * M.delta ≤ Real.log 2 / 4 := by
  have hslope := valueMaximalSlope_pos d
  have hne : valueMaximalSlope d ≠ 0 := ne_of_gt hslope
  have h := mul_le_mul_of_nonneg_left hdelta hslope.le
  rw [anchoredDelta0] at h
  have heq : valueMaximalSlope d * (Real.log 2 / (4 * valueMaximalSlope d)) =
      Real.log 2 / 4 := by
    field_simp
  rw [heq] at h
  exact h

/-! ## The two envelope shapes -/

/-- The random prefactor of the polynomial growth clause. -/
def polyEnvelopeOf (d : ℕ) (C1 C2 : ℝ) : ℝ :=
  8 * (Real.exp (C1 +
      (C2 * (gradSeriesConst + tailSeriesConst) / 2) ^ 2 / (4 * absorbEps)) *
    ((2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps))

/-- The random prefactor of the logarithmic-derivative growth clause. -/
def logEnvelopeOf (d : ℕ) (C2 : ℝ) : ℝ :=
  ((d : ℝ) + 1) * C2 * gradSeriesConst * sqrtLogConst

theorem polyEnvelopeOf_nonneg (d : ℕ) {C1 C2 : ℝ} (hC2 : 0 ≤ C2) :
    0 ≤ polyEnvelopeOf d C1 C2 := by
  have hG := gradSeriesConst_nonneg
  have heps := absorbEps_pos
  have hnum : (0 : ℝ) ≤ 2 + (d : ℝ) * C2 * gradSeriesConst := by positivity
  rw [polyEnvelopeOf]
  positivity

theorem logEnvelopeOf_nonneg (d : ℕ) {C2 : ℝ} (hC2 : 0 ≤ C2) :
    0 ≤ logEnvelopeOf d C2 := by
  have hG := gradSeriesConst_nonneg
  have hs := sqrtLogConst_nonneg
  rw [logEnvelopeOf]
  positivity

/-! ## Absorb and exponentiate -/

/-- The arithmetic–geometric absorption: a random multiple of `√T` is an
arbitrarily small *deterministic* multiple of `T` plus a random constant. -/
theorem mul_sqrt_le_absorb {E T : ℝ} (hT : 0 ≤ T) :
    E * Real.sqrt T ≤ absorbEps * T + E ^ 2 / (4 * absorbEps) := by
  have heps := absorbEps_pos
  have hr : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT
  have hr0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hkey : E * Real.sqrt T - absorbEps * (Real.sqrt T ^ 2) ≤
      E ^ 2 / (4 * absorbEps) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * absorbEps)]
    nlinarith [sq_nonneg (2 * absorbEps * Real.sqrt T - E)]
  rw [hr] at hkey
  linarith

/-- `T ≤ ε⁻¹ e^{εT}`: the polynomial prefactor is absorbed by an arbitrarily
small exponential. -/
theorem le_inv_mul_exp {T : ℝ} : T ≤ Real.exp (absorbEps * T) / absorbEps := by
  have heps := absorbEps_pos
  have h : absorbEps * T ≤ Real.exp (absorbEps * T) := by
    have := Real.add_one_le_exp (absorbEps * T)
    linarith
  rw [le_div_iff₀ heps, mul_comm]
  exact h

/-- The exponential comparison of the dyadic scale with the printed
`(1+|x|)^κ`. -/
theorem exp_mul_dyadic_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 3 * Real.log 2 / 4)
    (x : Vec d) :
    Real.exp (s * ((dyadicIndex x : ℝ) + 1)) ≤
      8 * (1 + ‖x‖) ^ anchoredKappa := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hx1 : (1 : ℝ) ≤ 2 + ‖x‖ := one_le_two_add_norm x
  have hxpos : (0 : ℝ) < 2 + ‖x‖ := lt_of_lt_of_le zero_lt_one hx1
  have hT := dyadicIndex_succ_le x
  -- push the dyadic index into a logarithm
  have hstep : s * ((dyadicIndex x : ℝ) + 1) ≤
      Real.log (2 + ‖x‖) * (s / Real.log 2) + 2 * s := by
    have := mul_le_mul_of_nonneg_left hT hs0
    calc s * ((dyadicIndex x : ℝ) + 1)
        ≤ s * (Real.log (2 + ‖x‖) / Real.log 2 + 2) := this
      _ = Real.log (2 + ‖x‖) * (s / Real.log 2) + 2 * s := by
          field_simp
  have hexp := Real.exp_le_exp.2 hstep
  rw [Real.exp_add] at hexp
  -- the first factor is the rpow
  have hrpow : Real.exp (Real.log (2 + ‖x‖) * (s / Real.log 2)) =
      (2 + ‖x‖) ^ (s / Real.log 2) := (Real.rpow_def_of_pos hxpos _).symm
  -- the exponent is below κ
  have hquot : s / Real.log 2 ≤ anchoredKappa := by
    rw [anchoredKappa, div_le_iff₀ hlog2]
    linarith
  have hmono : (2 + ‖x‖) ^ (s / Real.log 2) ≤ (2 + ‖x‖) ^ anchoredKappa :=
    Real.rpow_le_rpow_of_exponent_le hx1 hquot
  -- shift the base
  have hbase : (2 + ‖x‖) ^ anchoredKappa ≤ 2 * (1 + ‖x‖) ^ anchoredKappa := by
    have hle : 2 + ‖x‖ ≤ 2 * (1 + ‖x‖) := by
      have := norm_nonneg x
      linarith
    have h1 : (2 + ‖x‖) ^ anchoredKappa ≤ (2 * (1 + ‖x‖)) ^ anchoredKappa :=
      Real.rpow_le_rpow (by positivity) hle (by rw [anchoredKappa]; norm_num)
    have h2 : (2 * (1 + ‖x‖)) ^ anchoredKappa =
        (2 : ℝ) ^ anchoredKappa * (1 + ‖x‖) ^ anchoredKappa :=
      Real.mul_rpow (by norm_num) (by positivity)
    have h3 : (2 : ℝ) ^ anchoredKappa ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by rw [anchoredKappa]; norm_num : anchoredKappa ≤ (1 : ℝ))
      rwa [Real.rpow_one] at this
    have h4 : (0 : ℝ) ≤ (1 + ‖x‖) ^ anchoredKappa := Real.rpow_nonneg (by positivity) _
    calc (2 + ‖x‖) ^ anchoredKappa ≤ (2 * (1 + ‖x‖)) ^ anchoredKappa := h1
      _ = (2 : ℝ) ^ anchoredKappa * (1 + ‖x‖) ^ anchoredKappa := h2
      _ ≤ 2 * (1 + ‖x‖) ^ anchoredKappa :=
          mul_le_mul_of_nonneg_right h3 h4
  -- the second factor
  have hconst : Real.exp (2 * s) ≤ 4 := by
    have hle : 2 * s ≤ 2 * Real.log 2 := by linarith
    have h4 : Real.exp (2 * Real.log 2) = 4 := by
      have hlog : (2 : ℝ) * Real.log 2 = Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      rw [hlog, Real.exp_log (by norm_num)]
    calc Real.exp (2 * s) ≤ Real.exp (2 * Real.log 2) := Real.exp_le_exp.2 hle
      _ = 4 := h4
  have hnn : (0 : ℝ) ≤ (1 + ‖x‖) ^ anchoredKappa := Real.rpow_nonneg (by positivity) _
  calc Real.exp (s * ((dyadicIndex x : ℝ) + 1))
      ≤ Real.exp (Real.log (2 + ‖x‖) * (s / Real.log 2)) * Real.exp (2 * s) := hexp
    _ = (2 + ‖x‖) ^ (s / Real.log 2) * Real.exp (2 * s) := by rw [hrpow]
    _ ≤ (2 * (1 + ‖x‖) ^ anchoredKappa) * 4 := by
        refine mul_le_mul (hmono.trans hbase) hconst (Real.exp_pos _).le ?_
        linarith
    _ = 8 * (1 + ‖x‖) ^ anchoredKappa := by ring

/-- **The polynomial growth clause, exponentiated.**  The value bound and the
gradient bound at the dyadic index of `x` give the printed
`e.finite.cutoff.coefficient.polynomial.growth` with the deterministic exponent
`κ = 3/4`. -/
theorem exp_growth_bound {M : GMCModel d} (hdelta : M.delta ≤ anchoredDelta0 d)
    {C1 C2 : ℝ} (hC2 : 0 ≤ C2) {x : Vec d} {S : ℝ} {v : Vec d}
    (hS : |S| ≤ valueMaximalSlope d * M.delta * ((dyadicIndex x : ℝ) + 1) + C1 +
        C2 * (gradSeriesConst + tailSeriesConst) *
          Real.sqrt ((dyadicIndex x : ℝ) + 1) / 2)
    (hv : euclideanNorm v ≤
        (d : ℝ) * (C2 * gradSeriesConst * Real.sqrt ((dyadicIndex x : ℝ) + 1))) :
    Real.exp S + (Real.exp S)⁻¹ + euclideanNorm (Real.exp S • v) ≤
      polyEnvelopeOf d C1 C2 * (1 + ‖x‖) ^ anchoredKappa := by
  have heps := absorbEps_pos
  have hG := gradSeriesConst_nonneg
  have hH := tailSeriesConst_nonneg
  set T : ℝ := (dyadicIndex x : ℝ) + 1 with hT_def
  have hT1 : (1 : ℝ) ≤ T := one_le_natSucc_cast _
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hrT0 : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hrT : Real.sqrt T ≤ T := sqrt_le_self_of_one_le hT1
  set E : ℝ := C2 * (gradSeriesConst + tailSeriesConst) / 2 with hE_def
  have hE0 : (0 : ℝ) ≤ E := by rw [hE_def]; positivity
  set D : ℝ := C1 + E ^ 2 / (4 * absorbEps) with hD_def
  -- the absorbed value bound
  have hSabs : |S| ≤ (valueMaximalSlope d * M.delta + absorbEps) * T + D := by
    have habs := mul_sqrt_le_absorb (E := E) hT0
    have hrw : C2 * (gradSeriesConst + tailSeriesConst) * Real.sqrt T / 2 =
        E * Real.sqrt T := by rw [hE_def]; ring
    rw [hrw] at hS
    rw [hD_def]
    linarith
  -- the three terms
  have hexpS : Real.exp S ≤ Real.exp |S| := Real.exp_le_exp.2 (le_abs_self S)
  have hexpSinv : (Real.exp S)⁻¹ ≤ Real.exp |S| := by
    rw [← Real.exp_neg]
    exact Real.exp_le_exp.2 (neg_le_abs S)
  have hthird : euclideanNorm (Real.exp S • v) ≤
      Real.exp |S| * ((d : ℝ) * (C2 * gradSeriesConst * Real.sqrt T)) := by
    rw [euclideanNorm_smul, abs_of_pos (Real.exp_pos S)]
    exact mul_le_mul hexpS hv (euclideanNorm_nonneg v) (Real.exp_pos _).le
  have hsum : Real.exp S + (Real.exp S)⁻¹ + euclideanNorm (Real.exp S • v) ≤
      Real.exp |S| * (2 + (d : ℝ) * C2 * gradSeriesConst * Real.sqrt T) := by
    have hring : Real.exp |S| * (2 + (d : ℝ) * C2 * gradSeriesConst * Real.sqrt T) =
        Real.exp |S| + Real.exp |S| +
          Real.exp |S| * ((d : ℝ) * (C2 * gradSeriesConst * Real.sqrt T)) := by ring
    rw [hring]
    linarith
  -- the prefactor
  have hpre : 2 + (d : ℝ) * C2 * gradSeriesConst * Real.sqrt T ≤
      (2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps * Real.exp (absorbEps * T) := by
    have hcoef : (0 : ℝ) ≤ (d : ℝ) * C2 * gradSeriesConst := by positivity
    have h1 : 2 + (d : ℝ) * C2 * gradSeriesConst * Real.sqrt T ≤
        (2 + (d : ℝ) * C2 * gradSeriesConst) * T := by
      have := mul_le_mul_of_nonneg_left hrT hcoef
      nlinarith
    have h2 : (2 + (d : ℝ) * C2 * gradSeriesConst) * T ≤
        (2 + (d : ℝ) * C2 * gradSeriesConst) * (Real.exp (absorbEps * T) / absorbEps) :=
      mul_le_mul_of_nonneg_left le_inv_mul_exp (by linarith)
    have h3 : (2 + (d : ℝ) * C2 * gradSeriesConst) * (Real.exp (absorbEps * T) / absorbEps) =
        (2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps * Real.exp (absorbEps * T) := by
      field_simp
    linarith
  -- put the two exponentials together
  set s : ℝ := valueMaximalSlope d * M.delta + 2 * absorbEps with hs_def
  have hs0 : 0 ≤ s := by
    have := valueMaximalSlope_pos d
    have := M.shellPrefix.delta_pos
    rw [hs_def]
    positivity
  have hsle : s ≤ 3 * Real.log 2 / 4 := by
    have h := valueMaximalSlope_mul_delta_le hdelta
    rw [hs_def, absorbEps]
    linarith
  have hexpmul : Real.exp |S| * Real.exp (absorbEps * T) ≤
      Real.exp D * Real.exp (s * T) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : (valueMaximalSlope d * M.delta + absorbEps) * T + D + absorbEps * T =
        D + s * T := by rw [hs_def]; ring
    linarith [hSabs]
  have hkey : Real.exp |S| * (2 + (d : ℝ) * C2 * gradSeriesConst * Real.sqrt T) ≤
      Real.exp D * ((2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps) *
        Real.exp (s * T) := by
    have hnn : (0 : ℝ) ≤ (2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps := by
      have : (0 : ℝ) ≤ (d : ℝ) * C2 * gradSeriesConst := by positivity
      positivity
    calc Real.exp |S| * (2 + (d : ℝ) * C2 * gradSeriesConst * Real.sqrt T)
        ≤ Real.exp |S| *
            ((2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps *
              Real.exp (absorbEps * T)) :=
          mul_le_mul_of_nonneg_left hpre (Real.exp_pos _).le
      _ = (2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps *
            (Real.exp |S| * Real.exp (absorbEps * T)) := by ring
      _ ≤ (2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps *
            (Real.exp D * Real.exp (s * T)) :=
          mul_le_mul_of_nonneg_left hexpmul hnn
      _ = Real.exp D * ((2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps) *
            Real.exp (s * T) := by ring
  -- the dyadic comparison
  have hdy : Real.exp (s * T) ≤ 8 * (1 + ‖x‖) ^ anchoredKappa :=
    exp_mul_dyadic_le hs0 hsle x
  have hfac : (0 : ℝ) ≤ Real.exp D * ((2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps) := by
    have : (0 : ℝ) ≤ (d : ℝ) * C2 * gradSeriesConst := by positivity
    positivity
  calc Real.exp S + (Real.exp S)⁻¹ + euclideanNorm (Real.exp S • v)
      ≤ Real.exp |S| * (2 + (d : ℝ) * C2 * gradSeriesConst * Real.sqrt T) := hsum
    _ ≤ Real.exp D * ((2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps) *
          Real.exp (s * T) := hkey
    _ ≤ Real.exp D * ((2 + (d : ℝ) * C2 * gradSeriesConst) / absorbEps) *
          (8 * (1 + ‖x‖) ^ anchoredKappa) :=
        mul_le_mul_of_nonneg_left hdy hfac
    _ = polyEnvelopeOf d C1 C2 * (1 + ‖x‖) ^ anchoredKappa := by
        rw [polyEnvelopeOf, hD_def, hE_def]
        ring

/-- **The logarithmic-derivative growth clause.**  The frozen
`√(log(2+‖x‖))` price is the dyadic `√(n+1)` after
`sqrt_dyadicIndex_succ_le`. -/
theorem logDeriv_growth_bound {C2 : ℝ} (hC2 : 0 ≤ C2) {x : Vec d} {v : Vec d}
    {B : ℝ}
    (hv : euclideanNorm v ≤
        (d : ℝ) * (C2 * gradSeriesConst * Real.sqrt ((dyadicIndex x : ℝ) + 1)))
    (hB : B ≤ C2 * gradSeriesConst * Real.sqrt ((dyadicIndex x : ℝ) + 1)) :
    euclideanNorm v + B ≤
      logEnvelopeOf d C2 * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
  have hG := gradSeriesConst_nonneg
  have hsum : euclideanNorm v + B ≤
      ((d : ℝ) + 1) * (C2 * gradSeriesConst) *
        Real.sqrt ((dyadicIndex x : ℝ) + 1) := by
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith [hv, hB]
  refine hsum.trans ?_
  have hcoef : (0 : ℝ) ≤ ((d : ℝ) + 1) * (C2 * gradSeriesConst) := by positivity
  have hstep := mul_le_mul_of_nonneg_left (sqrt_dyadicIndex_succ_le x) hcoef
  refine hstep.trans_eq ?_
  rw [logEnvelopeOf]
  ring

/-! ## The measurable random constant -/

/-- The measurable random constant of the frozen conclusion, on the ambient
sample space. -/
def anchoredComegaBase (M : GMCModel d) (omega : PotentialSample d) : ℝ :=
  max (polyEnvelopeOf d (valueEnvelope M omega) (derivEnvelope omega))
    (logEnvelopeOf d (derivEnvelope omega))

/-- The measurable random constant of the frozen conclusion, on the anchored
carrier. -/
def anchoredComega (M : GMCModel d) (omega : AnchoredC11Sample d) : ℝ :=
  anchoredComegaBase M omega.1

theorem measurable_anchoredComegaBase (M : GMCModel d) :
    Measurable (anchoredComegaBase M) := by
  have hv := measurable_valueEnvelope M
  have hg := measurable_derivEnvelope (d := d)
  unfold anchoredComegaBase polyEnvelopeOf logEnvelopeOf
  refine Measurable.max ?_ ?_
  · refine measurable_const.mul (Measurable.mul ?_ ?_)
    · refine Real.measurable_exp.comp (hv.add ?_)
      exact Measurable.div_const
        (Measurable.pow_const (Measurable.div_const (hg.mul measurable_const) 2) 2) _
    · exact Measurable.div_const
        (measurable_const.add ((measurable_const.mul hg).mul measurable_const)) _
  · exact ((measurable_const.mul hg).mul measurable_const).mul measurable_const

theorem measurable_anchoredComega (M : GMCModel d) :
    Measurable (anchoredComega M) :=
  (measurable_anchoredComegaBase M).comp measurable_subtype_coe

theorem anchoredComegaBase_nonneg (M : GMCModel d) (omega : PotentialSample d) :
    0 ≤ anchoredComegaBase M omega :=
  le_max_of_le_right (logEnvelopeOf_nonneg d (derivEnvelope_nonneg omega))

theorem anchoredComega_nonneg (M : GMCModel d) (omega : AnchoredC11Sample d) :
    0 ≤ anchoredComega M omega :=
  anchoredComegaBase_nonneg M omega.1

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
