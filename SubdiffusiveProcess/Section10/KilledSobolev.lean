module

public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Analysis.FractionalCellVariance

@[expose] public section




open MeasureTheory Set Homogenization SubdiffusiveProcess
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- The source exponent for killed Sobolev, torsion and Nash. -/
def killedSobolevExponent (d : ℕ) : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 1)

lemma killedSobolevExponent_ge_two {d : ℕ} (hd : 2 ≤ d) :
    2 ≤ killedSobolevExponent d := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  unfold killedSobolevExponent
  rw [le_div_iff₀ (by linarith : 0 < (d : ℝ) - 1)]
  linarith

lemma killedSobolev_trace_margin {d : ℕ} (hd : 2 ≤ d) :
    (d : ℝ) / 2 - ((d : ℝ) - 1 / 2) / killedSobolevExponent d < 3 / 4 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have heq : (d : ℝ) / 2 - ((d : ℝ) - 1 / 2) / killedSobolevExponent d =
      3 / 4 - 1 / (4 * (d : ℝ)) := by
    unfold killedSobolevExponent
    field_simp
    ring
  rw [heq]
  have : 0 < 1 / (4 * (d : ℝ)) := by positivity
  linarith

/-- The raw fractional square integral in the existing static estimates. -/
def killedFractionalEnergy {d : ℕ} (V : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in V, ∫⁻ y in V, ENNReal.ofReal ((f x - f y) ^ 2) /
    ENNReal.ofReal (‖x - y‖ ^ ((d : ℝ) + 3 / 2))

/-- Extended nonnegative coefficient energy, before any real-integral conversion. -/
def killedCoefficientEnergy {d : ℕ} (A : SpatialCoordinates d → ℝ)
    {V : Set (SpatialCoordinates d)} (v : H1Function V) : ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal (A x * vecDot (v.grad x) (v.grad x))

/-- Exact existing general-p trace header specialized only in sigma and t. -/
def KilledTraceBound (d : ℕ) (r0 C : ℝ) : Prop :=
  ∀ (V : Set (SpatialCoordinates d)) (ν : Measure (SpatialCoordinates d))
    (Km : ℝ), 0 < Km → IsFiniteMeasure ν → MeasurableSet V → ν ≪ volume →
    ν {x | ¬ Metric.closedBall x r0 ⊆ V} = 0 →
    (∀ y ∈ V, ∀ r : ℝ, 0 < r → r ≤ r0 →
      ν (Metric.ball y r) ≤ ENNReal.ofReal (Km * r ^ ((d : ℝ) - 1 / 2))) →
    ∀ f : SpatialCoordinates d → ℝ, Measurable f → MemLp f 2 (volume.restrict V) →
      eLpNorm f (ENNReal.ofReal (killedSobolevExponent d)) ν ≤
        ENNReal.ofReal C *
          (ENNReal.ofReal (Km ^ (1 / killedSobolevExponent d)) *
              killedFractionalEnergy V f ^ (1 / 2 : ℝ) +
            ν univ ^ (1 / killedSobolevExponent d) *
              ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) *
                eLpNorm f 2 (volume.restrict V))

/-- Explicit dependence on the growth, total mass, trace and coercivity constants. -/
def killedSobolevConstant (d : ℕ) (r0 C Km mass Kc : ℝ) : ℝ :=
  (C * (Km ^ (1 / killedSobolevExponent d) +
    mass ^ (1 / killedSobolevExponent d) * r0 ^ (-((d : ℝ) / 2)))) ^ 2 * Kc

lemma killedFractionalEnergy_congr_ae {d : ℕ} {V : Set (SpatialCoordinates d)}
    {f g : SpatialCoordinates d → ℝ} (hfg : f =ᵐ[volume.restrict V] g) :
    killedFractionalEnergy V f = killedFractionalEnergy V g := by
  apply lintegral_congr_ae
  filter_upwards [hfg] with x hx
  apply lintegral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hx, hy]

lemma killedCoefficientEnergy_extendByZero {d : ℕ}
    {U V : Set (SpatialCoordinates d)} (hU : MeasurableSet U)
    (hV : IsOpen V) (hUV : U ⊆ V) (A : SpatialCoordinates d → ℝ)
    (v : H10Function U) :
    killedCoefficientEnergy A (v.extendByZeroToOpenSuperset hU hV hUV).toH1Function =
      killedCoefficientEnergy A v.toH1Function := by
  have heq : (fun x => ENNReal.ofReal
      (A x * vecDot (v.zeroExtensionGrad x) (v.zeroExtensionGrad x))) =
      U.indicator (fun x => ENNReal.ofReal (A x * vecDot (v.grad x) (v.grad x))) := by
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, H10Function.zeroExtensionGrad_apply_of_mem v hx]
    · rw [indicator_of_notMem hx, H10Function.zeroExtensionGrad_apply_of_not_mem v hx]
      simp only [vecDot_zero_left, mul_zero, ENNReal.ofReal_zero]
  change (∫⁻ x in V, ENNReal.ofReal
    (A x * vecDot (v.zeroExtensionGrad x) (v.zeroExtensionGrad x))) = _
  rw [heq, lintegral_indicator hU, Measure.restrict_restrict_of_subset hUV]
  rfl

/-- Every native zero extension has a globally measurable representative. Its
fractional energy, volume L2 norm and weighted Lp norm are independent of the
choice of representative. -/
theorem killed_sobolev_all_h10 {d : ℕ} (hd : 2 ≤ d)
    {U V : Set (SpatialCoordinates d)} (hU : MeasurableSet U) (hV : IsOpen V)
    (hUV : U ⊆ V) (μ : Measure (SpatialCoordinates d))
    (hμ : μ ≪ volume) [IsFiniteMeasure (μ.restrict U)]
    {r0 C Km Kc : ℝ} (hr0 : 0 < r0) (hC : 0 ≤ C) (hKm : 0 < Km) (hKc : 0 ≤ Kc)
    (htrace : KilledTraceBound d r0 C)
    (hsupport : (μ.restrict U) {x | ¬ Metric.closedBall x r0 ⊆ V} = 0)
    (hgrowth : ∀ y ∈ V, ∀ r : ℝ, 0 < r → r ≤ r0 →
      (μ.restrict U) (Metric.ball y r) ≤ ENNReal.ofReal (Km * r ^ ((d : ℝ) - 1 / 2)))
    (A : SpatialCoordinates d → ℝ)
    (hcoer : ∀ w : H10Function V,
      killedFractionalEnergy V w.toFun + ∫⁻ x in V, ENNReal.ofReal (w.toFun x ^ 2) ≤
        ENNReal.ofReal Kc * killedCoefficientEnergy A w.toH1Function)
    (v : H10Function U) :
    eLpNorm v.toFun (ENNReal.ofReal (killedSobolevExponent d)) (μ.restrict U) ^ 2 ≤
      ENNReal.ofReal (killedSobolevConstant d r0 C Km ((μ.restrict U) univ).toReal Kc) *
        killedCoefficientEnergy A v.toH1Function := by
  have hp0 : 0 < killedSobolevExponent d := lt_of_lt_of_le (by norm_num) (killedSobolevExponent_ge_two hd)
  let w := v.extendByZeroToOpenSuperset hU hV hUV
  let hf := w.toH1Function.memL2
  let f := hf.aestronglyMeasurable.mk w.toFun
  have hfm : Measurable f := hf.aestronglyMeasurable.measurable_mk
  have hwf : w.toFun =ᵐ[volume.restrict V] f := hf.aestronglyMeasurable.ae_eq_mk
  have hfL : MemLp f 2 (volume.restrict V) := (memLp_congr_ae hwf).mp hf
  have hνV : μ.restrict U ≪ volume.restrict V :=
    (hμ.restrict U).trans (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set volume hUV))
  have hwfν : w.toFun =ᵐ[μ.restrict U] f := hνV.ae_le hwf
  have hvw : v.toFun =ᵐ[μ.restrict U] w.toFun := by
    filter_upwards [ae_restrict_mem hU] with x hx
    exact (v.zeroExtension_apply_of_mem hx).symm
  have hLp : eLpNorm v.toFun (ENNReal.ofReal (killedSobolevExponent d)) (μ.restrict U) =
      eLpNorm f (ENNReal.ofReal (killedSobolevExponent d)) (μ.restrict U) :=
    eLpNorm_congr_ae (hvw.trans hwfν)
  have hG : killedFractionalEnergy V f = killedFractionalEnergy V w.toFun :=
    killedFractionalEnergy_congr_ae hwf.symm
  have hL : eLpNorm f 2 (volume.restrict V) ^ 2 =
      ∫⁻ x in V, ENNReal.ofReal (w.toFun x ^ 2) := by
    rw [← eLpNorm_congr_ae hwf]
    exact eLpNorm_two_sq_eq_lintegral_sq_of_aestronglyMeasurable _ _
      w.toH1Function.memL2.aestronglyMeasurable
  let S := killedFractionalEnergy V w.toFun +
    ∫⁻ x in V, ENNReal.ofReal (w.toFun x ^ 2)
  have hGS : killedFractionalEnergy V f ≤ S := by rw [hG]; exact le_self_add
  have hLS : eLpNorm f 2 (volume.restrict V) ≤ S ^ (1 / 2 : ℝ) := by
    have h := ENNReal.rpow_le_rpow (show eLpNorm f 2 (volume.restrict V) ^ 2 ≤ S from
      hL ▸ le_add_self) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h
    norm_num at h
    exact h
  have hmass : (μ.restrict U) univ ^ (1 / killedSobolevExponent d) =
      ENNReal.ofReal (((μ.restrict U) univ).toReal ^ (1 / killedSobolevExponent d)) := by
    calc
      _ = (ENNReal.ofReal (((μ.restrict U) univ).toReal)) ^ (1 / killedSobolevExponent d) :=
        congrArg (fun z : ℝ≥0∞ => z ^ (1 / killedSobolevExponent d))
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = _ := by rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity)]
  let L : ℝ := C * (Km ^ (1 / killedSobolevExponent d) +
    ((μ.restrict U) univ).toReal ^ (1 / killedSobolevExponent d) * r0 ^ (-((d : ℝ) / 2)))
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hbound : eLpNorm f (ENNReal.ofReal (killedSobolevExponent d)) (μ.restrict U) ≤
      ENNReal.ofReal L * S ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ _ := htrace V (μ.restrict U) Km hKm inferInstance hV.measurableSet
        (Measure.absolutelyContinuous_restrict.trans hμ) hsupport hgrowth f hfm hfL
      _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal (Km ^ (1 / killedSobolevExponent d)) * S ^ (1 / 2 : ℝ) +
            (μ.restrict U) univ ^ (1 / killedSobolevExponent d) *
              ENNReal.ofReal (r0 ^ (-((d : ℝ) / 2))) * S ^ (1 / 2 : ℝ)) := by
        gcongr

      _ = _ := by
        rw [hmass, ← ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _), ← add_mul,
          ← ENNReal.ofReal_add (Real.rpow_nonneg hKm.le _) (by positivity), ← mul_assoc,
          ← ENNReal.ofReal_mul hC]
  rw [hLp]
  calc
    _ ≤ (ENNReal.ofReal L * S ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left' hbound 2
    _ = ENNReal.ofReal (L ^ 2) * S := by
      rw [mul_pow, ← ENNReal.ofReal_pow hL0, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ ENNReal.ofReal (L ^ 2) * (ENNReal.ofReal Kc *
        killedCoefficientEnergy A w.toH1Function) := mul_le_mul_right (hcoer w) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul' hKc,
        killedCoefficientEnergy_extendByZero hU hV hUV]
      rfl

end SubdiffusiveProcess.Section10
