module

public import SubdiffusiveProcess.Static.Comparison
public import SubdiffusiveProcess.Main.InfraredAdmissible
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

/-! # Comparing admissible infrared factors

The comparison envelope has moments uniform in both admissible fields. In
particular its bound is independent of either infrared truncation index.
-/

open MeasureTheory TopologicalSpace SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Cauchy--Schwarz for a real moment of a product of nonnegative functions. -/
theorem product_moment_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) (p : ℝ) :
    (∫⁻ ω, ENNReal.ofReal ((f ω * g ω) ^ p) ∂μ) ≤
      (∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * p)) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ENNReal.ofReal (g ω ^ (2 * p)) ∂μ) ^ (1 / 2 : ℝ) := by
  have hF : AEMeasurable (fun ω => ENNReal.ofReal (f ω ^ p)) μ :=
    (ENNReal.measurable_ofReal.comp (hf.pow_const p)).aemeasurable
  have hG : AEMeasurable (fun ω => ENNReal.ofReal (g ω ^ p)) μ :=
    (ENNReal.measurable_ofReal.comp (hg.pow_const p)).aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hF hG
  have heq : ∀ ω, ENNReal.ofReal ((f ω * g ω) ^ p) =
      ENNReal.ofReal (f ω ^ p) * ENNReal.ofReal (g ω ^ p) := by
    intro ω
    rw [Real.mul_rpow (hf0 ω) (hg0 ω),
      ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 ω) _)]
  have hsquare : ∀ (u : Ω → ℝ), (∀ ω, 0 ≤ u ω) → ∀ ω,
      ENNReal.ofReal (u ω ^ p) ^ (2 : ℝ) = ENNReal.ofReal (u ω ^ (2 * p)) := by
    intro u hu ω
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hu ω) _) (by norm_num),
      ← Real.rpow_mul (hu ω), mul_comm]
  simp_rw [heq]
  refine h.trans_eq ?_
  simp only [one_div]
  congr 2
  · exact lintegral_congr fun ω => hsquare f hf0 ω
  · exact lintegral_congr fun ω => hsquare g hg0 ω

/-- A compact envelope comparing the exponentials of two infrared fields. -/
def infraredComparisonFactor {d : ℕ} (T : Compacts (SpatialCoordinates d))
    (H0 H1 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) : ℝ :=
  Real.exp (‖(H0 ω).restrict (T : Set (SpatialCoordinates d))‖ +
    ‖(H1 ω).restrict (T : Set (SpatialCoordinates d))‖)

/-- The envelope is at least one on every sample. -/
theorem one_le_infraredComparisonFactor {d : ℕ} (T : Compacts (SpatialCoordinates d))
    (H0 H1 : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d) :
    1 ≤ infraredComparisonFactor T H0 H1 ω :=
  Real.one_le_exp (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Measurability is inherited from the two fields. -/
theorem measurable_infraredComparisonFactor {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (T : Compacts (SpatialCoordinates d)) {H0 H1 : BilateralField d → C(SpatialCoordinates d, ℝ)}
    (h0 : Measurable H0) (h1 : Measurable H1) :
    Measurable (infraredComparisonFactor T H0 H1) := by
  letI : MeasurableSpace C(T, ℝ) := borel _
  letI : BorelSpace C(T, ℝ) := ⟨rfl⟩
  exact (((restrictC_continuous T).measurable.comp h0).norm.add
    ((restrictC_continuous T).measurable.comp h1).norm).exp

/-- Both pointwise exponential ratios are bounded by the same compact factor. -/
theorem exp_sub_le_infraredComparisonFactor {d : ℕ} (T : Compacts (SpatialCoordinates d))
    (H0 H1 : BilateralField d → C(SpatialCoordinates d, ℝ)) (ω : BilateralField d)
    {x : SpatialCoordinates d} (hx : x ∈ (T : Set (SpatialCoordinates d))) :
    Real.exp (H1 ω x - H0 ω x) ≤ infraredComparisonFactor T H0 H1 ω ∧
      Real.exp (H0 ω x - H1 ω x) ≤ infraredComparisonFactor T H0 H1 ω := by
  have h0 : |H0 ω x| ≤ ‖(H0 ω).restrict (T : Set (SpatialCoordinates d))‖ :=
    ((H0 ω).restrict (T : Set (SpatialCoordinates d))).norm_coe_le_norm ⟨x, hx⟩
  have h1 : |H1 ω x| ≤ ‖(H1 ω).restrict (T : Set (SpatialCoordinates d))‖ :=
    ((H1 ω).restrict (T : Set (SpatialCoordinates d))).norm_coe_le_norm ⟨x, hx⟩
  constructor <;> apply Real.exp_le_exp.mpr
  · linarith only [h0, h1, le_abs_self (H1 ω x), neg_le_abs (H0 ω x)]
  · linarith only [h0, h1, le_abs_self (H0 ω x), neg_le_abs (H1 ω x)]

/-- Uniform moment bound for the infrared comparison factor. -/
theorem exists_infraredComparisonFactor_moment_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ C : Compacts (SpatialCoordinates d) → ℝ, (∀ T, 0 ≤ C T) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (H0 H1 : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H0 → InfraredAdmissible M H1 →
        ∀ (T : Compacts (SpatialCoordinates d)) (p : ℝ), 0 ≤ p →
          (∫⁻ ω, ENNReal.ofReal (infraredComparisonFactor T H0 H1 ω ^ p)
            ∂(chaosSampleLaw M).toMeasure) ≤
              ENNReal.ofReal (2 * Real.exp (C T * (2 * p) ^ 2 * M.delta ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_uniform_compactExponentialMoment_of_admissible hd
  refine ⟨C, hC0, ?_⟩
  intro M H0 H1 h0 h1 T p hp
  letI : MeasurableSpace C(T, ℝ) := borel _
  letI : BorelSpace C(T, ℝ) := ⟨rfl⟩
  let f : BilateralField d → ℝ := fun ω =>
    Real.exp ‖(H0 ω).restrict (T : Set (SpatialCoordinates d))‖
  let g : BilateralField d → ℝ := fun ω =>
    Real.exp ‖(H1 ω).restrict (T : Set (SpatialCoordinates d))‖
  have hf : Measurable f := (((restrictC_continuous T).measurable.comp h0.measurable).norm).exp
  have hg : Measurable g := (((restrictC_continuous T).measurable.comp h1.measurable).norm).exp
  have heq : infraredComparisonFactor T H0 H1 = fun ω => f ω * g ω := by
    funext ω
    exact Real.exp_add _ _
  rw [heq]
  have hbound : ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H →
      (∫⁻ ω, ENNReal.ofReal ((Real.exp ‖(H ω).restrict
        (T : Set (SpatialCoordinates d))‖) ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ≤
          ENNReal.ofReal (2 * Real.exp (C T * (2 * p) ^ 2 * M.delta ^ 2)) := by
    intro H hH
    obtain ⟨hi, hb⟩ := hC M H hH T (2 * p) (mul_nonneg (by norm_num) hp)
    simp_rw [← Real.exp_mul]
    have hn : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure,
        0 ≤ Real.exp (‖(H ω).restrict (T : Set (SpatialCoordinates d))‖ * (2 * p)) :=
      Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
    have hi' : Integrable (fun ω => Real.exp
        (‖(H ω).restrict (T : Set (SpatialCoordinates d))‖ * (2 * p)))
          (chaosSampleLaw M).toMeasure := by simpa only [mul_comm] using hi
    rw [← ofReal_integral_eq_lintegral_ofReal hi' hn]
    exact ENNReal.ofReal_le_ofReal (by simpa only [mul_comm] using hb)
  calc
    _ ≤ (∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ENNReal.ofReal (g ω ^ (2 * p)) ∂(chaosSampleLaw M).toMeasure) ^ (1 / 2 : ℝ) :=
      product_moment_le _ hf hg (fun _ => (Real.exp_pos _).le)
        (fun _ => (Real.exp_pos _).le) p
    _ ≤ ENNReal.ofReal (2 * Real.exp (C T * (2 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (2 * Real.exp (C T * (2 * p) ^ 2 * M.delta ^ 2)) ^ (1 / 2 : ℝ) :=
      mul_le_mul' (ENNReal.rpow_le_rpow (hbound H0 h0) (by norm_num))
        (ENNReal.rpow_le_rpow (hbound H1 h1) (by norm_num))
    _ = _ := by
      rw [← ENNReal.rpow_add (1 / 2 : ℝ) (1 / 2 : ℝ) (by positivity)
        ENNReal.ofReal_ne_top]
      rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.rpow_one]

/-- Exact density factorization when the infrared field changes. -/
theorem cutoffSpeedDensity_infrared_ratio {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H0 H1 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffSpeedDensity M H1 ω N x =
      Real.exp (H1 ω x - H0 ω x) * cutoffSpeedDensity M H0 ω N x := by
  unfold cutoffSpeedDensity cutoffPotential
  rw [← Real.exp_add]
  congr 1
  ring

/-- Exact energy coefficient factorization when the infrared field changes. -/
theorem cutoffCoefficient_infrared_ratio {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H0 H1 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M H1 ω N x =
      Real.exp (H1 ω x - H0 ω x) * cutoffCoefficient M H0 ω N x := by
  change (ahom M N)⁻¹ * cutoffSpeedDensity M H1 ω N x =
    Real.exp (H1 ω x - H0 ω x) * ((ahom M N)⁻¹ * cutoffSpeedDensity M H0 ω N x)
  rw [cutoffSpeedDensity_infrared_ratio]
  ring

/-- The full local estimate transports to any infrared truncation on the same reference geometry. -/
theorem estimates_change_infrared {d p : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H0 H1 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (ω : BilateralField d) (N : ℕ) (T : Compacts (SpatialCoordinates d))
    {y0 : SpatialCoordinates d} {ρ0 K B : ℝ}
    {c : Fin p → SpatialCoordinates d} {s0 s1 : Fin p → ℝ}
    (hK : 1 ≤ K)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i)
    (hin : ∀ i, Metric.ball (c i) (s1 i / 2) ⊆ Metric.ball y0 (ρ0 / 2))
    (hT : Metric.ball y0 (ρ0 / 2) ⊆ (T : Set (SpatialCoordinates d)))
    (h : estimates (cutoffSpeedDensity M H0 ω N) (cutoffCoefficient M H0 ω N)
      y0 ρ0 c s0 s1 K B) :
    estimates (cutoffSpeedDensity M H1 ω N) (cutoffCoefficient M H1 ω N)
      y0 ρ0 c s0 s1 (infraredComparisonFactor T H0 H1 ω * K) B := by
  let F := infraredComparisonFactor T H0 H1 ω
  have hF : 1 ≤ F := one_le_infraredComparisonFactor T H0 H1 ω
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  have hb : ∀ x ∈ Metric.ball y0 (ρ0 / 2),
      cutoffSpeedDensity M H1 ω N x ≤ F * cutoffSpeedDensity M H0 ω N x ∧
      cutoffSpeedDensity M H0 ω N x ≤ F * cutoffSpeedDensity M H1 ω N x := by
    intro x hx
    obtain ⟨he10, he01⟩ := exp_sub_le_infraredComparisonFactor T H0 H1 ω (hT hx)
    constructor
    · rw [cutoffSpeedDensity_infrared_ratio M H0 H1]
      exact mul_le_mul_of_nonneg_right he10 (Real.exp_pos _).le
    · rw [cutoffSpeedDensity_infrared_ratio M H1 H0]
      exact mul_le_mul_of_nonneg_right he01 (Real.exp_pos _).le
  have hA : ∀ x ∈ Metric.ball y0 (ρ0 / 2),
      cutoffCoefficient M H1 ω N x ≤ F * cutoffCoefficient M H0 ω N x ∧
      cutoffCoefficient M H0 ω N x ≤ F * cutoffCoefficient M H1 ω N x := by
    intro x hx
    have hhom : 0 ≤ (ahom M N)⁻¹ := (inv_pos.mpr (ahom_pos M N)).le
    constructor
    · change (ahom M N)⁻¹ * cutoffSpeedDensity M H1 ω N x ≤
        F * ((ahom M N)⁻¹ * cutoffSpeedDensity M H0 ω N x)
      calc
        _ ≤ (ahom M N)⁻¹ * (F * cutoffSpeedDensity M H0 ω N x) :=
          mul_le_mul_of_nonneg_left (hb x hx).1 hhom
        _ = _ := by ring
    · change (ahom M N)⁻¹ * cutoffSpeedDensity M H0 ω N x ≤
        F * ((ahom M N)⁻¹ * cutoffSpeedDensity M H1 ω N x)
      calc
        _ ≤ (ahom M N)⁻¹ * (F * cutoffSpeedDensity M H1 ω N x) :=
          mul_le_mul_of_nonneg_left (hb x hx).2 hhom
        _ = _ := by ring
  apply estimates_of_comparison hK hF hs hin _ (fun x hx => (hb x hx).1)
    (fun x hx => (hA x hx).2) (fun x hx => (hA x hx).1) h
  intro x hx
  calc
    F⁻¹ * cutoffSpeedDensity M H0 ω N x ≤
        F⁻¹ * (F * cutoffSpeedDensity M H1 ω N x) :=
      mul_le_mul_of_nonneg_left (hb x hx).2 (inv_nonneg.mpr hF0.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hF0.ne', one_mul]

end SubdiffusiveProcess.Static
