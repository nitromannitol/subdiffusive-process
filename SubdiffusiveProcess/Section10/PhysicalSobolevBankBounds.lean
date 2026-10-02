import SubdiffusiveProcess.Section10.KilledSobolevMomentEnergy
import Mathlib.MeasureTheory.Integral.Lebesgue.Add



open MeasureTheory Homogenization SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

def PhysicalStaticBounds {d : ℕ} (b A : SpatialCoordinates d → ℝ) (B K : ℝ) : Prop :=
  (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) 2, ∀ r : ℝ, 0 < r → r ≤ 1 →
    weightedMeasure b (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2))) ∧
  (∀ w : H10Function (Metric.ball (0 : SpatialCoordinates d) 1),
    killedFractionalEnergy (Metric.ball (0 : SpatialCoordinates d) 1) w.toFun +
      ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) 1, ENNReal.ofReal (w.toFun x ^ 2) ≤
    ENNReal.ofReal (K * (2 : ℝ) ^ B) * killedCoefficientEnergy A w.toH1Function)

theorem PhysicalStaticBounds.mono {d : ℕ} {b A : SpatialCoordinates d → ℝ}
    {B K K' : ℝ} (h : PhysicalStaticBounds b A B K) (hKK' : K ≤ K') :
    PhysicalStaticBounds b A B K' := by
  constructor
  · intro x hx r hr hr1
    exact (h.1 x hx r hr hr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hKK' (Real.rpow_nonneg hr.le _)))
  · intro w
    exact (h.2 w).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hKK' (Real.rpow_nonneg (by norm_num) _))) _)

theorem PhysicalStaticBounds.exponent_mono {d : ℕ} {b A : SpatialCoordinates d → ℝ}
    {B B' K : ℝ} (h : PhysicalStaticBounds b A B K) (hK : 0 ≤ K) (hBB' : B ≤ B') :
    PhysicalStaticBounds b A B' K := by
  refine ⟨h.1, fun w => (h.2 w).trans ?_⟩
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hBB') hK)) _

/-- Mass pays the upper multiplier and coercivity pays its reciprocal lower
bound. The comparison uses the actual lower-integral energy. -/
theorem PhysicalStaticBounds.multiplier {d : ℕ} {b A b' A' : SpatialCoordinates d → ℝ}
    {B K R : ℝ} (h : PhysicalStaticBounds b A B K) (hR : 0 ≤ R)
    (hb : ∀ y ∈ Metric.ball (0 : SpatialCoordinates d) 4, b' y ≤ R * b y)
    (hA : ∀ y ∈ Metric.ball (0 : SpatialCoordinates d) 1, A y ≤ R * A' y) :
    PhysicalStaticBounds b' A' B (R * K) := by
  constructor
  · intro x hx r hr hr1
    have hmass : weightedMeasure b' (Metric.ball x r) ≤
        ENNReal.ofReal R * weightedMeasure b (Metric.ball x r) := by
      simp only [weightedMeasure, withDensity_apply _ measurableSet_ball]
      calc
        _ ≤ ∫⁻ y in Metric.ball x r, ENNReal.ofReal R * ENNReal.ofReal (b y) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
          have hy4 : y ∈ Metric.ball (0 : SpatialCoordinates d) 4 := by
            change dist y 0 < 4
            have hyx : dist y x < r := hy
            have hx0 : dist x 0 < 2 := hx
            linarith [dist_triangle y x (0 : SpatialCoordinates d)]
          simpa only [ENNReal.ofReal_mul hR] using ENNReal.ofReal_le_ofReal (hb y hy4)
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    calc
      _ ≤ ENNReal.ofReal R * weightedMeasure b (Metric.ball x r) := hmass
      _ ≤ ENNReal.ofReal R * ENNReal.ofReal (K * r ^ ((d : ℝ) - 1 / 2)) := by
        gcongr
        exact h.1 x hx r hr hr1
      _ = ENNReal.ofReal (R * K * r ^ ((d : ℝ) - 1 / 2)) := by
        rw [← ENNReal.ofReal_mul hR, mul_assoc]
  · intro w
    have henergy : killedCoefficientEnergy A w.toH1Function ≤
        ENNReal.ofReal R * killedCoefficientEnergy A' w.toH1Function := by
      unfold killedCoefficientEnergy
      calc
        _ ≤ ∫⁻ y in Metric.ball (0 : SpatialCoordinates d) 1,
            ENNReal.ofReal R * ENNReal.ofReal (A' y * vecDot (w.grad y) (w.grad y)) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
          have he := mul_le_mul_of_nonneg_right (hA y hy) (vecNormSq_nonneg (w.grad y))
          simpa only [mul_assoc, ENNReal.ofReal_mul hR] using ENNReal.ofReal_le_ofReal he
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    calc
      _ ≤ ENNReal.ofReal (K * (2 : ℝ) ^ B) * killedCoefficientEnergy A w.toH1Function := h.2 w
      _ ≤ ENNReal.ofReal (K * (2 : ℝ) ^ B) *
          (ENNReal.ofReal R * killedCoefficientEnergy A' w.toH1Function) := by gcongr
      _ = ENNReal.ofReal (R * K * (2 : ℝ) ^ B) *
          killedCoefficientEnergy A' w.toH1Function := by
        rw [← mul_assoc, mul_comm (ENNReal.ofReal (K * (2 : ℝ) ^ B)),
          ← ENNReal.ofReal_mul hR, mul_assoc]

/-- A product moment uses twice the requested order; no independence is needed. -/
theorem physicalBank_product_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {R K : Ω → ℝ} {Q CR CK : ℝ}
    (hR : Measurable R) (hR0 : ∀ ω, 0 ≤ R ω) (hK0 : ∀ ω, 0 ≤ K ω)
    (hCR : 0 ≤ CR) (hCK : 0 ≤ CK)
    (hRm : (∫⁻ ω, ENNReal.ofReal (R ω ^ (2 * Q)) ∂μ) ≤ ENNReal.ofReal CR)
    (hKm : (∫⁻ ω, ENNReal.ofReal (K ω ^ (2 * Q)) ∂μ) ≤ ENNReal.ofReal CK) :
    (∫⁻ ω, ENNReal.ofReal ((R ω * K ω) ^ Q) ∂μ) ≤ ENNReal.ofReal (CR + CK) := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (R ω ^ (2 * Q)) + ENNReal.ofReal (K ω ^ (2 * Q)) ∂μ := by
      apply lintegral_mono
      intro ω
      change ENNReal.ofReal ((R ω * K ω) ^ Q) ≤
        ENNReal.ofReal (R ω ^ (2 * Q)) + ENNReal.ofReal (K ω ^ (2 * Q))
      rw [← ENNReal.ofReal_add (Real.rpow_nonneg (hR0 ω) _) (Real.rpow_nonneg (hK0 ω) _)]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.mul_rpow (hR0 ω) (hK0 ω),
        show 2 * Q = Q * (2 : ℕ) by simp; ring,
        Real.rpow_mul_natCast (hR0 ω), Real.rpow_mul_natCast (hK0 ω)]
      nlinarith [sq_nonneg (R ω ^ Q - K ω ^ Q)]
    _ = (∫⁻ ω, ENNReal.ofReal (R ω ^ (2 * Q)) ∂μ) +
        (∫⁻ ω, ENNReal.ofReal (K ω ^ (2 * Q)) ∂μ) :=
      lintegral_add_left (ENNReal.measurable_ofReal.comp (hR.pow measurable_const)) _
    _ ≤ ENNReal.ofReal CR + ENNReal.ofReal CK := add_le_add hRm hKm
    _ = ENNReal.ofReal (CR + CK) := (ENNReal.ofReal_add hCR hCK).symm


end SubdiffusiveProcess.Section10
