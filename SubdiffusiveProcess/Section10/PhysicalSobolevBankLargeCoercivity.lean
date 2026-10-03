module

public import SubdiffusiveProcess.Section10.PhysicalSobolevBankLargeDomain

@[expose] public section

/-! The separate killed projection of the physical static certificate. Mass
can be supplied independently; the join consumes the existing exact physical
window pullback and incurs no additional moment cost. -/
open MeasureTheory Homogenization SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.Section10.PhysicalLocalTransport
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Section10

/-- Literal all-native-H10 fractional plus volume-L2 coercivity. -/
def PhysicalKilledCoercivity {d : ℕ} (A : SpatialCoordinates d → ℝ) (K : ℝ) : Prop :=
  ∀ w : H10Function (Metric.ball (0 : SpatialCoordinates d) 1),
    killedFractionalEnergy (Metric.ball (0 : SpatialCoordinates d) 1) w.toFun +
      ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) 1, ENNReal.ofReal (w.toFun x ^ 2) ≤
    ENNReal.ofReal K * killedCoefficientEnergy A w.toH1Function

theorem PhysicalKilledCoercivity.mono {d : ℕ} {A : SpatialCoordinates d → ℝ}
    {K K' : ℝ} (h : PhysicalKilledCoercivity A K) (hKK' : K ≤ K') :
    PhysicalKilledCoercivity A K' := by
  intro w
  exact (h w).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hKK') _)

/-- The coercivity projection transports through the actual physical-window
map on its own. It has the same moment bound. -/
theorem physicalRetainedWindow_killed_pullback {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) {l m : ℕ} (hlm : l ≤ m) (z : SpatialCoordinates d)
    {K : (Fin (l + 1) → C(SpatialCoordinates d, ℝ)) → ℝ} (hK : Measurable K)
    (hone : ∀ ξ, 1 ≤ K ξ) {Q C : ℝ}
    (hm : (∫⁻ ξ, ENNReal.ofReal (K ξ ^ Q) ∂windowLaw M l m) ≤ ENNReal.ofReal C)
    (hs : ∀ᵐ ξ ∂windowLaw M l m,
      PhysicalKilledCoercivity (retainedWindowCoefficient M l ξ) (K ξ)) :
    ∃ Kphys : AnchoredC11Sample d → ℝ, Measurable Kphys ∧ (∀ ω, 1 ≤ Kphys ω) ∧
      (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q) ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤
        ENNReal.ofReal C ∧
      ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
        PhysicalKilledCoercivity (localCoefficient M l m z ω) (Kphys ω) := by
  refine ⟨K ∘ physicalWindow l m z, hK.comp (measurable_physicalWindow l m z),
    fun ω => hone _, ?_, ?_⟩
  · exact ((physicalWindow_preserving M l m z).lintegral_comp
      (ENNReal.measurable_ofReal.comp (hK.pow measurable_const))).trans_le hm
  · filter_upwards [(physicalWindow_preserving M l m z).quasiMeasurePreserving.ae hs] with ω hω
    rw [retainedWindowCoefficient_physical M hlm] at hω
    exact hω

/-- The exact join consumer for independently constructed mass and killed
constants. This conditional deterministic helper is not an assumed model bank. -/
theorem physicalRetainedWindow_static_of_projections {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) {l m : ℕ} (hlm : l ≤ m) (z : SpatialCoordinates d)
    {K : (Fin (l + 1) → C(SpatialCoordinates d, ℝ)) → ℝ} (hK : Measurable K)
    (hone : ∀ ξ, 1 ≤ K ξ) {Q C : ℝ}
    (hm : (∫⁻ ξ, ENNReal.ofReal (K ξ ^ Q) ∂windowLaw M l m) ≤ ENNReal.ofReal C)
    (hmass : ∀ᵐ ξ ∂windowLaw M l m,
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) 2, ∀ r : ℝ, 0 < r → r ≤ 1 →
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.weightedMeasure
          (retainedWindowSpeed M l ξ) (Metric.ball x r) ≤
            ENNReal.ofReal (K ξ * r ^ ((d : ℝ) - 1 / 2)))
    (hcoer : ∀ᵐ ξ ∂windowLaw M l m,
      PhysicalKilledCoercivity (retainedWindowCoefficient M l ξ) (K ξ)) :
    ∃ Kphys : AnchoredC11Sample d → ℝ, Measurable Kphys ∧ (∀ ω, 1 ≤ Kphys ω) ∧
      (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q) ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤
        ENNReal.ofReal C ∧
      ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
        PhysicalStaticBounds (localSpeed M l m z ω) (localCoefficient M l m z ω) 0 (Kphys ω) := by
  apply physicalRetainedWindow_bank_pullback M hlm z hK hone hm
  filter_upwards [hmass, hcoer] with ξ hm hc
  refine ⟨hm, ?_⟩
  simpa only [PhysicalKilledCoercivity, Real.rpow_zero, mul_one] using! hc


/-- Independent projection constants are joined by their maximum. The moment
cost is the sum of the two supplied moments, and the existing physical static
pullback consumes the resulting literal certificate. -/
theorem physicalRetainedWindow_join_projection_banks {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : GMCModel d) {l m : ℕ} (hlm : l ≤ m) (z : SpatialCoordinates d)
    {Km Kc : (Fin (l + 1) → C(SpatialCoordinates d, ℝ)) → ℝ}
    (hKm : Measurable Km) (hKc : Measurable Kc)
    (hmone : ∀ ξ, 1 ≤ Km ξ) (hcone : ∀ ξ, 1 ≤ Kc ξ) {Q Cm Cc : ℝ}
    (hQ : 0 ≤ Q) (hCm : 0 ≤ Cm) (hCc : 0 ≤ Cc)
    (hm : (∫⁻ ξ, ENNReal.ofReal (Km ξ ^ Q) ∂windowLaw M l m) ≤ ENNReal.ofReal Cm)
    (hc : (∫⁻ ξ, ENNReal.ofReal (Kc ξ ^ Q) ∂windowLaw M l m) ≤ ENNReal.ofReal Cc)
    (hmass : ∀ᵐ ξ ∂windowLaw M l m,
      ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) 2, ∀ r : ℝ, 0 < r → r ≤ 1 →
        SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.weightedMeasure
          (retainedWindowSpeed M l ξ) (Metric.ball x r) ≤
            ENNReal.ofReal (Km ξ * r ^ ((d : ℝ) - 1 / 2)))
    (hcoer : ∀ᵐ ξ ∂windowLaw M l m,
      PhysicalKilledCoercivity (retainedWindowCoefficient M l ξ) (Kc ξ)) :
    ∃ Kphys : AnchoredC11Sample d → ℝ, Measurable Kphys ∧ (∀ ω, 1 ≤ Kphys ω) ∧
      (∫⁻ ω, ENNReal.ofReal (Kphys ω ^ Q) ∂(PhysicalAttachment.physicalLaw M).toMeasure) ≤
        ENNReal.ofReal (Cm + Cc) ∧
      ∀ᵐ ω ∂(PhysicalAttachment.physicalLaw M).toMeasure,
        PhysicalStaticBounds (localSpeed M l m z ω) (localCoefficient M l m z ω) 0 (Kphys ω) := by
  have hmoment := lintegral_max_rpow_le (windowLaw M l m) hKm
    (fun ξ => zero_le_one.trans (hmone ξ)) (fun ξ => zero_le_one.trans (hcone ξ))
    hQ hCm hCc hm hc
  apply physicalRetainedWindow_static_of_projections M hlm z (hKm.max hKc)
    (fun ξ => (hmone ξ).trans (le_max_left _ _)) hmoment
  · filter_upwards [hmass] with ξ hξ
    intro x hx r hr hr1
    exact (hξ x hx r hr hr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _)))
  · filter_upwards [hcoer] with ξ hξ
    exact hξ.mono (le_max_right _ _)



end SubdiffusiveProcess.Section10
