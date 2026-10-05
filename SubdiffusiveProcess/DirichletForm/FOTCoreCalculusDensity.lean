module

public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusSignedLinear
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

@[expose] public section

open MeasureTheory Filter Set Topology

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [BorelSpace X]

theorem continuous_integrable_of_compact_carrier {μ : Measure X} [IsFiniteMeasure μ]
    {K : Set X} (hK : IsCompact K) (hμ : μ Kᶜ = 0) {f : X → ℝ} (hf : Continuous f) :
    Integrable f μ := by
  have hr : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)
  have hi := hf.continuousOn.integrableOn_compact (μ := μ) hK
  change Integrable f (μ.restrict K) at hi
  rwa [hr] at hi

omit [TopologicalSpace X] [T2Space X] [BorelSpace X] in
theorem variation_le_of_measure_difference
    [_portSection0 : TopologicalSpace X] [_portSection1 : T2Space X] [_portSection2 : BorelSpace X] {ν : SignedMeasure X} {μ ρ : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    (hν : ν = μ.toSignedMeasure - ρ.toSignedMeasure) : ν.totalVariation ≤ μ + ρ := by
  apply signed_totalVariation_le
  intro B hB
  rw [hν, sub_apply, Measure.toSignedMeasure_apply_measurable hB,
    Measure.toSignedMeasure_apply_measurable hB, measureReal_def, measureReal_def,
    Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  exact (abs_sub _ _).trans (by simp only [abs_of_nonneg ENNReal.toReal_nonneg]; rfl)

/-- Multiplication of a signed measure by a real density, using! its Jordan parts. -/
def signedDensity (ν : SignedMeasure X) (k : X → ℝ) : SignedMeasure X :=
  ν.toJordanDecomposition.posPart.withDensityᵥ k - ν.toJordanDecomposition.negPart.withDensityᵥ k

omit [TopologicalSpace X] [T2Space X] [BorelSpace X] in
theorem signedDensity_apply
    [_portSection0 : TopologicalSpace X] [_portSection1 : T2Space X] [_portSection2 : BorelSpace X] (ν : SignedMeasure X) {k : X → ℝ} (hk : SignedIntegrable ν k)
    {B : Set X} (hB : MeasurableSet B) :
    signedDensity ν k B = _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B k := by
  simp only [signedDensity, sub_apply, withDensityᵥ_apply hk.1 hB,
    withDensityᵥ_apply hk.2 hB, _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn]

omit [TopologicalSpace X] [T2Space X] [BorelSpace X] in
theorem signedDensity_variation_ac
    [_portSection0 : TopologicalSpace X] [_portSection1 : T2Space X] [_portSection2 : BorelSpace X] (ν : SignedMeasure X) (k : X → ℝ) :
    (signedDensity ν k).totalVariation ≪ ν.totalVariation := by
  have hp : ν.toJordanDecomposition.posPart ≪ ν.totalVariation :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hn : ν.toJordanDecomposition.negPart ≪ ν.totalVariation :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hac : signedDensity ν k ≪ᵥ ν.totalVariation.toENNRealVectorMeasure := by
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro B hB hz
    rw [Measure.toENNRealVectorMeasure_apply_measurable hB] at hz
    have hpp := ν.toJordanDecomposition.posPart.withDensityᵥ_absolutelyContinuous k
    have hnn := ν.toJordanDecomposition.negPart.withDensityᵥ_absolutelyContinuous k
    rw [signedDensity, sub_apply,
      hpp (by rw [Measure.toENNRealVectorMeasure_apply_measurable hB]; exact hp hz),
      hnn (by rw [Measure.toENNRealVectorMeasure_apply_measurable hB]; exact hn hz), sub_self]
  rwa [SignedMeasure.absolutelyContinuous_ennreal_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at hac

theorem signedDensity_integrable (ν : SignedMeasure X) {K : Set X} (hK : IsCompact K)
    (hν : ν.totalVariation Kᶜ = 0) (k : X → ℝ) {f : X → ℝ} (hf : Continuous f) :
    SignedIntegrable (signedDensity ν k) f :=
  signedIntegrable_of_compact_carrier _ hK (signedDensity_variation_ac ν k hν) hf

theorem signedDensity_integral (ν : SignedMeasure X) {K : Set X} (hK : IsCompact K)
    (hν : ν.totalVariation Kᶜ = 0) {k f : X → ℝ} (hk : Continuous k) (hf : Continuous f)
    {B : Set X} (hB : MeasurableSet B) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (signedDensity ν k) B f =
      _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B (fun x => k x * f x) := by
  have hki := signedIntegrable_of_compact_carrier ν hK hν hk
  have hz : ν.toJordanDecomposition.posPart Kᶜ = 0 ∧ ν.toJordanDecomposition.negPart Kᶜ = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] using! hν
  let pp := ν.toJordanDecomposition.posPart.withDensity (fun x => ENNReal.ofReal (k x))
  let pn := ν.toJordanDecomposition.posPart.withDensity (fun x => ENNReal.ofReal (-k x))
  let np := ν.toJordanDecomposition.negPart.withDensity (fun x => ENNReal.ofReal (k x))
  let nn := ν.toJordanDecomposition.negPart.withDensity (fun x => ENNReal.ofReal (-k x))
  let : IsFiniteMeasure pp := isFiniteMeasure_withDensity_ofReal hki.1.2
  let : IsFiniteMeasure pn := isFiniteMeasure_withDensity_ofReal hki.1.neg.2
  let : IsFiniteMeasure np := isFiniteMeasure_withDensity_ofReal hki.2.2
  let : IsFiniteMeasure nn := isFiniteMeasure_withDensity_ofReal hki.2.neg.2
  have hpp : pp Kᶜ = 0 := withDensity_absolutelyContinuous _ _ hz.1
  have hpn : pn Kᶜ = 0 := withDensity_absolutelyContinuous _ _ hz.1
  have hnp : np Kᶜ = 0 := withDensity_absolutelyContinuous _ _ hz.2
  have hnn : nn Kᶜ = 0 := withDensity_absolutelyContinuous _ _ hz.2
  have heq : signedDensity ν k = (pp + nn).toSignedMeasure - (pn + np).toSignedMeasure := by
    rw [signedDensity, withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hki.1,
      withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hki.2,
      Measure.toSignedMeasure_add, Measure.toSignedMeasure_add]
    change (pp.toSignedMeasure - pn.toSignedMeasure) - (np.toSignedMeasure - nn.toSignedMeasure) = _
    abel
  have hδ : (signedDensity ν k).totalVariation Kᶜ = 0 := by
    apply le_antisymm _ bot_le
    apply (variation_le_of_measure_difference heq Kᶜ).trans
    simp [Measure.add_apply, hpp, hpn, hnp, hnn]
  have hfi := signedIntegrable_of_compact_carrier (signedDensity ν k) hK hδ hf
  have hfpp := continuous_integrable_of_compact_carrier hK hpp hf
  have hfpn := continuous_integrable_of_compact_carrier hK hpn hf
  have hfnp := continuous_integrable_of_compact_carrier hK hnp hf
  have hfnn := continuous_integrable_of_compact_carrier hK hnn hf
  rw [signedIntegralOn_of_measure_difference heq hfi
    (integrable_add_measure.mpr ⟨hfpp, hfnn⟩) (integrable_add_measure.mpr ⟨hfpn, hfnp⟩) B,
    Measure.restrict_add, Measure.restrict_add,
    integral_add_measure hfpp.integrableOn hfnn.integrableOn,
    integral_add_measure hfpn.integrableOn hfnp.integrableOn]
  have hp (μ : Measure X) :
      (∫ x in B, f x ∂μ.withDensity (fun x => ENNReal.ofReal (k x))) =
        ∫ x in B, max (k x) 0 * f x ∂μ := by
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hk.measurable.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f hB]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  have hneg : Measurable (fun x => -k x) := by
    simpa only [Pi.neg_apply] using! hk.neg.measurable
  have hn (μ : Measure X) :
      (∫ x in B, f x ∂μ.withDensity (fun x => ENNReal.ofReal (-k x))) =
        ∫ x in B, max (-k x) 0 * f x ∂μ := by
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hneg.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f hB]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  change (∫ x in B, f x ∂ν.toJordanDecomposition.posPart.withDensity _) +
    (∫ x in B, f x ∂ν.toJordanDecomposition.negPart.withDensity _) -
    ((∫ x in B, f x ∂ν.toJordanDecomposition.posPart.withDensity _) +
    (∫ x in B, f x ∂ν.toJordanDecomposition.negPart.withDensity _)) = _
  simp only [hp, hn]
  have hpi := signedIntegrable_of_compact_carrier ν hK hν ((hk.max (continuous_const (y := (0 : ℝ)))).mul hf)
  have hni := signedIntegrable_of_compact_carrier ν hK hν ((hk.neg.max (continuous_const (y := (0 : ℝ)))).mul hf)
  have hid (μ : Measure X) (hi : Integrable (fun x => max (k x) 0 * f x) μ)
      (hj : Integrable (fun x => max (-k x) 0 * f x) μ) :
      (∫ x in B, max (k x) 0 * f x ∂μ) - (∫ x in B, max (-k x) 0 * f x ∂μ) =
        ∫ x in B, k x * f x ∂μ := by
    rw [← integral_sub hi.integrableOn hj.integrableOn]
    apply integral_congr_ae
    filter_upwards [] with x
    rcases le_or_gt 0 (k x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith : -k x ≤ 0)]; ring
    · rw [max_eq_right hx.le, max_eq_left (by linarith : 0 ≤ -k x)]; ring
  unfold _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn
  linarith only [hid ν.toJordanDecomposition.posPart hpi.1 hni.1,
    hid ν.toJordanDecomposition.negPart hpi.2 hni.2]

theorem signedDensity_mul (ν : SignedMeasure X) {K : Set X} (hK : IsCompact K)
    (hν : ν.totalVariation Kᶜ = 0) {k f : X → ℝ} (hk : Continuous k) (hf : Continuous f) :
    signedDensity (signedDensity ν k) f = signedDensity ν (fun x => k x * f x) := by
  have hkf : Continuous (fun x => k x * f x) := by
    simpa only [Pi.mul_apply] using! hk.mul hf
  ext B hB
  rw [signedDensity_apply _ (signedDensity_integrable ν hK hν k hf) hB,
    signedDensity_integral ν hK hν hk hf hB,
    signedDensity_apply _ (signedIntegrable_of_compact_carrier ν hK hν hkf) hB]

theorem signedDensity_add_const (ν : SignedMeasure X) {K : Set X} (hK : IsCompact K)
    (hν : ν.totalVariation Kᶜ = 0) {f : X → ℝ} (hf : Continuous f) (c : ℝ) :
    signedDensity ν (fun x => f x + c) = signedDensity ν f + c • ν := by
  have hfc : Continuous (fun x => f x + c) := by
    simpa only [Pi.add_apply] using! hf.add (continuous_const (y := c))
  ext B hB
  rw [signedDensity_apply _ (signedIntegrable_of_compact_carrier ν hK hν
      hfc) hB,
    signedIntegralOn_add _ (signedIntegrable_of_compact_carrier ν hK hν hf)
      (signedIntegrable_of_compact_carrier ν hK hν continuous_const),
    signedIntegralOn_const _ hB c, add_apply, smul_apply,
    smul_eq_mul, signedDensity_apply _ (signedIntegrable_of_compact_carrier ν hK hν hf) hB]

end SubdiffusiveProcess.DirichletForm.FOTConstruction
