module

public import SubdiffusiveProcess.Comparison.InverseEnergyOrder
public import SubdiffusiveProcess.Paper.thm_prop_env_core

@[expose] public section





open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.Paper
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Comparison

/-- Scalar quadratic responses of an almost sure killed-inverse limit are measurable
up to completion, without requiring the caller to choose measurable operator versions. -/
theorem aemeasurable_quadratic_limit (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization model H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (N : ℕ → ℕ)
    (G : BilateralField d → DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr))
    (hlim : ∀ᵐ ω ∂(chaosSampleLaw model).toMeasure,
      Tendsto (fun n => volumeResponseOperator S
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H ω (N n) z hr)) atTop (𝓝 (G ω)))
    (f : DomainL2 (centeredCube z r hr)) :
    AEMeasurable (fun ω => inner ℝ f (G ω f)) (chaosSampleLaw model).toMeasure := by
  have hc : Continuous (fun A : DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr) => inner ℝ f (A f)) :=
    continuous_const.inner (ContinuousLinearMap.apply ℝ _ f).continuous
  have hm : ∀ n, Measurable (fun ω => inner ℝ f
      (volumeResponseOperator S (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H ω (N n) z hr) f)) :=
    fun n => (hc.comp_stronglyMeasurable
      (stronglyMeasurable_cutoffVolumeResponseOperator model H hH.1 (N n) z r hr S)).measurable
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hm n).aemeasurable)
    (hlim.mono (fun ω hω => (hc.tendsto (G ω)).comp hω))

/-- A comparison on a produced representation descends to every original-space
operator-limit pair through measurable quadratic readouts on a countable dense family. -/
theorem original_comparison_of_represented (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization model H)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF seq : ℕ → ℕ) (hseq : StrictMono seq)
    (GE0 GF0 : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hlimE : ∀ᵐ ω ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H ω (NE n) (z i) (hr i))) atTop (𝓝 (GE0 i ω)))
    (hlimF : ∀ᵐ ω ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H ω (NF n) (z i) (hr i))) atTop (𝓝 (GF0 i ω)))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hjoint : aux_conv_represented_env_interface_joint d model H Ω P field env env
      z r hr Sspace GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)))
    (c : ℝ) (hc : 0 < c)
    (hcompare : ∀ᵐ ω ∂P, ∀ i,
      limitFormDomain (GE i ω) ⊆ limitFormDomain (GF i ω) ∧
      ∀ u ∈ limitFormDomain (GE i ω),
        (limitFormEnergy (GF i ω) u).toReal ≤ c * (limitFormEnergy (GE i ω) u).toReal) :
    ∀ᵐ ω ∂(chaosSampleLaw model).toMeasure, ∀ i,
      limitFormDomain (GE0 i ω) ⊆ limitFormDomain (GF0 i ω) ∧
      ∀ u ∈ limitFormDomain (GE0 i ω),
        (limitFormEnergy (GF0 i ω) u).toReal ≤ c * (limitFormEnergy (GE0 i ω) u).toReal := by
  classical
  have hid := aux_thm_prop_env_identification d model H z r hr Sspace
    NE NF seq seq hseq hseq GE0 GF0 hlimE hlimF hH Ω P field env GNE GNF GE GF hjoint
  have hsn := aux_thm_prop_env_hsn d model H Ω P field env env z r hr Sspace
    GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) hjoint
  have hmp : MeasurePreserving field P (chaosSampleLaw model).toMeasure :=
    ⟨hjoint.2.1, hjoint.2.2.1⟩
  rw [ae_all_iff]
  intro i
  obtain ⟨D, hDc, hDd, _⟩ :=
    SubdiffusiveProcess.SmoothSources.exists_countable_dense_smooth_submodule (z i) (r i) (hr i)
  have htests : ∀ f ∈ (D : Set (DomainL2 (centeredCube (z i) (r i) (hr i)))),
      ∀ᵐ ω ∂(chaosSampleLaw model).toMeasure,
        inner ℝ f (GE0 i ω f) ≤ c * inner ℝ f (GF0 i ω f) := by
    intro f _
    have hE := aemeasurable_quadratic_limit d model H hH (z i) (r i) (hr i)
      (Sspace i) NE (GE0 i) (hlimE.mono (fun ω hω => hω i)) f
    have hF := aemeasurable_quadratic_limit d model H hH (z i) (r i) (hr i)
      (Sspace i) NF (GF0 i) (hlimF.mono (fun ω hω => hω i)) f
    apply ae_le_of_pullback P (chaosSampleLaw model).toMeasure field hmp
      (fun ω => inner ℝ f (GE0 i ω f)) (fun ω => c * inner ℝ f (GF0 i ω f))
      hE (aemeasurable_const.mul hF)
    filter_upwards [hid, hsn, hcompare] with ω hi hs he
    rw [← (hi i).1, ← (hi i).2]
    exact aux_thm_C0_response_le_of_form_le (GE i ω) (GF i ω)
      (hs i).1.1 (hs i).1.2 c hc (he i).1 (he i).2 f
  have hall := (ae_ball_iff hDc).mpr htests
  filter_upwards [hall] with ω hω
  exact form_le_of_response_le (GE0 i ω) (GF0 i ω) c hc
    (response_le_of_dense (GE0 i ω) (GF0 i ω) c (D : Set _) hDd hω)

end SubdiffusiveProcess.Comparison
