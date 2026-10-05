module

public import SubdiffusiveProcess.Paper.lem_response_reciprocal_positive
public import SubdiffusiveProcess.Paper.lem_response_reciprocal_negative
public import SubdiffusiveProcess.Paper.lem_response_reciprocal_fatou
public import SubdiffusiveProcess.Sobolev.VolumeResponseOperator

@[expose] public section

/-! Positive and negative moments of the quadratic forms `⟨f, G_N^Q f⟩`, and of the forms of every
extracted limit (paper `mfd:lem-response-reciprocal`), for every cube `Q` of side at most one (the
scope of the coercivity `mfd:lem-coercivity` invoked by the paper's proof). -/

open MeasureTheory Filter Topology SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Distributions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Lower moments follow from higher moments on a probability space. -/
theorem aux_lem_response_reciprocal_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (g : Ω → ℝ) {p q C : ℝ} (hpq : p ≤ q)
    (hmem : MemLp g (ENNReal.ofReal q) μ) (hb : eLpNorm g (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C) :
    MemLp g (ENNReal.ofReal p) μ ∧ eLpNorm g (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C :=
  ⟨hmem.mono_exponent (ENNReal.ofReal_le_ofReal hpq),
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)).trans hb⟩

/-- The quadratic form of a fixed source is continuous in the operator norm. -/
theorem aux_lem_response_reciprocal_quadratic_tendsto {d : ℕ} {Ω : TopologicalSpace.Opens (SpatialCoordinates d)}
    (f0 : DomainL2 Ω) {ι : Type*} {l : Filter ι} (T : ι → DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (T0 : DomainL2 Ω →L[ℝ] DomainL2 Ω) (h : Tendsto T l (𝓝 T0)) :
    Tendsto (fun i => inner ℝ f0 (T i f0)) l (𝓝 (inner ℝ f0 (T0 f0))) :=
  (((innerSL ℝ f0).comp (ContinuousLinearMap.apply ℝ (DomainL2 Ω) f0)).continuous.tendsto T0).comp h

/-- Positive and negative moments of the quadratic forms of a nonzero smooth source on a cube of
side at most one, at every finite cutoff and for every extracted limit. -/
theorem lem_response_reciprocal (d : ℕ) (hd : 2 ≤ d)
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (f : 𝓓(centeredCube z r hr, ℝ)) (hf : f ≠ 0) (p : ℝ) (hp : 0 < p) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization model H →
      ∀ (S : ResponseSpace (centeredCube z r hr)),
        S.space = killedSobolevGraph (centeredCube z r hr) →
      (∀ N : ℕ,
        (∀ om : BilateralField d, 0 < inner ℝ (testL2 f) (volumeResponseOperator S
          (cutoffPositiveCoefficient model H om N z hr) (testL2 f))) ∧
        MemLp (fun om : BilateralField d => inner ℝ (testL2 f) (volumeResponseOperator S
          (cutoffPositiveCoefficient model H om N z hr) (testL2 f))) (ENNReal.ofReal p)
          (chaosSampleLaw model).toMeasure ∧
        eLpNorm (fun om : BilateralField d => inner ℝ (testL2 f) (volumeResponseOperator S
          (cutoffPositiveCoefficient model H om N z hr) (testL2 f))) (ENNReal.ofReal p)
          (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal C ∧
        MemLp (fun om : BilateralField d => (inner ℝ (testL2 f) (volumeResponseOperator S
          (cutoffPositiveCoefficient model H om N z hr) (testL2 f)))⁻¹) (ENNReal.ofReal p)
          (chaosSampleLaw model).toMeasure ∧
        eLpNorm (fun om : BilateralField d => (inner ℝ (testL2 f) (volumeResponseOperator S
          (cutoffPositiveCoefficient model H om N z hr) (testL2 f)))⁻¹) (ENNReal.ofReal p)
          (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal C) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (env : ℕ → Ω → BilateralField d) (Ns : ℕ → ℕ),
        (∀ n, MeasurePreserving (env n) μ (chaosSampleLaw model).toMeasure) →
        ∀ G : Ω → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr),
          (∀ᵐ ω ∂μ, Tendsto (fun n => volumeResponseOperator S
            (cutoffPositiveCoefficient model H (env n ω) (Ns n) z hr)) atTop (𝓝 (G ω))) →
          (∀ᵐ ω ∂μ, 0 < inner ℝ (testL2 f) (G ω (testL2 f))) ∧
          MemLp (fun ω => inner ℝ (testL2 f) (G ω (testL2 f))) (ENNReal.ofReal p) μ ∧
          eLpNorm (fun ω => inner ℝ (testL2 f) (G ω (testL2 f))) (ENNReal.ofReal p) μ ≤
            ENNReal.ofReal C ∧
          MemLp (fun ω => (inner ℝ (testL2 f) (G ω (testL2 f)))⁻¹) (ENNReal.ofReal p) μ ∧
          eLpNorm (fun ω => (inner ℝ (testL2 f) (G ω (testL2 f)))⁻¹) (ENNReal.ofReal p) μ ≤
            ENNReal.ofReal C := by
  let measContinuous : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  let borelContinuous : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨deltaP, CP, hdeltaP, hCP, hpos⟩ := lem_response_reciprocal_positive hd E P z r hr hr1
    (testL2 f) (max p 1) (le_max_right _ _)
  obtain ⟨deltaN, CN, hdeltaN, hCN, hneg⟩ := lem_response_reciprocal_negative hd E X z r hr
    f hf (max p 1) (le_max_right _ _)
  refine ⟨min deltaP deltaN, max CP CN, lt_min hdeltaP hdeltaN, lt_max_of_lt_left hCP, ?_⟩
  intro ms bs
  have hms : ms = measContinuous := @BorelSpace.measurable_eq _ _ ms bs
  subst ms
  intro M hM H hH S hS
  have hMP := hM.trans (min_le_left _ _)
  have hMN := hM.trans (min_le_right _ _)
  -- the pointwise identification of the quadratic form with the inverse response
  have hY : ∀ (N : ℕ) (om : BilateralField d),
      inner ℝ (testL2 f) (volumeResponseOperator S (cutoffPositiveCoefficient M H om N z hr)
        (testL2 f)) = inverseResponse S (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL) := fun N om =>
    volumeResponseOperator_quadratic S _ _
  have hfin : ∀ N : ℕ,
      (∀ om : BilateralField d, 0 < inverseResponse S (cutoffPositiveCoefficient M H om N z hr)
        ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL)) ∧
      (MemLp (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL)) (ENNReal.ofReal (max p 1))
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => inverseResponse S (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL)) (ENNReal.ofReal (max p 1))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (max CP CN)) ∧
      (MemLp (fun om => (inverseResponse S (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL))⁻¹) (ENNReal.ofReal (max p 1))
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun om => (inverseResponse S (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL))⁻¹) (ENNReal.ofReal (max p 1))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (max CP CN)) := by
    intro N
    obtain ⟨hup1, hup2⟩ := hpos M H hH hMP S hS N
    obtain ⟨hpz, hlo1, hlo2⟩ := hneg M H hH hMN S hS N
    exact ⟨hpz, ⟨hup1, hup2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩,
      ⟨hlo1, hlo2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩⟩
  refine ⟨fun N => ?_, ?_⟩
  · obtain ⟨hpz, hup, hlo⟩ := hfin N
    simp only [hY]
    exact ⟨hpz, (aux_lem_response_reciprocal_mono _ _ (le_max_left p 1) hup.1 hup.2).1,
      (aux_lem_response_reciprocal_mono _ _ (le_max_left p 1) hup.1 hup.2).2,
      (aux_lem_response_reciprocal_mono _ _ (le_max_left p 1) hlo.1 hlo.2).1,
      (aux_lem_response_reciprocal_mono _ _ (le_max_left p 1) hlo.1 hlo.2).2⟩
  · intro Ω _ μ _ env Ns hEnv G hG
    let Y : ℕ → Ω → ℝ := fun n ω => inverseResponse S
      (cutoffPositiveCoefficient M H (env n ω) (Ns n) z hr)
      ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL)
    have hYmeas : ∀ n, AEStronglyMeasurable (Y n) μ := fun n =>
      ((aux_rem_bank_response_moments_measurable_inverseResponse M H hH.1 (Ns n) z hr S
        _).comp (hEnv n).measurable).aestronglyMeasurable
    have hYlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (𝓝 (inner ℝ (testL2 f) (G ω (testL2 f)))) := by
      filter_upwards [hG] with ω h
      have := aux_lem_response_reciprocal_quadratic_tendsto (testL2 f) _ _ h
      simpa only [Y, hY] using this
    have hYup : ∀ n, eLpNorm (Y n) (ENNReal.ofReal (max p 1)) μ ≤ ENNReal.ofReal (max CP CN) := by
      intro n
      have h := (hfin (Ns n)).2.1.2
      have hm' : AEStronglyMeasurable (fun om => inverseResponse S
          (cutoffPositiveCoefficient M H om (Ns n) z hr)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL)) (chaosSampleLaw M).toMeasure :=
        (aux_rem_bank_response_moments_measurable_inverseResponse M H hH.1 (Ns n) z hr S
          _).aestronglyMeasurable
      change eLpNorm ((fun om => inverseResponse S (cutoffPositiveCoefficient M H om (Ns n) z hr)
        ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL)) ∘ env n) _ μ ≤ _
      rw [eLpNorm_comp_measurePreserving hm' (hEnv n)]
      exact h
    have hYlow : ∀ n, eLpNorm (fun ω => (Y n ω)⁻¹) (ENNReal.ofReal (max p 1)) μ ≤
        ENNReal.ofReal (max CP CN) := by
      intro n
      have h := (hfin (Ns n)).2.2.2
      have hm' : AEStronglyMeasurable (fun om => (inverseResponse S
          (cutoffPositiveCoefficient M H om (Ns n) z hr)
          ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL))⁻¹) (chaosSampleLaw M).toMeasure :=
        ((aux_rem_bank_response_moments_measurable_inverseResponse M H hH.1 (Ns n) z hr S
          _).inv).aestronglyMeasurable
      change eLpNorm ((fun om => (inverseResponse S (cutoffPositiveCoefficient M H om (Ns n) z hr)
        ((sobolevVolumeLoad (testL2 f)).comp S.space.subtypeL))⁻¹) ∘ env n) _ μ ≤ _
      rw [eLpNorm_comp_measurePreserving hm' (hEnv n)]
      exact h
    obtain ⟨hpos0, ⟨hmem1, hbd1⟩, ⟨hmem2, hbd2⟩⟩ := lem_response_reciprocal_fatou μ (max p 1)
      (max CP CN) (lt_of_lt_of_le hp (le_max_left _ _)) Y _ hYmeas
      (fun n => Filter.Eventually.of_forall fun ω => (hfin (Ns n)).1 (env n ω)) hYlim hYup hYlow
    have h1 := aux_lem_response_reciprocal_mono μ _ (le_max_left p 1) hmem1 hbd1
    have h2 := aux_lem_response_reciprocal_mono μ _ (le_max_left p 1) hmem2 hbd2
    exact ⟨hpos0, h1.1, h1.2, h2.1, h2.2⟩

end
end SubdiffusiveProcess.Paper
