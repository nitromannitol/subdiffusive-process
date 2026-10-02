import SubdiffusiveProcess.Paper.represented_estimates_actual_model
import SubdiffusiveProcess.Paper.thm_C0
import SubdiffusiveProcess.Paper.thm_prop_env_core
import SubdiffusiveProcess.Paper.conv_represented_joint_grids
import SubdiffusiveProcess.Paper.conv_represented_root_family
import SubdiffusiveProcess.Comparison.InverseEnergyOrder

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.Comparison
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_mfd_thm_C0_conditional
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ddet : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha) :
    let L : ℝ := (3 : ℝ) ^ H1
    ∀ (hLlarge : 2 * Cd ^ (eta0 / 3) ≤ L ^ (eta0 / 3 - eta0 / 8))
      (hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) //
          ¬ Metric.closedBall (oddGridCenter zP R (subdivisionHalfWidth H1) i)
              (3 * (R / L) / 2) ⊆
            (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
          Cd * L ^ ((d : ℝ) - 1)),
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (envE envF : ℕ → Ω → BilateralField d)
        (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
        (responseE responseF : ℕ → Ω → ℝ)
        (eventE eventF : Set Ω)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ)
        (Gcatalog : Set Ω)
        (hGcatalogMeas : MeasurableSet Gcatalog)
        (hGcatalogFull : P Gcatalogᶜ = 0),
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (S i)
              (Lane4.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (S i)
              (Lane4.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1) ∧
        (∀ᵐ omega ∂P, ∀ i,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega))) ∧
        (∃ (root : ℕ)
          (hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
              Set (SpatialCoordinates d)) ⊆
            (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
          (Dcat : ∀ i, Submodule ℚ
            (DomainL2 (centeredCube (z i) (r i) (hr i))))
          (hDcat : ∀ i, Countable (Dcat i))
          (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
          (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
          (traceH1 : ∀ i, ℕ → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (S i).space)
          (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (Cext : ℝ) (I : Paper.in_J d)
          (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
          (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
          (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
          (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
          letI : ∀ i, Countable (Dcat i) := hDcat
          conv_represented_estimates d hd model H Ω P NE envE
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcE srcRepE ucellE Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
            (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
          conv_represented_estimates d hd model H Ω P NF envF
            ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
            usrcF srcRepF ucellF Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
            (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)) →
      aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr S GE GF NE NF →
      ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ G ⊆ Gcatalog ∧
        ∀ omega ∈ G, ∀ i : ℕ,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega)) ∧
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
              (limitFormEnergy (GF i omega) u).toReal ∧
            (limitFormEnergy (GF i omega) u).toReal ≤
              C0 * (limitFormEnergy (GE i omega) u).toReal := by
  exact thm_C0 d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp
    eta0 heta0 heta03 D theta alpha eta hD htheta htheta8 halpha halpha1
    heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha

theorem aux_mfd_thm_C0_joint
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ddet : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha) :
    let L : ℝ := (3 : ℝ) ^ H1
    ∀ (hLlarge : 2 * Cd ^ (eta0 / 3) ≤ L ^ (eta0 / 3 - eta0 / 8))
      (hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) //
          ¬ Metric.closedBall (oddGridCenter zP R (subdivisionHalfWidth H1) i)
              (3 * (R / L) / 2) ⊆
            (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
          Cd * L ^ ((d : ℝ) - 1)),
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
      conv_represented_joint_grids d hd model H Ω P field envE envF z r hr Sspace
        GNE GNF GE GF NE NF alpha eta I beta t →
      aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr
        Sspace GE GF NE NF →
      ∀ᵐ omega ∂P, ∀ i : ℕ,
        limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
        ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
          u ∈ limitFormDomain (GE i omega) →
          C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
            (limitFormEnergy (GF i omega) u).toReal ∧
          (limitFormEnergy (GF i omega) u).toReal ≤
            C0 * (limitFormEnergy (GE i omega) u).toReal := by
  intro L hLlarge hCdPad
  obtain ⟨delta0, C0, hdelta0, hC0, hmain⟩ :=
    aux_mfd_thm_C0_conditional d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp
    eta0 heta0 heta03 D theta alpha eta hD htheta htheta8 halpha halpha1
    heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
  refine ⟨delta0, C0, hdelta0, hC0, ?_⟩
  intro _ _ model hmodel Rm Sreg It H Ω _ P _ field envE envF
    z r hr Sspace GNE GNF GE GF NE NF hdata hBounds
  rw [ae_all_iff]
  intro i
  obtain ⟨e, he, hcat⟩ := hdata.2 i
  obtain ⟨j, hj⟩ := he i le_rfl
  obtain ⟨cR, cC, respE, respF, evE, evF, root, hunit, Dcat, hDcat, fcat,
    trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF,
    Cext, betaCat, tCat, ICat, cK, eK, lK, sRK, sGK, sHK, cRK, cGK, cHK,
    origin, gridRoot, gridKey, hmatch, hgrid, hbuffer, hcats⟩ := hcat
  rw [hmatch.2.1, hmatch.2.2] at hcats
  letI : ∀ j, Countable (Dcat j) := hDcat
  have hfinite := aux_thm_prop_env_joint_reindex d model H Ω P field envE envF
    z r hr Sspace GNE GNF GE GF NE NF e hdata.1
  obtain ⟨hP, hfield, hmap, hH, hNE, hNF, hMP, hEnv, hS, hGN, hlim⟩ := hfinite
  have hjoint : aux_thm_C0_JointHypU d hd alpha eta beta t model H Ω P field
      envE envF cR cC respE respF evE evF (z ∘ e) (r ∘ e) (fun j => hr (e j))
      (fun j => Sspace (e j)) (fun j => GNE (e j)) (fun j => GNF (e j))
      (fun j => GE (e j)) (fun j => GF (e j)) NE NF :=
    ⟨hP, hfield, hmap, hH, hNE, hNF, hMP, hEnv, hS, hGN, hlim,
      root, hunit, Dcat, hDcat, fcat, trace, traceH1,
      usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF, Cext, ICat,
      cK, eK, lK, sRK, sGK, sHK, cRK, cGK, cHK, origin, gridRoot, gridKey,
      hcats.1, hcats.2⟩
  have hfiniteBounds : aux_conv_represented_env_interface_bounds d hd model H Ω P
      envE envF (z ∘ e) (r ∘ e) (fun j => hr (e j)) (fun j => Sspace (e j))
      (fun j => GE (e j)) (fun j => GF (e j)) NE NF :=
    hBounds.mono (fun ω h j => h (e j))
  obtain ⟨G, hGmeas, hGfull, _, hcompare⟩ := hmain model hmodel Rm Sreg It H Ω P field envE envF
    cR cC respE respF evE evF (z ∘ e) (r ∘ e) (fun j => hr (e j))
    (fun j => Sspace (e j)) (fun j => GNE (e j)) (fun j => GNF (e j))
    (fun j => GE (e j)) (fun j => GF (e j)) NE NF
    Set.univ MeasurableSet.univ (by simp only [compl_univ, measure_empty])
    hjoint hfiniteBounds
  have hevent : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.mpr hGfull
  filter_upwards [hevent] with ω hω
  rw [← hj]
  exact (hcompare ω hω j).2.2


/-- Scalar quadratic responses of an almost sure killed-inverse limit are measurable
up to completion, without requiring the caller to choose measurable operator versions. -/
theorem aux_mfd_thm_C0_aemeasurable_quadratic_limit (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization model H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (N : ℕ → ℕ)
    (G : BilateralField d → DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr))
    (hlim : ∀ᵐ ω ∂(chaosSampleLaw model).toMeasure,
      Tendsto (fun n => volumeResponseOperator S
        (Lane4.cutoffPositiveCoefficient model H ω (N n) z hr)) atTop (𝓝 (G ω)))
    (f : DomainL2 (centeredCube z r hr)) :
    AEMeasurable (fun ω => inner ℝ f (G ω f)) (chaosSampleLaw model).toMeasure := by
  have hc : Continuous (fun A : DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr) => inner ℝ f (A f)) :=
    continuous_const.inner (ContinuousLinearMap.apply ℝ _ f).continuous
  have hm : ∀ n, Measurable (fun ω => inner ℝ f
      (volumeResponseOperator S (Lane4.cutoffPositiveCoefficient model H ω (N n) z hr) f)) :=
    fun n => (hc.comp_stronglyMeasurable
      (stronglyMeasurable_cutoffVolumeResponseOperator model H hH.1 (N n) z r hr S)).measurable
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hm n).aemeasurable)
    (hlim.mono (fun ω hω => (hc.tendsto (G ω)).comp hω))

/-- A comparison on a produced representation descends to every original-space
operator-limit pair through measurable quadratic readouts on a countable dense family. -/
theorem aux_mfd_thm_C0_original_comparison (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
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
        (Lane4.cutoffPositiveCoefficient model H ω (NE n) (z i) (hr i))) atTop (𝓝 (GE0 i ω)))
    (hlimF : ∀ᵐ ω ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (Sspace i)
        (Lane4.cutoffPositiveCoefficient model H ω (NF n) (z i) (hr i))) atTop (𝓝 (GF0 i ω)))
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
    have hE := aux_mfd_thm_C0_aemeasurable_quadratic_limit d model H hH (z i) (r i) (hr i)
      (Sspace i) NE (GE0 i) (hlimE.mono (fun ω hω => hω i)) f
    have hF := aux_mfd_thm_C0_aemeasurable_quadratic_limit d model H hH (z i) (r i) (hr i)
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


/-- Paper-literal represented-pair export (review Q1). Constants precede the model and cutoff pair. -/
theorem aux_mfd_thm_C0_represented
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ddet : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha) :
    let L : ℝ := (3 : ℝ) ^ H1
    ∀ (hLlarge : 2 * Cd ^ (eta0 / 3) ≤ L ^ (eta0 / 3 - eta0 / 8))
      (hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) //
          ¬ Metric.closedBall (oddGridCenter zP R (subdivisionHalfWidth H1) i)
              (3 * (R / L) / 2) ⊆
            (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
          Cd * L ^ ((d : ℝ) - 1)),
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization model H)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
        (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, z i c = (q : ℝ)) ∧ ∃ m : ℤ, r i = (3 : ℝ) ^ m)
        (hfam : conv_represented_root_family d z r hr)
        (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF),
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
          (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
          (GNE GNF : (i : ℕ) → ℕ → Ω →
            DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
              DomainL2 (centeredCube (z i) (r i) (hr i)))
          (GE GF : (i : ℕ) → Ω →
            DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
              DomainL2 (centeredCube (z i) (r i) (hr i))),
          conv_represented_joint_grids d hd model H Ω P field env env z r hr Sspace
            GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta I beta t ∧
          aux_conv_represented_env_interface_bounds d hd model H Ω P env env z r hr Sspace
            GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) ∧
          ∀ᵐ omega ∂P, ∀ i : ℕ,
            limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GE i omega) →
              C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
                (limitFormEnergy (GF i omega) u).toReal ∧
              (limitFormEnergy (GF i omega) u).toReal ≤
                C0 * (limitFormEnergy (GE i omega) u).toReal := by
  classical
  intro L hLlarge hCdPad
  letI canonicalMeas : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  letI canonicalBorel : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  have hAeta : 1 + eta < 2 * alpha := by linarith
  obtain ⟨_, _, hcharts⟩ := represented_estimates_actual_model d hd alpha eta beta t
    ht htd (by linarith) halpha1 heta hAeta hbeta hbetaAlpha
  obtain ⟨deltaB1, hdeltaB1, hB1⟩ := hcharts I
  obtain ⟨deltaCmp, C0, hdeltaCmp, hC0, hCmp⟩ :=
    aux_mfd_thm_C0_joint d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp
    eta0 heta0 heta03 D theta alpha eta hD htheta htheta8 halpha halpha1
    heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
  refine ⟨min deltaCmp deltaB1, C0, lt_min hdeltaCmp hdeltaB1, hC0, ?_⟩
  intro measC borelC
  have heq : measC = canonicalMeas := borelC.measurable_eq
  subst measC
  intro model hmodel Rm Sreg It H hH z r hr Sspace hS hrat hfam NE NF hNE hNF
  obtain ⟨seq, hseq, Ω, measΩ, P, probP, field, env, GNE, GNF, GE, GF, hdata, hBounds⟩ :=
    (hB1 model (hmodel.trans (min_le_right _ _))).2 H hH z r hr Sspace hS hrat hfam
      NE NF hNE hNF
  letI : MeasurableSpace Ω := measΩ
  letI : IsProbabilityMeasure P := probP
  refine ⟨seq, hseq, Ω, measΩ, P, probP, field, env, GNE, GNF, GE, GF, hdata, hBounds, ?_⟩
  exact hCmp model (hmodel.trans (min_le_left _ _)) Rm Sreg It H Ω P field env env
    z r hr Sspace GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) hdata hBounds

/-- Record-free original-space successor. The complete unbounded determining family follows from countably many rooted applications and intersection of their events. -/
theorem mfd_thm_C0
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ddet : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha) :
    let L : ℝ := (3 : ℝ) ^ H1
    ∀ (hLlarge : 2 * Cd ^ (eta0 / 3) ≤ L ^ (eta0 / 3 - eta0 / 8))
      (hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) //
          ¬ Metric.closedBall (oddGridCenter zP R (subdivisionHalfWidth H1) i)
              (3 * (R / L) / 2) ⊆
            (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
          Cd * L ^ ((d : ℝ) - 1)),
    ∃ delta0 C0 : ℝ, 0 < delta0 ∧ 1 ≤ C0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization model H)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
        (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, z i c = (q : ℝ)) ∧ ∃ m : ℤ, r i = (3 : ℝ) ^ m)
        (hfam : conv_represented_root_family d z r hr)
        (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF)
        (GE GF : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (hlimE : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (Lane4.cutoffPositiveCoefficient model H omega (NE n) (z i) (hr i))) atTop (𝓝 (GE i omega)))
        (hlimF : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (Lane4.cutoffPositiveCoefficient model H omega (NF n) (z i) (hr i))) atTop (𝓝 (GF i omega))),
      ∀ (Gcatalog : Set (BilateralField d))
        (hGcatalogMeas : MeasurableSet Gcatalog)
        (hGcatalogFull : (chaosSampleLaw model).toMeasure Gcatalogᶜ = 0),
      ∃ G : Set (BilateralField d), MeasurableSet G ∧
        (chaosSampleLaw model).toMeasure Gᶜ = 0 ∧ G ⊆ Gcatalog ∧
        ∀ omega ∈ G, ∀ i : ℕ,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (Lane4.cutoffPositiveCoefficient model H omega (NE n) (z i) (hr i))) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (Lane4.cutoffPositiveCoefficient model H omega (NF n) (z i) (hr i))) atTop (𝓝 (GF i omega)) ∧
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            C0⁻¹ * (limitFormEnergy (GE i omega) u).toReal ≤
              (limitFormEnergy (GF i omega) u).toReal ∧
            (limitFormEnergy (GF i omega) u).toReal ≤
              C0 * (limitFormEnergy (GE i omega) u).toReal := by
  classical
  intro L hLlarge hCdPad
  obtain ⟨delta0, C0, hdelta0, hC0, hrepresented⟩ :=
    aux_mfd_thm_C0_represented d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp Interp
    eta0 heta0 heta03 D theta alpha eta hD htheta htheta8 halpha halpha1
    heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
  refine ⟨delta0, C0, hdelta0, hC0, ?_⟩
  intro _ _ model hmodel Rm Sreg It H hH z r hr Sspace hS hrat hfam NE NF hNE hNF
    GE0 GF0 hlimE hlimF
    Gcatalog hGcatalogMeas hGcatalogFull
  obtain ⟨seq, hseq, Ω, measΩ, P, probP, field, env, GNE, GNF, GE, GF,
      hdata, hBounds, hcomparison⟩ :=
    hrepresented model hmodel Rm Sreg It H hH z r hr Sspace hS hrat hfam NE NF hNE hNF
  letI : MeasurableSpace Ω := measΩ
  letI : IsProbabilityMeasure P := probP
  have hCpos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hEF : ∀ᵐ ω ∂P, ∀ i,
      limitFormDomain (GE i ω) ⊆ limitFormDomain (GF i ω) ∧
      ∀ u ∈ limitFormDomain (GE i ω),
        (limitFormEnergy (GF i ω) u).toReal ≤ C0 * (limitFormEnergy (GE i ω) u).toReal := by
    filter_upwards [hcomparison] with ω hω i
    exact ⟨fun _ hu => (hω i).1 ▸ hu, fun u hu => ((hω i).2 u hu).2⟩
  have hFE : ∀ᵐ ω ∂P, ∀ i,
      limitFormDomain (GF i ω) ⊆ limitFormDomain (GE i ω) ∧
      ∀ u ∈ limitFormDomain (GF i ω),
        (limitFormEnergy (GE i ω) u).toReal ≤ C0 * (limitFormEnergy (GF i ω) u).toReal := by
    filter_upwards [hcomparison] with ω hω i
    refine ⟨fun _ hu => (hω i).1.symm ▸ hu, ?_⟩
    intro u hu
    have huE := (hω i).1.symm ▸ hu
    have hlower := ((hω i).2 u huE).1
    have h := mul_le_mul_of_nonneg_left hlower hCpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hCpos.ne', one_mul] using h
  have hswap : aux_conv_represented_env_interface_joint d model H Ω P field env env
      z r hr Sspace GNF GNE GF GE (fun n => NF (seq n)) (fun n => NE (seq n)) := by
    obtain ⟨hP, hm, hmap, hH', hNE', hNF', hMP, hEnv, hS', hGN, hlim⟩ := hdata.1
    exact ⟨hP, hm, hmap, hH', hNF', hNE',
      fun n => ⟨(hMP n).2, (hMP n).1⟩,
      hEnv.mono (fun ω hω => ⟨hω.2, hω.1⟩), hS',
      hGN.mono (fun ω hω i n f => ⟨(hω i n f).2, (hω i n f).1⟩),
      hlim.mono (fun ω hω i => ⟨(hω i).2, (hω i).1⟩)⟩
  have hEF0 := aux_mfd_thm_C0_original_comparison d model H hH z r hr Sspace NE NF seq hseq
    GE0 GF0 hlimE hlimF Ω P field env GNE GNF GE GF hdata.1 C0 hCpos hEF
  have hFE0 := aux_mfd_thm_C0_original_comparison d model H hH z r hr Sspace NF NE seq hseq
    GF0 GE0 hlimF hlimE Ω P field env GNF GNE GF GE hswap C0 hCpos hFE
  apply aux_thm_C0_common_event (chaosSampleLaw model).toMeasure _ _
    Gcatalog hGcatalogMeas hGcatalogFull
  filter_upwards [hlimE, hlimF, hEF0, hFE0] with ω hEω hFω hEFω hFEω i
  refine ⟨hEω i, hFω i, Set.Subset.antisymm (hEFω i).1 (hFEω i).1, ?_⟩
  intro u hu
  refine ⟨?_, (hEFω i).2 u hu⟩
  have h := mul_le_mul_of_nonneg_left ((hFEω i).2 u ((hEFω i).1 hu)) (inv_pos.mpr hCpos).le
  simpa only [← mul_assoc, inv_mul_cancel₀ hCpos.ne', one_mul] using h

end Paper






