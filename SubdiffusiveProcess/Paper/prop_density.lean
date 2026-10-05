module

public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.ResponseMoments.UpperDensity
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.lem_boundary
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_goodext
public import SubdiffusiveProcess.Paper.lem_skeleton
public import SubdiffusiveProcess.Paper.parameter_chain
public import SubdiffusiveProcess.Paper.prop_allchain
public import SubdiffusiveProcess.Paper.prop_density_core_closure
public import SubdiffusiveProcess.Paper.prop_density_core_comparison
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.reference_coefficients
public import SubdiffusiveProcess.Paper.prop_density_core_approximation
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Clause C (catalogue completeness) of `conv_represented_estimates`: if the unit cube lies in
the catalogue root, the determining family contains it. -/
theorem aux_prop_density_unit_index
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (root : ℕ) (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (Dcat : ∀ i, Submodule ℚ (DomainL2 (centeredCube (z i) (r i) (hr i))))
    [hDcat : ∀ i, Countable (Dcat i)]
    (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
    (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (traceH1 : ∀ i, ℕ → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (usrc : ∀ i, Dcat i → ℕ → Ω → (S i).space)
    (srcRep : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (Cext beta alpha eta t : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (resp : ℕ → ℕ → Ω → ℝ) (response : ℕ → Ω → ℝ) (consts : ℕ → ℕ → Ω → ℝ)
    (event : Set Ω)
    (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
    (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
    (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ)
    (h : conv_represented_estimates d hd model H Ω P cutoff env
      ℕ root z r hr S Dcat fcat (fun _ => ℕ) trace traceH1
      usrc srcRep ucell Cext beta alpha eta t {1} I
      ℕ resp response consts event
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)
    (hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d))) :
    ∃ i0 : ℕ, z i0 = 0 ∧ r i0 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hC4, -⟩ := h
  obtain ⟨j, hj1, hj2⟩ := hC4 0 1 one_pos (fun _ => ⟨0, by simp⟩) ⟨0, by simp⟩ hunitRoot
  exact ⟨j, hj1, hj2⟩



theorem prop_density
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (_X : _root_.SubdiffusiveProcess.Paper.in_extension d hd I)
    (_Sob : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (_Step : _root_.SubdiffusiveProcess.Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (Pin : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (Ddet : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d)
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
    ∀ (_hLlarge : 2 * Cd ^ (eta0 / 3) ≤ L ^ (eta0 / 3 - eta0 / 8))
      (_hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) //
          ¬ Metric.closedBall (oddGridCenter zP R (subdivisionHalfWidth H1) i)
              (3 * (R / L) / 2) ⊆
            (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
          Cd * L ^ ((d : ℝ) - 1)),
    ∃ delta0 Cstar : ℝ, 0 < delta0 ∧ 0 < Cstar ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d), model.delta ≤ delta0 →
      ∀ (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d model) (Sreg : _root_.SubdiffusiveProcess.Paper.in_6_16 d model)
        (_It : _root_.SubdiffusiveProcess.Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d)
        (envE envF : ℕ → Ω → BilateralField d)
        (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
        (responseE responseF : ℕ → Ω → ℝ)
        (eventE eventF : Set Ω)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (GNE GNF : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ),
      (IsProbabilityMeasure P ∧ Measurable field ∧
        Measure.map field P = (chaosSampleLaw model).toMeasure ∧
        InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
        (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
          MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
        (∀ᵐ omega ∂P,
          Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
          Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
        (∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
        (∀ᵐ omega ∂P, ∀ i n f,
          GNE i n omega f =
            (responseSolution (Sspace i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1 ∧
          GNF i n omega f =
            (responseSolution (Sspace i)
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
              ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1) ∧
        (∀ᵐ omega ∂P, ∀ i,
          Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
          Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega))) ∧
        (∃ (root : ℕ)
          (_hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
              Set (SpatialCoordinates d)) ⊆
            (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
          (Dcat : ∀ i, Submodule ℚ
            (DomainL2 (centeredCube (z i) (r i) (hr i))))
          (hDcat : ∀ i, Countable (Dcat i))
          (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
          (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
          (traceH1 : ∀ i, ℕ → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
          (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
          (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
            (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
          (Cext : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
          (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
          (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
          (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
          (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
          letI : ∀ i, Countable (Dcat i) := hDcat
          conv_represented_estimates d hd model H Ω P NE envE
            ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
            usrcE srcRepE ucellE Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
            (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
          conv_represented_estimates d hd model H Ω P NF envF
            ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
            usrcF srcRepF ucellF Cext beta alpha eta t {1} I
            ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
            (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
            coercivityKey extensionKey lambdaKey
            sourceResponseKey sourceGrowthKey sourceHolderKey
            cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey)) →
      aux_conv_represented_env_interface_bounds d hd model H Ω P envE envF z r hr Sspace GE GF NE NF →
      ∀ (eE eF : ℕ → ℝ), (∀ k, 0 < eE k ∧ 0 < eF k) →
      let kappa : ℕ → ℝ := fun N =>
        Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
      (∀ k, Tendsto (fun j => kappa (NE j - k) / kappa (NE j)) atTop (nhds (eE k))) →
      (∀ k, Tendsto (fun j => kappa (NF j - k) / kappa (NF j)) atTop (nhds (eF k))) →
      ∀ (Sset : ℕ → Prop) (a : ℝ), 0 < a → eta0 ≤ upperDensity Sset →
        (∀ n, Sset n → eF (H1 * n) / eE (H1 * n) ≤ a) →
        ∀ᵐ omega ∂P, ∀ i : ℕ,
          limitFormDomain (GE i omega) ⊆ limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            (limitFormEnergy (GF i omega) u).toReal ≤
              Cstar * a * (limitFormEnergy (GE i omega) u).toReal := by
  intro L hLlarge hCdPad
  have hB := lem_boundary d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp eta0 heta0 heta03 D theta alpha eta hD htheta htheta8
    halpha halpha1 heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
  obtain ⟨delta0, Cstar, hdelta0, hCstar, hmain⟩ := hB
  refine ⟨delta0, Cstar, hdelta0, hCstar, ?_⟩
  intro _ _ model hmodel Rm Sreg It H Ω _ P _ field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr Sspace GNE GNF GE GF NE NF hjointU hBoundsP
    eE eF hpos kappa hE hF Sset a ha hdens hratio
  obtain ⟨hP, hMeasF, hMap, hInfra, hNEmono, hNFmono, hMP, hEnvTend, hSdef, hGNdef, hGconv,
    hcat⟩ := hjointU
  obtain ⟨root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey,
    cellResponseKey, cellGrowthKey, cellHolderKey,
    origin, gridRoot, gridKey, hCatE, hCatF⟩ := hcat
  let : ∀ i, Countable (Dcat i) := hDcat
  have hunit : ∃ i0 : ℕ, z i0 = 0 ∧ r i0 = 1 :=
    aux_prop_density_unit_index d hd model H Ω P NE envE root z r hr Sspace Dcat fcat
      trace traceH1 usrcE srcRepE ucellE Cext beta alpha eta t I _ responseE _ eventE
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey origin gridRoot gridKey hCatE hunitRoot
  obtain ⟨unit, hunitz, hunitr⟩ := hunit
  exact hmain model hmodel Rm Sreg It H Ω P field envE envF catalogResponse catalogConstant
    responseE responseF eventE eventF z r hr Sspace GNE GNF GE GF NE NF
    ⟨hP, hMeasF, hMap, hInfra, hNEmono, hNFmono, hMP, hEnvTend, hSdef, hGNdef, hGconv,
      root, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE, ucellF,
      Cext, I, coercivityKey, extensionKey, lambdaKey,
      sourceResponseKey, sourceGrowthKey, sourceHolderKey,
      cellResponseKey, cellGrowthKey, cellHolderKey, origin, gridRoot, gridKey, hCatE, hCatF⟩
    hBoundsP eE eF hpos hE hF unit hunitz hunitr Sset a ha hdens hratio

end
end SubdiffusiveProcess.Paper
