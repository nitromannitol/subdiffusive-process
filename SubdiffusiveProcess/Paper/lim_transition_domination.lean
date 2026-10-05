module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.Main.CutoffSpeedMeasure
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Main.JointPathProbabilityMeasure
public import SubdiffusiveProcess.Main.PathLevyProkhorovDist
public import SubdiffusiveProcess.Main.DiffusionPath

public import SubdiffusiveProcess.Paper.lim_thm_measure
public import SubdiffusiveProcess.Paper.lim_thm_nongaussian

@[expose] public section




open Filter MeasureTheory ProbabilityTheory Topology Asymptotics Set
open MarkovProcess SubdiffusiveProcess SubdiffusiveProcess.Section10
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper


/-- One event supports the actual cutoff limit, retained density and spatial
laws, every positive-time marginal and every bounded-open killed estimate. -/
theorem aux_lim_transition_domination_actual_same_limit_transition_bounds {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ δ →
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      ∀ (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N)), in_crossing M H PN KN →
      ∀ (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hK : IsMarkovKernel K), aux_lim_thm_nongaussian_QuenchedConv M KN hKN K hK →
      ∃ mu0 : BilateralField d → Measure (SpatialCoordinates d), Measurable mu0 ∧
        (∀ w, IsLocallyFiniteMeasure (mu0 w)) ∧
        Measurable (infraredWeightedLimit H mu0) ∧
        (∀ w, IsLocallyFiniteMeasure (infraredWeightedLimit H mu0 w)) ∧
        SameLimitSpatialLaws M mu0 ∧
        ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
          SameLimitDensityProperties M H mu0 w ∧ aux_lim_thm_measure_SameLimitMeasureRegular H mu0 w ∧
          MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H w N)
            (infraredWeightedLimit H mu0 w) ∧
          (∀ x : SpatialCoordinates d, ∀ t : ℝ≥0, 0 < t →
            (K (w, x)).map (fun path : DiffusionPath d => path t) ≪
              infraredWeightedLimit H mu0 w) ∧
          ∀ U : Set (SpatialCoordinates d), IsOpen U → Bornology.IsBounded U →
            ∃ CU : ℝ, 0 < CU ∧ ∀ x ∈ U, ∀ t : ℝ≥0, 0 < t →
              ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
                K (w, x) {path | path t ∈ A ∧ (t : ℝ≥0∞) < ContinuousPath.exitTime U path} ≤
                  ENNReal.ofReal (CU * (t : ℝ) ^ (-(d : ℝ))) *
                    (infraredWeightedLimit H mu0 w).restrict U A := by
  obtain ⟨δm, hδm, hdata⟩ := aux_lim_thm_measure_exists_same_limit_measure_root_data hd 1 (by norm_num)
  obtain ⟨δt, hδt, htrans⟩ := aux_lim_thm_nongaussian_actual_limit_transition_bounds hd
  refine ⟨min δm δt, lt_min hδm hδt, ?_⟩
  intro M hM H hH PN KN hKN hin K hK hconv
  obtain ⟨mu0, hm, hl, hwm, hwl, hdensity, hspatial, _, _, _⟩ :=
    hdata M (hM.trans (min_le_left _ _)) H hH
  have hc : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H w N)
        (infraredWeightedLimit H mu0 w) := by
    filter_upwards [hdensity] with w hw
    exact measuresConvergeLocally_congr _ _ _
      (fun N => (cutoffSpeedMeasure_eq_weightedChaosCutoff M H w N).symm) hw.1.2.2.2.2.1
  have hdom := htrans M (hM.trans (min_le_right _ _)) H hH PN KN hKN hin K hK hconv
    (infraredWeightedLimit H mu0) hwl hc
  refine ⟨mu0, hm, hl, hwm, hwl, hspatial, ?_⟩
  filter_upwards [hdensity, hc, hdom] with w hm hw hp
  exact ⟨hm.1, hm.2, hw, hp.1, hp.2⟩


theorem lim_transition_domination
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (_Pc : in_poincare d hd Jc) (_Xc : in_extension d hd Jc)
    (_Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) (_W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (_Cp : _root_.SubdiffusiveProcess.EllipticRegularity.CampanatoInput d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M Jc Sreg),
        M.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N))
        (_hin : in_crossing M H PN KN)
        (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
          (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
        (_hL : ∀ N omega x,
          Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
            L N omega x)
        (_hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
            (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
        (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hK : IsMarkovKernel K)
        (_hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ B : Set (SpatialCoordinates d), IsCompact B →
            ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ x ∈ B,
              pathLevyProkhorovDist
                (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                (jointPathProbabilityMeasure K hK omega x) < epsilon),
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ mu : Measure (SpatialCoordinates d),
            MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) mu →
            ∀ (x : SpatialCoordinates d) (t : ℝ≥0), 0 < t →
              (K (omega, x)).map (fun w : DiffusionPath d => w t) ≪ mu := by
  obtain ⟨δ, hδ, hbound⟩ := aux_lim_transition_domination_actual_same_limit_transition_bounds hd
  refine ⟨δ, hδ, ?_⟩
  intro M Rm Sreg It hM H hH PN KN hKN hin L hL hLloc K hK hconv
  clear It Sreg Rm _Cp _W _Sf _Xc _Pc Jc hLloc hL L
  obtain ⟨mu0, _, _, _, hwl, _, hall⟩ :=
    hbound M hM H hH PN KN hKN hin K hK hconv
  filter_upwards [hall] with w hw
  intro mu hc x t ht
  let := hwl w
  let : (SubdiffusiveProcess.Section10.infraredWeightedLimit H mu0 w).IsOpenPosMeasure :=
    hw.2.1.2.2.2.2.2
  have heq := aux_lim_transition_domination_vague_identification
    (fun N => cutoffSpeedMeasure M H w N)
    (SubdiffusiveProcess.Section10.infraredWeightedLimit H mu0 w) mu hw.2.2.1 hc
  subst mu
  exact hw.2.2.2.1 x t ht


end SubdiffusiveProcess.Paper
