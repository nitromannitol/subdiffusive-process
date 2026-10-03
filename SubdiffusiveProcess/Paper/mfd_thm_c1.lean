module

public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Paper.s9_actual_uniqueness
public import SubdiffusiveProcess.Paper.in_killed_inverse_inprob
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_family_grids_actual
public import SubdiffusiveProcess.Paper.thm_c1_cube_positive_energy
public import SubdiffusiveProcess.Probability.ConvergenceInProbability
public import SubdiffusiveProcess.Section9.RepresentedComparisonDraft
public import SubdiffusiveProcess.Section9.CountableLimitSubsequence
public import SubdiffusiveProcess.Section9.ExtendedComparisonEndpoints
public import SubdiffusiveProcess.Section9.ActualLimitPositiveEnergy

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Section9
open scoped Topology ENNReal NNReal
noncomputable section
namespace Paper

/-- All original-law killed inverses have one measurable full-sequence limit.
Every analytic input and the original-space uniqueness criterion are produced. -/
theorem aux_mfd_thm_c1_actual_limits
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, 0 < M.delta → M.delta ≤ delta0 →
      ∃ G : KilledInverseFamily d (BilateralField d), (∀ i, Measurable (G i)) ∧
        ∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun N β => representedCutoffInverse d hd M (BilateralField d)
            (fun _ β => β) id i N β) atTop (G i) := by
  classical
  obtain ⟨Jc, Pc, Xc, Sf, W, Cp, D, hES, Step, Dbase, Interp, BD, BDQ,
    hcontract, hlifetime, EM, deltaR, Cresp, hdeltaR, hCresp, hresponses⟩ :=
    inputs_simultaneous d hd
  obtain ⟨deltaG, hdeltaG, hlimit⟩ :=
    in_killed_inverse_inprob d hd Interp Jc Pc Xc W Cp Sf
      (s9_actual_uniqueness d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ hcontract)
  refine ⟨min deltaR deltaG, lt_min hdeltaR hdeltaG, ?_⟩
  intro M hMpos hMle
  obtain ⟨Rm, Sreg, hRm, ⟨It⟩⟩ := hresponses M hMpos (hMle.trans (min_le_left _ _))
  have hH : InfraredCharacterization M (comparisonInfrared d hd M) :=
    Classical.choose_spec (exists_infraredCharacterization hd M)
  have hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, rationalTriadicCenter d i c = (q : ℝ)) ∧
      ∃ m : ℤ, rationalTriadicSide d i = (3 : ℝ) ^ m := by
    intro i
    exact ⟨fun c => ⟨(rationalTriadicEnumeration d i).1 c, rfl⟩,
      (rationalTriadicEnumeration d i).2, rfl⟩
  obtain ⟨G, hGmeas, hGprob⟩ := hlimit M Rm Sreg It (comparisonInfrared d hd M) hH
    (hMle.trans (min_le_right _ _)) (rationalTriadicCenter d) (rationalTriadicSide d)
    (rationalTriadicSide_pos d) (fun i => determiningResponseSpace d i) (fun _ => rfl) hrat
    (rationalTriadicCatalogue_complete d)
  refine ⟨G, hGmeas, fun i => ?_⟩
  apply (SubdiffusiveProcess.Probability.tendstoInMeasure_iff_probability_bounds
    (chaosSampleLaw M).toMeasure _ (G i)).mpr
  simpa only [representedCutoffInverse, Function.id_def, dist_eq_norm] using hGprob i


/-- Two cutoff branches converge to the canonical limit on one original-law event. -/
theorem aux_mfd_thm_c1_common_cutoff_limits
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (G : KilledInverseFamily d (BilateralField d))
    (hconv : ∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N β => representedCutoffInverse d hd M (BilateralField d)
        (fun _ β => β) id i N β) atTop (G i))
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∀ᵐ β ∂(chaosSampleLaw M).toMeasure, ∀ i,
        Tendsto (fun n => representedCutoffInverse d hd M (BilateralField d)
          (fun _ β => β) (NE ∘ seq) i n β) atTop (𝓝 (G i β)) ∧
        Tendsto (fun n => representedCutoffInverse d hd M (BilateralField d)
          (fun _ β => β) (NF ∘ seq) i n β) atTop (𝓝 (G i β)) := by
  let P := (chaosSampleLaw M).toMeasure
  let F : ℕ → Type := fun i =>
    (DomainL2 (determiningCube d i) →L[ℝ] DomainL2 (determiningCube d i)) ×
    (DomainL2 (determiningCube d i) →L[ℝ] DomainL2 (determiningCube d i))
  let X : ∀ i, ℕ → BilateralField d → F i := fun i n β =>
    (representedCutoffInverse d hd M (BilateralField d) (fun _ β => β) NE i n β,
     representedCutoffInverse d hd M (BilateralField d) (fun _ β => β) NF i n β)
  have hX : ∀ i, TendstoInMeasure P (X i) atTop (fun β => (G i β, G i β)) := by
    intro i
    exact tendstoInMeasure_prod P _ _ _ _
      ((hconv i).comp hNE.tendsto_atTop) ((hconv i).comp hNF.tendsto_atTop)
  obtain ⟨seq, hseq, hae⟩ := exists_common_ae_subsequence P X (fun i β => (G i β, G i β)) hX
  refine ⟨seq, hseq, ?_⟩
  filter_upwards [hae] with β hβ i
  have hp := hβ i
  dsimp only [F, X] at hp
  constructor
  · exact (continuous_fst.tendsto (G i β, G i β)).comp hp
  · exact (continuous_snd.tendsto (G i β, G i β)).comp hp

/-- The canonical in-probability limit inhabits every pair's common-refinement carrier. -/
theorem aux_mfd_thm_c1_joint_existence_of_actual_limit
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (G : KilledInverseFamily d (BilateralField d)) (hG : ∀ i, Measurable (G i))
    (hconv : ∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N β => representedCutoffInverse d hd M (BilateralField d)
        (fun _ β => β) id i N β) atTop (G i))
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF) :
    HasJointCutoffLimits d hd M NE NF := by
  obtain ⟨seq, hseq, hae⟩ := aux_mfd_thm_c1_common_cutoff_limits d hd M G hconv NE NF hNE hNF
  let P := (chaosSampleLaw M).toMeasure
  exact ⟨seq, hseq, BilateralField d, inferInstance, P, id, (fun _ β => β), G, G,
    inferInstance, MeasurePreserving.id P, hNE.comp hseq, hNF.comp hseq,
    (fun _ => MeasurePreserving.id P), Filter.Eventually.of_forall (fun _ => tendsto_const_nhds),
    hae, G, G, hG, hG, Filter.Eventually.of_forall (fun _ i => ⟨rfl, rfl⟩)⟩

/-- Every chosen representation has the actual full-sequence inverse limit at its field. -/
theorem aux_mfd_thm_c1_identify_actual_limit
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (G : KilledInverseFamily d (BilateralField d))
    (hconv : ∀ i, TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun N β => representedCutoffInverse d hd M (BilateralField d)
        (fun _ β => β) id i N β) atTop (G i))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
    (GE GF : KilledInverseFamily d Ω) (NE NF : ℕ → ℕ)
    (hjoint : JointCutoffLimits d hd M Ω P field env GE GF NE NF) :
    ∀ᵐ ω ∂P, ∀ i, GE i ω = G i (field ω) ∧ GF i ω = G i (field ω) := by
  obtain ⟨hP, hfield, hNE, hNF, hmp, henv, hops, hfactor⟩ := hjoint
  haveI : IsProbabilityMeasure P := hP
  have hH : InfraredCharacterization M (comparisonInfrared d hd M) :=
    Classical.choose_spec (exists_infraredCharacterization hd M)
  obtain ⟨seq, hseq, horig⟩ := aux_mfd_thm_c1_common_cutoff_limits d hd M G hconv NE NF hNE hNF
  choose Dsub hDc hDd hDs using fun i =>
    SmoothSources.exists_countable_dense_smooth_submodule
      (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
  rw [ae_all_iff]
  intro i
  have hlim : ∀ (N : ℕ → ℕ) (Glim : Ω → DomainL2 (determiningCube d i) →L[ℝ]
      DomainL2 (determiningCube d i)),
      (∀ᵐ β ∂(chaosSampleLaw M).toMeasure,
        Tendsto (fun n => representedCutoffInverse d hd M (BilateralField d)
          (fun _ β => β) (N ∘ seq) i n β) atTop (𝓝 (G i β))) →
      (∀ᵐ ω ∂P, Tendsto (fun n => representedCutoffInverse d hd M Ω env N i n ω)
        atTop (𝓝 (Glim ω))) →
      ∀ᵐ ω ∂P, Glim ω = G i (field ω) := by
    intro N Glim h0 h1
    apply aux_s9_actual_uniqueness_identify d M (comparisonInfrared d hd M) hH
      (rationalTriadicCenter d i) (rationalTriadicSide d i) (rationalTriadicSide_pos d i)
      (determiningResponseSpace d i) (Dsub i : Set _) (hDc i) (hDd i)
      (fun x hx y hy => (Dsub i).add_mem hx hy) (N ∘ seq) P field
      (fun n => env (seq n))
      (fun n ω => representedCutoffInverse d hd M Ω env N i (seq n) ω) Glim (G i)
      hfield (fun n => hmp (seq n))
    · filter_upwards [henv] with ω hω
      exact hω.comp hseq.tendsto_atTop
    · exact Filter.Eventually.of_forall fun ω n f => volumeResponseOperator_apply _ _ f
    · filter_upwards [h1] with ω hω
      exact hω.comp hseq.tendsto_atTop
    · exact h0
  have hE := hlim NE (GE i) (horig.mono fun β h => (h i).1)
    (hops.mono fun ω h => (h i).1)
  have hF := hlim NF (GF i) (horig.mono fun β h => (h i).2)
    (hops.mono fun ω h => (h i).2)
  filter_upwards [hE, hF] with ω he hf
  exact ⟨he, hf⟩


theorem aux_mfd_thm_c1_positive_energy
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        0 < M.delta → M.delta ≤ delta0 →
      ∀ G : BilateralField d →
          DomainL2 (determiningCube d 0) →L[ℝ] DomainL2 (determiningCube d 0),
        Measurable G →
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun N β => representedCutoffInverse d hd M (BilateralField d)
            (fun _ β => β) id 0 N β) atTop G →
        ∀ᵐ β ∂(chaosSampleLaw M).toMeasure,
          ∃ u : DomainL2 (determiningCube d 0),
            u ∈ limitFormDomain (G β) ∧
            0 < (limitFormEnergy (G β) u).toReal := by
  classical
  obtain ⟨Jc, Pc, Xc, Sf, W, Cp, D, hES, Step, Serr, hInterp, hBD, hBDQ,
    hContract, hLife, EM, deltaInputs, Cresp, hDeltaInputs, hCresp, hInputs⟩ :=
    Paper.inputs_simultaneous d hd
  obtain ⟨deltaFamily, hDeltaFamily, hFamily⟩ :=
    Paper.conv_represented_thm_c1_family_grids_actual d hd hInterp Jc Pc Xc W Cp Sf
      (3 / 4) (1 / 4) (2 / 3) ((d : ℝ) - 1 / 2)
      (by linarith) (by linarith) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨min deltaInputs deltaFamily, lt_min hDeltaInputs hDeltaFamily, ?_⟩
  intro M hMpos hMle G hGmeas hConv
  obtain ⟨Rm, Sreg, hRm, ⟨It⟩⟩ :=
    hInputs M hMpos (hMle.trans (min_le_left _ _))
  have hH : InfraredCharacterization M (comparisonInfrared d hd M) :=
    Classical.choose_spec (exists_infraredCharacterization hd M)
  obtain ⟨cutoff, hCutoff, hOriginal⟩ := hConv.exists_seq_tendsto_ae
  have hSpaces : ∀ i, (determiningResponseSpace d i).space =
      killedSobolevGraph (determiningCube d i) := fun i => rfl
  have hRational : ∀ i,
      (∀ j : Fin d, ∃ q : ℚ, rationalTriadicCenter d i j = (q : ℝ)) ∧
        ∃ k : ℤ, rationalTriadicSide d i = (3 : ℝ) ^ k := by
    intro i
    exact ⟨fun j => ⟨(rationalTriadicEnumeration d i).1 j, rfl⟩,
      ⟨(rationalTriadicEnumeration d i).2, rfl⟩⟩
  obtain ⟨seq, hSeq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF,
      hJoint, hBounds, hForms⟩ :=
    hFamily M Rm Sreg It (comparisonInfrared d hd M) hH
      (hMle.trans (min_le_right _ _)) (rationalTriadicCenter d)
      (rationalTriadicSide d) (rationalTriadicSide_pos d) (fun i => determiningResponseSpace d i)
      hSpaces hRational (rationalTriadicCatalogue_complete d) cutoff cutoff hCutoff hCutoff
  haveI : IsProbabilityMeasure Ph := hPh
  obtain ⟨hProbability, hFieldMeas, hFieldLaw, hInfrared, hNE, hNF,
      hEnvLaw, hEnvConv, hKilledSpaces, hOperators, hLimits⟩ := hJoint.1
  have hFieldMP : MeasurePreserving field Ph (chaosSampleLaw M).toMeasure :=
    ⟨hFieldMeas, hFieldLaw⟩
  obtain ⟨Dtest, hDcount, hDdense, hDsmooth⟩ :=
    SmoothSources.exists_countable_dense_smooth_submodule
      (rationalTriadicCenter d 0) (rationalTriadicSide d 0) (rationalTriadicSide_pos d 0)
  have hIdentify : ∀ᵐ ω ∂Ph, GE 0 ω = G (field ω) := by
    apply Paper.aux_s9_actual_uniqueness_identify d M (comparisonInfrared d hd M) hH
      (rationalTriadicCenter d 0) (rationalTriadicSide d 0) (rationalTriadicSide_pos d 0)
      (determiningResponseSpace d 0) (Dtest : Set _) hDcount hDdense
      (fun x hx y hy => Dtest.add_mem hx hy) (fun n => cutoff (seq n)) Ph
      field env (GNE 0) (GE 0) G hFieldMP (fun n => (hEnvLaw n).1)
    · filter_upwards [hEnvConv] with ω hω
      exact hω.1
    · filter_upwards [hOperators] with ω hω
      exact fun n f => (hω 0 n f).1
    · filter_upwards [hLimits] with ω hω
      exact (hω 0).1
    · filter_upwards [hOriginal] with β hβ
      exact hβ.comp hSeq.tendsto_atTop
  have hRepresentedNonzero : ∀ᵐ ω ∂Ph, GE 0 ω ≠ 0 := by
    filter_upwards [hForms] with ω hω
    obtain ⟨LE, LF, hLocal, hConsistency⟩ := hω
    exact limitInverse_ne_zero_of_positive_energy (GE 0 ω)
      (Paper.aux_thm_c1_cube_positive_energy
        (rationalTriadicCenter d 0) (rationalTriadicSide d 0) (rationalTriadicSide_pos d 0)
        (GE 0 ω) (LE 0).form.toClosedForm (LE 0).energy_eq)
  have hFieldNonzero : ∀ᵐ ω ∂Ph, G (field ω) ≠ 0 := by
    filter_upwards [hIdentify, hRepresentedNonzero] with ω hIdentifyω hNonzeroω
    rwa [← hIdentifyω]
  have hNonzero : ∀ᵐ β ∂(chaosSampleLaw M).toMeasure, G β ≠ 0 := by
    have hEvent : MeasurableSet {β | G β ≠ 0} :=
      (hGmeas (isClosed_singleton.measurableSet : MeasurableSet { (0 : DomainL2 (determiningCube d 0) →L[ℝ] DomainL2 (determiningCube d 0))})).compl
    rw [← hFieldMP.map_eq]
    exact (ae_map_iff hFieldMeas.aemeasurable hEvent).2 hFieldNonzero
  filter_upwards [hOriginal, hNonzero] with β hLimit hNonzeroβ
  have hSymmPos := Paper.aux_s9_actual_uniqueness_limit_symm_pos d M
    (comparisonInfrared d hd M) (rationalTriadicCenter d 0) (rationalTriadicSide d 0)
    (rationalTriadicSide_pos d 0) (determiningResponseSpace d 0) cutoff β (G β) hLimit
  exact exists_positive_energy_of_symmetric_positive_ne_zero
    (G β) hSymmPos.1 hSymmPos.2 hNonzeroβ


/-- One actual producer supplies nonvacuity, universal inverse equality, and a
positive finite-energy reference test on every already chosen joint representation. -/
theorem aux_mfd_thm_c1_joint_conclusions
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, 0 < M.delta → M.delta ≤ delta0 →
      (∀ (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
        HasJointCutoffLimits d hd M NE NF) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
        (GE GF : KilledInverseFamily d Ω) (NE NF : ℕ → ℕ),
        JointCutoffLimits d hd M Ω P field env GE GF NE NF →
        ∀ᵐ ω ∂P, (∀ i, GE i ω = GF i ω) ∧
          ∃ u : DomainL2 (determiningCube d 0),
            u ∈ limitFormDomain (GE 0 ω) ∧
            0 < (limitFormEnergy (GE 0 ω) u).toReal := by
  obtain ⟨deltaA, hdeltaA, hactual⟩ := aux_mfd_thm_c1_actual_limits d hd
  obtain ⟨deltaB, hdeltaB, hpositive⟩ := aux_mfd_thm_c1_positive_energy d hd
  refine ⟨min deltaA deltaB, lt_min hdeltaA hdeltaB, ?_⟩
  intro M hMpos hMle
  obtain ⟨G, hG, hconv⟩ := hactual M hMpos (hMle.trans (min_le_left _ _))
  have hPos := hpositive M hMpos (hMle.trans (min_le_right _ _)) (G 0) (hG 0) (hconv 0)
  refine ⟨fun NE NF hNE hNF =>
    aux_mfd_thm_c1_joint_existence_of_actual_limit d hd M G hG hconv NE NF hNE hNF, ?_⟩
  intro Ω _ P field env GE GF NE NF hjoint
  have hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure := hjoint.2.1
  have hId := aux_mfd_thm_c1_identify_actual_limit d hd M G hconv Ω P field env GE GF NE NF hjoint
  filter_upwards [hId, hfield.quasiMeasurePreserving.ae hPos] with ω hω hp
  refine ⟨fun i => (hω i).1.trans (hω i).2.symm, ?_⟩
  simpa only [(hω 0).1] using hp

theorem mfd_thm_c1
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, 0 < M.delta → M.delta ≤ delta0 →
      (∀ (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
        HasJointCutoffLimits d hd M NE NF) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
        (GE GF : KilledInverseFamily d Ω) (NE NF : ℕ → ℕ),
        JointCutoffLimits d hd M Ω P field env GE GF NE NF →
      (∀ᵐ ω ∂P, ∀ i, GE i ω = GF i ω) ∧
      (∀ᵐ ω ∂P, ProportionalLimitForms d Ω GE GF 1 ω) ∧
      ∀ c : ℝ, 0 < c → (∀ᵐ ω ∂P, ProportionalLimitForms d Ω GE GF c ω) → c = 1 := by
  obtain ⟨delta0, hdelta0, hactual⟩ := aux_mfd_thm_c1_joint_conclusions d hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hMpos hMle
  obtain ⟨hExists, hSelected⟩ := hactual M hMpos hMle
  refine ⟨hExists, ?_⟩
  intro Ω _ P field env GE GF NE NF hjoint
  have h := hSelected Ω P field env GE GF NE NF hjoint
  have hEq := h.mono fun ω hω => hω.1
  have hProp := h.mono fun ω hω => proportional_one_of_inverse_eq GE GF ω hω.1
  refine ⟨hEq, hProp, ?_⟩
  intro c hc hpc
  haveI : IsProbabilityMeasure P := hjoint.1
  have hScalar : ∀ᵐ ω ∂P, c = 1 := by
    filter_upwards [h, hpc] with ω hω hp
    obtain ⟨u, hu, hpos⟩ := hω.2
    exact proportional_scalar_eq GE GF ω c 1 hc zero_lt_one hp
      (proportional_one_of_inverse_eq GE GF ω hω.1) ⟨0, u, hu, hpos⟩
  obtain ⟨ω, hω⟩ := hScalar.exists
  exact hω

end Paper
