module

public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.MeasurabilityProviders
public import Homogenization.Book.Ch04.Law

@[expose] public section

/-!
# Chapter 4 law carrier for a finite GMC cutoff

This module packages the literal scalar coefficient `aCutoff M L` as a
measurable `RegCoeffField`-valued random variable and proves that its
pushforward law is supported on the Chapter 4 locally uniformly elliptic
carrier.

PROVENANCE: this is the scalar-exponential analogue of
`Algsuperdiff/Section3/Cutoff/Law.lean` and
`Algsuperdiff/Section3/Cutoff/LawCarrier.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory ProbabilityTheory Homogenization Homogenization.Book

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The finite scalar cutoff as a regular matrix-valued coefficient field. -/
noncomputable def aCutoffRegCoeffField {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    RegCoeffField d where
  toFun x := scalarMatrix (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)
  entry_measurable := fun i j => by
    have hcont : Continuous (fun x : Vec d =>
        scalarMatrix (d := d) (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)) :=
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).smul
        (continuous_const : Continuous (fun _ : Vec d => (1 : Mat d)))
    exact ((continuous_apply j).comp ((continuous_apply i).comp hcont)).measurable
  entry_locInt := fun i j => by
    have hcont : Continuous (fun x : Vec d =>
        scalarMatrix (d := d) (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)) :=
      (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).smul
        (continuous_const : Continuous (fun _ : Vec d => (1 : Mat d)))
    exact ((continuous_apply j).comp
      ((continuous_apply i).comp hcont)).locallyIntegrable

@[simp]
theorem aCutoffRegCoeffField_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (x : Vec d) :
    aCutoffRegCoeffField M L omega x =
      scalarMatrix (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) :=
  rfl



theorem measurable_aCutoffRegCoeffField {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    Measurable (aCutoffRegCoeffField M L) := by
  refine measurable_into_regCoeffField' ?_ ?_
  · intro x i j
    have hmat : Measurable (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        scalarMatrix (d := d) (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x)) :=
      (SubdiffusiveProcess.Frozen.Assumptions.measurable_aCutoff M L x).smul
        (measurable_const : Measurable (fun _ : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => (1 : Mat d)))
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmat)
  · intro i j phi hphi
    let F : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d → ℝ := fun z =>
      scalarMatrix (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2) i j * phi z.2
    have hmat : Measurable (fun z : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d =>
        scalarMatrix (d := d) (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2)) :=
      (measurable_cutoff_uncurry M L).smul
        (measurable_const : Measurable (fun _ : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d × Vec d => (1 : Mat d)))
    have hF : Measurable F :=
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmat)).mul
        (hphi.measurable.comp measurable_snd)
    have hInt : StronglyMeasurable (fun omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        ∫ x, F (omega, x) ∂volume) :=
      hF.stronglyMeasurable.integral_prod_right'
    simpa [F, entryTestR, aCutoffRegCoeffField] using hInt.measurable

/-- Probability-law packaging for the finite scalar cutoff. -/
noncomputable def aCutoffProbabilityLaw {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    ProbabilityMeasure (RegCoeffField d) :=
  M.P.map (aCutoffRegCoeffField M L)

/-- The finite cutoff as a Chapter 4 restriction coefficient law. -/
noncomputable def aCutoffRestrictionLaw {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    Ch04.RestrictionCoeffLaw d :=
  (aCutoffProbabilityLaw M L).toMeasure

noncomputable instance aCutoffRestrictionLaw_isProbability {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    IsProbabilityMeasure (aCutoffRestrictionLaw M L) := by
  change IsProbabilityMeasure
    (M.P.map (aCutoffRegCoeffField M L)).toMeasure
  infer_instance

@[simp]
theorem aCutoffRestrictionLaw_eq_map {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    aCutoffRestrictionLaw M L =
      Measure.map (aCutoffRegCoeffField M L) M.P.toMeasure := by
  rfl

private theorem measurableSet_aeLocallyUniformlyEllipticField {d : ℕ} :
    MeasurableSet {a : RegCoeffField d |
      Ch04.AELocallyUniformlyEllipticField a} := by
  classical
  have hEq : {a : RegCoeffField d | Ch04.AELocallyUniformlyEllipticField a} =
      ⋂ Q : TriadicCube d, ⋃ k : ℕ,
        {a : RegCoeffField d |
          AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro ha Q
      exact ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q
    · intro ha Q
      obtain ⟨k, hk⟩ := ha Q
      have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      have h1le : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hle : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 :=
        le_trans ((inv_le_one₀ (by positivity)).2 h1le) h1le
      refine ⟨((k : ℝ) + 1)⁻¹, (k : ℝ) + 1, hkpos, hle, ?_⟩
      have hslice : IsAEEllipticFieldOn ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)
          (cubeSet Q) a.toFun := hk
      exact hslice.mono (measurableSet_openCubeSet Q)
        (openCubeSet_subset_cubeSet Q)
  rw [hEq]
  refine MeasurableSet.iInter fun Q => MeasurableSet.iUnion fun k => ?_
  exact LocalSigmaR_le (cubeSet Q) _
    (Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k)

/-- Every finite-cutoff realization is locally a.e. uniformly elliptic. -/
theorem aCutoffRegCoeffField_aeLocallyUniformlyEllipticField {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    Ch04.AELocallyUniformlyEllipticField (aCutoffRegCoeffField M L omega) := by
  intro Q
  let data := aCutoffCoeffOnData M L omega (Ch02.cubeDomain Q)
  refine ⟨data.lam, data.Lam, data.lam_pos, data.lam_le_Lam, ?_⟩
  change IsAEEllipticFieldOn data.lam data.Lam
    (openCubeSet Q) (aCutoffRegCoeffField M L omega).toFun
  refine ⟨(Ch02.cubeDomain Q).measurableSet, ?_, ?_⟩
  · simpa [data, aCutoffRegCoeffField, ScalarCoeffOnData.toCoeffOn,
      Ch02.cubeDomain_coe] using! data.toCoeffOn.aeStronglyMeasurable
  · simpa [data, aCutoffRegCoeffField, ScalarCoeffOnData.toCoeffOn,
      Ch02.cubeDomain_coe, scalarCoeffField] using data.toCoeffOn.aeElliptic

/-- The finite-cutoff pushforward law is supported on the exact Chapter 4
local-ellipticity carrier. -/
theorem aCutoffRestrictionLaw_aeLocallyUniformlyElliptic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    Ch04.AELocallyUniformlyEllipticLaw (aCutoffRestrictionLaw M L) := by
  rw [Ch04.AELocallyUniformlyEllipticLaw, aCutoffRestrictionLaw_eq_map,
    ae_map_iff (measurable_aCutoffRegCoeffField M L).aemeasurable
      measurableSet_aeLocallyUniformlyEllipticField]
  exact Filter.Eventually.of_forall fun omega =>
    aCutoffRegCoeffField_aeLocallyUniformlyEllipticField M L omega

/-- The finite cutoff supplies the Chapter 4 probability/local-ellipticity
law carrier. -/
theorem aCutoffRestrictionLaw_lawCarrier {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) :
    Ch04.RestrictionLawCarrier (aCutoffRestrictionLaw M L) :=
  Ch04.lawCarrier_of_aeLocallyUniformlyElliptic
    (aCutoffRestrictionLaw_aeLocallyUniformlyElliptic M L)

end

end SubdiffusiveProcess.CoarseGrainingVocab
