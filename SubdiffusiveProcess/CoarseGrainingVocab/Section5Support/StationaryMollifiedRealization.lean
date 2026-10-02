import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryMollifiedPotentialCurl
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryRepresentativeMollification
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationarySpatialPrimitive

/-!
# Spatial realization of mollified stationary potential fields

This is the literal-carrier counterpart of the realization step in
`Algsuperdiff/Section3/Provider/Corrector/PotentialApproximation.lean`.
The Hilbert-space mollifier is first represented by an honest samplewise
convolution.  The closed-potential curl identity then holds pointwise almost
surely at the origin.  Stationarity, a countable dense set, and smoothness
upgrade it to every spatial point, where the Euclidean Poincare lemma supplies
a global smooth primitive.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The canonical strongly measurable representative selected from a
stationary vector `L²` class. -/
def stationaryVectorRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure) : Sample d → HilbertVec d :=
  (Lp.aestronglyMeasurable P).mk P

theorem stronglyMeasurable_stationaryVectorRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure) :
    StronglyMeasurable (stationaryVectorRepresentative M P) :=
  (Lp.aestronglyMeasurable P).stronglyMeasurable_mk

theorem ae_eq_stationaryVectorRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure) :
    (P : Sample d → HilbertVec d) =ᵐ[M.P.toMeasure]
      stationaryVectorRepresentative M P :=
  (Lp.aestronglyMeasurable P).ae_eq_mk

theorem memLp_two_stationaryVectorRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure) :
    MemLp (stationaryVectorRepresentative M P) 2 M.P.toMeasure :=
  (Lp.memLp P).ae_eq (ae_eq_stationaryVectorRepresentative M P)

theorem toLp_stationaryVectorRepresentative {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure) :
    (memLp_two_stationaryVectorRepresentative M P).toLp
        (stationaryVectorRepresentative M P) = P := by
  rw [MemLp.toLp_congr (memLp_two_stationaryVectorRepresentative M P)
    (Lp.memLp P) (ae_eq_stationaryVectorRepresentative M P).symm,
    Lp.toLp_coeFn]

/-- The honest spatial vector field obtained by mollifying the canonical
representative of `P`. -/
def stationaryMollifiedRealization {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (kappa : Vec d → ℝ) (P : Stationary.VectorL2 d M.P.toMeasure)
    (omega : Sample d) (x : Vec d) : Vec d :=
  (realize (representativeMollify kappa
      (stationaryVectorRepresentative M P)) omega x).toVec

theorem stationaryMollifiedRealization_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (kappa : Vec d → ℝ) (P : Stationary.VectorL2 d M.P.toMeasure)
    (omega : Sample d) (x : Vec d) (i : Fin d) :
    stationaryMollifiedRealization M kappa P omega x i =
      (realize (representativeMollify kappa
        (stationaryVectorRepresentative M P)) omega x).toVec i := rfl

private theorem toLp_representativeMollify_stationaryVectorRepresentative
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure)
    (hP : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z P))
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) :
    letI := potentialSequenceVAddInvariant M
    (memLp_two_representativeMollify M hkappa
      (hkappa.integrable_of_hasCompactSupport hcompact)
      (stronglyMeasurable_stationaryVectorRepresentative M P)
      (memLp_two_stationaryVectorRepresentative M P)).toLp
        (representativeMollify kappa
          (stationaryVectorRepresentative M P)) =
      Stationary.mollifyL2 (mu := M.P.toMeasure) kappa P := by
  letI := potentialSequenceVAddInvariant M
  have hrep := toLp_representativeMollify_eq_mollifyL2 M hkappa hcompact
    (stronglyMeasurable_stationaryVectorRepresentative M P)
    (memLp_two_stationaryVectorRepresentative M P)
    (by simpa only [toLp_stationaryVectorRepresentative] using hP)
  simpa only [toLp_stationaryVectorRepresentative] using hrep

/-- The coordinate of a representative mollification is an honest
representative of the coordinate of the Hilbert-space mollifier. -/
private theorem toLp_coord_representativeMollify_eq {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure)
    (hP : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z P))
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa) (j : Fin d) :
    letI := potentialSequenceVAddInvariant M
    let F := representativeMollify kappa
      (stationaryVectorRepresentative M P)
    let hFm := stronglyMeasurable_representativeMollify hkappa
      (stronglyMeasurable_stationaryVectorRepresentative M P)
    let hF := memLp_two_representativeMollify M hkappa
      (hkappa.integrable_of_hasCompactSupport hcompact)
      (stronglyMeasurable_stationaryVectorRepresentative M P)
      (memLp_two_stationaryVectorRepresentative M P)
    (memLp_representativeCoord M hFm hF j).toLp
        (representativeCoord F j) =
      Stationary.vectorL2Coord (mu := M.P.toMeasure) j
        (Stationary.mollifyL2 (mu := M.P.toMeasure) kappa P) := by
  letI := potentialSequenceVAddInvariant M
  let F := representativeMollify kappa
    (stationaryVectorRepresentative M P)
  let hFm := stronglyMeasurable_representativeMollify hkappa
    (stronglyMeasurable_stationaryVectorRepresentative M P)
  let hF := memLp_two_representativeMollify M hkappa
    (hkappa.integrable_of_hasCompactSupport hcompact)
    (stronglyMeasurable_stationaryVectorRepresentative M P)
    (memLp_two_stationaryVectorRepresentative M P)
  calc
    (memLp_representativeCoord M hFm hF j).toLp
        (representativeCoord F j) =
      Stationary.vectorL2Coord (mu := M.P.toMeasure) j (hF.toLp F) :=
        (vectorL2Coord_toLp_representative M hFm hF j).symm
    _ = Stationary.vectorL2Coord (mu := M.P.toMeasure) j
        (Stationary.mollifyL2 (mu := M.P.toMeasure) kappa P) := by
      rw [toLp_representativeMollify_stationaryVectorRepresentative
        M P hP hkappa hcompact]

/-- The mixed derivatives of the samplewise mollified representative commute
almost surely at the origin. -/
theorem ae_representativeMollify_kernelDeriv_coord_comm
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure)
    (hPpot : letI := potentialSequenceVAddInvariant M
      P ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d))
    (hP : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z P))
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) (i j : Fin d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (representativeMollify (Stationary.kernelDeriv kappa i)
        (stationaryVectorRepresentative M P) omega).toVec j =
      (representativeMollify (Stationary.kernelDeriv kappa j)
        (stationaryVectorRepresentative M P) omega).toVec i := by
  letI := potentialSequenceVAddInvariant M
  let Pi := representativeMollify (Stationary.kernelDeriv kappa i)
    (stationaryVectorRepresentative M P)
  let Pj := representativeMollify (Stationary.kernelDeriv kappa j)
    (stationaryVectorRepresentative M P)
  let hiM := stronglyMeasurable_representativeMollify
    (Stationary.continuous_kernelDeriv hkappa i)
    (stronglyMeasurable_stationaryVectorRepresentative M P)
  let hjM := stronglyMeasurable_representativeMollify
    (Stationary.continuous_kernelDeriv hkappa j)
    (stronglyMeasurable_stationaryVectorRepresentative M P)
  let hiL := memLp_two_representativeMollify M
    (Stationary.continuous_kernelDeriv hkappa i)
    ((Stationary.continuous_kernelDeriv hkappa i)
      |>.integrable_of_hasCompactSupport
        (Stationary.hasCompactSupport_kernelDeriv hcompact i))
    (stronglyMeasurable_stationaryVectorRepresentative M P)
    (memLp_two_stationaryVectorRepresentative M P)
  let hjL := memLp_two_representativeMollify M
    (Stationary.continuous_kernelDeriv hkappa j)
    ((Stationary.continuous_kernelDeriv hkappa j)
      |>.integrable_of_hasCompactSupport
        (Stationary.hasCompactSupport_kernelDeriv hcompact j))
    (stronglyMeasurable_stationaryVectorRepresentative M P)
    (memLp_two_stationaryVectorRepresentative M P)
  let hij := memLp_representativeCoord M hiM hiL j
  let hji := memLp_representativeCoord M hjM hjL i
  have hclassLeft : hij.toLp (representativeCoord Pi j) =
      Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa i)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) j P) := by
    rw [toLp_coord_representativeMollify_eq M P hP
      (Stationary.continuous_kernelDeriv hkappa i)
      (Stationary.hasCompactSupport_kernelDeriv hcompact i) j]
    exact Stationary.vectorL2Coord_mollifyL2_of_continuous
      (mu := M.P.toMeasure)
      (Stationary.continuous_kernelDeriv hkappa i)
      (Stationary.hasCompactSupport_kernelDeriv hcompact i) P hP j
  have hclassRight : hji.toLp (representativeCoord Pj i) =
      Stationary.mollifyL2 (mu := M.P.toMeasure)
        (Stationary.kernelDeriv kappa j)
        (Stationary.vectorL2Coord (mu := M.P.toMeasure) i P) := by
    rw [toLp_coord_representativeMollify_eq M P hP
      (Stationary.continuous_kernelDeriv hkappa j)
      (Stationary.hasCompactSupport_kernelDeriv hcompact j) i]
    exact Stationary.vectorL2Coord_mollifyL2_of_continuous
      (mu := M.P.toMeasure)
      (Stationary.continuous_kernelDeriv hkappa j)
      (Stationary.hasCompactSupport_kernelDeriv hcompact j) P hP i
  have hcurl :=
    mollifyL2_kernelDeriv_coord_comm_of_mem_potential_of_continuous
      M P hPpot hP hcompact hkappa i j
  have hclasses : hij.toLp (representativeCoord Pi j) =
      hji.toLp (representativeCoord Pj i) := by
    rw [hclassLeft, hclassRight, hcurl]
  have hcoe :
      (hij.toLp (representativeCoord Pi j) : Sample d → ℝ) =ᵐ[M.P.toMeasure]
        (hji.toLp (representativeCoord Pj i) : Sample d → ℝ) := by
    rw [hclasses]
  filter_upwards [hij.coeFn_toLp, hji.coeFn_toLp, hcoe]
    with omega hleft hright heq
  exact hleft.symm.trans (heq.trans hright)

/-- The origin curl identity sweeps to every spatial point almost surely.
The only uncountable upgrade is deterministic: smooth coordinate functions
which agree on Mathlib's fixed dense sequence agree everywhere. -/
theorem ae_stationaryMollifiedRealization_kernelDeriv_coord_comm
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure)
    (hPpot : letI := potentialSequenceVAddInvariant M
      P ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d))
    (hP : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z P))
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ (x : Vec d) (i j : Fin d),
      stationaryMollifiedRealization M
          (Stationary.kernelDeriv kappa i) P omega x j =
        stationaryMollifiedRealization M
          (Stationary.kernelDeriv kappa j) P omega x i := by
  letI := potentialSequenceVAddInvariant M
  classical
  let z : ℕ → Vec d := TopologicalSpace.denseSeq (Vec d)
  have hdense : DenseRange z := TopologicalSpace.denseRange_denseSeq _
  have hsmooth : ∀ i : Fin d, ∀ᵐ omega ∂M.P.toMeasure,
      ContDiff ℝ (⊤ : ℕ∞)
        (realize (representativeMollify (Stationary.kernelDeriv kappa i)
          (stationaryVectorRepresentative M P)) omega) := by
    intro i
    exact ae_contDiff_realize_representativeMollify M
      (Stationary.hasCompactSupport_kernelDeriv hcompact i)
      (Stationary.contDiff_kernelDeriv hkappa i)
      (stronglyMeasurable_stationaryVectorRepresentative M P)
      (memLp_two_stationaryVectorRepresentative M P)
  rw [← ae_all_iff] at hsmooth
  have horigin : ∀ i j : Fin d, ∀ᵐ omega ∂M.P.toMeasure,
      (representativeMollify (Stationary.kernelDeriv kappa i)
        (stationaryVectorRepresentative M P) omega).toVec j =
      (representativeMollify (Stationary.kernelDeriv kappa j)
        (stationaryVectorRepresentative M P) omega).toVec i :=
    fun i j => ae_representativeMollify_kernelDeriv_coord_comm
      M P hPpot hP hcompact hkappa i j
  have hdenseEq : ∀ n : ℕ, ∀ i j : Fin d, ∀ᵐ omega ∂M.P.toMeasure,
      stationaryMollifiedRealization M
          (Stationary.kernelDeriv kappa i) P omega (z n) j =
        stationaryMollifiedRealization M
          (Stationary.kernelDeriv kappa j) P omega (z n) i := by
    intro n i j
    have hshift := (Stationary.measurePreserving_const_vadd
      (mu := M.P.toMeasure) (z n)).quasiMeasurePreserving.ae (horigin i j)
    simpa only [stationaryMollifiedRealization, realize_apply] using hshift
  have hdenseEqJ : ∀ n : ℕ, ∀ i : Fin d, ∀ᵐ omega ∂M.P.toMeasure,
      ∀ j : Fin d,
        stationaryMollifiedRealization M
            (Stationary.kernelDeriv kappa i) P omega (z n) j =
          stationaryMollifiedRealization M
            (Stationary.kernelDeriv kappa j) P omega (z n) i :=
    fun n i => ae_all_iff.2 (hdenseEq n i)
  have hdenseEqI : ∀ n : ℕ, ∀ᵐ omega ∂M.P.toMeasure,
      ∀ i j : Fin d,
        stationaryMollifiedRealization M
            (Stationary.kernelDeriv kappa i) P omega (z n) j =
          stationaryMollifiedRealization M
            (Stationary.kernelDeriv kappa j) P omega (z n) i :=
    fun n => ae_all_iff.2 (hdenseEqJ n)
  have hdenseEqAll : ∀ᵐ omega ∂M.P.toMeasure, ∀ n : ℕ, ∀ i j : Fin d,
      stationaryMollifiedRealization M
          (Stationary.kernelDeriv kappa i) P omega (z n) j =
        stationaryMollifiedRealization M
          (Stationary.kernelDeriv kappa j) P omega (z n) i :=
    ae_all_iff.2 hdenseEqI
  filter_upwards [hsmooth, hdenseEqAll] with omega homega hpoints
  intro x i j
  let Li : Vec d → ℝ := fun y =>
    stationaryMollifiedRealization M
      (Stationary.kernelDeriv kappa i) P omega y j
  let Rj : Vec d → ℝ := fun y =>
    stationaryMollifiedRealization M
      (Stationary.kernelDeriv kappa j) P omega y i
  have hLi : Continuous Li := by
    exact (PiLp.proj (𝕜 := ℝ) (p := 2)
      (β := fun _ : Fin d => ℝ) j).continuous.comp (homega i).continuous
  have hRj : Continuous Rj := by
    exact (PiLp.proj (𝕜 := ℝ) (p := 2)
      (β := fun _ : Fin d => ℝ) i).continuous.comp (homega j).continuous
  have heq : Li = Rj := hdense.equalizer hLi hRj (by
    funext n
    exact hpoints n i j)
  exact congrFun heq x

/-- Almost every mollified realization of a stationary potential `L²` field
is the gradient of a genuine globally defined smooth scalar function. -/
theorem ae_exists_contDiff_primitive_stationaryMollifiedRealization
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure)
    (hPpot : letI := potentialSequenceVAddInvariant M
      P ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d))
    (hP : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z P))
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ∃ phi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) phi ∧
        ∀ (x : Vec d) (i : Fin d),
          fderiv ℝ phi x (basisVec i) =
            stationaryMollifiedRealization M kappa P omega x i := by
  letI := potentialSequenceVAddInvariant M
  let Prep := stationaryVectorRepresentative M P
  have hsmooth : ∀ᵐ omega ∂M.P.toMeasure,
      ContDiff ℝ (⊤ : ℕ∞)
        (realize (representativeMollify kappa Prep) omega) :=
    ae_contDiff_realize_representativeMollify M hcompact hkappa
      (stronglyMeasurable_stationaryVectorRepresentative M P)
      (memLp_two_stationaryVectorRepresentative M P)
  have hloc : ∀ᵐ omega ∂M.P.toMeasure,
      LocallyIntegrable (realize Prep omega) volume :=
    ae_locallyIntegrable_realize M
      (stronglyMeasurable_stationaryVectorRepresentative M P)
      (memLp_two_stationaryVectorRepresentative M P)
  have hcurl := ae_stationaryMollifiedRealization_kernelDeriv_coord_comm
    M P hPpot hP hcompact hkappa
  filter_upwards [hsmooth, hloc, hcurl] with omega homega hlocal hcomm
  let G : Vec d → HilbertVec d :=
    realize (representativeMollify kappa Prep) omega
  let F : Vec d → Vec d := fun x => (G x).toVec
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := homega
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (HilbertVec.continuousLinearEquivVec d).contDiff.comp hG
  have hderiv : ∀ (x : Vec d) (i : Fin d),
      fderiv ℝ F x (basisVec i) =
        stationaryMollifiedRealization M
          (Stationary.kernelDeriv kappa i) P omega x := by
    intro x i
    have hcomp :=
      (HilbertVec.continuousLinearEquivVec d).hasFDerivAt.comp x
        ((hG.differentiable (by simp) x).hasFDerivAt)
    have hcompF : HasFDerivAt F
        ((HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap.comp
          (fderiv ℝ G x)) x := by
      simpa only [F, Function.comp_def,
        HilbertVec.continuousLinearEquivVec_apply] using hcomp
    rw [hcompF.fderiv]
    change (HilbertVec.continuousLinearEquivVec d)
        (fderiv ℝ G x (basisVec i)) = _
    rw [show fderiv ℝ G x (basisVec i) =
        realize (representativeMollify
          (Stationary.kernelDeriv kappa i) Prep) omega x by
      exact fderiv_realize_representativeMollify_apply
        hcompact hkappa hlocal x i]
    rfl
  have hsymm : ∀ (x : Vec d) (i j : Fin d),
      fderiv ℝ F x (basisVec i) j =
        fderiv ℝ F x (basisVec j) i := by
    intro x i j
    rw [hderiv x i, hderiv x j]
    exact hcomm x i j
  obtain ⟨phi, hphismooth, hphi⟩ :=
    exists_contDiff_globalPrimitive_of_fderiv_basis_symmetric hF hsymm
  exact ⟨phi, hphismooth, by
    intro x i
    simpa only [F, stationaryMollifiedRealization, G, Prep] using hphi x i⟩

/-- Coordinate-only compatibility wrapper for the original realization API. -/
theorem ae_exists_primitive_stationaryMollifiedRealization
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (P : Stationary.VectorL2 d M.P.toMeasure)
    (hPpot : letI := potentialSequenceVAddInvariant M
      P ∈ Stationary.stationaryPotentialSubspace
        (mu := M.P.toMeasure) (d := d))
    (hP : letI := potentialSequenceVAddInvariant M
      Continuous (fun z : Vec d =>
        Stationary.koopman (mu := M.P.toMeasure) z P))
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ∃ phi : Vec d → ℝ, ∀ (x : Vec d) (i : Fin d),
        fderiv ℝ phi x (basisVec i) =
          stationaryMollifiedRealization M kappa P omega x i := by
  filter_upwards [ae_exists_contDiff_primitive_stationaryMollifiedRealization
    M P hPpot hP hcompact hkappa] with omega homega
  exact ⟨homega.choose, homega.choose_spec.2⟩

/-- The realization endpoint specialized to the projected one-step forcing
used in `l.one.step.upper` and `l.one.step.lower`. -/
theorem ae_exists_primitive_oneStepPotentialProjection
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (hh : 0 < h)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ∃ phi : Vec d → ℝ, ∀ (x : Vec d) (i : Fin d),
        fderiv ℝ phi x (basisVec i) =
          stationaryMollifiedRealization M kappa
            (oneStepPotentialProjection M n h p hh) omega x i := by
  exact ae_exists_primitive_stationaryMollifiedRealization M
    (oneStepPotentialProjection M n h p hh)
    (oneStepPotentialProjection_mem_stationaryPotentialSubspace
      M n h p hh)
    (continuous_koopman_oneStepPotentialProjection M n h p hh)
    hcompact hkappa

/-- Smooth specialization for the projected one-step forcing. -/
theorem ae_exists_contDiff_primitive_oneStepPotentialProjection
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (hh : 0 < h)
    {kappa : Vec d → ℝ} (hcompact : HasCompactSupport kappa)
    (hkappa : ContDiff ℝ (⊤ : ℕ∞) kappa) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ∃ phi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) phi ∧
        ∀ (x : Vec d) (i : Fin d),
          fderiv ℝ phi x (basisVec i) =
            stationaryMollifiedRealization M kappa
              (oneStepPotentialProjection M n h p hh) omega x i := by
  exact ae_exists_contDiff_primitive_stationaryMollifiedRealization M
    (oneStepPotentialProjection M n h p hh)
    (oneStepPotentialProjection_mem_stationaryPotentialSubspace
      M n h p hh)
    (continuous_koopman_oneStepPotentialProjection M n h p hh)
    hcompact hkappa

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
