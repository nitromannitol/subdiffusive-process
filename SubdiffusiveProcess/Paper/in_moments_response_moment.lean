module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.stationary_family
public import SubdiffusiveProcess.Paper.in_moments_family_transport
public import SubdiffusiveProcess.Paper.annealed_limit_response_transport
public import SubdiffusiveProcess.Section4.CoarseGrainedBound
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseSupremum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowMomentPolynomialGrowth
public import Homogenization.Internal.Ch02.SubadditivityScaling
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Book.Ch02.Matrices
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Mathlib.Tactic



@[expose] public section

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_in_moments_response_moment_max
    (d : ℕ) (hd : 1 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (U : Homogenization.Book.Ch02.Domain d)
    (a : Homogenization.Book.Ch02.CoeffOn U) :
    ∃ r : ℝ, IsGreatest
      {v : ℝ | ∃ e : Fin d → ℝ,
        (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = Homogenization.Book.Ch02.responseJ U a e e} r := by
  let S : Set (Homogenization.Vec d) :=
    {e | (∑ i : Fin d, e i ^ 2) = 1}
  have hS : S = Homogenization.euclideanSphere (0 : Homogenization.Vec d) 1 := by
    ext e
    simp [S, Homogenization.euclideanSphere, Homogenization.euclideanSqDist,
      Homogenization.vecNormSq, Homogenization.vecDot, pow_two]
  have hSc : IsCompact S := by
    rw [hS]
    exact (Homogenization.isCompact_euclideanClosedBall
      (0 : Homogenization.Vec d) (by norm_num)).of_isClosed_subset
      (Homogenization.isClosed_euclideanSphere _ _)
      (Homogenization.euclideanSphere_subset_euclideanClosedBall _ _)
  have hSn : S.Nonempty := by
    let i0 : Fin d := ⟨0, by omega⟩
    refine ⟨Pi.single i0 1, ?_⟩
    classical
    simp [S, Pi.single_apply]
  let hM : Homogenization.Book.Ch02.ResponseMatrixExists U a := I.matrices U a
  let f : Homogenization.Vec d → ℝ :=
    fun e => Homogenization.Book.Ch02.responseJ U a e e
  have hdot : ∀ (f g : Homogenization.Vec d → Homogenization.Vec d),
      Continuous f → Continuous g →
        Continuous (fun e => Homogenization.vecDot (f e) (g e)) := by
    intro f g hf hg
    unfold Homogenization.vecDot
    exact continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)
  have hf : Continuous f := by
    have heq : f = fun e =>
          (1 / 2 : ℝ) * Homogenization.vecDot e
              (Homogenization.matVecMul
                (Homogenization.Book.Ch02.sigmaMatrix hM) e) +
            (1 / 2 : ℝ) * Homogenization.vecDot
              (e + Homogenization.matVecMul
                (Homogenization.Book.Ch02.kappaMatrix hM) e)
              (Homogenization.matVecMul
                (Homogenization.Book.Ch02.sigmaStarInvMatrix hM)
                (e + Homogenization.matVecMul
                  (Homogenization.Book.Ch02.kappaMatrix hM) e)) -
            Homogenization.vecDot e e := by
      funext e
      exact Homogenization.Book.Ch02.responseJ_eq_responseMatrices_formula hM e e
    rw [heq]
    have hσ : Continuous (fun e : Homogenization.Vec d =>
        Homogenization.matVecMul
          (Homogenization.Book.Ch02.sigmaMatrix hM) e) :=
      Homogenization.continuous_matVecMul _
    have hκ : Continuous (fun e : Homogenization.Vec d =>
        Homogenization.matVecMul
          (Homogenization.Book.Ch02.kappaMatrix hM) e) :=
      Homogenization.continuous_matVecMul _
    have hσstar : Continuous (fun e : Homogenization.Vec d =>
        Homogenization.matVecMul
          (Homogenization.Book.Ch02.sigmaStarInvMatrix hM) e) :=
      Homogenization.continuous_matVecMul _
    have hleft := hdot (fun e : Homogenization.Vec d => e)
      (fun e => Homogenization.matVecMul
        (Homogenization.Book.Ch02.sigmaMatrix hM) e) continuous_id hσ
    have hsum : Continuous (fun e : Homogenization.Vec d =>
        e + Homogenization.matVecMul
          (Homogenization.Book.Ch02.kappaMatrix hM) e) :=
      continuous_id.add hκ
    have hright := hdot
      (fun e : Homogenization.Vec d =>
        e + Homogenization.matVecMul
          (Homogenization.Book.Ch02.kappaMatrix hM) e)
      (fun e => Homogenization.matVecMul
        (Homogenization.Book.Ch02.sigmaStarInvMatrix hM)
        (e + Homogenization.matVecMul
          (Homogenization.Book.Ch02.kappaMatrix hM) e))
      hsum (hσstar.comp hsum)
    have hdiag := hdot (fun e : Homogenization.Vec d => e)
      (fun e : Homogenization.Vec d => e) continuous_id continuous_id
    exact (continuous_const.mul hleft).add
      (continuous_const.mul hright) |>.sub hdiag
  obtain ⟨emax, hemax, hmax⟩ := hSc.exists_isMaxOn hSn hf.continuousOn
  refine ⟨f emax, ?_⟩
  constructor
  · refine ⟨emax, hemax, ?_⟩
    rfl
  · rintro v ⟨e, he, rfl⟩
    exact hmax he

noncomputable def aux_in_moments_response_moment_countable
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (alpha : ℝ)
    (a : Homogenization.RegCoeffField d) : ℝ≥0∞ :=
  ⨆ i : ℕ, ENNReal.ofReal
    (Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
      ((Real.sqrt alpha)⁻¹ •
        (TopologicalSpace.denseSeq (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
          Homogenization.Vec d))
      (Real.sqrt alpha •
        (TopologicalSpace.denseSeq (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
          Homogenization.Vec d)) a)

theorem aux_in_moments_response_moment_source_countable
    (d N k : ℕ) (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    [NeZero d] :
    ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      aux_in_moments_response_moment_countable
          (Homogenization.originCube d (k : ℤ))
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)
          (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)) =
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefectCountableRepresentative model N
        (Homogenization.Book.Ch02.cubeDomain
          (Homogenization.originCube d ((N + k : ℕ) : ℤ))) omega := by
  intro omega
  unfold aux_in_moments_response_moment_countable
  rw [SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefectCountableRepresentative]
  apply iSup_congr
  intro i
  rw [Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
    (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField_aeLocallyUniformlyEllipticField
      model N omega) N k]
  have hresp : Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet
        (Homogenization.originCube d ((N + k : ℕ) : ℤ))
        ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N))⁻¹ •
          (TopologicalSpace.denseSeq
            (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d))
        (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) •
          (TopologicalSpace.denseSeq
            (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d))
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega) =
      Homogenization.Book.Ch02.responseJ
        (Homogenization.Book.Ch02.cubeDomain
          (Homogenization.originCube d ((N + k : ℕ) : ℤ)))
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffCoeffOnData model N omega
          (Homogenization.Book.Ch02.cubeDomain
            (Homogenization.originCube d ((N + k : ℕ) : ℤ)))).toCoeffOn
        ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N))⁻¹ •
          (TopologicalSpace.denseSeq
            (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d))
        (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) •
          (TopologicalSpace.denseSeq
            (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d)) := by
    rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
    simpa [Homogenization.Book.Ch02.cubeDomain_coe] using!
      (Homogenization.responseJ_cubeSet_eq_openCubeSet_of_triadicCube
        (Homogenization.originCube d ((N + k : ℕ) : ℤ))
        ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N))⁻¹ •
          (TopologicalSpace.denseSeq
            (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d))
        (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) •
          (TopologicalSpace.denseSeq
            (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d))
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega).toFun)
  rw [hresp]

theorem aux_in_moments_response_moment_isEllipticMatrix_smul
    {d : ℕ} {lam Lam c : ℝ} {A : Homogenization.Mat d}
    (hc : 0 < c) (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix (c * lam) (c * Lam) (c • A) := by
  rcases hA with ⟨hlam, hlamLam, hlower, hupper⟩
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
  have hdet : IsUnit A.det :=
    Homogenization.isUnit_det_of_isEllipticMatrix
      ⟨hlam, hlamLam, hlower, hupper⟩
  refine ⟨mul_pos hc hlam,
    mul_le_mul_of_nonneg_left hlamLam (le_of_lt hc), ?_, ?_⟩
  · intro ξ
    rw [smul_matVecMul, vecDot_smul_right]
    have hmul := mul_le_mul_of_nonneg_left (hlower ξ) (le_of_lt hc)
    nlinarith
  · intro ξ
    have hcne : c ≠ 0 := hc.ne'
    have hinv : ((c • A)⁻¹ : Homogenization.Mat d) = c⁻¹ • A⁻¹ := by
      rw [nonsing_inv_smul c hcne hdet]
    rw [hinv, smul_matVecMul, vecDot_smul_right]
    have hcinv_nonneg : 0 ≤ c⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hupper ξ) hcinv_nonneg
    have hleft : (c * Lam)⁻¹ * vecNormSq ξ =
        c⁻¹ * (Lam⁻¹ * vecNormSq ξ) := by
      field_simp [hcne, hLam.ne']
    rw [hleft]
    exact hmul

noncomputable def aux_in_moments_response_moment_scaledCoeffOn
    {d : ℕ} {U : Homogenization.Book.Ch02.Domain d}
    (c : ℝ) (hc : 0 < c) (a : Homogenization.Book.Ch02.CoeffOn U) :
    Homogenization.Book.Ch02.CoeffOn U where
  toCoeffField := c • a.toCoeffField
  lam := c * a.lam
  Lam := c * a.Lam
  lam_pos := mul_pos hc a.lam_pos
  lam_le_Lam := mul_le_mul_of_nonneg_left a.lam_le_Lam (le_of_lt hc)
  aeStronglyMeasurable := by
    intro i j
    have hfun :
        (fun x : Homogenization.Vec d =>
          Homogenization.restrictCoeffField (U : Set (Homogenization.Vec d))
            (c • a.toCoeffField) x i j) =
        c • (fun x : Homogenization.Vec d =>
          Homogenization.restrictCoeffField (U : Set (Homogenization.Vec d))
            a.toCoeffField x i j) := by
      funext x
      by_cases hx : x ∈ (U : Set (Homogenization.Vec d)) <;>
        simp [Homogenization.restrictCoeffField, hx, smul_eq_mul]
    rw [hfun]
    exact (a.aeStronglyMeasurable i j).const_smul c
  aeElliptic := by
    filter_upwards [a.aeElliptic] with x hx
    exact aux_in_moments_response_moment_isEllipticMatrix_smul hc hx

noncomputable def aux_in_moments_response_moment_cutoffField
    {d : ℕ} (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (omega : BilateralField d) : C(SpatialCoordinates d, ℝ) :=
  ⟨fun x => SubdiffusiveProcess.cutoffCoefficient model
      (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x, by
    unfold SubdiffusiveProcess.cutoffCoefficient
      SubdiffusiveProcess.cutoffPotential
    apply continuous_const.mul
    apply Real.continuous_exp.comp
    apply Continuous.sub
    · apply Continuous.add
      · exact continuous_const
      · apply continuous_finsetSum
        intro j hj
        exact (omega (-(j : ℤ))).continuous
    · exact continuous_const⟩

theorem aux_in_moments_response_moment_countable_aemeasurable
    {d : ℕ} [NeZero d]
    (P : Homogenization.Book.Ch04.RestrictionCoeffLaw d)
    (hP : Homogenization.Book.Ch04.RestrictionLawCarrier P)
    (Q : TriadicCube d) (alpha : ℝ) :
    AEMeasurable
      (aux_in_moments_response_moment_countable Q alpha) P := by
  unfold aux_in_moments_response_moment_countable
  exact AEMeasurable.iSup fun i =>
    (hP.aemeasurable_restrictionResponseJObservableCubeSet Q
      ((Real.sqrt alpha)⁻¹ •
        (TopologicalSpace.denseSeq (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
          Homogenization.Vec d))
      (Real.sqrt alpha •
        (TopologicalSpace.denseSeq (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
          Homogenization.Vec d))).ennreal_ofReal

theorem aux_in_moments_response_moment_dense_max
    (d : ℕ) [NeZero d] (hd : 1 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (U : Homogenization.Book.Ch02.Domain d)
    (a : Homogenization.Book.Ch02.CoeffOn U) (r : ℝ)
    (hmax : IsGreatest
      {v : ℝ | ∃ e : Homogenization.Vec d,
        (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = Homogenization.Book.Ch02.responseJ U a e e} r) :
    (⨆ i : ℕ, ENNReal.ofReal
      (Homogenization.Book.Ch02.responseJ U a
        (TopologicalSpace.denseSeq (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
          Homogenization.Vec d)
        (TopologicalSpace.denseSeq (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
          Homogenization.Vec d))) = ENNReal.ofReal r := by
  let S : Set (Homogenization.Vec d) :=
    {e | (∑ i : Fin d, e i ^ 2) = 1}
  have hSc : IsCompact S := by
    rw [show S = Homogenization.euclideanSphere (0 : Homogenization.Vec d) 1 by
      ext e
      simp [S, Homogenization.euclideanSphere, Homogenization.euclideanSqDist,
        Homogenization.vecNormSq, Homogenization.vecDot, pow_two]]
    exact (Homogenization.isCompact_euclideanClosedBall
      (0 : Homogenization.Vec d) (by norm_num)).of_isClosed_subset
      (Homogenization.isClosed_euclideanSphere _ _)
      (Homogenization.euclideanSphere_subset_euclideanClosedBall _ _)
  have hSn : S.Nonempty := by
    let i0 : Fin d := ⟨0, by omega⟩
    refine ⟨Pi.single i0 1, ?_⟩
    classical
    simp [S, Pi.single_apply]
  let hM : Homogenization.Book.Ch02.ResponseMatrixExists U a := I.matrices U a
  let f : Homogenization.Vec d → ℝ :=
    fun e => Homogenization.Book.Ch02.responseJ U a e e
  have hdot : ∀ (f g : Homogenization.Vec d → Homogenization.Vec d),
      Continuous f → Continuous g →
        Continuous (fun e => Homogenization.vecDot (f e) (g e)) := by
    intro f g hf hg
    unfold Homogenization.vecDot
    exact continuous_finsetSum Finset.univ fun i _ =>
      ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)
  have hf : Continuous f := by
    have heq : f = fun e =>
          (1 / 2 : ℝ) * Homogenization.vecDot e
              (Homogenization.matVecMul
                (Homogenization.Book.Ch02.sigmaMatrix hM) e) +
            (1 / 2 : ℝ) * Homogenization.vecDot
              (e + Homogenization.matVecMul
                (Homogenization.Book.Ch02.kappaMatrix hM) e)
              (Homogenization.matVecMul
                (Homogenization.Book.Ch02.sigmaStarInvMatrix hM)
                (e + Homogenization.matVecMul
                  (Homogenization.Book.Ch02.kappaMatrix hM) e)) -
            Homogenization.vecDot e e := by
      funext e
      exact Homogenization.Book.Ch02.responseJ_eq_responseMatrices_formula hM e e
    rw [heq]
    have hσ : Continuous (fun e : Homogenization.Vec d =>
        Homogenization.matVecMul
          (Homogenization.Book.Ch02.sigmaMatrix hM) e) :=
      Homogenization.continuous_matVecMul _
    have hκ : Continuous (fun e : Homogenization.Vec d =>
        Homogenization.matVecMul
          (Homogenization.Book.Ch02.kappaMatrix hM) e) :=
      Homogenization.continuous_matVecMul _
    have hσstar : Continuous (fun e : Homogenization.Vec d =>
        Homogenization.matVecMul
          (Homogenization.Book.Ch02.sigmaStarInvMatrix hM) e) :=
      Homogenization.continuous_matVecMul _
    have hleft := hdot (fun e : Homogenization.Vec d => e)
      (fun e => Homogenization.matVecMul
        (Homogenization.Book.Ch02.sigmaMatrix hM) e) continuous_id hσ
    have hsum : Continuous (fun e : Homogenization.Vec d =>
        e + Homogenization.matVecMul
          (Homogenization.Book.Ch02.kappaMatrix hM) e) :=
      continuous_id.add hκ
    have hright := hdot
      (fun e : Homogenization.Vec d =>
        e + Homogenization.matVecMul
          (Homogenization.Book.Ch02.kappaMatrix hM) e)
      (fun e => Homogenization.matVecMul
        (Homogenization.Book.Ch02.sigmaStarInvMatrix hM)
        (e + Homogenization.matVecMul
          (Homogenization.Book.Ch02.kappaMatrix hM) e))
      hsum (hσstar.comp hsum)
    have hdiag := hdot (fun e : Homogenization.Vec d => e)
      (fun e : Homogenization.Vec d => e) continuous_id continuous_id
    exact (continuous_const.mul hleft).add
      (continuous_const.mul hright) |>.sub hdiag
  let T : ℝ≥0∞ := ⨆ i : ℕ, ENNReal.ofReal
    (f (TopologicalSpace.denseSeq
      (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d))
  have hTle : T ≤ ENNReal.ofReal r := by
    unfold T
    refine iSup_le fun i => ?_
    apply ENNReal.ofReal_le_ofReal
    exact hmax.2 (by
      refine ⟨(TopologicalSpace.denseSeq
        (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d), ?_, rfl⟩
      simpa [Homogenization.vecNormSq, Homogenization.vecDot, pow_two] using
        (TopologicalSpace.denseSeq
          (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i).property)
  have hTtop : T ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTle
  have hfull : ENNReal.ofReal r ≤ T := by
    obtain ⟨emax, hemax, hmaxeq⟩ := hmax.1
    let emaxS : SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d :=
      ⟨emax, by simpa [Homogenization.vecNormSq, Homogenization.vecDot, pow_two] using hemax⟩
    have hr : r = f (emaxS : Homogenization.Vec d) := hmaxeq
    rw [hr]
    apply (ENNReal.ofReal_le_iff_le_toReal hTtop).2
    by_contra hnot
    push Not at hnot
    let eps := f emax - T.toReal
    have heps : 0 < eps := by dsimp [eps]; linarith
    obtain ⟨delta, hdelta, hball⟩ :=
      Metric.continuousAt_iff.1 hf.continuousAt eps heps
    obtain ⟨i, hi⟩ :=
      (TopologicalSpace.denseRange_denseSeq
        (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d)).exists_dist_lt emaxS hdelta
    have hclose := hball (show dist
        ((TopologicalSpace.denseSeq
          (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
            SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) : Homogenization.Vec d)
          (emaxS : Homogenization.Vec d) < delta by
      simpa [Subtype.dist_eq, dist_comm] using hi)
    rw [Real.dist_eq] at hclose
    have hiENN : ENNReal.ofReal (f
        (TopologicalSpace.denseSeq
          (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i : Homogenization.Vec d)) ≤ T := by
      exact le_iSup (fun j : ℕ => ENNReal.ofReal (f
        (TopologicalSpace.denseSeq
          (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) j : Homogenization.Vec d))) i
    have hiReal := (ENNReal.ofReal_le_iff_le_toReal hTtop).mp hiENN
    dsimp [eps] at hclose
    have habs := (abs_lt.mp hclose).1
    linarith
  exact le_antisymm hTle hfull

theorem aux_in_moments_response_moment_countable_transport
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k : ℕ) :
    ProbabilityTheory.IdentDistrib
      (fun omega : BilateralField d =>
        aux_in_moments_response_moment_countable
          (Homogenization.originCube d (k : ℤ))
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)
          ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) •
            (aux_annealed_limit_response_transport_scalarRegCoeffField
              (aux_in_moments_response_moment_cutoffField model N omega))))
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        aux_in_moments_response_moment_countable
          (Homogenization.originCube d (k : ℤ))
          (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)
          (Homogenization.rescaleReg N
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)))
      (chaosSampleLaw model).toMeasure model.P.toMeasure := by
  let alpha : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
  let s : ℝ := alpha⁻¹
  let r : ℝ := s * Real.exp (-(N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)
  let c : ℝ := s⁻¹
  have halpha : 0 < alpha := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N
  have hs : 0 < s := inv_pos.mpr halpha
  have hc : 0 < c := inv_pos.mpr hs
  have hcs : c * s = 1 := by
    dsimp [c, s]
    field_simp
  have hcr : c * r = Real.exp (-(N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) := by
    dsimp [r]
    rw [show c * (s * Real.exp (-(N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) =
      (c * s) * Real.exp (-(N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) by ring]
    rw [hcs, one_mul]
  let fA : BilateralField d → C(SpatialCoordinates d, ℝ) := fun omega =>
    ⟨fun x =>
      (Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) * alpha)⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x), by
      apply continuous_const.mul
      apply Real.continuous_exp.comp
      apply continuous_finsetSum
      intro j hj
      exact (omega (-(j : ℤ))).continuous⟩
  let g0 : BilateralField d → C(SpatialCoordinates d, ℝ) := fun omega =>
    ⟨fun x => s * Real.exp (∑ j ∈ Finset.range (N + 1),
      ((omega (j : ℤ)) ((3 : ℝ) ^ N • x) -
        _root_.SubdiffusiveProcess.Model.tauSq model.P)), by
      apply continuous_const.mul
      apply Real.continuous_exp.comp
      exact continuous_finsetSum (Finset.range (N + 1)) (by
        intro j hj
        exact ((omega (j : ℤ)).continuous.comp
          (by fun_prop)).sub continuous_const)⟩
  have hnorm : ProbabilityTheory.IdentDistrib fA g0
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
    have h := aux_annealed_limit_response_transport_normalized_field_law
      (model := model) N
    simpa [fA, g0, alpha, s] using h
  let gsource : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      C(SpatialCoordinates d, ℝ) := fun omega =>
    ⟨fun x => r * Real.exp ((∑ j ∈ Finset.range (N + 1),
      ((omega (j : ℕ)).1.1) ((3 : ℝ) ^ N • x)) -
        _root_.SubdiffusiveProcess.Model.tauSq model.P), by
      apply continuous_const.mul
      apply Real.continuous_exp.comp
      exact (continuous_finsetSum (Finset.range (N + 1)) (by
        intro j hj
        exact ((omega (j : ℕ)).1.1).continuous.comp
          (by fun_prop))).sub continuous_const⟩
  let dilate : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => (3 : ℝ) ^ N • x, by fun_prop⟩
  let compD : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ dilate
  let T : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) :=
    fun f => r • compD f
  have hTmeas : Measurable T := by
    have hTcont : Continuous T := by
      dsimp only [T]
      fun_prop
    exact hTcont.measurable
  have hpos := aux_annealed_limit_response_transport_positive_field_law
    (model := model) N
  have htrans := hpos.comp hTmeas
  have hsourceT : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      T (⟨fun x => Real.exp ((∑ i : Fin (N + 1),
        (((omega (i : ℕ)).1.1) x)) - _root_.SubdiffusiveProcess.Model.tauSq model.P), by continuity⟩ :
        C(SpatialCoordinates d, ℝ))) = gsource := by
    funext omega
    ext x
    dsimp [T, compD, dilate, gsource]
    change r * Real.exp ((∑ i : Fin (N + 1),
        ((omega (i : ℕ)).1.1) ((3 : ℝ) ^ N • x)) -
          _root_.SubdiffusiveProcess.Model.tauSq model.P) =
      r * Real.exp ((∑ j ∈ Finset.range (N + 1),
        ((omega (j : ℕ)).1.1) ((3 : ℝ) ^ N • x)) -
          _root_.SubdiffusiveProcess.Model.tauSq model.P)
    congr 2
    rw [Finset.sum_fin_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [dite_eq_left (Finset.mem_range.mp hj)]
  have htargetT : (fun omega : BilateralField d =>
      T (⟨fun x => Real.exp ((∑ i : Fin (N + 1),
        ((omega (i : ℤ)) x)) - _root_.SubdiffusiveProcess.Model.tauSq model.P), by
          apply Real.continuous_exp.comp
          exact (continuous_finsetSum Finset.univ (by
            intro i hi
            exact (omega (i : ℤ)).continuous)).sub continuous_const⟩ :
        C(SpatialCoordinates d, ℝ))) = g0 := by
    funext omega
    ext x
    dsimp [T, compD, dilate, g0]
    change r * Real.exp ((∑ i : Fin (N + 1),
        (omega (i : ℤ)) ((3 : ℝ) ^ N • x)) -
          _root_.SubdiffusiveProcess.Model.tauSq model.P) = _
    have hsum :
        (∑ i : Fin (N + 1), (omega (i : ℤ)) ((3 : ℝ) ^ N • x)) =
          ∑ i ∈ Finset.range (N + 1),
            (omega (i : ℤ)) ((3 : ℝ) ^ N • x) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [dite_eq_left (Finset.mem_range.mp hi)]
    rw [hsum]
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [show r = s * Real.exp (-(N : ℝ) *
        _root_.SubdiffusiveProcess.Model.tauSq model.P) by rfl]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have htrans' : ProbabilityTheory.IdentDistrib
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        T (⟨fun x => Real.exp ((∑ i : Fin (N + 1),
          (((omega (i : ℕ)).1.1) x)) - _root_.SubdiffusiveProcess.Model.tauSq model.P), by
            apply Real.continuous_exp.comp
            exact (continuous_finsetSum Finset.univ (by
              intro i hi
              exact (omega (i : ℕ)).1.1.continuous)).sub continuous_const⟩ :
          C(SpatialCoordinates d, ℝ)))
      (fun omega : BilateralField d =>
        T (⟨fun x => Real.exp ((∑ i : Fin (N + 1),
          ((omega (i : ℤ)) x)) - _root_.SubdiffusiveProcess.Model.tauSq model.P), by
            apply Real.continuous_exp.comp
            exact (continuous_finsetSum Finset.univ (by
              intro i hi
              exact (omega (i : ℤ)).continuous)).sub continuous_const⟩ :
          C(SpatialCoordinates d, ℝ)))
      model.P.toMeasure (chaosSampleLaw model).toMeasure := by
    simpa [Function.comp_def] using htrans
  rw [hsourceT, htargetT] at htrans'
  have hnormP : ProbabilityTheory.IdentDistrib fA gsource
      (chaosSampleLaw model).toMeasure model.P.toMeasure :=
    hnorm.trans htrans'.symm
  have hscalar := hnorm.comp
    aux_annealed_limit_response_transport_measurable_scalarRegCoeffField
  have hscale : Measurable (fun z : Homogenization.RegCoeffField d => c • z) := by
    apply Homogenization.measurable_of_entryTestR_transport
    · intro y i j
      simpa [Homogenization.RegCoeffField.smul_toFun] using!
        (Homogenization.measurable_apply_entry y i j).const_smul c
    · intro i j φ hφ
      exact ⟨c, i, j, φ, hφ,
        fun z => Homogenization.entryTestR_smul i j c z⟩
  have hscalarP := hnormP.comp
    aux_annealed_limit_response_transport_measurable_scalarRegCoeffField
  have hscaled := hscalarP.comp hscale
  have hsource : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      c • aux_annealed_limit_response_transport_scalarRegCoeffField (gsource omega) =
        Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega) := by
    intro omega
    apply Homogenization.RegCoeffField.ext
    intro x
    rw [Homogenization.RegCoeffField.smul_toFun]
    dsimp [gsource]
    change c • Homogenization.scalarMatrix
        (r * Real.exp ((∑ j ∈ Finset.range (N + 1),
          ((omega (j : ℕ)).1.1) ((3 : ℝ) ^ N • x)) -
            _root_.SubdiffusiveProcess.Model.tauSq model.P)) = _
    have hsum :
        (∑ i : Fin (N + 1), ((omega (i : ℕ)).1.1) ((3 : ℝ) ^ N • x)) =
          ∑ j ∈ Finset.range (N + 1),
            ((omega (j : ℕ)).1.1) ((3 : ℝ) ^ N • x) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      rw [dite_eq_left (Finset.mem_range.mp hj)]
    rw [← hsum]
    exact aux_annealed_limit_response_transport_source_matrix model N omega
      ((3 : ℝ) ^ N • x) c r (_root_.SubdiffusiveProcess.Model.tauSq model.P) hcr rfl
  have hfield : ProbabilityTheory.IdentDistrib
      (fun omega : BilateralField d =>
        c • aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
      (chaosSampleLaw model).toMeasure model.P.toMeasure := by
    have hright : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        c • aux_annealed_limit_response_transport_scalarRegCoeffField (gsource omega)) =
        (fun omega => Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)) := by
      funext omega
      exact hsource omega
    simpa [Function.comp_def, hright] using hscaled
  let Pscaled : Homogenization.Book.Ch04.RestrictionCoeffLaw d :=
    Homogenization.Book.Ch04.restrictionScaleNormalizedLaw N
      (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw model N)
  have hPscaled : Homogenization.Book.Ch04.RestrictionLawCarrier Pscaled := by
    exact (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw_lawCarrier model N).scaleNormalized N
  have hF : AEMeasurable
      (aux_in_moments_response_moment_countable
        (Homogenization.originCube d (k : ℤ)) alpha) Pscaled := by
    exact aux_in_moments_response_moment_countable_aemeasurable Pscaled hPscaled _ _
  have hFmap : Measure.map
      (fun omega : BilateralField d =>
        c • aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
      (chaosSampleLaw model).toMeasure = Pscaled := by
    dsimp [Pscaled]
    rw [Homogenization.Book.Ch04.restrictionScaleNormalizedLaw_eq_map_rescaleReg,
      SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw_eq_map]
    rw [Measure.map_map (Homogenization.measurable_rescaleReg N)
      (SubdiffusiveProcess.CoarseGrainingVocab.measurable_aCutoffRegCoeffField model N)]
    exact hfield.map_eq
  have hstat := stationary_family d hd model
  dsimp at hstat
  have hfAcut : fA = aux_in_moments_response_moment_cutoffField model N := by
    funext omega
    ext x
    simpa [fA, aux_in_moments_response_moment_cutoffField, alpha,
      SubdiffusiveProcess.cutoffCoefficient,
      SubdiffusiveProcess.cutoffPotential] using (hstat.1 N omega x).symm
  have hID := hfield.comp_of_aemeasurable (by simpa [hFmap] using hF)
  rw [hfAcut] at hID
  simpa [c, s, alpha, Function.comp_def] using! hID

theorem aux_in_moments_response_moment_family_countable
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k : ℕ)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamily : ∀ (N : ℕ) (ω : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N ω).coeffOn Q).toCoeffField x =
          scalarMatrix
            (cutoffCoefficient model
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x))
    (omega : BilateralField d) (r : ℝ)
    (hmax : IsGreatest
      {v : ℝ | ∃ e : Fin d → ℝ,
        (∑ i : Fin d, e i ^ 2) = 1 ∧
        v = responseJ (cubeDomain (originCube d (k : ℤ)))
          ((family N omega).coeffOn (originCube d (k : ℤ))) e e} r) :
    aux_in_moments_response_moment_countable
        (originCube d (k : ℤ)) (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)
        ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) •
          aux_annealed_limit_response_transport_scalarRegCoeffField
            (aux_in_moments_response_moment_cutoffField model N omega)) =
      ENNReal.ofReal r := by
  let alpha : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
  let Q : TriadicCube d := originCube d (k : ℤ)
  let U : Homogenization.Book.Ch02.Domain d := cubeDomain Q
  let b : Homogenization.Book.Ch02.CoeffOn U := (family N omega).coeffOn Q
  have halpha : 0 < alpha := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N
  let as : Homogenization.Book.Ch02.CoeffOn U :=
    aux_in_moments_response_moment_scaledCoeffOn alpha halpha b
  have hcoeff : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Homogenization.Vec d))]
      (fun x => scalarMatrix
        (cutoffCoefficient model
          (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x)) := by
    simpa [b, U, Q, Homogenization.Book.Ch02.cubeDomain_coe,
      Homogenization.volumeMeasureOn] using! hfamily N omega Q
  have hcoeffR :
      (fun x => Homogenization.restrictCoeffField (U : Set (Homogenization.Vec d))
        b.toCoeffField x) =ᵐ[volumeMeasureOn (U : Set (Homogenization.Vec d))]
      (fun x => Homogenization.restrictCoeffField (U : Set (Homogenization.Vec d))
        (fun y => scalarMatrix
          (cutoffCoefficient model
            (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N y)) x) := by
    filter_upwards [hcoeff] with x hx
    by_cases hxu : x ∈ (U : Set (Homogenization.Vec d))
    · simp [Homogenization.restrictCoeffField, hxu, hx]
    · simp [Homogenization.restrictCoeffField, hxu]
  let bc : Homogenization.Book.Ch02.CoeffOn U :=
    { toCoeffField := fun x => scalarMatrix
        (cutoffCoefficient model
          (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x)
      lam := b.lam
      Lam := b.Lam
      lam_pos := b.lam_pos
      lam_le_Lam := b.lam_le_Lam
      aeStronglyMeasurable := by
        intro i j
        exact (b.aeStronglyMeasurable i j).congr
          (hcoeffR.mono fun x hx => by
            exact congrFun (congrFun hx i) j)
      aeElliptic := by
        filter_upwards [b.aeElliptic, hcoeff] with x hx hxc
        rw [← hxc]
        exact hx }
  have hbc : Homogenization.Book.Ch02.CoeffOn.AEEq b bc := by
    simpa [bc] using! hcoeff
  let ac : Homogenization.Book.Ch02.CoeffOn U :=
    aux_in_moments_response_moment_scaledCoeffOn alpha halpha bc
  have hterm : ∀ i : ℕ,
      Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet Q
          ((Real.sqrt alpha)⁻¹ •
            (TopologicalSpace.denseSeq
              (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
                Homogenization.Vec d))
          (Real.sqrt alpha •
            (TopologicalSpace.denseSeq
              (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
                Homogenization.Vec d))
          (alpha • aux_annealed_limit_response_transport_scalarRegCoeffField
            (aux_in_moments_response_moment_cutoffField model N omega)) =
        responseJ U b
          (TopologicalSpace.denseSeq
            (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
              Homogenization.Vec d)
          (TopologicalSpace.denseSeq
            (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
              Homogenization.Vec d) := by
    intro i
    have hobs := Homogenization.Book.Ch04.restrictionResponseJObservableCubeSet_apply
      Q
      ((Real.sqrt alpha)⁻¹ •
        (TopologicalSpace.denseSeq
          (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
            Homogenization.Vec d))
      (Real.sqrt alpha •
        (TopologicalSpace.denseSeq
          (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
            Homogenization.Vec d))
      (alpha • aux_annealed_limit_response_transport_scalarRegCoeffField
        (aux_in_moments_response_moment_cutoffField model N omega))
    rw [hobs]
    rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
    rw [Homogenization.responseJ_cubeSet_eq_openCubeSet_of_triadicCube]
    have hraw : Homogenization.ResponseJ (openCubeSet Q)
          ((Real.sqrt alpha)⁻¹ •
            (TopologicalSpace.denseSeq
              (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
                Homogenization.Vec d))
          (Real.sqrt alpha •
            (TopologicalSpace.denseSeq
              (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
                Homogenization.Vec d))
          (alpha • aux_annealed_limit_response_transport_scalarRegCoeffField
            (aux_in_moments_response_moment_cutoffField model N omega)).toFun =
        responseJ U ac
          ((Real.sqrt alpha)⁻¹ •
            (TopologicalSpace.denseSeq
              (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
                Homogenization.Vec d))
          (Real.sqrt alpha •
            (TopologicalSpace.denseSeq
              (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
                Homogenization.Vec d)) := by
      have hcoefEq :
          (alpha • aux_annealed_limit_response_transport_scalarRegCoeffField
            (aux_in_moments_response_moment_cutoffField model N omega)).toFun =
            ac.toCoeffField := by
        funext x
        simp [ac, aux_in_moments_response_moment_scaledCoeffOn,
          bc,
          aux_in_moments_response_moment_cutoffField,
          aux_annealed_limit_response_transport_scalarRegCoeffField_apply]
      rw [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ]
      rw [← Homogenization.responseJ_cubeSet_eq_openCubeSet_of_triadicCube]
      change Homogenization.ResponseJ (cubeSet Q) _ _ _ =
        Homogenization.ResponseJ (openCubeSet Q) _ _ ac.toCoeffField
      rw [← hcoefEq]
      exact (Homogenization.responseJ_cubeSet_eq_openCubeSet_of_triadicCube
        Q _ _ _)
    rw [hraw]
    have hhom := I.responseJ_scalar_hom U ac bc alpha halpha
      (fun x => by
        simp [ac, bc, aux_in_moments_response_moment_scaledCoeffOn,
          smul_smul, halpha.ne'])
    rw [hhom]
    exact Homogenization.Book.Ch02.responseJ_eq_ofAEEq hbc.symm _ _
  rw [show aux_in_moments_response_moment_countable
      Q alpha (alpha • aux_annealed_limit_response_transport_scalarRegCoeffField
        (aux_in_moments_response_moment_cutoffField model N omega)) =
      ⨆ i : ℕ, ENNReal.ofReal
        (responseJ U b
          (TopologicalSpace.denseSeq
            (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
              Homogenization.Vec d)
          (TopologicalSpace.denseSeq
            (SubdiffusiveProcess.CoarseGrainingVocab.ScalarProbeUnitSphere d) i :
              Homogenization.Vec d)) by
    unfold aux_in_moments_response_moment_countable
    apply iSup_congr
    intro i
    rw [hterm i]]
  exact aux_in_moments_response_moment_dense_max d (by omega) I U b r
    (by simpa [U, Q, b] using hmax)

theorem aux_in_moments_response_moment_cutoff_sup_nonneg
    {d : ℕ} (hd : 1 ≤ d)
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffResponseSupremum
      model L n omega 0 := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffResponseSupremum
  let A : Set ℝ := {t : ℝ | ∃ e : Homogenization.Vec d,
    Homogenization.vecNormSq e = 1 ∧
      t = SubdiffusiveProcess.CoarseGrainingVocab.section6Response model n (min n L) omega 0 e}
  have hAne : A.Nonempty := by
    let i : Fin d := ⟨0, by omega⟩
    refine ⟨SubdiffusiveProcess.CoarseGrainingVocab.section6Response model n (min n L)
      omega 0 (Pi.single i 1), ?_⟩
    refine ⟨Pi.single i 1, ?_, rfl⟩
    simp [Homogenization.vecNormSq, Homogenization.vecDot, Pi.single_apply]
  have hAbdd : BddAbove A := by
    simpa [A] using
      (SubdiffusiveProcess.CoarseGrainingVocab.bddAbove_section6Response_unitSphere
        model n (min n L) omega 0)
  obtain ⟨_, e, he, rfl⟩ := hAne
  have hJ : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.section6Response model n (min n L)
      omega 0 e := by
    unfold SubdiffusiveProcess.CoarseGrainingVocab.section6Response
      SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe
    exact Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
  exact hJ.trans (le_csSup hAbdd ⟨e, he, rfl⟩)



theorem in_moments_response_moment (d : ℕ) (hd : 2 ≤ d) (I : _root_.SubdiffusiveProcess.Paper.in_J d) :
    ∃ Cresp : ℝ, 0 < Cresp ∧
      ∀ (xi : ℕ), Even xi → 128 * d ≤ xi →
        ∃ disorder0 : ℝ, 0 < disorder0 ∧
          ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
            [BorelSpace C(SpatialCoordinates d, ℝ)]
            (model : _root_.SubdiffusiveProcess.Model.GMCModel d),
            model.delta ≤ disorder0 →
              ∀ (family : ℕ → BilateralField d → TriadicCoeffFamily d),
                (∀ (N : ℕ) (ω : BilateralField d) (Q : TriadicCube d),
                  ∀ᵐ x ∂volume.restrict (openCubeSet Q),
                    ((family N ω).coeffOn Q).toCoeffField x =
                      scalarMatrix
                        (cutoffCoefficient model
                          (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x)) →
                (xi : ℝ) ≤
                  Cresp⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹ →
                ∃ Jsup : ℕ → ℕ → BilateralField d → ℝ,
                  (∀ (N k : ℕ) (ω : BilateralField d),
                    IsGreatest
                      {v : ℝ | ∃ e : Fin d → ℝ,
                        (∑ i : Fin d, e i ^ 2) = 1 ∧
                        v = responseJ (cubeDomain (originCube d (k : ℤ)))
                          ((family N ω).coeffOn (originCube d (k : ℤ))) e e}
                      (Jsup N k ω)) ∧
                  (∀ (N k : ℕ),
                    AEStronglyMeasurable (Jsup N k)
                      (chaosSampleLaw model).toMeasure) ∧
                  (∀ (N k : ℕ),
                    eLpNorm (Jsup N k) (ENNReal.ofReal (xi : ℝ))
                        (chaosSampleLaw model).toMeasure ≤
                      ENNReal.ofReal
                        (Cresp * (xi : ℝ) * Real.log (2 + (xi : ℝ)) *
                          model.delta ^ 2)) := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) hd)⟩
  obtain ⟨c0, Cresp, hc0, hCresp, hmoment⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.exists_cutoffResponseSupremum_moment_bound d
  refine ⟨Cresp, hCresp, ?_⟩
  intro xi hxiEven hxiNat
  have hxiOne : 1 ≤ (xi : ℝ) := by
    exact_mod_cast (show 1 ≤ xi by omega)
  refine ⟨1, by norm_num, ?_⟩
  intro instC instB model hdelta family hfamily hxiBound
  have hdeltaOne : model.delta ≤ (1 : ℝ) :=
    model.shellPrefix.delta_le_half.trans (by norm_num)
  let Jsup : ℕ → ℕ → BilateralField d → ℝ := fun N k omega =>
    Classical.choose
      (aux_in_moments_response_moment_max d (by omega) I
        (cubeDomain (originCube d (k : ℤ)))
        ((family N omega).coeffOn (originCube d (k : ℤ))))
  have hJgreatest : ∀ (N k : ℕ) (omega : BilateralField d),
      IsGreatest
        {v : ℝ | ∃ e : Fin d → ℝ,
          (∑ i : Fin d, e i ^ 2) = 1 ∧
          v = responseJ (cubeDomain (originCube d (k : ℤ)))
            ((family N omega).coeffOn (originCube d (k : ℤ))) e e}
        (Jsup N k omega) := by
    intro N k omega
    dsimp [Jsup]
    exact Classical.choose_spec
      (aux_in_moments_response_moment_max d (by omega) I
        (cubeDomain (originCube d (k : ℤ)))
        ((family N omega).coeffOn (originCube d (k : ℤ))))
  have hJnonneg : ∀ (N k : ℕ) (omega : BilateralField d),
      0 ≤ Jsup N k omega := by
    intro N k omega
    obtain ⟨e, he, hEq⟩ := (hJgreatest N k omega).1
    rw [hEq]
    exact Homogenization.Book.Ch02.responseJ_nonneg _ _ _ _
  let Ftarget : ℕ → ℕ → BilateralField d → ℝ≥0∞ := fun N k omega =>
    aux_in_moments_response_moment_countable
      (originCube d (k : ℤ)) (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N •
        aux_annealed_limit_response_transport_scalarRegCoeffField
          (aux_in_moments_response_moment_cutoffField model N omega))
  let Fsource : ℕ → ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ :=
    fun N k omega =>
      aux_in_moments_response_moment_countable
        (originCube d (k : ℤ)) (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)
        (Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
  have hcountJ : ∀ (N k : ℕ) (omega : BilateralField d),
      Ftarget N k omega = ENNReal.ofReal (Jsup N k omega) := by
    intro N k omega
    dsimp [Ftarget]
    exact aux_in_moments_response_moment_family_countable hd I model N k
      family hfamily omega (Jsup N k omega) (hJgreatest N k omega)
  have hsourceEq : ∀ (N k : ℕ)
      (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d),
      Fsource N k omega = ENNReal.ofReal
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffResponseSupremum
          model N (N + k) omega 0) := by
    intro N k omega
    dsimp [Fsource]
    rw [aux_in_moments_response_moment_source_countable d N k model omega]
    rw [← SubdiffusiveProcess.CoarseGrainingVocab.normalizedDefect_eq_countableRepresentative
      model N (cubeDomain (originCube d ((N + k : ℕ) : ℤ))) omega]
    have hcut :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ofReal_cutoffResponseSupremum_zero_eq_normalizedDefect
        model N (N + k) omega
    rw [Nat.min_eq_right (Nat.le_add_right N k)] at hcut
    exact hcut.symm
  have hmeas : ∀ (N k : ℕ),
      AEStronglyMeasurable (Jsup N k)
        (chaosSampleLaw model).toMeasure := by
    intro N k
    have hF : AEMeasurable (Ftarget N k) (chaosSampleLaw model).toMeasure := by
      simpa [Ftarget] using
        (aux_in_moments_response_moment_countable_transport hd model N k).aemeasurable_fst
    have hto : AEMeasurable (fun z : ℝ≥0∞ => z.toReal)
        (Measure.map (Ftarget N k) (chaosSampleLaw model).toMeasure) := by
      exact (Measurable.ennreal_toReal measurable_id).aemeasurable
    have hFr : AEMeasurable (fun omega => (Ftarget N k omega).toReal)
        (chaosSampleLaw model).toMeasure := hto.comp_aemeasurable hF
    have heq : (fun omega => (Ftarget N k omega).toReal) =ᵐ[
        (chaosSampleLaw model).toMeasure] (Jsup N k) :=
      Filter.Eventually.of_forall (fun omega => by
        change (Ftarget N k omega).toReal = Jsup N k omega
        rw [hcountJ N k omega, ENNReal.toReal_ofReal (hJnonneg N k omega)])
    exact (hFr.congr heq).aestronglyMeasurable
  have hrealID : ∀ (N k : ℕ),
      ProbabilityTheory.IdentDistrib (Jsup N k)
        (fun omega =>
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffResponseSupremum
            model N (N + k) omega 0)
        (chaosSampleLaw model).toMeasure model.P.toMeasure := by
    intro N k
    have hcount := aux_in_moments_response_moment_countable_transport hd model N k
    have hto : Measurable (fun z : ℝ≥0∞ => z.toReal) :=
      Measurable.ennreal_toReal measurable_id
    have hreal : ProbabilityTheory.IdentDistrib
        (fun omega => (Ftarget N k omega).toReal)
        (fun omega => (Fsource N k omega).toReal)
        (chaosSampleLaw model).toMeasure model.P.toMeasure := by
      simpa [Ftarget, Fsource, Function.comp_def] using hcount.comp hto
    have hfst : (fun omega => (Ftarget N k omega).toReal) =ᵐ[
        (chaosSampleLaw model).toMeasure] (Jsup N k) :=
      Filter.Eventually.of_forall (fun omega => by
        change (Ftarget N k omega).toReal = Jsup N k omega
        rw [hcountJ N k omega, ENNReal.toReal_ofReal (hJnonneg N k omega)])
    have hsupnonneg : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffResponseSupremum
          model N (N + k) omega 0 := by
      intro omega
      exact aux_in_moments_response_moment_cutoff_sup_nonneg (by omega)
        model N (N + k) omega
    have hsnd : (fun omega => (Fsource N k omega).toReal) =ᵐ[
        model.P.toMeasure] (fun omega =>
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffResponseSupremum
            model N (N + k) omega 0) :=
      Filter.Eventually.of_forall (fun omega => by
        change (Fsource N k omega).toReal =
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffResponseSupremum
            model N (N + k) omega 0
        rw [hsourceEq N k omega, ENNReal.toReal_ofReal (hsupnonneg omega)])
    refine
      { aemeasurable_fst := hreal.aemeasurable_fst.congr hfst
        aemeasurable_snd := hreal.aemeasurable_snd.congr hsnd
        map_eq := ?_ }
    calc
      Measure.map (Jsup N k) (chaosSampleLaw model).toMeasure =
          Measure.map (fun omega => (Ftarget N k omega).toReal)
            (chaosSampleLaw model).toMeasure := Measure.map_congr hfst.symm
      _ = Measure.map (fun omega => (Fsource N k omega).toReal)
            model.P.toMeasure := hreal.map_eq
      _ = Measure.map (fun omega =>
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffResponseSupremum
            model N (N + k) omega 0) model.P.toMeasure := Measure.map_congr hsnd
  refine ⟨Jsup, hJgreatest, ?_, ?_⟩
  · exact hmeas
  · intro N k
    have hxiPos : 0 < (xi : ℝ) := lt_of_lt_of_le zero_lt_one hxiOne
    have hpaper := hmoment model (xi : ℝ) hxiOne hxiBound N (N + k)
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.paperENNRealLpNorm_ofReal_eq_eLpNorm_of_nonnegative
      model.P.toMeasure hxiPos
      (fun omega => aux_in_moments_response_moment_cutoff_sup_nonneg (by omega)
        model N (N + k) omega)] at hpaper
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded
      (hrealID N k).aemeasurable_snd.aestronglyMeasurable] at hpaper
    calc
      eLpNorm (Jsup N k) (ENNReal.ofReal (xi : ℝ))
          (chaosSampleLaw model).toMeasure =
        eLpNorm (fun omega =>
          SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.cutoffResponseSupremum
            model N (N + k) omega 0) (ENNReal.ofReal (xi : ℝ))
          model.P.toMeasure := (hrealID N k).eLpNorm_eq _
      _ ≤ ENNReal.ofReal
          (Cresp * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2) :=
        hpaper

end SubdiffusiveProcess.Paper
