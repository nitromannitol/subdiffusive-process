module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCenteredWeakHessian
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepConcreteCellCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHessianObservableMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepWeightedPrincipalClosure

@[expose] public section

/-!
# Weak Hessians for the canonical measurable one-step solutions

The deterministic Calderon--Zygmund theorem is applied samplewise to the
already measurable canonical Lax--Milgram solution.  Only its `W^{2,4}`
representative is selected; the solution itself is never replaced by a
second, nonmeasurable choice.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Samplewise CZ representatives and a measurable Hessian observable for
the literal canonical origin-cube Dirichlet solution. -/
theorem exists_measurable_oneStepCanonicalDirichlet_cellB
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (hh : 0 < h),
        ∃ (V : ∀ _omega, CubeVectorW1pFunction
              (originCube d m) oneStepFourExponent),
          ∃ hV : ∀ omega,
              (V omega).toField =
                (oneStepOriginDirichletSolution M n h p m omega hh
                  ).toH1Function.grad,
            Measurable (fun omega ↦
              oneStepCellB (originCube d m)
                (weakHessianOfCubeVectorW1pFour (V omega) (hV omega))) ∧
            ∀ omega,
              eLpNorm (fun x ↦ HilbertMat.ofMat ((V omega).jacobian x)) 4
                  (normalizedCubeMeasure (originCube d m)) ≤
                C * eLpNorm (fun x ↦ HilbertMat.ofMat
                  ((oneStepShellForcingW14 M n h omega p
                    (originCube d m) hh).jacobian x)) 4
                  (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCtop, hCZ⟩ := exists_oneStepShell_scalarDivergence_cz d
  refine ⟨C, hCtop, ?_⟩
  intro M n h p m hh
  let Q := originCube d m
  let uD : _root_.SubdiffusiveProcess.Model.PotentialSample d → H10Function (openCubeSet Q) := fun omega ↦
    oneStepOriginDirichletSolution M n h p m omega hh
  have huD : ∀ omega,
      CubeDirichletDivergenceProblem Q (uD omega)
        (oneStepShellForcingH1 M n h omega p Q hh).toField := by
    intro omega phi
    have hweak := oneStepOriginDirichletSolution_isWeakSolution
      M n h p m omega hh phi
    have hfield : ∀ x,
        (oneStepShellForcingH1 M n h omega p Q hh).toField x =
          oneStepMultiplierAt M n h x omega • p := by
      intro x
      rw [oneStepShellForcing_paired_toField M n h omega p Q hh,
        oneStepShellForcingW14_toField_apply]
    change (∫ x in openCubeSet Q,
        vecDot ((uD omega).toH1Function.grad x)
          (phi.toH1Function.grad x)
          ∂volume) = _
    calc
      _ = ∫ x in openCubeSet Q,
          vecDot (-oneStepMultiplierAt M n h x omega • p)
            (phi.toH1Function.grad x) ∂volume := by
        simpa only [Q, uD, matVecMul_identityCoeffField, one_mul] using hweak
      _ = -∫ x in openCubeSet Q,
          vecDot ((oneStepShellForcingH1 M n h omega p Q hh).toField x)
            (phi.toH1Function.grad x) ∂volume := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with x
        rw [hfield]
        rw [neg_smul, vecDot_neg_left]
  choose V hV hbound using fun omega ↦
    hCZ M n h omega p m hh (uD omega) (huD omega)
  refine ⟨V, hV, ?_, hbound⟩
  exact measurable_oneStepShellDirichlet_cellB M n h p Q hh uD huD
    (fun omega ↦ weakHessianOfCubeVectorW1pFour (V omega) (hV omega))



theorem oneStepOriginDirichlet_grad_ae_eq_triadic
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
    (oneStepTriadicDirichletSolution M n h p (originCube d m) omega hh
      ).toH1Function.grad := by
  let Q := originCube d m
  let u := oneStepOriginDirichletGradientL2 M n h p m omega
  let v := H1Function.gradToHilbertVectorL2
    (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
  have huv : u = v :=
    oneStepOriginDirichletGradientL2_eq_triadic M n h p m omega hh
  have huCoe :=
    (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function
      |>.coeFn_gradToHilbertVectorL2
  have hvCoe :=
    (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
      |>.coeFn_gradToHilbertVectorL2
  rw [oneStepOriginDirichletSolution_gradient_eq
    M n h p m omega hh] at huCoe
  change (u : Vec d → HilbertVec d) =ᵐ[volumeMeasureOn (openCubeSet Q)]
    fun x ↦ HilbertVec.ofVec
      ((oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad x)
      at huCoe
  change (v : Vec d → HilbertVec d) =ᵐ[volumeMeasureOn (openCubeSet Q)]
    fun x ↦ HilbertVec.ofVec
      ((oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function.grad x)
      at hvCoe
  rw [huv] at huCoe
  filter_upwards [huCoe, hvCoe] with x hux hvx
  have hvec := congrArg HilbertVec.toVec (hux.symm.trans hvx)
  simpa only [u, v, Q, hilbertifyVecField,
    HilbertVec.toVec_ofVec] using hvec

/-- Weak uniqueness in the concrete shell problem, stated at the spatial
gradient representative.  This lets the pointwise Calderón--Zygmund witness
chosen by `exists_measurable_oneStepShellDirichlet_cellB` feed the canonical
source-cell fluctuation without replacing either measurable solution map. -/
theorem oneStepShellDirichlet_grad_ae_eq_origin
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (u : H10Function (openCubeSet (originCube d m)))
    (hu : CubeDirichletDivergenceProblem (originCube d m) u
      (oneStepShellForcingH1 M n h omega p (originCube d m) hh).toField) :
    u.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad := by
  let Q := originCube d m
  let G := oneStepShellForcingH1 M n h omega p Q hh
  let hG : MemVectorL2 (openCubeSet Q) G.toField :=
    G.memVectorL2_toField_openCubeSet
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q)
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization
        (openCubeSet Q) :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q)
  let D := oneStepDirichletGradientOfForcingClass
    (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q))
    (openCubeSet_nonempty_internal Q) hEll
  have hweak : IsZeroTraceDirichletRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) u (fun x ↦ -G.toField x) := by
    intro phi
    have hbase := hu phi
    simp only [matVecMul_identityCoeffField]
    change
      ∫ x in openCubeSet Q,
          vecDot (u.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (-G.toField x) (phi.toH1Function.grad x) ∂volume
    calc
      _ = -∫ x in openCubeSet Q,
          vecDot (G.toField x) (phi.toH1Function.grad x) ∂volume := by
        simpa only [Q, G, CubeDirichletDivergenceProblem,
          matVecMul_identityCoeffField] using hbase
      _ = _ := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with x
        exact (vecDot_neg_left (G.toField x) (phi.toH1Function.grad x)).symm
  have huClass : u.toH1Function.gradToHilbertVectorL2 =
      oneStepOriginDirichletGradientL2 M n h p m omega := by
    calc
      u.toH1Function.gradToHilbertVectorL2 =
          D (toHilbertVectorL2OfVecField hG.neg) := by
        exact gradToHilbertVectorL2_eq_oneStepDirichletGradientOfForcingClass
          hG.neg hRealize (openCubeSet_nonempty_internal Q) hEll hweak
      _ = D (-oneStepShellForcingL2 M n h p Q omega) := by
        apply congrArg D
        rw [toHilbertVectorL2OfVecField_neg_oneStep hG]
        congr 1
        exact (oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
          M n h p Q omega hh).symm
      _ = oneStepOriginDirichletGradientL2 M n h p m omega := rfl
  have huCoe := u.toH1Function.coeFn_gradToHilbertVectorL2
  have hvCoe :=
    (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function
      |>.coeFn_gradToHilbertVectorL2
  rw [huClass] at huCoe
  rw [oneStepOriginDirichletSolution_gradient_eq
    M n h p m omega hh] at hvCoe
  filter_upwards [huCoe, hvCoe] with x hux hvx
  have hvec := congrArg HilbertVec.toVec (hux.symm.trans hvx)
  simpa only [Q, hilbertifyVecField, HilbertVec.toVec_ofVec] using hvec

/-- Restricting and centering the canonical CZ solution produces exactly the
source-cell fluctuation already used by the stochastic partition, modulo the
unavoidable Sobolev representative equality. -/
theorem oneStepCanonicalCenteredRestriction_grad_ae_eq_cellFluctuation
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (R : TriadicCube d)
    (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    (oneStepCenteredRestriction
        (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function hR
      ).grad =ᵐ[volumeMeasureOn (openCubeSet R)]
      oneStepDirichletCellFluctuationField M n h p (originCube d m) R
        omega hh := by
  let Q := originCube d m
  let uD := (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function
  let uT :=
    (oneStepTriadicDirichletSolution M n h p Q omega hh).toH1Function
  have hgradQ : uD.grad =ᵐ[volumeMeasureOn (openCubeSet Q)] uT.grad := by
    simpa only [Q, uD, uT] using
      oneStepOriginDirichlet_grad_ae_eq_triadic M n h p m omega hh
  have hRQ : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hgradR : uD.grad =ᵐ[volumeMeasureOn (openCubeSet R)] uT.grad :=
    hgradQ.filter_mono <| MeasureTheory.ae_mono <|
      Measure.restrict_mono_set volume hRQ
  have hgradCube : uD.grad =ᵐ[volume.restrict (cubeSet R)] uT.grad := by
    simpa only [volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hgradR
  have havg : cubeAverageVec R uD.grad = cubeAverageVec R uT.grad :=
    cubeAverageVec_eq_of_ae_eq_on_cubeSet hgradCube
  rw [oneStepDirichletCellFluctuationField_eq_centeredTriadicGrad
    M n h p Q R omega hh hR]
  filter_upwards [hgradR] with x hx
  rw [oneStepCenteredRestriction_grad, hx, havg]

/-- Centering any weakly equivalent shell solution gives the same concrete
source-cell fluctuation.  This is the representative-stable version used by
the descendant Calderón--Zygmund package. -/
theorem oneStepShellCenteredRestriction_grad_ae_eq_cellFluctuation
    {d j : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (m : ℤ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (u : H10Function (openCubeSet (originCube d m)))
    (hu : CubeDirichletDivergenceProblem (originCube d m) u
      (oneStepShellForcingH1 M n h omega p (originCube d m) hh).toField)
    (R : TriadicCube d)
    (hR : R ∈ descendantsAtDepth (originCube d m) j) :
    (oneStepCenteredRestriction u.toH1Function hR).grad
      =ᵐ[volumeMeasureOn (openCubeSet R)]
      oneStepDirichletCellFluctuationField M n h p (originCube d m) R
        omega hh := by
  let u0 :=
    (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function
  have hgradQ : u.toH1Function.grad
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))] u0.grad :=
    oneStepShellDirichlet_grad_ae_eq_origin M n h p m omega hh u hu
  have hRQ : openCubeSet R ⊆ openCubeSet (originCube d m) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hgradR : u.toH1Function.grad
      =ᵐ[volumeMeasureOn (openCubeSet R)] u0.grad :=
    hgradQ.filter_mono <| MeasureTheory.ae_mono <|
      Measure.restrict_mono_set volume hRQ
  have hgradCube : u.toH1Function.grad
      =ᵐ[volume.restrict (cubeSet R)] u0.grad := by
    simpa only [volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hgradR
  have havg : cubeAverageVec R u.toH1Function.grad =
      cubeAverageVec R u0.grad :=
    cubeAverageVec_eq_of_ae_eq_on_cubeSet hgradCube
  have hcanonical :=
    oneStepCanonicalCenteredRestriction_grad_ae_eq_cellFluctuation
      M n h p m omega hh R hR
  filter_upwards [hgradR, hcanonical] with x hx hcan
  rw [oneStepCenteredRestriction_grad, hx, havg]
  simpa only [u0, oneStepCenteredRestriction_grad] using hcan

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
