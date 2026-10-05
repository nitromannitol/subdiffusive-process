module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellLocalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMeasurableCorrectors
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.WeakHessianMeasurability

@[expose] public section

/-!
# Borel weak-Hessian carriers and the literal one-step `B_z`

The manuscript observable  is the cell side times
the normalized spatial `L²` norm of the weak Hessian of the corrector.  This
module packages all Hessian coordinates in a finite Hilbert-product carrier
and proves that the carrier, its coordinate-norm sum, and hence the literal
`B_z` are Borel functions of the sample.

The analytic `W^{2,4}` estimate is separate: it bounds the fourth random
moment of this measurable `L²` observable, but does not define a replacement
observable.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- Finite coordinate carrier of a weak Hessian in scalar `L²(U)`. -/
abbrev WeakHessianL2Carrier {d : ℕ} (U : Set (Vec d)) :=
  Fin d → Fin d → ScalarL2 U

/-- Forget the weak-derivative proofs and retain all represented Hessian
coordinates in the finite `L²` carrier. -/
def weakHessianL2CarrierOf {d : ℕ} {U : Set (Vec d)}
    {u : H1Function U} (H : HasWeakHessianOn U u) :
    WeakHessianL2Carrier U :=
  fun i j => H.hessCoordToScalarL2 i j



def weakHessianOfCubeVectorW1pFour {d : ℕ} {Q : TriadicCube d}
    {u : H1Function (openCubeSet Q)}
    (V : CubeVectorW1pFunction Q oneStepFourExponent)
    (hV : V.toField = u.grad) :
    HasWeakHessianOn (openCubeSet Q) u where
  hess := fun i j x => V.jacobian x i j
  hess_memL2 := by
    intro i j
    let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
      isFiniteMeasure_volumeMeasureOn_openCubeSet Q
    exact ((V.coord i).gradMemLp j).mono_exponent
      (show (2 : ENNReal) ≤ 4 by norm_num)
  weak_second := by
    intro i j
    have hweak := (V.coord i).hasWeakGradient j
    simpa only [CubeVectorW1pFunction.jacobian_apply, ← hV,
      CubeVectorW1pFunction.toField_apply] using hweak

/-- A sample-dependent weak Hessian is Borel as a finite `L²` matrix whenever
the underlying gradient class is Borel. -/
theorem measurable_weakHessianL2Carrier
    {Omega : Type*} [MeasurableSpace Omega]
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : volume U ≠ ⊤) (u : Omega → H1Function U)
    (H : ∀ omega, HasWeakHessianOn U (u omega))
    (hgrad : Measurable fun omega => (u omega).gradToHilbertVectorL2) :
    Measurable fun omega => weakHessianL2CarrierOf (H omega) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact measurable_weakHessianCoordScalarL2 hUopen hUfinite u H hgrad i j

/-- The coordinate-sum `L²` size is Borel on the weak-Hessian carrier. -/
theorem measurable_weakHessianCoordL2NormSum
    {Omega : Type*} [MeasurableSpace Omega]
    {d : ℕ} {U : Set (Vec d)} (hUopen : IsOpen U)
    (hUfinite : volume U ≠ ⊤) (u : Omega → H1Function U)
    (H : ∀ omega, HasWeakHessianOn U (u omega))
    (hgrad : Measurable fun omega => (u omega).gradToHilbertVectorL2) :
    Measurable fun omega => (H omega).hessianCoordL2NormSum := by
  have hcarrier := measurable_weakHessianL2Carrier hUopen hUfinite u H hgrad
  unfold HasWeakHessianOn.hessianCoordL2NormSum
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp hcarrier)).norm

/-- The literal normalized cell Hessian size is Borel. -/
theorem measurable_oneStepCellNormalizedHessianSize
    {Omega : Type*} [MeasurableSpace Omega]
    {d : ℕ} (R : TriadicCube d)
    (u : Omega → H1Function (openCubeSet R))
    (H : ∀ omega, HasWeakHessianOn (openCubeSet R) (u omega))
    (hgrad : Measurable fun omega => (u omega).gradToHilbertVectorL2) :
    Measurable fun omega => oneStepCellNormalizedHessianSize R (H omega) := by
  unfold oneStepCellNormalizedHessianSize
  exact measurable_const.mul
    (measurable_weakHessianCoordL2NormSum (isOpen_openCubeSet R)
      (volume_openCubeSet_lt_top R).ne u H hgrad)

/-- The manuscript's literal `B_z`: cell side times normalized weak-Hessian
`L²` size. -/
def oneStepCellB {d : ℕ} (R : TriadicCube d)
    {u : H1Function (openCubeSet R)}
    (H : HasWeakHessianOn (openCubeSet R) u) : ℝ :=
  cubeScaleFactor R * oneStepCellNormalizedHessianSize R H

theorem measurable_oneStepCellB
    {Omega : Type*} [MeasurableSpace Omega]
    {d : ℕ} (R : TriadicCube d)
    (u : Omega → H1Function (openCubeSet R))
    (H : ∀ omega, HasWeakHessianOn (openCubeSet R) (u omega))
    (hgrad : Measurable fun omega => (u omega).gradToHilbertVectorL2) :
    Measurable fun omega => oneStepCellB R (H omega) := by
  unfold oneStepCellB
  exact measurable_const.mul
    (measurable_oneStepCellNormalizedHessianSize R u H hgrad)

/-- Dirichlet specialization: every weak-Hessian family above arbitrary
one-step weak solutions has a measurable carrier. -/
theorem measurable_oneStepShellDirichlet_weakHessianL2Carrier
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (uD : _root_.SubdiffusiveProcess.Model.PotentialSample d → H10Function (openCubeSet Q))
    (huD : ∀ omega,
      CubeDirichletDivergenceProblem Q (uD omega)
        (oneStepShellForcingH1 M n h omega p Q hh).toField)
    (H : ∀ omega,
      HasWeakHessianOn (openCubeSet Q) (uD omega).toH1Function) :
    Measurable fun omega => weakHessianL2CarrierOf (H omega) := by
  exact measurable_weakHessianL2Carrier (isOpen_openCubeSet Q)
    (volume_openCubeSet_lt_top Q).ne (fun omega => (uD omega).toH1Function) H
    (measurable_oneStepShellDirichletGradL2 M n h p Q hh uD huD)

/-- Dirichlet `B_z` itself is measurable for every supplied weak-Hessian
witness family. -/
theorem measurable_oneStepShellDirichlet_cellB
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (uD : _root_.SubdiffusiveProcess.Model.PotentialSample d → H10Function (openCubeSet Q))
    (huD : ∀ omega,
      CubeDirichletDivergenceProblem Q (uD omega)
        (oneStepShellForcingH1 M n h omega p Q hh).toField)
    (H : ∀ omega,
      HasWeakHessianOn (openCubeSet Q) (uD omega).toH1Function) :
    Measurable fun omega => oneStepCellB Q (H omega) := by
  exact measurable_oneStepCellB Q (fun omega => (uD omega).toH1Function) H
    (measurable_oneStepShellDirichletGradL2 M n h p Q hh uD huD)



theorem exists_measurable_oneStepShellDirichlet_cellB (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (p : Vec d) (m : ℤ) (hh : 0 < h),
        ∃ (uD : _root_.SubdiffusiveProcess.Model.PotentialSample d → H10Function
              (openCubeSet (originCube d m)))
          (V : ∀ _omega, CubeVectorW1pFunction
              (originCube d m) oneStepFourExponent),
          ∃ hV : ∀ omega,
              (V omega).toField = (uD omega).toH1Function.grad,
            (∀ omega,
              CubeDirichletDivergenceProblem (originCube d m) (uD omega)
                (oneStepShellForcingH1 M n h omega p
                  (originCube d m) hh).toField) ∧
            Measurable (fun omega =>
              oneStepCellB (originCube d m)
                (weakHessianOfCubeVectorW1pFour (V omega) (hV omega))) ∧
            ∀ omega,
              eLpNorm (fun x => HilbertMat.ofMat ((V omega).jacobian x)) 4
                  (normalizedCubeMeasure (originCube d m)) ≤
                C * eLpNorm (fun x => HilbertMat.ofMat
                  ((oneStepShellForcingW14 M n h omega p
                    (originCube d m) hh).jacobian x)) 4
                  (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCtop, hCZ⟩ :=
    exists_canonical_oneStepShell_dirichlet_corrector d
  refine ⟨C, hCtop, ?_⟩
  intro M n h p m hh
  choose uD huD V hV hbound using fun omega => hCZ M n h omega p m hh
  refine ⟨uD, V, hV, huD, ?_, hbound⟩
  exact measurable_oneStepShellDirichlet_cellB M n h p
    (originCube d m) hh uD huD
    (fun omega => weakHessianOfCubeVectorW1pFour (V omega) (hV omega))

/-- Neumann specialization of the measurable weak-Hessian carrier. -/
theorem measurable_oneStepShellNeumann_weakHessianL2Carrier
    {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (uN : _root_.SubdiffusiveProcess.Model.PotentialSample d → H1MeanZeroFunction (openCubeSet Q))
    (huN : ∀ omega,
      IsMeanZeroNeumannRhsWeakSolution
        (identityCoeffField d) (openCubeSet Q) (uN omega)
        (fun x => -(oneStepShellForcingH1 M n h omega p Q hh).toField x))
    (H : ∀ omega,
      HasWeakHessianOn (openCubeSet Q) (uN omega).toH1Function) :
    Measurable fun omega => weakHessianL2CarrierOf (H omega) := by
  exact measurable_weakHessianL2Carrier (isOpen_openCubeSet Q)
    (volume_openCubeSet_lt_top Q).ne (fun omega => (uN omega).toH1Function) H
    (measurable_oneStepShellNeumannGradL2 M n h p Q hh uN huN)

/-- Neumann `B_z` measurability. -/
theorem measurable_oneStepShellNeumann_cellB
    {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h)
    (uN : _root_.SubdiffusiveProcess.Model.PotentialSample d → H1MeanZeroFunction (openCubeSet Q))
    (huN : ∀ omega,
      IsMeanZeroNeumannRhsWeakSolution
        (identityCoeffField d) (openCubeSet Q) (uN omega)
        (fun x => -(oneStepShellForcingH1 M n h omega p Q hh).toField x))
    (H : ∀ omega,
      HasWeakHessianOn (openCubeSet Q) (uN omega).toH1Function) :
    Measurable fun omega => oneStepCellB Q (H omega) := by
  exact measurable_oneStepCellB Q (fun omega => (uN omega).toH1Function) H
    (measurable_oneStepShellNeumannGradL2 M n h p Q hh uN huN)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
