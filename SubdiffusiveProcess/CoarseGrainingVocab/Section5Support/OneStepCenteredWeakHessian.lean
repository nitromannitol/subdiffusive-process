import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannRecenteringComposition
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFinalSpecialization

/-!
# Centered restrictions with weak Hessians

The cell oscillation in the one-step proof is the gradient of a restricted
large-cube solution after subtracting its cell-average slope.  This file
packages that operation as an honest `H1Function` and transports the weak
Hessian by adding an affine function whose Hessian is zero.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- An affine Sobolev function carries the zero weak Hessian. -/
noncomputable def weakHessianAffineOnCube {d : ℕ}
    (Q : TriadicCube d) (p : Vec d)
    [IsFiniteMeasure (volumeMeasureOn (openCubeSet Q))] :
    HasWeakHessianOn (openCubeSet Q)
      (H1Function.affineOnIsSobolevRegularDomain
        (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p) where
  hess := fun _ _ _ ↦ 0
  hess_memL2 := fun _ _ ↦ MeasureTheory.MemLp.zero
  weak_second := by
    intro i j
    have hconst : HasWeakPartialDerivOn (openCubeSet Q) j
        (fun _ : Vec d ↦ p i) (fun _ ↦ 0) := by
      simpa using
        (HasWeakPartialDerivOn.of_contDiff
          (U := openCubeSet Q) (i := j) (f := fun _ : Vec d ↦ p i)
          contDiff_const)
    simpa only [H1Function.affineOnIsSobolevRegularDomain_grad] using hconst

/-- Restrict to a descendant and subtract the cell-average slope by adding
the affine function with the opposite gradient. -/
noncomputable def oneStepCenteredRestriction {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (u : H1Function (openCubeSet Q))
    (hR : R ∈ descendantsAtDepth Q j) : H1Function (openCubeSet R) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  exact u.restrictToOpenSubcube hR +
    H1Function.affineOnIsSobolevRegularDomain
      (isOpenBoundedConvexDomain_openCubeSet R).isSobolevRegularDomain
      (-cubeAverageVec R u.grad)

@[simp] theorem oneStepCenteredRestriction_grad {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (u : H1Function (openCubeSet Q))
    (hR : R ∈ descendantsAtDepth Q j) (x : Vec d) :
    (oneStepCenteredRestriction u hR).grad x =
      u.grad x - cubeAverageVec R u.grad := by
  simp only [oneStepCenteredRestriction, H1Function.add_grad,
    H1Function.restrictToOpenSubcube_grad,
    H1Function.affineOnIsSobolevRegularDomain_grad]
  abel

/-- The centered restriction has zero average gradient. -/
theorem cubeAverageVec_oneStepCenteredRestriction_grad_eq_zero {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (u : H1Function (openCubeSet Q))
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeAverageVec R (oneStepCenteredRestriction u hR).grad = 0 := by
  have h := cubeAverageVec_oneStepCellFluctuationField_eq_zero hR u
  simpa only [oneStepCellFluctuationField,
    oneStepCenteredRestriction_grad] using h

/-- The restricted weak Hessian, plus the zero affine Hessian, is a weak
Hessian for the centered restriction. -/
noncomputable def HasWeakHessianOn.centeredRestriction {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (hR : R ∈ descendantsAtDepth Q j) :
    HasWeakHessianOn (openCubeSet R) (oneStepCenteredRestriction u hR) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  exact weakHessianAdd
    (H.restrict (isOpen_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR))
    (weakHessianAffineOnCube R (-cubeAverageVec R u.grad))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
