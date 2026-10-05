module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Support
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.Localizations

@[expose] public section

/-!
# The direct squared-cutoff boundary test

The manuscript's boundary energy argument tests the divergence-form equation
with `eta^2 (u-h)`.  This module constructs that test from the structural
`H¹₀` witness in `IsDirichletSolutionOn` and records its exact gradient.

 this is the nonzero-datum analogue of the squared-cutoff weak test
used in CoarseGraining's `WeakInteriorDQ/Localizations.lean`.  It is also the
first move of `l.coarse.grained.Caccioppoli.RHS.ASD`; unlike the public
Chapter-3 wrapper, the datum has not been replaced by a zero-boundary lift.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The gradient of the admissible test `eta^2 (u-h)`, written in the physical
solution and datum representatives. -/
def boundarySqCutoffTestGradient
    {Q : TriadicCube d} (eta : Vec d → ℝ)
    (u h : H1Function (openCubeSet Q)) : Vec d → Vec d :=
  fun x i =>
    eta x ^ 2 * (u.grad x i - h.grad x i) +
      (u.toFun x - h.toFun x) * (2 * eta x * euclideanGradient eta x i)

/-- The explicit gradient of the squared-cutoff boundary test belongs to the
ambient vector `L²` space.  This is the measure-theoretic interface needed to
justify both sides of the weak identity without carrying ad hoc
integrability hypotheses through the radius iteration. -/
theorem memVectorL2_boundarySqCutoffTestGradient
    {Q : TriadicCube d} {u h : H1Function (openCubeSet Q)}
    (hdir : HasZeroTraceDifferenceOn (openCubeSet Q) u h)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    MemVectorL2 (openCubeSet Q) (boundarySqCutoffTestGradient eta u h) := by
  obtain ⟨rho, hrhoVal, hrhoGrad⟩ := hdir
  have hetaSq : ContDiff ℝ (⊤ : ℕ∞) (fun x => eta x ^ 2) := heta.pow 2
  have hetaSqCompact : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using! hetaCompact.mul_left (f := eta)
  let phi : H10Function (openCubeSet Q) :=
    rho.mulContDiffHasCompactSupport hetaSq hetaSqCompact
  have hphiGrad : phi.toH1Function.grad = boundarySqCutoffTestGradient eta u h := by
    funext x i
    rw [show phi.toH1Function =
        rho.toH1Function.mulContDiffHasCompactSupport hetaSq hetaSqCompact by rfl,
      H1Function.mulContDiffHasCompactSupport_grad]
    change eta x ^ 2 * rho.toH1Function.grad x i +
        rho.toH1Function.toFun x *
          (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) = _
    rw [show (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) =
        2 * eta x * euclideanGradient eta x i by
      simpa [euclideanCoordDeriv, euclideanGradient] using! euclideanCoordDeriv_sq heta i x]
    have hval : rho.toH1Function.toFun x = u.toFun x - h.toFun x := by
      linarith only [hrhoVal x]
    have hgradVec : rho.toH1Function.grad x = u.grad x - h.grad x := by
      rw [hrhoGrad x]
      abel
    rw [hval, hgradVec]
    rfl
  simpa only [hphiGrad] using phi.toH1Function.grad_memVectorL2

/-- The direct boundary coercive-test identity.  No boundary mean is chosen:
the test depends only on the constant-invariant difference `u-h`. -/
theorem setIntegral_boundarySqCutoffTestGradient_identity
    {Q : TriadicCube d} {a : Vec d → ℝ}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hdir : IsDirichletSolutionOn a Q u h g)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta) :
    ∫ x in openCubeSet Q,
        vecDot (a x • u.grad x) (boundarySqCutoffTestGradient eta u h x) ∂volume =
      -∫ x in openCubeSet Q,
        vecDot (g x) (boundarySqCutoffTestGradient eta u h x) ∂volume := by
  obtain ⟨rho, hrhoVal, hrhoGrad⟩ := hdir.1
  have hetaSq : ContDiff ℝ (⊤ : ℕ∞) (fun x => eta x ^ 2) := heta.pow 2
  have hetaSqCompact : HasCompactSupport (fun x => eta x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using! hetaCompact.mul_left (f := eta)
  let phi : H10Function (openCubeSet Q) :=
    rho.mulContDiffHasCompactSupport hetaSq hetaSqCompact
  have hphiGrad : phi.toH1Function.grad = boundarySqCutoffTestGradient eta u h := by
    funext x i
    rw [show phi.toH1Function =
        rho.toH1Function.mulContDiffHasCompactSupport hetaSq hetaSqCompact by rfl,
      H1Function.mulContDiffHasCompactSupport_grad]
    change eta x ^ 2 * rho.toH1Function.grad x i +
        rho.toH1Function.toFun x *
          (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) = _
    rw [show (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) =
        2 * eta x * euclideanGradient eta x i by
      simpa [euclideanCoordDeriv, euclideanGradient] using! euclideanCoordDeriv_sq heta i x]
    have hval : rho.toH1Function.toFun x = u.toFun x - h.toFun x := by
      linarith only [hrhoVal x]
    have hgradVec : rho.toH1Function.grad x = u.grad x - h.grad x := by
      rw [hrhoGrad x]
      abel
    rw [hval, hgradVec]
    rfl
  have hweak := hdir.2 phi
  rw [hphiGrad] at hweak
  exact hweak

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
