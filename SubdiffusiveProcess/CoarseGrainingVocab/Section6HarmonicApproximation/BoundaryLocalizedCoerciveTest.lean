import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveTest
import Homogenization.Sobolev.H1.LocalizedZeroTrace

/-!
# Localized nonzero-datum boundary test

The manuscript applies its boundary Caccioppoli argument on a projected cube
whose artificial faces do not carry the original Dirichlet datum.  The right
carrier is therefore `LocalizedZeroTraceFunctionOn`, not a full-domain trace
condition.  This module records the exact weak-test identity in that carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The squared-cutoff direct weak identity under a localized boundary trace.
Only the support of the cutoff must lie in the trace window. -/
theorem setIntegral_boundarySqCutoffTestGradient_identity_of_localizedZeroTrace
    {Q : TriadicCube d} {a : Vec d → ℝ}
    {u h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hweak : IsDivFormWeakSolutionOn a (openCubeSet Q) u g)
    {V : Set (Vec d)}
    (hzero : LocalizedZeroTraceFunctionOn (openCubeSet Q) V
      (fun y => u.toFun y - h.toFun y))
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetaCompact : HasCompactSupport eta)
    (hetaSupport : tsupport eta ⊆ V) :
    ∫ x in openCubeSet Q,
        vecDot (a x • u.grad x) (boundarySqCutoffTestGradient eta u h x) ∂volume =
      -∫ x in openCubeSet Q,
        vecDot (g x) (boundarySqCutoffTestGradient eta u h x) ∂volume := by
  let U : Set (Vec d) := openCubeSet Q
  let w : H1Function U := u - h
  let etaSq : Vec d → ℝ := fun x => eta x ^ 2
  have hetaSq : ContDiff ℝ (⊤ : ℕ∞) etaSq := heta.pow 2
  have hetaSqCompact : HasCompactSupport etaSq := by
    dsimp only [etaSq]
    simpa only [pow_two] using hetaCompact.mul_left (f := eta)
  have hetaSqSupport : tsupport etaSq ⊆ V := by
    exact (tsupport_sq_subset eta).trans hetaSupport
  have hmem : MemH10 U (fun x => etaSq x * w.toFun x) := by
    simpa only [U, w, H1Function.sub_toFun] using
      (localizedZeroTraceFunctionOn_memH10_mul hzero hetaSq hetaSqCompact
        hetaSqSupport)
  obtain ⟨phi, hphiVal⟩ := hmem
  let psi : H1Function U := w.mulContDiffHasCompactSupport hetaSq hetaSqCompact
  have hpsiVal : psi.toFun = fun x => etaSq x * w.toFun x := by
    funext x
    simp [psi, H1Function.mulContDiffHasCompactSupport_toFun]
  have hcoordAE : ∀ i : Fin d,
      (fun x => phi.toH1Function.grad x i) =ᵐ[volume.restrict U]
        fun x => psi.grad x i := by
    intro i
    have hphiLoc : LocallyIntegrableOn (fun x => phi.toH1Function.grad x i)
        U volume :=
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((phi.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num))
    have hpsiLoc : LocallyIntegrableOn (fun x => psi.grad x i) U volume :=
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((psi.gradMemL2 i).locallyIntegrable (by norm_num))
    have hphiWeak : HasWeakPartialDerivOn U i
        (fun x => etaSq x * w.toFun x)
        (fun x => phi.toH1Function.grad x i) := by
      simpa only [hphiVal] using phi.toH1Function.hasWeakGradient i
    have hpsiWeak : HasWeakPartialDerivOn U i
        (fun x => etaSq x * w.toFun x) (fun x => psi.grad x i) := by
      simpa only [hpsiVal] using psi.hasWeakGradient i
    exact HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
      hphiLoc hpsiLoc hphiWeak hpsiWeak
  have hgradAE : phi.toH1Function.grad =ᵐ[volume.restrict U] psi.grad := by
    filter_upwards [Filter.eventually_all.2 hcoordAE] with x hx
    funext i
    exact hx i
  have hpsiGrad : psi.grad = boundarySqCutoffTestGradient eta u h := by
    funext x i
    rw [show psi = w.mulContDiffHasCompactSupport hetaSq hetaSqCompact by rfl,
      H1Function.mulContDiffHasCompactSupport_grad]
    change eta x ^ 2 * w.grad x i + w.toFun x *
        (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) = _
    rw [show (fderiv ℝ (fun y => eta y ^ 2) x) (basisVec i) =
        2 * eta x * euclideanGradient eta x i by
      simpa [euclideanCoordDeriv] using euclideanCoordDeriv_sq heta i x]
    simp only [w, H1Function.sub_grad, H1Function.sub_toFun]
    rfl
  have hleft :
      ∫ x in U, vecDot (a x • u.grad x) (psi.grad x) ∂volume =
        ∫ x in U,
          vecDot (a x • u.grad x) (phi.toH1Function.grad x) ∂volume := by
    apply integral_congr_ae
    filter_upwards [hgradAE] with x hx
    rw [hx]
  have hright :
      ∫ x in U, vecDot (g x) (psi.grad x) ∂volume =
        ∫ x in U, vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
    apply integral_congr_ae
    filter_upwards [hgradAE] with x hx
    rw [hx]
  have hphi := hweak phi
  change
    ∫ x in U, vecDot (a x • u.grad x)
        (boundarySqCutoffTestGradient eta u h x) ∂volume =
      -∫ x in U, vecDot (g x)
        (boundarySqCutoffTestGradient eta u h x) ∂volume
  rw [← hpsiGrad, hleft, hright]
  exact hphi

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
