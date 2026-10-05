module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCrossScaleSummation
public import Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingPDE

@[expose] public section

/-!
# Restricting public forced solutions to descendant cells

The finite-cell boundary summation uses the same physical solution on each
triadic descendant.  This module packages the zero-extension argument which
restricts the public Chapter 3 weak equation together with its coefficient
family representative.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem setIntegral_vecDot_extendByZeroToOpenSuperset
    {U V : Set (Vec d)} (hU : MeasurableSet U) (hV : IsOpen V)
    (hUV : U ⊆ V) (F : Vec d → Vec d) (phi : H10Function U) :
    ∫ x in V, vecDot (F x)
        ((phi.extendByZeroToOpenSuperset hU hV hUV).grad x) ∂volume =
      ∫ x in U, vecDot (F x) (phi.grad x) ∂volume := by
  let phiV : H10Function V := phi.extendByZeroToOpenSuperset hU hV hUV
  have hgrad : phiV.grad = phi.zeroExtensionGrad := by
    simpa only [phiV] using!
      H10Function.extendByZeroToOpenSuperset_grad phi hU hV hUV
  have hindicator : (fun x ↦ vecDot (F x) (phiV.grad x)) =
      U.indicator (fun x ↦ vecDot (F x) (phi.grad x)) := by
    funext x
    rw [hgrad]
    by_cases hx : x ∈ U
    · simp only [H10Function.zeroExtensionGrad_apply_of_mem _ hx,
        Set.indicator_of_mem hx]
    · simp only [H10Function.zeroExtensionGrad_apply_of_not_mem _ hx,
        Set.indicator_of_notMem hx, vecDot_zero_right]
  rw [show (phi.extendByZeroToOpenSuperset hU hV hUV).grad = phiV.grad by rfl,
    hindicator, integral_indicator hU, Measure.restrict_restrict hU,
    Set.inter_eq_left.mpr hUV]

/-- A public forced cube solution restricts to every triadic descendant, with
the original coefficient family and forcing. -/
noncomputable def restrictForcedCubeSolutionToDescendant
    {Q R : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    {j : ℕ} (u : ForcedCubeSolution Q a g)
    (hR : R ∈ descendantsAtDepth Q j) : ForcedCubeSolution R a g where
  toH1 := u.toH1.restrictToOpenSubcube hR
  weakSolution := by
    intro phi
    let hRQ : openCubeSet R ⊆ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR
    let phiQ : H10Function (openCubeSet Q) :=
      phi.extendByZeroToOpenSuperset (measurableSet_openCubeSet R)
        (isOpen_openCubeSet Q) hRQ
    let F : Vec d → Vec d := fun x ↦
      matVecMul ((a.coeffOn Q).toCoeffField x) (u.toH1.grad x)
    have hflux := setIntegral_vecDot_extendByZeroToOpenSuperset
      (measurableSet_openCubeSet R) (isOpen_openCubeSet Q) hRQ F phi
    have hforcing := setIntegral_vecDot_extendByZeroToOpenSuperset
      (measurableSet_openCubeSet R) (isOpen_openCubeSet Q) hRQ g phi
    have hcoeff : (a.coeffOn R).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet R)] (a.coeffOn Q).toCoeffField :=
      a.restrictsTo_of_subset hRQ
    have hleft :
        ∫ x in openCubeSet R,
            vecDot (matVecMul ((a.coeffOn R).toCoeffField x)
              ((u.toH1.restrictToOpenSubcube hR).grad x))
              (phi.toH1Function.grad x) ∂volume =
          ∫ x in openCubeSet Q,
            vecDot (F x) (phiQ.toH1Function.grad x) ∂volume := by
      calc
        _ = ∫ x in openCubeSet R,
            vecDot (F x) (phi.toH1Function.grad x) ∂volume := by
              apply integral_congr_ae
              filter_upwards [hcoeff] with x hx
              have hg : (u.toH1.restrictToOpenSubcube hR).grad x = u.toH1.grad x := by
                simpa only using! congrFun
                  (H1Function.restrictToOpenSubcube_grad u.toH1 hR) x
              simp only [F, hx, hg]
        _ = _ := by
          simpa only [phiQ] using! hflux.symm
    have hweak := u.weakSolution phiQ
    calc
      ∫ x in openCubeSet R,
          vecDot (matVecMul ((a.coeffOn R).toCoeffField x)
            ((u.toH1.restrictToOpenSubcube hR).grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (F x) (phiQ.toH1Function.grad x) ∂volume := hleft
      _ = ∫ x in openCubeSet Q,
          vecDot (g x) (phiQ.toH1Function.grad x) ∂volume := by
            simpa only [F, Ch02.cubeDomain_coe] using! hweak
      _ = ∫ x in openCubeSet R,
          vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
            simpa only [phiQ] using! hforcing

@[simp] theorem restrictForcedCubeSolutionToDescendant_toFun
    {Q R : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    {j : ℕ} (u : ForcedCubeSolution Q a g)
    (hR : R ∈ descendantsAtDepth Q j) :
    (restrictForcedCubeSolutionToDescendant u hR).toH1.toFun = u.toH1.toFun :=
  rfl

@[simp] theorem restrictForcedCubeSolutionToDescendant_grad
    {Q R : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    {j : ℕ} (u : ForcedCubeSolution Q a g)
    (hR : R ∈ descendantsAtDepth Q j) :
    (restrictForcedCubeSolutionToDescendant u hR).toH1.grad = u.toH1.grad :=
  rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
