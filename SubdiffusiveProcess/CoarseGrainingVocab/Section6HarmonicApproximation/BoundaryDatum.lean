module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryTrace
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationTranslation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FullWspTransport
public import Homogenization.Sobolev.Foundations.HodgeCubeBridge

@[expose] public section

/-!
# The projected boundary Caccioppoli datum

This module restricts the Dirichlet problem to the well-placed cube,
pulls it back to the origin frame, constructs the rough Dirichlet solution with
the transported datum, and proves the localized zero-trace relation for their
difference.

The composition specializes to a scalar GMC coefficient.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ} [NeZero d]

private theorem publicIsForcedEquation_neg_of_divForm
    {Q : TriadicCube d} {a : CoeffFamily d}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (h : IsDivFormWeakSolutionOn
      (fun x => ((a.coeffOn Q).toCoeffField x) 0 0) (openCubeSet Q) u g)
    (hscalar : ∀ x, (a.coeffOn Q).toCoeffField x =
      scalarMatrix (d := d) (((a.coeffOn Q).toCoeffField x) 0 0)) :
    IsForcedEquation Q a u (fun x => -g x) := by
  intro phi
  have hflux : ∀ x,
      matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x) =
        (((a.coeffOn Q).toCoeffField x) 0 0) • u.grad x := by
    intro x
    have ha := congrArg (fun A => matVecMul A (u.grad x)) (hscalar x)
    exact ha.trans (matVecMul_scalarMatrix _ _)
  have hneg : (fun x => vecDot (-g x) (phi.toH1Function.grad x)) =
      fun x => -vecDot (g x) (phi.toH1Function.grad x) := by
    funext x
    exact vecDot_neg_left _ _
  simp only [Ch02.cubeDomain_coe]
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot ((((a.coeffOn Q).toCoeffField x) 0 0) • u.grad x)
          (phi.toH1Function.grad x) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          exact congrArg (fun z => vecDot z (phi.toH1Function.grad x)) (hflux x))
    _ = -∫ x in openCubeSet Q,
        vecDot (g x) (phi.toH1Function.grad x) ∂volume := h phi
    _ = ∫ x in openCubeSet Q,
        vecDot ((fun x => -g x) x) (phi.toH1Function.grad x) ∂volume := by
      rw [hneg, integral_neg]

/-- The local rough solution and its boundary trace, in the well-placed cube's
origin frame.  The public Chapter-3 forcing is the negative of the manuscript
forcing because the two weak formulations use opposite signs. -/
theorem exists_projectedBoundaryDatum
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (m : ℕ) (k : ℤ) (q : Vec d)
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d)
    (hdir : IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
      (originCube d (m : ℤ)) u h g)
    (hg : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) g)
    (hkm : k ≤ (m : ℤ)) :
    let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
    let Q := originCube d k
    let A := aCutoffFamily M L (translatePotentialSample c omega)
    ∃ g0 : Vec d → Vec d,
      ∃ u0 h0 : H1Function (openCubeSet Q),
      ∃ v : DirichletForcedCubeSolution Q A (fun x => -g0 x),
        (∀ x, g0 x = g (x + c)) ∧
        (∀ x, u0.toFun x = u.toFun (x + c)) ∧
        (∀ x, u0.grad x = u.grad (x + c)) ∧
        IsForcedEquation Q A u0 (fun x => -g0 x) ∧
        v.boundaryData = h0 ∧
        (∀ y, h0.toFun y = h.toFun (y + c)) ∧
        (∀ y, h0.grad y = h.grad (y + c)) ∧
        Ch01.LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (openCubeAtScale (q - c) (k - 1))
          (fun y => u0.toFun y - v.toH1.toFun y) := by
  dsimp only
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : TriadicCube d := originCube d k
  let A : CoeffFamily d := aCutoffFamily M L (translatePotentialSample c omega)
  have hP : translateSet c (openCubeSet Q) = translatedCube d k c := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  have hsub : translateSet c (openCubeSet Q) ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    rw [hP]
    simpa [c, cube] using
      (Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hkm)
  have hPopen : IsOpen (translateSet c (openCubeSet Q)) :=
    ((isOpenBoundedConvexDomain_openCubeSet Q).translateSet c).isOpen
  let uP : H1Function (translateSet c (openCubeSet Q)) := u.restrict hPopen hsub
  let hPfun : H1Function (translateSet c (openCubeSet Q)) := h.restrict hPopen hsub
  let u0 : H1Function (openCubeSet Q) := H1Function.untranslate c uP
  let h0 : H1Function (openCubeSet Q) := H1Function.untranslate c hPfun
  let g0 : Vec d → Vec d := fun x => g (x + c)
  have heqP : IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
      (translateSet c (openCubeSet Q)) uP g :=
    isDivFormWeakSolutionOn_restrict
      (isOpenBoundedConvexDomain_openCubeSet (originCube d (m : ℤ))).isOpen
      hPopen hsub hdir.2
  have heq0 : IsDivFormWeakSolutionOn
      (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M L omega (x + c))
      (openCubeSet Q) u0 g0 :=
    isDivFormWeakSolutionOn_untranslate c heqP
  have hcoeff : ∀ x, (A.coeffOn Q).toCoeffField x =
      scalarMatrix (d := d) (((A.coeffOn Q).toCoeffField x) 0 0) := by
    intro x
    simp [A, aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField]
  have hfield : (fun x => ((A.coeffOn Q).toCoeffField x) 0 0) =
      fun x => _root_.SubdiffusiveProcess.Model.aCutoff M L omega (x + c) := by
    funext x
    simp [A, aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      Section6Covariance.aCutoff_translatePotentialSample]
  have heqPublic : IsForcedEquation Q A u0 (fun x => -g0 x) := by
    apply publicIsForcedEquation_neg_of_divForm (a := A) (g := g0)
    · rw [hfield]
      exact heq0
    · exact hcoeff
  have hgP : MemVectorL2 (translateSet c (openCubeSet Q)) g :=
    hg.mono_measure (Measure.restrict_mono_set volume hsub)
  have hg0base : MemVectorL2 (openCubeSet Q) g0 := by
    exact memVectorL2_comp_addRight_of_memVectorL2_translateSet hgP
  have hg0neg : MemVectorL2 (openCubeSet Q) (fun x => -g0 x) := hg0base.neg
  obtain ⟨v, hvdatum, rho, hrho⟩ :=
    exists_dirichletForcedCubeSolution_boundaryData Q A h0 hg0neg
  obtain ⟨wu, huw, _huwgrad⟩ := hdir.1
  have hwu : Ch01.LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (openCubeAtScale (q - c) (k - 1))
      (fun y => wu.toH1Function.toFun (y + c)) := by
    simpa [c] using
      localizedZeroTraceFunctionOn_wellPlacedCube_untranslate q hkm wu
  have hrhoTrace : Ch01.LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (openCubeAtScale (q - c) (k - 1)) rho.toH1Function.toFun :=
    Section6SchauderDatum.localizedZeroTraceFunctionOn_of_memH10 ⟨rho, rfl⟩
  have htrace0 := Homogenization.localizedZeroTraceFunctionOn_sub hwu hrhoTrace
  have htrace : Ch01.LocalizedZeroTraceFunctionOn (openCubeSet Q)
      (openCubeAtScale (q - c) (k - 1))
      (fun y => u0.toFun y - v.toH1.toFun y) := by
    exact Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun y => by
        rw [hrho y]
        change wu.toH1Function.toFun (y + c) -
            (v.toH1.toFun y - h.toFun (y + c)) =
          u.toFun (y + c) - v.toH1.toFun y
        rw [huw (y + c)]
        ring) htrace0
  exact ⟨g0, u0, h0, v, fun _ => rfl, fun _ => rfl, fun _ => rfl, heqPublic,
    hvdatum, fun _ => rfl, fun _ => rfl, htrace⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
