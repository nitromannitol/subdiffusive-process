module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryRegularity

@[expose] public section

/-!
# The direct projected boundary datum

The adaptive boundary estimate only needs a localized zero-trace comparison
field; it does not require the auxiliary rough Dirichlet solution used by the
older one-cube Caccioppoli API.  We therefore retain the translated physical
datum itself.  This avoids introducing a boundary mean defect in the final
finite-cover summation.

 this is the direct-datum branch of
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryDatumTransport.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Recenter the physical solution and physical boundary datum, preserving
the forced equation, inhomogeneous fractional memberships, and the localized
zero-trace relation of their difference. -/
theorem exists_projectedBoundaryDirectDatum
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (m : ℕ) (k : ℤ) (q : Vec d) (sOrder : FractionalOrder)
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d)
    (hdir : IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
      (originCube d (m : ℤ)) u h g)
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g)
    (hh : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) sOrder FiniteLpExponent.two h.grad)
    (hkm : k ≤ (m : ℤ)) :
    let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
    let Q := originCube d k
    let A := aCutoffFamily M L (translatePotentialSample c omega)
    ∃ g0 : Vec d → Vec d,
      ∃ u0 h0 : H1Function (openCubeSet Q),
        (∀ x, g0 x = g (x + c)) ∧
        (∀ x, u0.toFun x = u.toFun (x + c)) ∧
        Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
          FiniteLpExponent.two (fun x ↦ g (x + c)) ∧
        (∀ x, u0.grad x = u.grad (x + c)) ∧
        IsForcedEquation Q A u0 (fun x ↦ -g0 x) ∧
        (∀ x, h0.toFun x = h.toFun (x + c)) ∧
        (∀ x, h0.grad x = h.grad (x + c)) ∧
        Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder
          FiniteLpExponent.two (fun x ↦ h.grad (x + c)) ∧
        ForceBesovRegularity Q sOrder.1 (fun x ↦ -g0 x) ∧
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (openCubeAtScale (q - c) (k - 1))
          (fun y ↦ u0.toFun y - h0.toFun y) := by
  dsimp only
  obtain ⟨g0, u0, h0, v, hg0, hu0, hgLocal, hu0grad, heq, _hv,
      hh0, hh0grad, hhLocal, _htrace, hgReg, _hhReg⟩ :=
    exists_projectedBoundaryDatum_regular M L omega m k q sOrder u h g
      hdir hg hh hkm
  obtain ⟨rho, hrho, _hrhoGrad⟩ := hdir.1
  let c := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  have hrhoLocal := localizedZeroTraceFunctionOn_wellPlacedCube_untranslate
    q hkm rho
  have htrace : LocalizedZeroTraceFunctionOn
      (openCubeSet (originCube d k)) (openCubeAtScale (q - c) (k - 1))
      (fun y ↦ u0.toFun y - h0.toFun y) :=
    Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
      (fun y ↦ by
        rw [hu0 y, hh0 y, hrho (y + c)]
        ring) hrhoLocal
  exact ⟨g0, u0, h0, hg0, hu0, hgLocal, hu0grad, heq, hh0, hh0grad,
    hhLocal, hgReg, htrace⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
