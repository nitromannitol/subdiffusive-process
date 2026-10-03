module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationRestriction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Carrier

@[expose] public section

/-!
# Restriction of the matrix-coefficient equation

The Schauder iteration solves a comparison problem on every inner ball.  This
is the zero-extension transport of the ambient weak equation to those balls;
it is the matrix-valued analogue of the scalar Section 6 restriction lemma.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory
open Homogenization

noncomputable section

variable {d : ℕ}

/-- The matrix divergence-form equation depends only on the selected weak
gradient representative. -/
theorem IsMatrixDivFormWeakSolutionOn.congr_grad {a : CoeffField d}
    {W : Set (Vec d)} {u v : H1Function W} {f : Vec d → Vec d}
    (h : IsMatrixDivFormWeakSolutionOn a W u f)
    (huv : ∀ x, v.grad x = u.grad x) :
    IsMatrixDivFormWeakSolutionOn a W v f := by
  intro phi
  simpa only [huv] using h phi

/-- A matrix divergence-form weak equation restricts from an open set to an
open subset. -/
theorem isMatrixDivFormWeakSolutionOn_restrict {a : CoeffField d}
    {W V : Set (Vec d)} (hW : IsOpen W) (hV : IsOpen V) (hVW : V ⊆ W)
    {u : H1Function W} {f : Vec d → Vec d}
    (h : IsMatrixDivFormWeakSolutionOn a W u f) :
    IsMatrixDivFormWeakSolutionOn a V (u.restrict hV hVW) f := by
  intro phi
  have hflux :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.setIntegral_vecDot_extendByZero
      hW hV hVW (fun p => matVecMul (a p) (u.grad p)) phi
  have hforce :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.setIntegral_vecDot_extendByZero
      hW hV hVW f phi
  calc
    ∫ p in V, vecDot (matVecMul (a p) ((u.restrict hV hVW).grad p))
          (phi.toH1Function.grad p) ∂volume =
        ∫ p in W, vecDot (matVecMul (a p) (u.grad p))
          (((phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function).grad p)
          ∂volume := by
            change (∫ p in V, vecDot (matVecMul (a p) (u.grad p))
              (phi.toH1Function.grad p) ∂volume) = _
            exact hflux.symm
    _ = -∫ p in W, vecDot (f p)
          (((phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function).grad p)
          ∂volume :=
      h (phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW)
    _ = -∫ p in V, vecDot (f p) (phi.toH1Function.grad p) ∂volume := by
      rw [hforce]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
