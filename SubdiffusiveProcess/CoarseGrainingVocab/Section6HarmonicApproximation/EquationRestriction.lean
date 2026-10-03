module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.Restriction

@[expose] public section

/-!
# Restricting the section 6 divergence-form equation

The harmonic-approximation argument uses the equation first on the ambient
cube and then on an arbitrarily translated inner cube.  This is the public
zero-extension argument behind that restriction.

PROVENANCE: this is the scalar GMC specialization of
`Algsuperdiff/Section4/Provider/ExcessDecay/EquationRestriction.lean`; unlike
the older analogue it uses CoarseGraining's now-public
`H10Function.extendByZeroToOpenSuperset` through
`Section6BoundaryL2.setIntegral_vecDot_extendByZero`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open MeasureTheory
open Homogenization (Vec H1Function H10Function vecDot)
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- The weak divergence-form equation depends only on the chosen gradient
representative of its `H¹` solution. -/
theorem IsDivFormWeakSolutionOn.congr_grad {a : Vec d → ℝ} {W : Set (Vec d)}
    {u v : H1Function W} {g : Vec d → Vec d}
    (h : IsDivFormWeakSolutionOn a W u g) (huv : ∀ x, v.grad x = u.grad x) :
    IsDivFormWeakSolutionOn a W v g := by
  intro φ
  simpa only [huv] using h φ

/-- A divergence-form weak equation restricts from an open set to any open
subset. -/
theorem isDivFormWeakSolutionOn_restrict {a : Vec d → ℝ} {W V : Set (Vec d)}
    (hW : IsOpen W) (hV : IsOpen V) (hVW : V ⊆ W) {u : H1Function W}
    {g : Vec d → Vec d} (h : IsDivFormWeakSolutionOn a W u g) :
    IsDivFormWeakSolutionOn a V (u.restrict hV hVW) g := by
  intro φ
  have hflux :=
    Section6BoundaryL2.setIntegral_vecDot_extendByZero hW hV hVW
      (fun p => a p • u.grad p) φ
  have hforce :=
    Section6BoundaryL2.setIntegral_vecDot_extendByZero hW hV hVW g φ
  calc
    ∫ p in V, vecDot (a p • (u.restrict hV hVW).grad p)
          (φ.toH1Function.grad p) ∂volume =
        ∫ p in W, vecDot (a p • u.grad p)
          (((φ.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function).grad p)
          ∂volume := by
            change (∫ p in V, vecDot (a p • u.grad p) (φ.toH1Function.grad p) ∂volume) = _
            exact hflux.symm
    _ = -∫ p in W, vecDot (g p)
          (((φ.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function).grad p)
          ∂volume :=
      h (φ.extendByZeroToOpenSuperset hV.measurableSet hW hVW)
    _ = -∫ p in V, vecDot (g p) (φ.toH1Function.grad p) ∂volume := by
      rw [hforce]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
