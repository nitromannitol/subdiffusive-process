module

public import SubdiffusiveProcess.Sobolev.FoldDiscounts

@[expose] public section

/-!
# Continuous positive fields as exponential potentials

`SubdiffusiveProcess.triadicDefectSup_fold_discounts` is proved for the coefficients
`expPotentialCoefficient (compactPotentialLp K g)` of a continuous potential `g` on the
closed cube.  Part A applies it to an arbitrary continuous, strictly positive field `a`.
The two classes coincide: `a = exp (log a)` on the cube, with `log ∘ a` continuous there
because `a` never vanishes.  This file carries that representation and the `L^∞`-class
identification it needs.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.EllipticRegularity

variable {d : ℕ}

/-- `log ∘ a` as a continuous map on the closed cube. -/
def logPotentialOnCube (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : SpatialCoordinates d → ℝ) (hcont : Continuous a) (hpos : ∀ x, 0 < a x) :
    C(closedCube z r hr, ℝ) :=
  ⟨fun p => Real.log (a (p : SpatialCoordinates d)),
    (hcont.comp continuous_subtype_val).log fun _p => ne_of_gt (hpos _)⟩

/-- The exponential-potential coefficient of `log ∘ a` is `a` itself, as an `L^∞` class on
the open cube.  This is the representation that lets the fold discount, proved for
exponential potentials, be applied to an arbitrary continuous positive field. -/
theorem expPotentialCoefficient_logPotentialOnCube_coeFn
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : SpatialCoordinates d → ℝ) (hcont : Continuous a) (hpos : ∀ x, 0 < a x) :
    ((expPotentialCoefficient (Ω := centeredCube z r hr)
          (compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr)
            (logPotentialOnCube z hr a hcont hpos))).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] a := by
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (closedCube z r hr : Set (SpatialCoordinates d)) :=
    centeredCube_subset_closedCube z hr
  filter_upwards [expPotentialCoefficient_coeFn (Ω := centeredCube z r hr)
      (compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr)
        (logPotentialOnCube z hr a hcont hpos)),
    compactPotentialLp_on_domain (Ω := centeredCube z r hr) (closedCube z r hr) hsub
      (logPotentialOnCube z hr a hcont hpos),
    self_mem_ae_restrict (centeredCube z r hr).isOpen.measurableSet] with x h1 h2 hx
  rw [h1, h2 hx]
  exact Real.exp_log (hpos x)

end SubdiffusiveProcess.EllipticRegularity
