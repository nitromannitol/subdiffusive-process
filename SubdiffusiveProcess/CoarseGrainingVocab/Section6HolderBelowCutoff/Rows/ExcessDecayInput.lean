import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.Geometry
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffExcessDecayInput

/-!
# The interior-branch conditional input for the interior Hölder ladder

The former version-3 boundary carrier transcribed the conclusion of the DRAFT
`l.excess.decay.good.scales.GMC` at D-057.  That shape was unusable on the
interior branch because it was stated for a
*Dirichlet pair* `IsDirichletSolutionOn (aCutoff M L ω) (□_m) u h g` together
with `MemHolder (□_m) (1/2) h.grad`, and the interior anchor
`p.cutoff.Holder.regularity.interior` (D-060/D-061) supplies no datum `h` at all
— that is precisely the point of the re-cut (OPEN-11: no `H^{1/2}` trace
approximation exists in the source).

`InteriorHolderExcessDecayInput_cut` below is the *interior branch* of that same
draft conclusion:

* the Dirichlet hypothesis is weakened to the printed weak-harmonicity
  `IsDivFormWeakSolutionOn (aCutoff M L ω) (cube d m) u g` — the D-060 re-cut;
* the datum hypothesis `MemHolder (□_m) (1/2) h.grad` is deleted;
* the window is required to be interior,
  `¬ BoundaryTouches (truncatedCube d m n x) (cube d m)`, which is what
  `Geometry.not_boundaryTouches_of_interior` supplies from an interior base
  point; and
* the two `BoundaryTouches` legs of the right-hand side are deleted, since the
  interior binder makes both of them literally `0`.

The interior carrier below instead uses the proved version-4 exponents.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows

open SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {L : ℕ}
attribute [local instance] Classical.propDecidable

/-- The interior branch of the DRAFT `l.excess.decay.good.scales.GMC`
conclusion, with the Dirichlet pair replaced by the D-060 weak-harmonicity
hypothesis and both boundary legs deleted. -/
abbrev InteriorHolderExcessDecayInput_cut (d : ℕ) : Prop :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.InteriorCutoffHolderExcessDecayInput
    d (-2 : ℝ) (-8 : ℝ)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.Rows
