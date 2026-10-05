module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.DimensionZero
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.Conclusions

@[expose] public section

/-!
# The degenerate zero-dimensional interior conclusion

As for the boundary package, the frozen interior three-row conclusion is
automatic on `Vec 0`, so the interior provider may enter the analytic ladder
under `[NeZero d]` without narrowing the frozen dimension binder.

The proof needs no new analysis: the zero-dimensional boundary package holds
for *every* datum, in particular for the degenerate choice `h := u`, and the
interior package is a weakening of it.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section
attribute [local instance] Classical.propDecidable

/-- `InteriorHolderRegularityConclusions` is automatic in dimension zero. -/
theorem interiorHolderRegularityConclusions_dim_zero
    (M : _root_.SubdiffusiveProcess.Model.GMCModel 0) (C : ℝ) (hC : 0 ≤ C)
    (L : ℕ) (ω : _root_.SubdiffusiveProcess.Model.PotentialSample 0) (alpha : ℝ)
    (m X : ℕ) (u : H1Function (openCubeSet (originCube 0 m)))
    (g : Vec 0 → Vec 0) :
    InteriorHolderRegularityConclusions M C L ω alpha m X u g :=
  interiorHolderRegularityConclusions_of_conclusions M C L ω alpha m X u u g
    (Section6Holder.holderRegularityConclusions_dim_zero M C hC L ω alpha m X u u g)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
