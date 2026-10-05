module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.SubquadraticGrowth

@[expose] public section

/-!
# The uniqueness clause of the whole-space resolvent estimates

The frozen anchor for the whole-space resolvent estimates (v3) asserts, for
almost every sample and **every** `L²` datum supported in the source ball,
existence of a whole-space divergence-resolvent solution which is a.e. equal
to every other such solution.

The established almost-sure subquadratic growth of the finite cutoff
(`ae_exists_aCutoff_subquadratic_majorant`) is uniform in the datum: the
majorant sequence `A` is built from the sample alone.  Consequently the
pathwise uniqueness theorem
`finiteCutoffWholeSpaceSolution_ae_eq_of_subquadratic_bound` can be applied
after the datum quantifier, which is exactly the shape required by the frozen
block.

## References

* `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open _root_.SubdiffusiveProcess.Model
open _root_.SubdiffusiveProcess.Section8
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- **The uniqueness clause of the whole-space resolvent estimates.**

Almost surely, the finite-cutoff whole-space divergence-resolvent carrier is
unique *simultaneously for every* `L²` datum: the exceptional sample set does
not depend on the datum.

Source: `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem ae_forall_finiteCutoffWholeSpaceSolution_unique
    (M : GMCModel d) (L : ℕ) {t : ℝ} (ht : 0 < t) (x0 : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ∀ f : Vec d → ℝ, MemLp f 2 volume →
        ∀ u v : WholeSpaceDivergenceResolventSolution
            (aCutoff M L omega) t f,
          u.toFun =ᵐ[volume] v.toFun ∧ u.grad =ᵐ[volume] v.grad := by
  refine (ae_exists_aCutoff_subquadratic_majorant M L x0).mono ?_
  rintro omega ⟨A, hA, hAlim⟩ f hf u v
  exact finiteCutoffWholeSpaceSolution_ae_eq_of_subquadratic_bound
    M L omega ht hf hA hAlim u v

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
