module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderL2Datum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderEnergy

@[expose] public section

/-!
# The almost-sure solvability clause of the whole-space resolvent estimates

Combining

* the almost-sure uniqueness of the finite-cutoff whole-space carrier
  (`ae_forall_finiteCutoffWholeSpaceSolution_unique`, from the almost-sure
  subquadratic growth of `aCutoff`),
* the pathwise compact-data carrier with its two sharp bounds
  (`exists_finiteCutoffWholeSpaceSolution_of_compactSupport_with_energy`), and
* the `L²`-datum extension (`exists_wholeSpaceSolution_of_memLp`),

gives the solvability-and-uniqueness half of the almost-sure clause of
the whole-space resolvent estimates: almost surely, *every* `L²` datum has a
whole-space divergence-resolvent solution, unique up to null sets, with the
sharp `L²` contraction and the sharp coefficient-weighted energy bound.

No support restriction on the datum is needed; the block's
`Function.support f ⊆ Metric.ball x0 R` is a strictly stronger hypothesis.

## References

* `s.fixed.coefficient` and `mfd:sec-speed`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open _root_.SubdiffusiveProcess.Model
open _root_.SubdiffusiveProcess.Section8
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported

noncomputable section

variable {d : ℕ}

/-- **The almost-sure solvability and uniqueness clause.**

Almost surely, for every square-integrable datum there is a whole-space
divergence-resolvent solution for the finite cutoff coefficient, it is a.e.
equal to every other such solution, and it satisfies both sharp bounds.

Source: `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem ae_forall_exists_finiteCutoffWholeSpaceSolution [NeZero d]
    (M : GMCModel d) (L : ℕ) {t : ℝ} (ht : 0 < t) (x0 : Vec d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ f : Vec d → ℝ, MemLp f 2 volume →
      ∃ u : WholeSpaceDivergenceResolventSolution (aCutoff M L omega) t f,
        (∀ v : WholeSpaceDivergenceResolventSolution
            (aCutoff M L omega) t f,
          u.toFun =ᵐ[volume] v.toFun ∧ u.grad =ᵐ[volume] v.grad) ∧
        (∫ x, u.toFun x ^ 2 ∂volume ≤ ∫ x, f x ^ 2 ∂volume) ∧
        (∫ x, aCutoff M L omega x * vecNormSq (u.grad x) ∂volume ≤
          2⁻¹ * t⁻¹ * ∫ x, f x ^ 2 ∂volume) := by
  refine (ae_forall_finiteCutoffWholeSpaceSolution_unique M L ht x0).mono ?_
  intro omega huniq f hf
  obtain ⟨u, hL2, hEn⟩ :=
    exists_wholeSpaceSolution_of_memLp (continuous_aCutoff M L omega)
      (aCutoff_pos M L omega) ht
      (fun g ↦ exists_finiteCutoffWholeSpaceSolution_of_compactSupport_with_energy
        M L omega ht g)
      huniq hf
  exact ⟨u, fun v ↦ huniq f hf u v, hL2, hEn⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
