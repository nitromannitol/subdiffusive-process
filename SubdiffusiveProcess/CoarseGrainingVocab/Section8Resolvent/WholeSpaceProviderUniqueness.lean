import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.SubquadraticGrowth




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.Frozen.Section8
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}



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
