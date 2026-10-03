module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderL2Datum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderEnergy

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.Frozen.Section8
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported

noncomputable section

variable {d : ℕ}



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
