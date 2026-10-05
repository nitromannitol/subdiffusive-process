module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.StepSevenConditional

@[expose] public section

/-!
# Hölder regularity: internal exact-export wrapper

This module records the final existential assembly below the provider surface.
The intermediate Step-6 aggregation hypothesis is consumed earlier, by
`holderRegularityConclusions_of_campanato_excess_and_energy`; it is therefore
absent from this wrapper and cannot become a provider premise.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The exact pathwise-and-tail package immediately below the outer
dimension-only existential in `p.Holder.regularity`. -/
def HolderRegularityInternalPathwiseInput (d : ℕ) (C : ℝ) : Prop :=
  ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
    M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ m : ℕ, ∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
        Measurable X ∧ (∀ omega, 0 < X omega) ∧
        (∀ k : ℕ, 0 < k → M.P.toMeasure {omega | k < X omega} ≤ ENNReal.ofReal
          (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
            (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
        ∀ L : ℕ, m ≤ L → ∀ omega,
          ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
            IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
                (originCube d m) u h g →
            MemHolder (cube d m) (1 / 2) g →
            MemHolder (cube d m) (1 / 2) h.grad →
            HolderRegularityConclusions M C L omega alpha m (X omega) u h g

/-- Exact outer assembly for the Hölder statement.  Once the internal
pathwise package is unconditional, the provider application is mechanical. -/
theorem exists_holderRegularity_of_internalPathwiseInput
    (d : ℕ) (C : ℝ) (hC : 0 < C)
    (hpath : HolderRegularityInternalPathwiseInput d C) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ m : ℕ, ∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
          Measurable X ∧ (∀ omega, 0 < X omega) ∧
          (∀ k : ℕ, 0 < k → M.P.toMeasure {omega | k < X omega} ≤ ENNReal.ofReal
            (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
          ∀ L : ℕ, m ≤ L → ∀ omega,
            ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
              IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
                  (originCube d m) u h g →
              MemHolder (cube d m) (1 / 2) g →
              MemHolder (cube d m) (1 / 2) h.grad →
              HolderRegularityConclusions M C L omega alpha m (X omega) u h g) := by
  exact ⟨C, hC, hpath⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
