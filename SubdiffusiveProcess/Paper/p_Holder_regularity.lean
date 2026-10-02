import SubdiffusiveProcess.Frozen.Section6.HolderRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Paper



theorem p_Holder_regularity
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ m : ℕ, ∃ X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
          Measurable X ∧ (∀ ω, 0 < X ω) ∧
          (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
            (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
          ∀ L : ℕ, m ≤ L → ∀ ω,
            ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
              IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
              MemHolder (cube d m) (1 / 2) g →
              MemHolder (cube d m) (1 / 2) h.grad →
              HolderRegularityConclusions M C L ω alpha m (X ω) u h g) :=
  SubdiffusiveProcess.Frozen.Section6.holder_regularity d

end Paper
