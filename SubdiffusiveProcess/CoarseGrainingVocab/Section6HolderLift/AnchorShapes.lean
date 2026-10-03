module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Support

@[expose] public section

/-!
# Exact proposition shapes for the Section 6 Holder lift

The two definitions in this file reproduce the bodies of the draft frozen
Holder anchors.  Keeping the shapes in the vocabulary layer allows the support
proof to be tested without importing either draft theorem file.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The exact conclusion type of `p.Holder.regularity`. -/
def HolderRegularityInput (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
    (M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ m : ℕ, ∃ X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
        Measurable X ∧ (∀ omega, 0 < X omega) ∧
        (∀ k : ℕ, 0 < k → M.P.toMeasure {omega | k < X omega} ≤ ENNReal.ofReal
          (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
            (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
        ∀ L : ℕ, m ≤ L → ∀ omega,
          ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
            IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (originCube d m) u h g →
            MemHolder (cube d m) (1 / 2) g →
            MemHolder (cube d m) (1 / 2) h.grad →
            HolderRegularityConclusions M C L omega alpha m (X omega) u h g)

/-- The exact conclusion type of `p.cutoff.Holder.regularity`. -/
def CutoffHolderRegularityInput (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
    (M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ L m : ℕ,
        (∃ X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
          Measurable X ∧ (∀ omega, 0 < X omega) ∧
          (∀ k : ℕ, 0 < k → M.P.toMeasure {omega | k < X omega} ≤ ENNReal.ofReal
            (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
          ∀ omega, ∀ (u h : H1Function (openCubeSet (originCube d m)))
              (g : Vec d → Vec d),
            IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (originCube d m) u h g →
            MemHolder (cube d m) (1 / 2) g →
            MemHolder (cube d m) (1 / 2) h.grad →
            HolderRegularityConclusions M C L omega alpha m (X omega) u h g) ∧
        (m ≤ L → ∃ Xuncut : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
          Measurable Xuncut ∧ (∀ omega, 0 < Xuncut omega) ∧
          (∀ k : ℕ, 0 < k → M.P.toMeasure {omega | k < Xuncut omega} ≤
            ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
          ∀ J : ℕ, m ≤ J → ∀ omega,
            ∀ (u h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J omega)
                  (originCube d m) u h g →
              MemHolder (cube d m) (1 / 2) g →
              MemHolder (cube d m) (1 / 2) h.grad →
              HolderRegularityConclusions M C J omega alpha m (Xuncut omega) u h g) ∧
        ∀ y : Vec d,
          (∃ Xy : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable Xy ∧ (∀ omega, 0 < Xy omega) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {omega | k < Xy omega} ≤
              ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ omega, ∀ (u h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDirichletSolutionOn
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
                    (translatePotentialSample y omega))
                  (originCube d m) u h g →
              MemHolder (cube d m) (1 / 2) g →
              MemHolder (cube d m) (1 / 2) h.grad →
              HolderRegularityConclusions M C L (translatePotentialSample y omega)
                alpha m (Xy omega) u h g) ∧
          (m ≤ L → ∃ XuncutY : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable XuncutY ∧ (∀ omega, 0 < XuncutY omega) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {omega | k < XuncutY omega} ≤
              ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ omega,
              ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDirichletSolutionOn
                    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J
                      (translatePotentialSample y omega))
                    (originCube d m) u h g →
                MemHolder (cube d m) (1 / 2) g →
                MemHolder (cube d m) (1 / 2) h.grad →
                HolderRegularityConclusions M C J (translatePotentialSample y omega)
                  alpha m (XuncutY omega) u h g))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift
