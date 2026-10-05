module

public import SubdiffusiveProcess.Providers.Section6.CutoffHolderRegularityInterior
public import SubdiffusiveProcess.Section6.Defs.InteriorHolderRegularityConclusions

@[expose] public section

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

theorem SubdiffusiveProcess.Section6.cutoff_holder_regularity_interior
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ L m : ℕ,
          (∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
                  (cube d m) u g →
              MemHolder (cube d m) (1 / 2) g →
              InteriorHolderRegularityConclusions M C L ω alpha m (X ω) u g) ∧
          (m ≤ L → ∃ Xuncut : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C J ω alpha m (Xuncut ω) u g) ∧
          ∀ y : Vec d,
            (∃ Xy : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDivFormWeakSolutionOn
                    (_root_.SubdiffusiveProcess.Model.aCutoff M L
                      (translatePotentialSample y ω))
                    (cube d m) u g →
                MemHolder (cube d m) (1 / 2) g →
                InteriorHolderRegularityConclusions M C L (translatePotentialSample y ω)
                  alpha m (Xy ω) u g) ∧
            (m ≤ L → ∃ XuncutY : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable XuncutY ∧ (∀ ω, 0 < XuncutY ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < XuncutY ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDivFormWeakSolutionOn
                      (_root_.SubdiffusiveProcess.Model.aCutoff M J
                        (translatePotentialSample y ω))
                      (cube d m) u g →
                  MemHolder (cube d m) (1 / 2) g →
                  InteriorHolderRegularityConclusions M C J (translatePotentialSample y ω)
                    alpha m (XuncutY ω) u g))
:= SubdiffusiveProcess.Providers.Section6.cutoff_holder_regularity_interior d
