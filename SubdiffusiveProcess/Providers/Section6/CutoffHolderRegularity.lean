import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.CutoffHolderPackageAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.CutoffHolderExcessDecayInput
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.ThresholdedPackageAssembly
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.HarmonicPassages
import SubdiffusiveProcess.Providers.Section6.ExcessDecayGoodScales

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable


theorem SubdiffusiveProcess.Providers.Section6.cutoff_holder_regularity
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      (M.delta ≤ C⁻¹ →
      ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
        ∀ L m : ℕ,
          (∃ X : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable X ∧ (∀ ω, 0 < X ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ ω, ∀ (u h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω) (originCube d m) u h g →
              MemHolder (cube d m) (1 / 2) g →
              MemHolder (cube d m) (1 / 2) h.grad →
              HolderRegularityConclusions M C L ω alpha m (X ω) u h g) ∧
          -- AMBIGUITY (H7): “may take equal” at source lines 9126--9129 is
          -- rendered by existence of one witness compatible with the
          -- uncutoff conclusion, not by an identity forced on every witness.
          (m ≤ L → ∃ Xuncut : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDirichletSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J ω) (originCube d m) u h g →
                MemHolder (cube d m) (1 / 2) g →
                MemHolder (cube d m) (1 / 2) h.grad →
                HolderRegularityConclusions M C J ω alpha m (Xuncut ω) u h g) ∧
          ∀ y : Vec d,
            (∃ Xy : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
              Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDirichletSolutionOn
                    (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
                      (translatePotentialSample y ω))
                    (originCube d m) u h g →
                MemHolder (cube d m) (1 / 2) g →
                MemHolder (cube d m) (1 / 2) h.grad →
                HolderRegularityConclusions M C L (translatePotentialSample y ω) alpha m
                  (Xy ω) u h g) ∧
            (m ≤ L → ∃ XuncutY : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℕ,
              Measurable XuncutY ∧ (∀ ω, 0 < XuncutY ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < XuncutY ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u h : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDirichletSolutionOn
                      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M J
                        (translatePotentialSample y ω))
                      (originCube d m) u h g →
                  MemHolder (cube d m) (1 / 2) g →
                  MemHolder (cube d m) (1 / 2) h.grad →
                  HolderRegularityConclusions M C J (translatePotentialSample y ω) alpha m
                    (XuncutY ω) u h g))

:= by
  let hHarmonic := SubdiffusiveProcess.Providers.Section6.harmonicApproximationInput_all d
  by_cases hd : d = 0
  · subst d
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.cutoffHolderRegularityInput_zero
  · letI : NeZero d := ⟨hd⟩
    obtain ⟨C, hC, hpath, huniform⟩ :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.exists_boundaryCutoffInputs
        d
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderLift.boundaryHolderExcessDecayInput_of_harmonicInput
          d hHarmonic)
        hHarmonic
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.boundaryCutoffHarmonicApproximationInputV6 d)
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.boundaryCutoffHolderExcessDecayInputV4 d)
    exact
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.exists_cutoffHolderRegularity_of_boundaryInputs
        d C hC hpath huniform
