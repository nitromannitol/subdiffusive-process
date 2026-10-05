module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.CutoffHolderScale
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.OuterAssembly

@[expose] public section

/-!
# Pinning the frozen witness `X` to the proved stopping carriers

`OuterAssembly` reduces the whole frozen interior statement to two sample-space
packages, each of which still bundles *probability* (the Γ₁ tail) with
*analysis* (the three pathwise rows).  This module separates them by naming the
witness.

* The fixed-cutoff witness is `Section6Stopping.measurableCutoffHolderStoppingScale`
  at the manuscript's Hölder parameters — the finite-cutoff combined stopping
  depth, measurable hull.
* The cutoff-uniform witness is `Section6Stopping.measurableHolderStoppingScale`,
  which does **not** depend on the cutoff at all; that independence is exactly
  the common-scale interpretation of the source, and is why one
  scale can serve every `J ≥ m`.

Measurability and strict positivity of both carriers are proved, so the split
theorems below consume only the tail estimate and the pathwise rows.  Using the
Γ₁ tail bound, each `…_of_parts` becomes a one-term discharge of the
corresponding `OuterAssembly` input.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable



abbrev holderLambdaAt (C alpha : ℝ) : ℝ :=
  Section6Stopping.holderStoppingLambda C alpha

/-- See `holderLambdaAt`. -/
abbrev holderEpsilonAt (C alpha : ℝ) : ℝ :=
  Section6Stopping.holderStoppingEpsilon C alpha

/-- The Γ₁ tail of the finite-cutoff stopping carrier, in the frozen shape. -/
def CutoffStoppingGammaOneTail (d : ℕ) (C : ℝ) (step : ℕ) : Prop :=
  ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
    M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ L m : ℕ, ∀ k : ℕ, 0 < k →
        M.P.toMeasure {ω | k <
            Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
              (holderLambdaAt C alpha) (holderEpsilonAt C alpha) step m ω} ≤
          ENNReal.ofReal
            (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|)))

/-- The Γ₁ tail of the cutoff-independent stopping carrier. -/
def UncutStoppingGammaOneTail (d : ℕ) (C : ℝ) (step : ℕ) : Prop :=
  ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
    M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ m : ℕ, ∀ k : ℕ, 0 < k →
        M.P.toMeasure {ω | k <
            Section6Stopping.measurableHolderStoppingScale M alpha
              (holderLambdaAt C alpha) (holderEpsilonAt C alpha) step m ω} ≤
          ENNReal.ofReal
            (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|)))

/-- The purely deterministic content of the fixed-cutoff package: the three
frozen interior rows hold beyond the named stopping scale, for every sample. -/
def InteriorCutoffDeterministicRows (d : ℕ) (C : ℝ) (step : ℕ) : Prop :=
  ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
    M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ L m : ℕ, ∀ ω,
        ∀ (u : H1Function (openCubeSet (originCube d m)))
            (g : Vec d → Vec d),
          IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
              (cube d m) u g →
          MemHolder (cube d m) (1 / 2) g →
          InteriorHolderRegularityConclusions M C L ω alpha m
            (Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
              (holderLambdaAt C alpha) (holderEpsilonAt C alpha) step m ω) u g

/-- The deterministic content of the cutoff-uniform package.  The stopping
scale is the cutoff-independent carrier, so a single witness serves every
`J ≥ m`. -/
def InteriorUncutDeterministicRows (d : ℕ) (C : ℝ) (step : ℕ) : Prop :=
  ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
    M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ m : ℕ, ∀ J : ℕ, m ≤ J → ∀ ω,
        ∀ (u : H1Function (openCubeSet (originCube d m)))
            (g : Vec d → Vec d),
          IsDivFormWeakSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
              (cube d m) u g →
          MemHolder (cube d m) (1 / 2) g →
          InteriorHolderRegularityConclusions M C J ω alpha m
            (Section6Stopping.measurableHolderStoppingScale M alpha
              (holderLambdaAt C alpha) (holderEpsilonAt C alpha) step m ω) u g

/-- Probability and analysis recombine into the fixed-cutoff package. -/
theorem interiorCutoffPathwiseInput_of_parts {d : ℕ} {C : ℝ} {step : ℕ}
    (htail : CutoffStoppingGammaOneTail d C step)
    (hrows : InteriorCutoffDeterministicRows d C step) :
    InteriorCutoffPathwiseInput d C := by
  intro M hdelta alpha halpha L m
  refine ⟨Section6Stopping.measurableCutoffHolderStoppingScale M L alpha
      (holderLambdaAt C alpha) (holderEpsilonAt C alpha) step m,
    Section6Stopping.measurable_measurableCutoffHolderStoppingScale M L alpha
      (holderLambdaAt C alpha) (holderEpsilonAt C alpha) step m,
    fun ω => Section6Stopping.measurableCutoffHolderStoppingScale_pos M L alpha
      (holderLambdaAt C alpha) (holderEpsilonAt C alpha) step m ω,
    htail M hdelta alpha halpha L m, ?_⟩
  intro ω u g hsol hg
  exact hrows M hdelta alpha halpha L m ω u g hsol hg

/-- Probability and analysis recombine into the cutoff-uniform package. -/
theorem interiorCutoffUniformInput_of_parts {d : ℕ} {C : ℝ} {step : ℕ}
    (htail : UncutStoppingGammaOneTail d C step)
    (hrows : InteriorUncutDeterministicRows d C step) :
    InteriorCutoffUniformInput d C := by
  intro M hdelta alpha halpha m
  refine ⟨Section6Stopping.measurableHolderStoppingScale M alpha
      (holderLambdaAt C alpha) (holderEpsilonAt C alpha) step m,
    Section6Stopping.measurable_measurableHolderStoppingScale M alpha
      (holderLambdaAt C alpha) (holderEpsilonAt C alpha) step m,
    fun ω => Section6Stopping.measurableHolderStoppingScale_pos M alpha
      (holderLambdaAt C alpha) (holderEpsilonAt C alpha) step m ω,
    htail M hdelta alpha halpha m, ?_⟩
  intro J hJ ω u g hsol hg
  exact hrows M hdelta alpha halpha m J hJ ω u g hsol hg

/-- The whole frozen interior statement from four separated obligations: two
Γ₁ tails and two deterministic row packages. -/
theorem exists_cutoffHolderRegularityInterior_of_tails_and_rows
    (d : ℕ) (C : ℝ) (hC : 0 < C) (step : ℕ)
    (htailCut : CutoffStoppingGammaOneTail d C step)
    (hrowsCut : InteriorCutoffDeterministicRows d C step)
    (htailUncut : UncutStoppingGammaOneTail d C step)
    (hrowsUncut : InteriorUncutDeterministicRows d C step) :
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
                    alpha m (XuncutY ω) u g)) :=
  exists_cutoffHolderRegularityInterior_of_inputs d C hC
    (interiorCutoffPathwiseInput_of_parts htailCut hrowsCut)
    (interiorCutoffUniformInput_of_parts htailUncut hrowsUncut)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
