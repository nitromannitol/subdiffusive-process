module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.ConclusionAssembly

@[expose] public section

/-!
# Interior Hölder regularity: the outer four-conjunct assembly

The boundary anchor  packages the
pathwise conclusion four times: at the fixed cutoff `L`, uniformly over all
cutoffs `J ≥ m`, and both of those again at every translate
`translatePotentialSample y ω`.  This module reduces all four to the two
sample-space packages that the interior ladder actually produces,

* `BoundaryCutoffPathwiseInput` — one stopping scale per `(L, m)`;
* `BoundaryCutoffUniformInput` — one stopping scale per `m`, valid for every
  cutoff `J ≥ m` (the common-scale interpretation).

The two translate conjuncts are *free*: the sample translation is a measurable
automorphism preserving the layer law
(`Section6Covariance.measure_preimage_translatePotentialSample`), so composing a
witness with it transports the stopping scale, its positivity and its Γ₁ tail
unchanged.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The pathwise-and-tail package at one fixed cutoff `L`. -/
def BoundaryCutoffPathwiseInput (d : ℕ) (C : ℝ) : Prop :=
  ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
    M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ L m : ℕ,
        ∃ X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
          Measurable X ∧ (∀ ω, 0 < X ω) ∧
          (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
            (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
          ∀ ω, ∀ (u h : H1Function (openCubeSet (originCube d m)))
              (g : Vec d → Vec d),
            IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
                (originCube d m) u h g →
            MemHolder (cube d m) (1 / 2) g →
            MemHolder (cube d m) (1 / 2) h.grad →
            HolderRegularityConclusions M C L ω alpha m (X ω) u h g

/-- The cutoff-uniform pathwise-and-tail package: one stopping scale serving
every cutoff `J ≥ m` at once. -/
def BoundaryCutoffUniformInput (d : ℕ) (C : ℝ) : Prop :=
  ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
    M.delta ≤ C⁻¹ →
    ∀ alpha ∈ Set.Icc (1 / 2 : ℝ)
        (1 - C * M.delta * |Real.log M.delta| ^ (1 / 2 : ℝ)),
      ∀ m : ℕ,
        ∃ Xuncut : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
          Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
          (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
            (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
          ∀ J : ℕ, m ≤ J → ∀ ω,
            ∀ (u h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
                  (originCube d m) u h g →
              MemHolder (cube d m) (1 / 2) g →
            MemHolder (cube d m) (1 / 2) h.grad →
              HolderRegularityConclusions M C J ω alpha m (Xuncut ω) u h g

/-- Composition with a sample translation preserves measurability, positivity
and the Γ₁ tail of a stopping scale. -/
theorem translate_stoppingScale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (C alpha : ℝ)
    (X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ) (y : Vec d)
    (hmeas : Measurable X) (hpos : ∀ ω, 0 < X ω)
    (htail : ∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < X ω} ≤ ENNReal.ofReal
      (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
        (C * M.delta ^ 2 * |Real.log M.delta|)))) :
    Measurable (fun ω ↦ X (translatePotentialSample y ω)) ∧
      (∀ ω, 0 < X (translatePotentialSample y ω)) ∧
      ∀ k : ℕ, 0 < k →
        M.P.toMeasure {ω | k < X (translatePotentialSample y ω)} ≤
          ENNReal.ofReal
            (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
              (C * M.delta ^ 2 * |Real.log M.delta|))) := by
  refine ⟨hmeas.comp (Section6Covariance.measurable_translatePotentialSample y),
    fun ω ↦ hpos _, fun k hk ↦ ?_⟩
  have hset : {ω | k < X (translatePotentialSample y ω)} =
      translatePotentialSample y ⁻¹' {ω | k < X ω} := rfl
  rw [hset, Section6Covariance.measure_preimage_translatePotentialSample M y]
  exact htail k hk

/-- **Outer assembly.**  The two sample-space packages produce the exact
boundary statement, translates and all. -/
theorem exists_cutoffHolderRegularity_of_boundaryInputs
    (d : ℕ) (C : ℝ) (hC : 0 < C)
    (hpath : BoundaryCutoffPathwiseInput d C)
    (huniform : BoundaryCutoffUniformInput d C) :
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
            ∀ ω, ∀ (u h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d),
              IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω)
                  (originCube d m) u h g →
              MemHolder (cube d m) (1 / 2) g →
            MemHolder (cube d m) (1 / 2) h.grad →
              HolderRegularityConclusions M C L ω alpha m (X ω) u h g) ∧
          (m ≤ L → ∃ Xuncut : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
            Measurable Xuncut ∧ (∀ ω, 0 < Xuncut ω) ∧
            (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xuncut ω} ≤ ENNReal.ofReal
              (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ J : ℕ, m ≤ J → ∀ ω,
              ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M J ω)
                    (originCube d m) u h g →
                MemHolder (cube d m) (1 / 2) g →
            MemHolder (cube d m) (1 / 2) h.grad →
                HolderRegularityConclusions M C J ω alpha m (Xuncut ω) u h g) ∧
          ∀ y : Vec d,
            (∃ Xy : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable Xy ∧ (∀ ω, 0 < Xy ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < Xy ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω, ∀ (u h : H1Function (openCubeSet (originCube d m)))
                  (g : Vec d → Vec d),
                IsDirichletSolutionOn
                    (_root_.SubdiffusiveProcess.Model.aCutoff M L
                      (translatePotentialSample y ω))
                    (originCube d m) u h g →
                MemHolder (cube d m) (1 / 2) g →
            MemHolder (cube d m) (1 / 2) h.grad →
                HolderRegularityConclusions M C L (translatePotentialSample y ω)
                  alpha m (Xy ω) u h g) ∧
            (m ≤ L → ∃ XuncutY : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℕ,
              Measurable XuncutY ∧ (∀ ω, 0 < XuncutY ω) ∧
              (∀ k : ℕ, 0 < k → M.P.toMeasure {ω | k < XuncutY ω} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - alpha) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ J : ℕ, m ≤ J → ∀ ω,
                ∀ (u h : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d),
                  IsDirichletSolutionOn
                      (_root_.SubdiffusiveProcess.Model.aCutoff M J
                        (translatePotentialSample y ω))
                      (originCube d m) u h g →
                  MemHolder (cube d m) (1 / 2) g →
            MemHolder (cube d m) (1 / 2) h.grad →
                  HolderRegularityConclusions M C J (translatePotentialSample y ω)
                    alpha m (XuncutY ω) u h g)) := by
  refine ⟨C, hC, ?_⟩
  intro M hdelta alpha halpha L m
  obtain ⟨X, hXmeas, hXpos, hXtail, hXpath⟩ := hpath M hdelta alpha halpha L m
  obtain ⟨Xu, hXumeas, hXupos, hXutail, hXupath⟩ := huniform M hdelta alpha halpha m
  refine ⟨⟨X, hXmeas, hXpos, hXtail, hXpath⟩,
    fun _ ↦ ⟨Xu, hXumeas, hXupos, hXutail, hXupath⟩, fun y ↦ ⟨?_, fun _ ↦ ?_⟩⟩
  · obtain ⟨hmeas, hpos, htail⟩ :=
      translate_stoppingScale M C alpha X y hXmeas hXpos hXtail
    exact ⟨fun ω ↦ X (translatePotentialSample y ω), hmeas, hpos, htail,
      fun ω ↦ hXpath (translatePotentialSample y ω)⟩
  · obtain ⟨hmeas, hpos, htail⟩ :=
      translate_stoppingScale M C alpha Xu y hXumeas hXupos hXutail
    exact ⟨fun ω ↦ Xu (translatePotentialSample y ω), hmeas, hpos, htail,
      fun J hJ ω ↦ hXupath J hJ (translatePotentialSample y ω)⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows
