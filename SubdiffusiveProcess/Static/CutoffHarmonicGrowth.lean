module

public import SubdiffusiveProcess.Static.HarmonicCellUniformGrowth
public import SubdiffusiveProcess.Static.HarmonicPairNormalization
public import SubdiffusiveProcess.Static.HarmonicTailTransport
public import SubdiffusiveProcess.Static.LocalEstimateClauses
public import SubdiffusiveProcess.Section6.Defs.CoefficientAt
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Vocab.Ahom

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Uniform harmonic cutoff growth in the physical local normalization,
including finite cutoffs above and below the parent scale and the anchored
infinite coefficient. The exponent is fixed before every moment order. -/
theorem exists_uniform_local_harmonic_cutoffs (d : ℕ) (p : ℕ)
    (c : Fin p → Vec d) (s0 s1 : Fin p → ℝ)
    (hs : ∀ i, 0 < s0 i ∧ s0 i < s1 i) :
    ∀ q : ℝ, 1 ≤ q →
      ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
          ∃ C : ℝ, 0 < C ∧
            ∀ (L : WithTop ℕ) (m : ℕ) (z : Vec d),
              ∃ K : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d → ℝ, Measurable K ∧
                (∀ ω, 1 ≤ K ω) ∧
                (∫⁻ ω, ENNReal.ofReal (K ω ^ q)
                  ∂(_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure) ≤
                  ENNReal.ofReal C ∧
                ∀ᵐ ω ∂(_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measurableSet_anchoredC11GoodSet d)
                    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.measure_anchoredC11GoodSet_eq_one M)).toMeasure,
                  let j : ℕ := match L with
                    | ⊤ => m
                    | (n : ℕ) => min m n
                  let cz : ℝ := coefficientAt M L ω z /
                    _root_.SubdiffusiveProcess.Model.aCutoff M j ω.1 z
                  let b : Vec d → ℝ := fun x => cz⁻¹ * coefficientAt M L ω (z + (3 : ℝ) ^ m • x)
                  localHarmonicCutoffEstimates (fun x => (ahom M j)⁻¹ * b x)
                    c s0 s1 (K ω) 5 := by
  intro q hq
  have hprefix := exists_uniform_local_harmonic_prefix_of_cell_growth d p c s0 s1 hs
    (exists_uniform_cutoffHarmonicCell_growth d) (2 * q) (by linarith)
  exact localHarmonicCutoffSupplier_of_prefix d p c s0 s1 hs q hq hprefix

end SubdiffusiveProcess.Static
