import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalUniformProvider
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalLinearBudget
import SubdiffusiveProcess.CoarseGrainingVocab.Section9PercolationAlmostSure
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.EventIndependence
import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
set_option autoImplicit false
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal
noncomputable section




namespace SubdiffusiveProcess.Providers.Section9

/-- **The frozen conclusion of `l.weighted.multiscale.percolation` v2, with no
hypothesis beyond the frozen binders.**

The statement is the block of `SubdiffusiveProcess/Frozen/Section9/WeightedMultiscalePercolation.lean`
verbatim.  The proof is P-379's route
`weightedMultiscalePercolation_of_uniformChemicalDistanceBoundBox` applied to the
**proved** chemical-distance bound `uniformChemicalDistanceBoundBox_linear`. -/
theorem weighted_multiscale_percolation (d Cdep : ℕ)
    (Cprob cprob : ℝ) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hd : 2 ≤ d) :
    ∃ q0 L0 Cbox : ℕ, ∃ c C : ℝ,
      0 < c ∧ 0 < C ∧ 1 ≤ L0 ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (crossing z omega : ℝ) - L0)) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          AEFiniteRangePercolationGeometry mu E Cbox
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
            c C q crossing component :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.weightedMultiscalePercolation_of_uniformChemicalDistanceBoundBox
    d Cdep Cprob cprob hd hCprob hcprob
    (SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.uniformChemicalDistanceBoundBox_linear
      d Cdep Cprob cprob hd hCprob hcprob)

end SubdiffusiveProcess.Providers.Section9
