import SubdiffusiveProcess.CoarseGrainingVocab.Section9PercolationAlmostSure
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.EventIndependence
import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import SubdiffusiveProcess.Providers.Section9.WeightedMultiscalePercolation
set_option autoImplicit false
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal
noncomputable section


theorem SubdiffusiveProcess.Frozen.Section9.weighted_multiscale_percolation (d Cdep : ℕ)
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
            c C q crossing component

:= SubdiffusiveProcess.Providers.Section9.weighted_multiscale_percolation d Cdep Cprob cprob hCprob hcprob hd
