module

public import SubdiffusiveProcess.Frozen.Section6.FiniteCutoffCoefficientConvergence

@[expose] public section

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal Topology
open SubdiffusiveProcess SubdiffusiveProcess.Frozen SubdiffusiveProcess.Frozen.Section6

noncomputable section

namespace Paper

theorem l_finite_cutoff_coefficient_convergence
    (d : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
        ∃ hmeas : MeasurableSet (SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet d),
        ∃ hfull : M.P.toMeasure (SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet d) = 1,
        ∃ kappa : ℝ, kappa ∈ Set.Ioo (0 : ℝ) 1 ∧
          ∃ Comega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d → ℝ,
            Measurable Comega ∧
            ∀ᵐ omega ∂(SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M hmeas hfull).toMeasure,
              0 ≤ Comega omega ∧
              (∀ x : Vec d,
                SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega x +
                      (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega x)⁻¹ +
                      euclideanNorm
                        (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega x •
                          shellGradient (SubdiffusiveProcess.Frozen.Assumptions.anchoredLog omega) x) ≤
                    Comega omega * (1 + ‖x‖) ^ kappa ∧
                  ∀ L : ℕ,
                    anchoredCutoff M L omega.1 x +
                          (anchoredCutoff M L omega.1 x)⁻¹ +
                          euclideanNorm
                            (anchoredCutoff M L omega.1 x •
                              shellGradient
                                (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega.1 L) x) ≤
                        Comega omega * (1 + ‖x‖) ^ kappa) ∧
              (∀ K : Set (Vec d), IsCompact K →
                TendstoUniformlyOn
                    (fun L x ↦ anchoredCutoff M L omega.1 x)
                    (SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega) atTop K ∧
                  TendstoUniformlyOn
                    (fun L x ↦ anchoredCutoff M L omega.1 x •
                      shellGradient
                        (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega.1 L) x)
                    (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega x •
                      shellGradient (SubdiffusiveProcess.Frozen.Assumptions.anchoredLog omega) x) atTop K ∧
                  ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
                    LipschitzOnWith (Real.toNNReal epsilon)
                      (fun x ↦
                        anchoredCutoff M L omega.1 x •
                            shellGradient
                              (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega.1 L) x -
                          SubdiffusiveProcess.Frozen.Assumptions.aAnchored M omega x •
                            shellGradient (SubdiffusiveProcess.Frozen.Assumptions.anchoredLog omega) x) K) ∧
              (∀ K : Set (Vec d), IsCompact K →
                TendstoUniformlyOn
                    (fun L x ↦ shellGradient
                      (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega.1 L) x)
                    (shellGradient (SubdiffusiveProcess.Frozen.Assumptions.anchoredLog omega)) atTop K ∧
                  ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
                    LipschitzOnWith (Real.toNNReal epsilon)
                      (fun x ↦
                        shellGradient
                            (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega.1 L) x -
                          shellGradient (SubdiffusiveProcess.Frozen.Assumptions.anchoredLog omega) x) K) ∧
              ∀ x : Vec d, ∀ L : ℕ,
                euclideanNorm
                    (shellGradient
                      (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega.1 L) x) +
                    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.unitCubeDerivLipschitzSeminorm
                      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate x
                        (SubdiffusiveProcess.Frozen.Assumptions.anchoredPartialSumField omega.1 L)) ≤
                  Comega omega * (1 + Real.sqrt (Real.log (2 + ‖x‖))) :=
  SubdiffusiveProcess.Frozen.Section6.finite_cutoff_coefficient_convergence d

end Paper
