module

public import SubdiffusiveProcess.Section6.FiniteCutoffCoefficientConvergence

@[expose] public section

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.Section6

noncomputable section

namespace SubdiffusiveProcess.Paper

theorem l_finite_cutoff_coefficient_convergence
    (d : ℕ) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
        ∃ hmeas : MeasurableSet (_root_.SubdiffusiveProcess.Model.anchoredC11GoodSet d),
        ∃ hfull : M.P.toMeasure (_root_.SubdiffusiveProcess.Model.anchoredC11GoodSet d) = 1,
        ∃ kappa : ℝ, kappa ∈ Set.Ioo (0 : ℝ) 1 ∧
          ∃ Comega : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d → ℝ,
            Measurable Comega ∧
            ∀ᵐ omega ∂(_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M hmeas hfull).toMeasure,
              0 ≤ Comega omega ∧
              (∀ x : Vec d,
                _root_.SubdiffusiveProcess.Model.aAnchored M omega x +
                      (_root_.SubdiffusiveProcess.Model.aAnchored M omega x)⁻¹ +
                      euclideanNorm
                        (_root_.SubdiffusiveProcess.Model.aAnchored M omega x •
                          shellGradient (_root_.SubdiffusiveProcess.Model.anchoredLog omega) x) ≤
                    Comega omega * (1 + ‖x‖) ^ kappa ∧
                  ∀ L : ℕ,
                    anchoredCutoff M L omega.1 x +
                          (anchoredCutoff M L omega.1 x)⁻¹ +
                          euclideanNorm
                            (anchoredCutoff M L omega.1 x •
                              shellGradient
                                (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField omega.1 L) x) ≤
                        Comega omega * (1 + ‖x‖) ^ kappa) ∧
              (∀ K : Set (Vec d), IsCompact K →
                TendstoUniformlyOn
                    (fun L x ↦ anchoredCutoff M L omega.1 x)
                    (_root_.SubdiffusiveProcess.Model.aAnchored M omega) atTop K ∧
                  TendstoUniformlyOn
                    (fun L x ↦ anchoredCutoff M L omega.1 x •
                      shellGradient
                        (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField omega.1 L) x)
                    (fun x ↦ _root_.SubdiffusiveProcess.Model.aAnchored M omega x •
                      shellGradient (_root_.SubdiffusiveProcess.Model.anchoredLog omega) x) atTop K ∧
                  ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
                    LipschitzOnWith (Real.toNNReal epsilon)
                      (fun x ↦
                        anchoredCutoff M L omega.1 x •
                            shellGradient
                              (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField omega.1 L) x -
                          _root_.SubdiffusiveProcess.Model.aAnchored M omega x •
                            shellGradient (_root_.SubdiffusiveProcess.Model.anchoredLog omega) x) K) ∧
              (∀ K : Set (Vec d), IsCompact K →
                TendstoUniformlyOn
                    (fun L x ↦ shellGradient
                      (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField omega.1 L) x)
                    (shellGradient (_root_.SubdiffusiveProcess.Model.anchoredLog omega)) atTop K ∧
                  ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
                    LipschitzOnWith (Real.toNNReal epsilon)
                      (fun x ↦
                        shellGradient
                            (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField omega.1 L) x -
                          shellGradient (_root_.SubdiffusiveProcess.Model.anchoredLog omega) x) K) ∧
              ∀ x : Vec d, ∀ L : ℕ,
                euclideanNorm
                    (shellGradient
                      (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField omega.1 L) x) +
                    _root_.SubdiffusiveProcess.Model.PotentialField.unitCubeDerivLipschitzSeminorm
                      (_root_.SubdiffusiveProcess.Model.PotentialField.translate x
                        (_root_.SubdiffusiveProcess.Model.anchoredPartialSumField omega.1 L)) ≤
                  Comega omega * (1 + Real.sqrt (Real.log (2 + ‖x‖))) :=
  _root_.SubdiffusiveProcess.Section6.finite_cutoff_coefficient_convergence d

end SubdiffusiveProcess.Paper
