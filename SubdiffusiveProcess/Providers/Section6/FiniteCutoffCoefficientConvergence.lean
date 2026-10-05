module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.AnchoredClauses
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.CoefficientLipschitz
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable

@[expose] public section

/-!
# Anchored finite-cutoff convergence `l.finite.cutoff.coefficient.convergence`


This module is the final assembly of the anchored package
`SubdiffusiveProcess/CoarseGrainingVocab/Section6Anchored/`; every ingredient is proved there
and consumed here verbatim.

## Route

* `delta0 = anchoredDelta0 d = log 2 / (4 · valueMaximalSlope d)`, positive by
  `anchoredDelta0_pos` — the printed `δ₀(d)` of `step .5`.
* `hmeas` is `measurableSet_anchoredC11GoodSet`: the canonical anchored event
  is rewritten as the intrinsic Cauchy condition of the anchored partial sums
  (`CauchyLimit.lean`) and then as a countable intersection of closed
  conditions tested at a fixed dense sequence of points
  (`GoodSetMeasurable.lean`).
* `hfull` is `measure_anchoredC11GoodSet_eq_one`, the a.s. summability of the
  shell gauges (`ShellSummable.lean`, the derivative Borel–Cantelli of
  `step .1`).
* `kappa = anchoredKappa = 3/4`, deterministic — the additive graded envelope
  of `GradedAdditiveEnvelope.lean` is what keeps the slope deterministic.
* `Comega = anchoredComega M`, measurable by `measurable_anchoredComega`; it is
  a countable supremum of measurable gauges (`MeasurableEnvelope.lean`), not a
  measurable selection.
* the two convergence blocks `e.finite.cutoff.coefficient.C11.convergence`
   are the unconditional `anchoredCutoff_locally_C11` and
  `anchoredLogGradient_locally_C01` of `CoefficientLipschitz.lean`;
* the polynomial-growth clause  and the log-derivative growth clause
   are `ae_anchored_growth_clauses` of `AnchoredClauses.lean`.
-/

namespace SubdiffusiveProcess.Providers.Section6

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal Topology

noncomputable section

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

/-- **Provider for `l.finite.cutoff.coefficient.convergence`.** -/
theorem finite_cutoff_coefficient_convergence (d : ℕ) :
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
                  Comega omega * (1 + Real.sqrt (Real.log (2 + ‖x‖))) := by
  refine ⟨anchoredDelta0 d, anchoredDelta0_pos d, fun M hdelta ↦ ?_⟩
  refine ⟨measurableSet_anchoredC11GoodSet d, measure_anchoredC11GoodSet_eq_one M,
    anchoredKappa, anchoredKappa_mem, anchoredComega M, measurable_anchoredComega M, ?_⟩
  filter_upwards [ae_anchored_growth_clauses M hdelta
    (measurableSet_anchoredC11GoodSet d) (measure_anchoredC11GoodSet_eq_one M)]
    with omega homega
  obtain ⟨h0, hpoly, hlog⟩ := homega
  exact ⟨h0, hpoly, fun K hK ↦ anchoredCutoff_locally_C11 M omega K hK,
    fun K hK ↦ anchoredLogGradient_locally_C01 omega K hK, hlog⟩

end

end SubdiffusiveProcess.Providers.Section6
