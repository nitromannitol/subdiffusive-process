module

public import SubdiffusiveProcess.Section6.LargeScaleHolderMultifractal
public import SubdiffusiveProcess.Model.ACutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
public import SubdiffusiveProcess.Section6.Defs.CoefficientAt
public import SubdiffusiveProcess.Section6.Defs.GammaReg
@[expose] public section

/-!
# Provider for `t.C` — Theorem C from the Section 6 large-scale Hölder theorem

`t.large.scale.Holder.multifractal` (Section 6) already carries every
display of Theorem C: the same `gammaReg`, the same `L`-uniform tail, both the `L²` and the
energy display, and the Liouville conclusion under the liminf hypothesis.  What Theorem C adds
is the **main-theorem packaging**:

* Section 6 produces, for each `(L, m)`, its own random scale `X`.  Theorem C asks for a
  single `Lscale : WithTop ℕ → ℕ → AnchoredC11Sample d → ℕ` whose tail is uniform in `L`.
  The assembly is by choice over `(L, m)`, with `Lscale L 0 := 0` (Section 6 supplies `X` only
  for `0 < m`, and at `m = 0` the tail set `{k < 0}` is empty for every `k : ℕ`).
* Section 6 states its conclusions on explicit full-measure sets, one for the regularity
  clause and one for the Liouville clause.  Theorem C states a single `∀ᵐ` covering both, so
  the two sets are intersected.
* The `hmeas`/`hfull` that Section 6 existentially produces are propositions, so the measure
  they build is the canonical `anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
  (measure_anchoredC11GoodSet_eq_one M)` by proof irrelevance.
-/

set_option autoImplicit false

open Filter SubdiffusiveProcess _root_.SubdiffusiveProcess.Model MeasureTheory ProbabilityTheory
open Homogenization hiding Vec
open Set
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

namespace SubdiffusiveProcess.Providers.Main

theorem anomalous_holder_regularity (d : ℕ) (_hd : 2 ≤ d) :
    ∃ delta0 C0 C : ℝ, 0 < delta0 ∧ 0 < C0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
        let mu := (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
          (measure_anchoredC11GoodSet_eq_one M)).toMeasure
        gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
        ∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
          ∃ Lscale : WithTop ℕ → ℕ → AnchoredC11Sample d → ℕ,
            (∀ (L : WithTop ℕ) (m k : ℕ), 0 < k →
              mu {omega | k < Lscale L m omega} ≤
                ENNReal.ofReal (C * Real.exp (
                  -((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                    (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ᵐ omega ∂mu,
              (∀ (L : WithTop ℕ) (m : ℕ), 0 < m →
                ∀ u : H1Function (openCubeSet (originCube d m)),
                  IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) u →
                  ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (Lscale L m omega : ℤ) →
                    ∀ z : Vec d, OnTriadicGrid n z →
                    translatedCube d n z ⊆ cube d (m - 1) →
                      normalizedL2On (translatedCube d n z)
                          (fun x => u.toFun x - averageOn (translatedCube d n z) u.toFun) ≤
                        C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
                          normalizedL2On (cube d m)
                            (fun x => u.toFun x - averageOn (cube d m) u.toFun) ∧
                      vectorNormalizedL2On (translatedCube d n z)
                          (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x) ≤
                        C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
                          vectorNormalizedL2On (cube d m)
                            (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x)) ∧
              (∀ (L : WithTop ℕ) (u : Vec d → ℝ),
                (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
                  (∀ x, um.toFun x = u x) ∧
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um) →
                (∀ eps > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
                    sInf {r : ℝ | ∃ c : ℝ,
                      r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x => u x - c)} < eps) →
                ∃ uRep : Vec d → ℝ,
                  Continuous uRep ∧ uRep =ᵐ[volume] u ∧
                  (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
                    (∀ x, um.toFun x = u x) →
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um →
                    uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
                  ∃ c : ℝ, ∀ x, uRep x = c) := by
  classical
  obtain ⟨delta0, C0, C, hdelta0, hC0, hC, hmain⟩ :=
    _root_.SubdiffusiveProcess.Section6.large_scale_holder_multifractal d
  refine ⟨delta0, C0, C, hdelta0, hC0, hC, ?_⟩
  intro M hM
  obtain ⟨hmeasGood, hfullGood, hrange, hreg, hliou⟩ := hmain M hM
  refine ⟨hrange, ?_⟩
  intro gamma hgamma
  obtain ⟨full1, hfull1meas, hfull1one, hX⟩ := hreg gamma hgamma
  obtain ⟨full2, hfull2meas, hfull2one, hLiou⟩ := hliou
  refine ⟨fun L m => if h : 0 < m then (hX L m h).choose else fun _ => 0, ?_, ?_⟩
  · intro L m k hk
    by_cases hm : 0 < m
    · simp only [dite_eq_left hm]
      exact (hX L m hm).choose_spec.2.2.1 k hk
    · simp only [dite_eq_right hm]
      have hempty : {omega : AnchoredC11Sample d | k < 0} = (∅ : Set (AnchoredC11Sample d)) := by
        ext omega
        simp
      rw [hempty, measure_empty]
      exact zero_le
  · have hae1 : ∀ᵐ omega ∂(anchoredC11SampleLaw M hmeasGood hfullGood).toMeasure,
        omega ∈ full1 := by
      rw [MeasureTheory.ae_iff]
      simpa using! (prob_compl_eq_zero_iff hfull1meas).mpr hfull1one
    have hae2 : ∀ᵐ omega ∂(anchoredC11SampleLaw M hmeasGood hfullGood).toMeasure,
        omega ∈ full2 := by
      rw [MeasureTheory.ae_iff]
      simpa using! (prob_compl_eq_zero_iff hfull2meas).mpr hfull2one
    filter_upwards [hae1, hae2] with omega h1 h2
    refine ⟨?_, ?_⟩
    · intro L m hm u hu n hn z hz hsub
      refine (hX L m hm).choose_spec.2.2.2 omega h1 u hu n ?_ z hz hsub
      simpa only [dite_eq_left hm] using hn
    · intro L u hu heps
      exact hLiou omega h2 L u hu heps

end SubdiffusiveProcess.Providers.Main
