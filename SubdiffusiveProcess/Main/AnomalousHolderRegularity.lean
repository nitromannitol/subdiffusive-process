module

public import SubdiffusiveProcess.Model.ACutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GoodSetMeasurable
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellSummable
public import SubdiffusiveProcess.Section6.Defs.CoefficientAt
public import SubdiffusiveProcess.Section6.Defs.GammaReg
public import SubdiffusiveProcess.Providers.Main.AnomalousHolderRegularity
public import Homogenization.Sobolev.Foundations.Cutoff.Euclidean

@[expose] public section

/-!
# Theorem C: large-scale regularity and Liouville constancy

A given small-disorder `GMCModel d` supplies the law on `AnchoredC11Sample d`.
The cutoff index is `WithTop ℕ`: finite values select cutoff coefficients and
`⊤` selects the anchored uncut coefficient. Harmonic functions on cubes belong
to `H1Function`; harmonicity is the weak divergence-form equation.

For each deterministic exponent `gamma` between `1/2` and `gammaReg`, the
conclusion supplies random integer scales indexed by cutoff and observation
scale. Their tail bound has deterministic constants chosen before the model
and is uniform in the cutoff. One full-measure event handles all cutoffs,
observation cubes, harmonic functions and admissible subcubes. The estimates
control normalized `L²` oscillation and the coefficient-weighted gradient
energy at scales above the random minimum. They do not assert microscopic
pointwise Hölder continuity.

The Liouville clause assumes entire weak harmonicity through local `H¹`
representatives and a subcritical liminf growth condition. It produces a
continuous representative agreeing almost everywhere with the original
function, and proves that representative constant. Agreement on each local
cube repeats the global a.e. agreement to expose the local `H¹` interface.
`SubdiffusiveProcess.Paper.t_C` additionally makes every minimal-scale random variable measurable.
The dimension argument repeats the dimension stored in `GMCModel`.
-/

set_option autoImplicit false

open Filter SubdiffusiveProcess _root_.SubdiffusiveProcess.Model MeasureTheory ProbabilityTheory
open Homogenization hiding Vec
open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open scoped ENNReal NNReal

noncomputable section


theorem SubdiffusiveProcess.Main.anomalous_holder_regularity (d : ℕ) (hd : 2 ≤ d) :
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
                  ∃ c : ℝ, ∀ x, uRep x = c)

:= SubdiffusiveProcess.Providers.Main.anomalous_holder_regularity d hd
