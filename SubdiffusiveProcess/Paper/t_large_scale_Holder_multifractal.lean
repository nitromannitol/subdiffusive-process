module

public import SubdiffusiveProcess.Frozen.Section6.LargeScaleHolderMultifractal

@[expose] public section

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology
attribute [local instance] Classical.propDecidable
open SubdiffusiveProcess SubdiffusiveProcess.Frozen SubdiffusiveProcess.Frozen.Section6

noncomputable section

namespace Paper

theorem t_large_scale_Holder_multifractal
    (d : ℕ) :
    ∃ delta0 C0 C : ℝ, 0 < delta0 ∧ 0 < C0 ∧ 0 < C ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, (M.delta ≤ delta0 →
      ∃ hmeas : MeasurableSet (SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet d),
      ∃ hfull : M.P.toMeasure (SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet d) = 1,
      gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
      (∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
        ∃ full : Set (SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d),
          MeasurableSet full ∧
          (SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
          ∀ L : WithTop ℕ, ∀ m : ℕ, 0 < m →
            ∃ X : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d → ℕ,
              Measurable X ∧ (∀ ω, 0 < X ω) ∧
              (∀ k : ℕ, 0 < k →
                (SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M hmeas hfull).toMeasure
                    {ω' | k < X ω'} ≤ ENNReal.ofReal
                (C * Real.exp (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
              ∀ ω ∈ full,
              ∀ u : H1Function (openCubeSet (originCube d m)),
                IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) u →
                ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (X ω : ℤ) →
                  ∀ z : Vec d, OnTriadicGrid n z →
                  translatedCube d n z ⊆ cube d (m - 1) →
                  normalizedL2On (translatedCube d n z)
                      (fun x => u.toFun x - averageOn (translatedCube d n z) u.toFun) ≤
                    C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
                      normalizedL2On (cube d m)
                        (fun x => u.toFun x - averageOn (cube d m) u.toFun) ∧
                  vectorNormalizedL2On (translatedCube d n z)
                      (fun x => Real.sqrt (coefficientAt M L ω x) • u.grad x) ≤
                    C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
                      vectorNormalizedL2On (cube d m)
                        (fun x => Real.sqrt (coefficientAt M L ω x) • u.grad x)) ∧
      (∃ full : Set (SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d),
        MeasurableSet full ∧
        (SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
        ∀ ω ∈ full, ∀ L : WithTop ℕ, ∀ u : Vec d → ℝ,
          (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
            (∀ x, um.toFun x = u x) ∧
              IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) um) →
          (∀ ε > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
              sInf {r : ℝ | ∃ c : ℝ,
                r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x => u x - c)} < ε) →
          ∃ uRep : Vec d → ℝ,
            Continuous uRep ∧
            uRep =ᵐ[volume] u ∧
            (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
              (∀ x, um.toFun x = u x) →
              IsWeaklyHarmonicOn (coefficientAt M L ω) (cube d m) um →
              uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
            ∃ c : ℝ, ∀ x, uRep x = c)) :=
  SubdiffusiveProcess.Frozen.Section6.large_scale_holder_multifractal d

end Paper
