module
public import SubdiffusiveProcessAudit.AnomalousHolderRegularity.SolutionBridge
@[expose] public section
noncomputable section
namespace SubdiffusiveProcessAudit.AnomalousHolderRegularity
open Filter SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions MeasureTheory ProbabilityTheory
open Homogenization
open Set
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology

theorem theoremC (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 C0 C : ℝ, 0 < delta0 ∧ 0 < C0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
        let mu := Measure.comap (Subtype.val : AnchoredC11Sample d → PotentialSample d) M.P.toMeasure
        gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
        ∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
          ∃ Lscale : WithTop ℕ → ℕ → AnchoredC11Sample d → ℕ,
            (∀ (L : WithTop ℕ) (m : ℕ), Measurable (Lscale L m)) ∧
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
                    ∀ z : Homogenization.Vec d, OnTriadicGrid n z →
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
              (∀ (L : WithTop ℕ) (u : Homogenization.Vec d → ℝ),
                (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
                  (∀ x, um.toFun x = u x) ∧
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um) →
                (∀ eps > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
                    sInf {r : ℝ | ∃ c : ℝ,
                      r = normalizedL2On (Metric.ball (0 : Homogenization.Vec d) R) (fun x => u x - c)} < eps) →
                ∃ uRep : Homogenization.Vec d → ℝ,
                  Continuous uRep ∧ uRep =ᵐ[volume] u ∧
                  (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
                    (∀ x, um.toFun x = u x) →
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um →
                    uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
                  ∃ c : ℝ, ∀ x, uRep x = c)  := by
  apply transferC d
  exact Paper.t_C d hd
end SubdiffusiveProcessAudit.AnomalousHolderRegularity
