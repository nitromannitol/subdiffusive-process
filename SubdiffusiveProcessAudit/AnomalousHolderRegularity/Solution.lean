module
public import SubdiffusiveProcessAudit.AnomalousHolderRegularity.SolutionBridge
@[expose] public section
noncomputable section
namespace SubdiffusiveProcessAudit.AnomalousHolderRegularity
open Filter _root_.SubdiffusiveProcessAudit.AnomalousHolderRegularity.SubdiffusiveProcess _root_.SubdiffusiveProcessAudit.AnomalousHolderRegularity.SubdiffusiveProcess.Model MeasureTheory
open _root_.SubdiffusiveProcessAudit.AnomalousHolderRegularity.Homogenization
open Set
open _root_.SubdiffusiveProcessAudit.AnomalousHolderRegularity.SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology
/-- **Theorem C** (`t.C`). The constants `δ₀, C₀, C` depend only on `d` and are chosen before the
model; `γ_reg = 1 − C₀ δ √|log δ|`. For each `γ ∈ [1/2, γ_reg]` the random minimal scales `𝓛_L(γ,
m)` (`Lscale L m`) are chosen first; the almost-sure event then holds simultaneously for all
cutoffs `L` (including `L = ∞`), all `m`, all weakly harmonic `u`, all `n` and `z`, and all
Liouville candidates. The sample law is the pullback of `M.P` to the anchored `C^{1,1}` carrier.
-/
theorem theoremC (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 C0 C : ℝ,
      0 < delta0 ∧
        0 < C0 ∧
          0 < C ∧
            ∀ M : GMCModel d,
              M.delta ≤ delta0 →
                let mu :=
                  Measure.comap (Subtype.val : AnchoredC11Sample d → PotentialSample d)
                    M.P.toMeasure
                gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
                  ∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
                    ∃ Lscale : WithTop ℕ → ℕ → AnchoredC11Sample d → ℕ,
                      (∀ (L : WithTop ℕ) (m : ℕ), Measurable (Lscale L m)) ∧
                        (∀ (L : WithTop ℕ) (m k : ℕ),
                            0 < k →
                              mu {omega | k < Lscale L m omega} ≤
                                ENNReal.ofReal
                                  (C *
                                    Real.exp
                                      (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                                        (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
                          ∀ᵐ omega ∂mu,
                            (∀ (L : WithTop ℕ) (m : ℕ),
                                0 < m →
                                  ∀ u : H1Function (openCubeSet (originCube d m)),
                                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) u →
                                      ∀ n : ℕ,
                                        (n : ℤ) ≤ (m : ℤ) - (Lscale L m omega : ℤ) →
                                          ∀ z : Homogenization.Vec d,
                                            OnTriadicGrid n z →
                                              translatedCube d n z ⊆ cube d (m - 1) →
                                                OscillationDecay gamma C m n z u ∧
                                                  EnergyGrowth (coefficientAt M L omega) gamma C m n
                                                    z u) ∧
                              (∀ (L : WithTop ℕ) (u : Homogenization.Vec d → ℝ),
                                IsEntireHarmonic (coefficientAt M L omega) u →
                                  HasSubcriticalGrowth (gammaReg C0 M.delta) u →
                                    ∃ uRep : Homogenization.Vec d → ℝ,
                                      Continuous uRep ∧
                                        uRep =ᵐ[volume] u ∧
                                          (∀ m : ℤ,
                                              ∀ um : H1Function (openCubeSet (originCube d m)),
                                                (∀ x, um.toFun x = u x) →
                                                  IsWeaklyHarmonicOn (coefficientAt M L omega)
                                                      (cube d m) um →
                                                    uRep =ᵐ[volume.restrict
                                                        (openCubeSet (originCube d m))]
                                                      um.toFun) ∧
                                            ∃ c : ℝ, ∀ x, uRep x = c) :=
  by
  apply transferC d
  exact _root_.SubdiffusiveProcess.Paper.t_C d hd
end SubdiffusiveProcessAudit.AnomalousHolderRegularity
