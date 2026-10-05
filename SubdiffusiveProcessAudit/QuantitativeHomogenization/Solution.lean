module
public import SubdiffusiveProcessAudit.QuantitativeHomogenization.SolutionBridge
@[expose] public section
noncomputable section
namespace SubdiffusiveProcessAudit.QuantitativeHomogenization
open MeasureTheory
open _root_.SubdiffusiveProcessAudit.QuantitativeHomogenization.SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcessAudit.QuantitativeHomogenization.Homogenization
open scoped ENNReal
/-- **Theorem B** (`t.B`). In (i) the constants `δ₀` and `C` depend only on `(ϑ, q, d)` and are
chosen before the model, while the random variables `Z L N` (`Z_{L,N}`) are chosen for the model
and all `L ≤ N`. In (ii) `α_hom` depends only on `d`, and `C` on `(L, q, d, δ)`; both are chosen
before the model, and `Y` (`Y_{L,q}`) after it. The three summands of `𝒟` are the `L²` distance
of the solutions and the `H⁻¹` distances of the gradients and of the fluxes. -/
theorem theoremB (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ vartheta q : ℝ,
        vartheta ∈ Set.Ioo (0 : ℝ) 1 →
          1 ≤ q →
            ∃ delta0 C : ℝ,
              0 < delta0 ∧
                ∀ M : SubdiffusiveProcess.Model.GMCModel d,
                  (M.delta ≤ delta0 →
                    ∃ Z : ℕ → ℕ → SubdiffusiveProcess.Model.PotentialSample d → ℝ,
                      (∀ L N,
                          L ≤ N →
                            CoefficientMeasurable
                              (fun omega ↦ rescaledCutoffCoefficient M L N omega) (Z L N)) ∧
                        (∀ L N omega, L ≤ N → 1 ≤ Z L N omega) ∧
                          (∀ L N,
                              L ≤ N →
                                eLpNorm (Z L N) (ENNReal.ofReal q) M.P.toMeasure ≤
                                  ENNReal.ofReal C) ∧
                            ∀ᵐ omega ∂M.P.toMeasure,
                              ∀ L N : ℕ,
                                L ≤ N →
                                  ∀ f : Homogenization.Vec d → ℝ,
                                    MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))) →
                                      ∀ h : H2Datum (originCube d 0),
                                        DirichletComparison (rescaledCutoffCoefficient M L N omega)
                                          f h
                                          (fun error =>
                                            error ≤
                                                ENNReal.ofReal (Z L N omega * M.delta ^ vartheta) *
                                                  (l2Size (originCube d 0) f + h.norm) ∧
                                              (f = 0 →
                                                error ≤
                                                  ENNReal.ofReal (Z L N omega * C * M.delta) *
                                                    h.norm)))) ∧
      (∃ alphaHom : ℝ,
        0 < alphaHom ∧
          ∀ L : ℕ,
            ∀ q : ℝ,
              1 ≤ q →
                ∀ delta : ℝ,
                  ∃ C : ℝ,
                    0 < C ∧
                      ∀ M : SubdiffusiveProcess.Model.GMCModel d,
                        M.delta = delta →
                          ∃ Y : SubdiffusiveProcess.Model.PotentialSample d → ℝ,
                            CoefficientMeasurable
                                (SubdiffusiveProcess.Model.aCutoff M L) Y ∧
                              (∀ omega, 1 ≤ Y omega) ∧
                                eLpNorm Y (ENNReal.ofReal q) M.P.toMeasure ≤ ENNReal.ofReal C ∧
                                  ∀ᵐ omega ∂M.P.toMeasure,
                                    ∀ N : ℕ,
                                      L ≤ N →
                                        ∀ f : Homogenization.Vec d → ℝ,
                                          MemLp f 2
                                              (volume.restrict (openCubeSet (originCube d 0))) →
                                            ∀ h : H2Datum (originCube d 0),
                                              DirichletComparison
                                                (rescaledCutoffCoefficient M L N omega) f h
                                                (fun error =>
                                                  error ≤
                                                    ENNReal.ofReal
                                                        (Y omega *
                                                          (3 : ℝ) ^
                                                            (-alphaHom * ((N : ℝ) - (L : ℝ)))) *
                                                      (l2Size (originCube d 0) f + h.norm))) :=
  by exact transfer_B d hd (_root_.SubdiffusiveProcess.Paper.t_B d hd)
end SubdiffusiveProcessAudit.QuantitativeHomogenization
