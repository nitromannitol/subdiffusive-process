module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryArbitraryH1Circ
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCorrectedFluxBesov
public import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.CenteredProductFullDual

@[expose] public section

/-!
# Multiscale cutoff pairing for nonzero boundary data

This file replaces the crude pointwise-coefficient cutoff estimate by the
full-dual product route.  The corrected flux is measured at exponent `t / 2`
in `q = 2`, upgraded to `q = 1` at exponent `t` by the geometric Cauchy
conversion, while the arbitrary `H¹` scalar factor is priced by its actual
coefficient energy through the local harmonic-replacement controls.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem memLp_normalized_of_memVectorL2_cubeSet
    {Q : TriadicCube d} {F : Vec d → Vec d} (hF : MemVectorL2 (cubeSet Q) F) :
    MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
  memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hF

/-- The `q=2`, exponent-`t/2` corrected weak-flux estimate supplies the
`q=1`, exponent-`t` input used by the full-dual cutoff pairing. -/
theorem exists_correctedFlux_qone_partial_le_weakFlux_halfExponent
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g),
        0 < t → t < 1 → ForceBesovRegularity Q (t / 2) g →
        ∀ N : ℕ,
          cubeBesovNegativeVectorPartialSeminorm Q t N
              (forcedSolutionCorrectedFluxField Q a g u) ≤
            Real.sqrt ((1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
              (Real.sqrt 2 *
                (weakFluxWithRHSRHS C Q a (t / 2) g u +
                  boundaryNegativeToL2Factor t *
                    boundaryNormalizedEuclideanL2 Q g)) := by
  obtain ⟨C, hC, hcorr⟩ :=
    exists_correctedFlux_negativeBesov_le_weakFlux_add_forcingL2 d
  refine ⟨C, hC, ?_⟩
  intro Q a t g u ht ht1 hg N
  let F := forcedSolutionCorrectedFluxField Q a g u
  have htHalf : 0 < t / 2 := div_pos ht (by norm_num)
  have htHalf1 : t / 2 < 1 := by linarith
  have hfull := hcorr u htHalf htHalf1 hg
  have hFL2 : MemVectorL2 (cubeSet Q) F := by
    simpa only [F] using memVectorL2_forcedSolutionCorrectedFluxField u hg
  have hBdd : BddAbove (Set.range fun K : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q (t / 2) K F) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q htHalf F
      (memLp_normalized_of_memVectorL2_cubeSet hFL2)
  have htwo : cubeBesovNegativeVectorPartialSeminormTwo Q (t / 2) N F ≤
      Real.sqrt 2 *
        (weakFluxWithRHSRHS C Q a (t / 2) g u +
          boundaryNegativeToL2Factor t * boundaryNormalizedEuclideanL2 Q g) := by
    rw [scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
      at hfull
    exact (cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
      Q (t / 2) F hBdd N).trans (by simpa [show 2 * (t / 2) = t by ring] using hfull)
  have hconvert :=
    cubeBesovNegativeVectorPartialSeminorm_le_gap_geometric_mul_partialSeminormTwo
      Q (a := t) (b := t / 2) (by linarith) N F
  have hconvert' : cubeBesovNegativeVectorPartialSeminorm Q t N F ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-t))⁻¹) *
        cubeBesovNegativeVectorPartialSeminormTwo Q (t / 2) N F := by
    simpa [show -2 * (t - t / 2) = -t by ring] using hconvert
  exact hconvert'.trans (mul_le_mul_of_nonneg_left htwo (Real.sqrt_nonneg _))

omit [NeZero d] in
/-- The depth-zero term of the `q=1` negative seminorm controls the norm of
the vector average. -/
theorem norm_cubeAverageVec_le_scaleWeight_mul_negativePartial
    {Q : TriadicCube d} {t : ℝ} {F : Vec d → Vec d} :
    ‖cubeAverageVec Q F‖ ≤
      cubeBesovNegativeVectorPartialSeminorm Q t 0 F := by
  have hnorm : ‖cubeAverageVec Q F‖ ≤ euclideanNorm (cubeAverageVec Q F) :=
    norm_le_euclideanNorm _
  have hdepth :
      cubeBesovNegativeVectorPartialSeminorm Q t 0 F =
        euclideanNorm (cubeAverageVec Q F) := by
    simp [cubeBesovNegativeVectorPartialSeminorm,
      cubeBesovNegativeVectorDepthSeminorm,
      cubeBesovNegativeVectorDepthAverage, descendantsAverage,
      descendantsAtDepth_zero, euclideanNorm]
  calc
    ‖cubeAverageVec Q F‖ ≤ euclideanNorm (cubeAverageVec Q F) := hnorm
    _ = cubeBesovNegativeVectorPartialSeminorm Q t 0 F := hdepth.symm

/-- Exact full-dual cutoff-product bound with the coefficient-energy-sized
gradient `circ` budgets exposed.  This is the analytic half-absorption input;
the following good-event wrapper supplies `Bcirc1` and `BcircS` from
`lambdaS`, without pointwise coefficient caps. -/
theorem abs_correctedFlux_centeredH1CutoffPairing_le_multiscale
    {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
    {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
    (w : H1Function (openCubeSet Q)) (xi : Vec d → Vec d)
    {Bu Bcirc1 BcircS B : ℝ}
    (ht : 0 < t) (ht1 : t < 1)
    (hg : ForceBesovRegularity Q (t / 2) g)
    (hBu : 0 ≤ Bu)
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q t N
        (forcedSolutionCorrectedFluxField Q a g u) ≤ Bu)
    (hB : 0 ≤ B)
    (hxiLp : MemLp xi ∞ (normalizedCubeMeasure Q))
    (hxi : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => xi x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => xi x i) z‖ ≤ B)
    (hBcirc1 : 0 ≤ Bcirc1) (hBcircS : 0 ≤ BcircS)
    (hcirc1 : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => w.grad x i) ≤ Bcirc1)
    (hcircS : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q (1 - t) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => w.grad x i) ≤ BcircS) :
    let Cfull := fullVectorPoincareCubeConstant Q
    let Bg :=
      2 * (cubeScaleFactor Q * B *
          (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹) *
            (((3 / 2 : ℝ) * Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
        cubeLpNorm Q ∞ xi *
          (cubeBesovScaleWeight (-t) Q *
            ((((3 / 2 : ℝ) * Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (1 - (3 : ℝ) ^ (-t))⁻¹) *
                ((Fintype.card (Fin d) : ℝ) * BcircS))))
    |cubeAverage Q (fun x =>
        vecDot (forcedSolutionCorrectedFluxField Q a g u x)
          ((w.toFun x - cubeAverage Q w.toFun) • xi x))| ≤
      (d : ℝ) *
          (Bu *
            (cubeLpNorm Q ∞ xi *
              (((3 / 2 : ℝ) * Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
                ((Fintype.card (Fin d) : ℝ) * Bcirc1)))) +
        (d : ℝ) *
          ((((3 : ℝ) ^ ((d : ℝ) + t) *
              (cubeBesovScaleWeight (-t) Q * Bu)) *
            (cubeBesovScaleWeight t Q * Bg))) := by
  dsimp only
  let F := forcedSolutionCorrectedFluxField Q a g u
  let Cfull := fullVectorPoincareCubeConstant Q
  let Bg :=
    2 * (cubeScaleFactor Q * B *
        (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹) *
          (((3 / 2 : ℝ) * Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc1))) +
      cubeLpNorm Q ∞ xi *
        (cubeBesovScaleWeight (-t) Q *
          ((((3 / 2 : ℝ) * Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            (1 - (3 : ℝ) ^ (-t))⁻¹) *
              ((Fintype.card (Fin d) : ℝ) * BcircS))))
  have hFL2 : MemVectorL2 (cubeSet Q) F := by
    simpa only [F] using memVectorL2_forcedSolutionCorrectedFluxField u hg
  have hF : MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memVectorL2_cubeSet hFL2
  have hw : MemLp w.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    w.memL2_normalizedCubeMeasure
  have hG : ∀ i : Fin d,
      MemLp (fun x => w.grad x i) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    intro i
    exact w.grad_memL2_normalizedCubeMeasure i
  have hfull : ∀ N : ℕ,
      CubeDescendantDualFullVectorPoincareEstimate Q Cfull
        (cubeFluctuation Q w.toFun) w.grad N := by
    intro N
    simpa only [Cfull] using boundaryH1_fullDualPoincare Q w N
  have havg : ‖cubeAverageVec Q F‖ ≤ Bu :=
    (norm_cubeAverageVec_le_scaleWeight_mul_negativePartial
      (Q := Q) (t := t) (F := F)).trans
      (hneg 0)
  have hBg : 0 ≤ Bg := by
    dsimp [Bg]
    have hgeom1 : 0 ≤ (1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹ := by
      have hp : Real.rpow (3 : ℝ) (2 * (t - 1)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      exact inv_nonneg.mpr (sub_nonneg.mpr hp.le)
    have hgeom2 : 0 ≤ (1 - (3 : ℝ) ^ (-t))⁻¹ := by
      have hp : (3 : ℝ) ^ (-t) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      exact inv_nonneg.mpr (sub_nonneg.mpr hp.le)
    have hC : 0 ≤ Cfull := fullVectorPoincareCubeConstant_nonneg Q
    have hpow : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1) := Real.rpow_nonneg (by norm_num) _
    have hcard : 0 ≤ (Fintype.card (Fin d) : ℝ) := by positivity
    exact mul_nonneg (by norm_num) <| add_nonneg
      (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
        (mul_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) hC) hpow)
            (mul_nonneg hcard hBcirc1))))
      (mul_nonneg (cubeLpNorm_nonneg Q ∞ xi)
        (mul_nonneg (cubeBesovScaleWeight_nonneg (-t) Q)
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) hC) hpow) hgeom2)
            (mul_nonneg hcard hBcircS))))
  have hmain :=
    abs_cubeAverage_vecDot_centered_scalar_smul_le_collapsed_sharp_note_terms_of_dualFull_fullCirc
      Q t F w.toFun w.grad xi hB ht ht1 hF hw hG hxiLp hBg
      hBu
      (fullVectorPoincareCubeConstant_nonneg Q) hBcirc1 hBcircS
      havg hneg hfull hxi hderiv hcirc1 hcircS (le_refl Bg)
  simpa only [F, Cfull, Bg, Fintype.card_fin] using hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
