module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryWeightedFiniteHeight
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCorrectedFluxBesov

@[expose] public section

/-!
# Coefficient-weighted finite-height cutoff product

This is the nonzero-datum cutoff product used by the boundary Caccioppoli
step.  Low depths are paid by the centered scalar `L²` norm.  The tunably
small fine tail is paid by the gradient `circ` norm at exponent `t`, so the
good event can control it through `lambdaS` rather than through a pointwise
coefficient minimum.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Positive Besov budget for the centered cutoff product, with the fine
part expressed in the coefficient-weighted `circ` carrier. -/
theorem centeredH1CutoffProduct_positiveBesovWeightedFiniteHeightBudget
    {Q : TriadicCube d} {t : ℝ} (u : H1Function (openCubeSet Q))
    (xi : Vec d → Vec d) {B Bcirc : ℝ} (height : ℕ)
    (ht : 0 < t) (htHalf : t < 1 / 2)
    (hB : 0 ≤ B) (hBcirc : 0 ≤ Bcirc)
    (hxiLp : MemLp xi ∞ (normalizedCubeMeasure Q))
    (hxi : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => xi x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => xi x i) z‖ ≤ B)
    (hcirc : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x => u.grad x i) ≤ Bcirc) :
    let v : Vec d → ℝ := cubeFluctuation Q u.toFun
    let H : Vec d → Vec d := fun x => v x • xi x
    let Gs : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
    let C : ℝ := fullVectorPoincareCubeConstant Q
    let Br : ℝ := cubeBesovScaleWeight (-(1 - t)) Q *
      ((C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((Fintype.card (Fin d) : ℝ) * Bcirc))
    let X : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) v
    let P : ℝ := (d : ℝ) * cubeLpNorm Q ∞ xi * X +
      2 * (cubeScaleFactor Q * B * (Gs * X) +
        cubeLpNorm Q ∞ xi *
          (boundaryFiniteHeightHeadGlobalCoeff t height * X +
            boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br))
    ForceBesovRegularity Q t H ∧
      scaleNormalizedPositiveBesovVectorNormTwo Q t H ≤ P := by
  dsimp only
  let v : Vec d → ℝ := cubeFluctuation Q u.toFun
  let H : Vec d → Vec d := fun x => v x • xi x
  let Gs : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let C : ℝ := fullVectorPoincareCubeConstant Q
  let Br : ℝ := cubeBesovScaleWeight (-(1 - t)) Q *
    ((C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Bcirc))
  let X : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) v
  let P : ℝ := (d : ℝ) * cubeLpNorm Q ∞ xi * X +
    2 * (cubeScaleFactor Q * B * (Gs * X) +
      cubeLpNorm Q ∞ xi *
        (boundaryFiniteHeightHeadGlobalCoeff t height * X +
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br))
  have hu : MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hv : MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hu.sub (memLp_const (cubeAverage Q u.toFun))
  have hH : MemLp H (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by infer_instance
    simpa [H] using! hv.smul (p := (2 : ℝ≥0∞)) (r := (2 : ℝ≥0∞)) hxiLp
  have hL2 : ∀ N : ℕ,
      cubeL2ScalarPartialSeminormTwo Q (t - 1) N v ≤ Gs * X := by
    intro N
    simpa [v, Gs, X] using!
      cubeL2ScalarPartialSeminormTwo_le_geometric_mul_cubeLpNorm_two_of_neg
        Q (t - 1) N v hv (by linarith)
  have hpos : ∀ N : ℕ,
      cubeBesovPositiveScalarPartialSeminormTwo Q t N v ≤
        boundaryFiniteHeightHeadGlobalCoeff t height * X +
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br := by
    intro N
    simpa only [v, X, C, Br] using!
      cubeBesovPositiveScalarPartialSeminormTwo_h1_le_weightedFiniteHeight
        Q t N height u ht htHalf hBcirc hcirc
  have hpartial : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q t N H ≤
        2 * (cubeScaleFactor Q * B * (Gs * X) +
          cubeLpNorm Q ∞ xi *
            (boundaryFiniteHeightHeadGlobalCoeff t height * X +
              boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br)) := by
    intro N
    have hraw :=
      cubeBesovPositiveVectorPartialSeminormTwo_centered_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
        Q t N u.toFun xi hB hu hxiLp hxi hderiv
    have h1 := mul_le_mul_of_nonneg_left (hL2 N)
      (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
    have h2 := mul_le_mul_of_nonneg_left (hpos N) (cubeLpNorm_nonneg Q ∞ xi)
    dsimp only [H, v]
    exact hraw.trans (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num))
  have hreg : ForceBesovRegularity Q t H := by
    refine ⟨hH, ?_⟩
    exact ⟨_, by rintro _ ⟨N, rfl⟩; exact hpartial N⟩
  have hsemi := cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q t H hpartial
  have havgNorm : ‖cubeAverageVec Q H‖ ≤ cubeLpNorm Q ∞ xi * X := by
    simpa [H, X] using!
      norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two
        Q v xi hv hxiLp
  have havgEuclidean : Real.sqrt (vecNormSq (cubeAverageVec Q H)) ≤
      (d : ℝ) * cubeLpNorm Q ∞ xi * X := by
    calc
      Real.sqrt (vecNormSq (cubeAverageVec Q H)) = euclideanNorm (cubeAverageVec Q H) := rfl
      _ ≤ (d : ℝ) * ‖cubeAverageVec Q H‖ := euclideanNorm_le_dimension_mul_norm _
      _ ≤ (d : ℝ) * (cubeLpNorm Q ∞ xi * X) :=
        mul_le_mul_of_nonneg_left havgNorm (by positivity)
      _ = _ := by ring
  refine ⟨hreg, ?_⟩
  unfold scaleNormalizedPositiveBesovVectorNormTwo
  exact add_le_add havgEuclidean hsemi

/-- Corrected-flux pairing with the weighted finite-height budget.  This is
the direct replacement for the pointwise-coefficient cutoff leg. -/
theorem exists_abs_correctedFlux_h1CutoffPairing_weightedFiniteHeight_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {t : ℝ}
        {g : Vec d → Vec d} (u : ForcedCubeSolution Q a g)
        (w : H1Function (openCubeSet Q))
        {eta : Vec d → ℝ} {B Bcirc : ℝ} (height : ℕ),
        0 < t → t < 1 / 2 → ForceBesovRegularity Q t g →
        ContDiff ℝ (⊤ : ℕ∞) eta → HasCompactSupport eta →
        tsupport eta ⊆ openCubeSet Q → 0 ≤ B → 0 ≤ Bcirc →
        MemLp (scalarCutoffGradientField eta) ∞ (normalizedCubeMeasure Q) →
        (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
          (fun x => scalarCutoffGradientField eta x i)) →
        (∀ i : Fin d, ∀ z ∈ cubeSet Q,
          ‖fderiv ℝ (fun x => scalarCutoffGradientField eta x i) z‖ ≤ B) →
        (∀ i : Fin d, ∀ N : ℕ,
          cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x => w.grad x i) ≤ Bcirc) →
        Integrable (fun x =>
          vecDot (forcedSolutionCorrectedFluxField Q a g u x)
            (w.toFun x • scalarCutoffGradientField eta x))
          (normalizedCubeMeasure Q) →
        Integrable (fun x =>
          vecDot (forcedSolutionCorrectedFluxField Q a g u x)
            ((cubeAverage Q w.toFun) • scalarCutoffGradientField eta x))
          (normalizedCubeMeasure Q) →
        let xi := scalarCutoffGradientField eta
        let v := cubeFluctuation Q w.toFun
        let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
        let Cfull := fullVectorPoincareCubeConstant Q
        let Br := cubeBesovScaleWeight (-(1 - t)) Q *
          ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc))
        let X := cubeLpNorm Q (2 : ℝ≥0∞) v
        let P := (d : ℝ) * cubeLpNorm Q ∞ xi * X +
          2 * (cubeScaleFactor Q * B * (Gs * X) +
            cubeLpNorm Q ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * X +
                boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br))
        |cubeAverage Q (fun x =>
          vecDot (forcedSolutionCorrectedFluxField Q a g u x)
            (w.toFun x • xi x))| ≤
          C * (weakFluxWithRHSRHS C Q a t g u +
            boundaryNegativeToL2Factor (2 * t) *
              boundaryNormalizedEuclideanL2 Q g) * P := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_abs_correctedFlux_pairing_le_weakFlux_mul_positiveBesov d
  refine ⟨C, hC, ?_⟩
  intro Q a t g u w eta B Bcirc height ht htHalf hg heta hetaCompact hetaSupport
    hB hBcirc hxiLp hxi hderiv hcirc hmain hconst
  dsimp only
  let xi := scalarCutoffGradientField eta
  let v := cubeFluctuation Q w.toFun
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Cfull := fullVectorPoincareCubeConstant Q
  let Br := cubeBesovScaleWeight (-(1 - t)) Q *
    ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Bcirc))
  let X := cubeLpNorm Q (2 : ℝ≥0∞) v
  let P := (d : ℝ) * cubeLpNorm Q ∞ xi * X +
    2 * (cubeScaleFactor Q * B * (Gs * X) +
      cubeLpNorm Q ∞ xi *
        (boundaryFiniteHeightHeadGlobalCoeff t height * X +
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br))
  have hproduct := centeredH1CutoffProduct_positiveBesovWeightedFiniteHeightBudget
    (Q := Q) (t := t) w xi height ht htHalf hB hBcirc hxiLp hxi hderiv hcirc
  have hprodReg : ForceBesovRegularity Q t
      (fun x => cubeFluctuation Q w.toFun x • xi x) := by
    simpa only [xi, cubeFluctuation] using! hproduct.1
  have hprodNorm : scaleNormalizedPositiveBesovVectorNormTwo Q t
      (fun x => cubeFluctuation Q w.toFun x • xi x) ≤ P := by
    simpa only [xi, v, Gs, Cfull, Br, X, P, cubeFluctuation] using! hproduct.2
  have hP : 0 ≤ P := by
    have hX : 0 ≤ X := by dsimp [X]; exact cubeLpNorm_nonneg Q 2 _
    have hxiNorm : 0 ≤ cubeLpNorm Q ∞ xi := cubeLpNorm_nonneg Q ∞ xi
    have hGs : 0 ≤ Gs := by dsimp [Gs]; exact Real.sqrt_nonneg _
    have hhead : 0 ≤ boundaryFiniteHeightHeadGlobalCoeff t height :=
      boundaryFiniteHeightHeadGlobalCoeff_nonneg t height
    have htail : 0 ≤ boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height :=
      boundaryFiniteHeightTailBetweenGlobalCoeff_nonneg t (1 - t) height
    have hBr : 0 ≤ Br := by
      dsimp [Br, Cfull]
      exact mul_nonneg (cubeBesovScaleWeight_nonneg (-(1 - t)) Q)
        (mul_nonneg
          (mul_nonneg (fullVectorPoincareCubeConstant_nonneg Q)
            (Real.rpow_nonneg (by norm_num) _))
          (mul_nonneg (by positivity) hBcirc))
    dsimp only [P]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hxiNorm) hX)
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
            (mul_nonneg hGs hX))
          (mul_nonneg hxiNorm
            (add_nonneg (mul_nonneg hhead hX) (mul_nonneg htail hBr)))))
  have hcenter := cubeAverage_correctedFlux_scalar_smul_cutoffGradient_eq_centered
    u hg w.toFun heta hetaCompact hetaSupport hmain hconst
  have hbound := hpair u ht (by linarith) hg hprodReg hP hprodNorm
  rw [hcenter]
  simpa only [xi, P, X, Gs, Br, Cfull, cubeFluctuation] using! hbound

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
