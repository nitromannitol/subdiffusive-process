module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySupportAwarePairing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryWeightedFiniteHeight

@[expose] public section

/-!
# Uncentered finite-height cutoff product on active cells

The global annular cutoff is not supported in an individual active cell, so
the cellwise corrected-flux pairing must retain the uncentered scalar factor.
The finite-height split still localizes its fine tail through the gradient
`circ` budget.  Only the finite low-frequency head pays the uncentered local
`L²` norm.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The weighted finite-height scalar estimate is unchanged by restoring the
constant mode, except that the low-frequency head is bounded by the
uncentered local `L²` norm. -/
theorem cubeBesovPositiveScalarPartialSeminormTwo_h1_uncentered_le_weightedFiniteHeight
    (Q : TriadicCube d) (t : ℝ) (N height : ℕ)
    (u : H1Function (openCubeSet Q))
    (ht : 0 < t) (htHalf : t < 1 / 2) {Bcirc : ℝ}
    (hBcirc : 0 ≤ Bcirc)
    (hcirc : ∀ i : Fin d, ∀ M : ℕ,
      cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) M
        (fun x ↦ u.grad x i) ≤ Bcirc) :
    let C := fullVectorPoincareCubeConstant Q
    let Br := cubeBesovScaleWeight (-(1 - t)) Q *
      ((C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((Fintype.card (Fin d) : ℝ) * Bcirc))
    cubeBesovPositiveScalarPartialSeminormTwo Q t N u.toFun ≤
      boundaryFiniteHeightHeadGlobalCoeff t height *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) +
        boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br := by
  dsimp only
  have hcenter :=
    cubeBesovPositiveScalarPartialSeminormTwo_h1_le_weightedFiniteHeight
      Q t N height u ht htHalf hBcirc hcirc
  have hmem : ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
      MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure R) := by
    intro j hj R hR
    exact memLp_on_descendant_of_memLp_generic (E := ℝ) hR
      u.memL2_normalizedCubeMeasure
  have heq := cubeBesovPositiveScalarPartialSeminormTwo_sub_const
    Q t N u.toFun (cubeAverage Q u.toFun) hmem
  rw [← heq]
  simpa only [cubeFluctuation] using! hcenter

/-- Positive-Besov budget for the uncentered cutoff product on an active
cell.  The term `X₀` is the only new price compared with the centered
product; the fine coefficient `mu` continues to multiply `Bcirc`. -/
theorem uncenteredH1CutoffProduct_positiveBesovWeightedFiniteHeightBudget
    {Q : TriadicCube d} {t : ℝ} (u : H1Function (openCubeSet Q))
    (xi : Vec d → Vec d) {B Bcirc : ℝ} (height : ℕ)
    (ht : 0 < t) (htHalf : t < 1 / 2)
    (hB : 0 ≤ B) (hBcirc : 0 ≤ Bcirc)
    (hxiLp : MemLp xi ∞ (normalizedCubeMeasure Q))
    (hxi : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ xi x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x ↦ xi x i) z‖ ≤ B)
    (hcirc : ∀ i : Fin d, ∀ N : ℕ,
      cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x ↦ u.grad x i) ≤ Bcirc) :
    let H : Vec d → Vec d := fun x ↦ u.toFun x • xi x
    let Gs : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
    let C : ℝ := fullVectorPoincareCubeConstant Q
    let Br : ℝ := cubeBesovScaleWeight (-(1 - t)) Q *
      ((C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((Fintype.card (Fin d) : ℝ) * Bcirc))
    let X₀ : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) u.toFun
    let Xc : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun)
    let P : ℝ := (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
      2 * (cubeScaleFactor Q * B * (Gs * X₀) +
        cubeLpNorm Q ∞ xi *
          (boundaryFiniteHeightHeadGlobalCoeff t height * Xc +
            boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br))
    ForceBesovRegularity Q t H ∧
      scaleNormalizedPositiveBesovVectorNormTwo Q t H ≤ P := by
  dsimp only
  let H : Vec d → Vec d := fun x ↦ u.toFun x • xi x
  let Gs : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let C : ℝ := fullVectorPoincareCubeConstant Q
  let Br : ℝ := cubeBesovScaleWeight (-(1 - t)) Q *
    ((C * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Bcirc))
  let X₀ : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) u.toFun
  let Xc : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun)
  let P : ℝ := (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
    2 * (cubeScaleFactor Q * B * (Gs * X₀) +
      cubeLpNorm Q ∞ xi *
        (boundaryFiniteHeightHeadGlobalCoeff t height * Xc +
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br))
  have hu : MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hH : MemLp H (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    let : ENNReal.HolderTriple (2 : ℝ≥0∞) ∞ (2 : ℝ≥0∞) := by
      infer_instance
    simpa [H] using! hu.smul (p := (2 : ℝ≥0∞))
      (r := (2 : ℝ≥0∞)) hxiLp
  have hL2 : ∀ N : ℕ,
      cubeL2ScalarPartialSeminormTwo Q (t - 1) N u.toFun ≤ Gs * X₀ := by
    intro N
    simpa only [Gs, X₀] using
      cubeL2ScalarPartialSeminormTwo_le_geometric_mul_cubeLpNorm_two_of_neg
        Q (t - 1) N u.toFun hu (by linarith)
  have hpos : ∀ N : ℕ,
      cubeBesovPositiveScalarPartialSeminormTwo Q t N u.toFun ≤
        boundaryFiniteHeightHeadGlobalCoeff t height * Xc +
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br := by
    intro N
    simpa only [Xc, C, Br] using
      cubeBesovPositiveScalarPartialSeminormTwo_h1_uncentered_le_weightedFiniteHeight
        Q t N height u ht htHalf hBcirc hcirc
  have hpartial : ∀ N : ℕ,
      cubeBesovPositiveVectorPartialSeminormTwo Q t N H ≤
        2 * (cubeScaleFactor Q * B * (Gs * X₀) +
          cubeLpNorm Q ∞ xi *
            (boundaryFiniteHeightHeadGlobalCoeff t height * Xc +
              boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br)) := by
    intro N
    have hraw :=
      cubeBesovPositiveVectorPartialSeminormTwo_scalar_smul_le_cutoff_terms_of_contDiff_component_bound
        Q t N u.toFun xi hB hu hxiLp hxi hderiv
    have h₁ := mul_le_mul_of_nonneg_left (hL2 N)
      (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
    have h₂ := mul_le_mul_of_nonneg_left (hpos N) (cubeLpNorm_nonneg Q ∞ xi)
    simpa only [H] using
      hraw.trans (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by norm_num))
  have hreg : ForceBesovRegularity Q t H := by
    refine ⟨hH, ?_⟩
    exact ⟨_, by rintro _ ⟨N, rfl⟩; exact hpartial N⟩
  have hsemi := cubeBesovPositiveVectorSeminormTwo_le_of_partialBound Q t H hpartial
  have havgNorm : ‖cubeAverageVec Q H‖ ≤ cubeLpNorm Q ∞ xi * X₀ := by
    simpa [H, X₀] using
      norm_cubeAverageVec_scalar_smul_le_cubeLpNorm_infty_mul_cubeLpNorm_two
        Q u.toFun xi hu hxiLp
  have havgEuclidean : Real.sqrt (vecNormSq (cubeAverageVec Q H)) ≤
      (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ := by
    calc
      Real.sqrt (vecNormSq (cubeAverageVec Q H)) = euclideanNorm (cubeAverageVec Q H) := rfl
      _ ≤ (d : ℝ) * ‖cubeAverageVec Q H‖ := euclideanNorm_le_dimension_mul_norm _
      _ ≤ (d : ℝ) * (cubeLpNorm Q ∞ xi * X₀) :=
        mul_le_mul_of_nonneg_left havgNorm (by positivity)
      _ = _ := by ring
  refine ⟨hreg, ?_⟩
  unfold scaleNormalizedPositiveBesovVectorNormTwo
  exact add_le_add havgEuclidean hsemi

/-- Support-free corrected-flux pairing with the uncentered finite-height
product budget substituted.  This is the analytic local-cell theorem that
can be summed over descendants meeting a parent annular cutoff. -/
theorem exists_abs_boundaryCorrectedFluxDensity_weightedFiniteHeight_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        {Q : TriadicCube d} {t : ℝ} {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (w : H1Function (openCubeSet Q))
        {eta : Vec d → ℝ} {B Bcirc : ℝ} (height : ℕ),
        0 < t → t < 1 / 2 →
        ForceBesovRegularity Q t (fun x ↦ -g₀ x) →
        0 ≤ B → 0 ≤ Bcirc →
        MemLp (scalarCutoffGradientField (fun y ↦ eta y ^ 2)) ∞
          (normalizedCubeMeasure Q) →
        (∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
          (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i)) →
        (∀ i : Fin d, ∀ z ∈ cubeSet Q,
          ‖fderiv ℝ
              (fun x ↦ scalarCutoffGradientField (fun y ↦ eta y ^ 2) x i) z‖ ≤ B) →
        (∀ i : Fin d, ∀ N : ℕ,
          cubeBesovCircPartialNorm Q t (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
            (fun x ↦ w.grad x i) ≤ Bcirc) →
        let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
        let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
        let Cfull := fullVectorPoincareCubeConstant Q
        let Br := cubeBesovScaleWeight (-(1 - t)) Q *
          ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((Fintype.card (Fin d) : ℝ) * Bcirc))
        let X₀ := cubeLpNorm Q (2 : ℝ≥0∞) w.toFun
        let Xc := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
        let P := (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
          2 * (cubeScaleFactor Q * B * (Gs * X₀) +
            cubeLpNorm Q ∞ xi *
              (boundaryFiniteHeightHeadGlobalCoeff t height * Xc +
                boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br))
        |cubeAverage Q
            (boundaryCorrectedFluxCutoffPairingDensity
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta
              w.toFun u.toH1.grad g₀)| ≤
          C *
              (weakFluxWithRHSRHS C Q (aCutoffFamily M L omega) t
                  (fun x ↦ -g₀ x) u +
                boundaryNegativeToL2Factor (2 * t) *
                  boundaryNormalizedEuclideanL2 Q (fun x ↦ -g₀ x)) * P := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_abs_boundaryCorrectedFluxDensity_le_weakFlux_mul_positiveBesov d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q t g₀ u w eta B Bcirc height ht htHalf hg hB hBcirc
    hxiLp hxi hderiv hcirc
  dsimp only
  let xi := scalarCutoffGradientField (fun y ↦ eta y ^ 2)
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Cfull := fullVectorPoincareCubeConstant Q
  let Br := cubeBesovScaleWeight (-(1 - t)) Q *
    ((Cfull * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((Fintype.card (Fin d) : ℝ) * Bcirc))
  let X₀ := cubeLpNorm Q (2 : ℝ≥0∞) w.toFun
  let Xc := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q w.toFun)
  let P := (d : ℝ) * cubeLpNorm Q ∞ xi * X₀ +
    2 * (cubeScaleFactor Q * B * (Gs * X₀) +
      cubeLpNorm Q ∞ xi *
        (boundaryFiniteHeightHeadGlobalCoeff t height * Xc +
          boundaryFiniteHeightTailBetweenGlobalCoeff t (1 - t) height * Br))
  have hproduct :=
    uncenteredH1CutoffProduct_positiveBesovWeightedFiniteHeightBudget
      (Q := Q) (t := t) w xi height ht htHalf hB hBcirc hxiLp hxi hderiv hcirc
  have hreg : ForceBesovRegularity Q t (fun x ↦ w.toFun x • xi x) := by
    simpa only [xi] using hproduct.1
  have hnorm : scaleNormalizedPositiveBesovVectorNormTwo Q t
      (fun x ↦ w.toFun x • xi x) ≤ P := by
    simpa only [xi, Gs, Cfull, Br, X₀, Xc, P] using hproduct.2
  have hP : 0 ≤ P := by
    have hGs : 0 ≤ Gs := Real.sqrt_nonneg _
    have hX₀ : 0 ≤ X₀ := cubeLpNorm_nonneg Q 2 _
    have hXc : 0 ≤ Xc := cubeLpNorm_nonneg Q 2 _
    have hxiNorm : 0 ≤ cubeLpNorm Q ∞ xi := cubeLpNorm_nonneg Q ∞ xi
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
      (mul_nonneg (mul_nonneg (by positivity) hxiNorm) hX₀)
      (mul_nonneg (by norm_num)
        (add_nonneg
          (mul_nonneg (mul_nonneg (cubeScaleFactor_nonneg Q) hB)
            (mul_nonneg hGs hX₀))
          (mul_nonneg hxiNorm
            (add_nonneg (mul_nonneg hhead hXc) (mul_nonneg htail hBr)))))
  have hraw := hpair M L omega u ht (by linarith) hg hreg hP hnorm rfl
  simpa only [xi, Gs, Cfull, Br, X₀, Xc, P] using hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
