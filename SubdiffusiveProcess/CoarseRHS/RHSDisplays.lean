module

public import SubdiffusiveProcess.CoarseRHS.RHSScalar
public import SubdiffusiveProcess.CoarseRHS.RHSBridge2

@[expose] public section

/-!
# The gradient and flux displays of `l.coarse.graining.RHS`, in the paper's normalization

`Ch03.coarsePoincareRHSTheory` and `Ch03.weakFluxRHSTheory` (CoarseGraining, the formalization of
[ASD, Lemma 2.11]) bound the library negative Besov seminorms of `∇u` and `a ∇u`.  The paper's
seminorm is `s ^ (1 / 2)` times the library's and its forcing seminorm is `s ^ (1 / 2)` times the
library's Gagliardo seminorm; the library bounds have powers `s ^ (-3/2), s ^ (-3)` (gradient) and
`s ^ (-1), s ^ (-5/2)` (flux), so the conversion is absorbed into the printed powers
`s ^ (-3/2), s ^ (-3)` and `s ^ (-3/2), s ^ (-9/2)`.
-/

namespace SubdiffusiveProcess.CoarseRHS

open Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec Mat TriadicCube

theorem forceBesov_neg {d : ℕ} [NeZero d] {Q : Homogenization.TriadicCube d} (s : FractionalOrder)
    (G : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    Ch03.ForceBesovRegularity Q s.1 (fun x => -G.toField x) :=
  Ch03.Legacy.ForceSobolevRegularity.toForceBesovRegularity
    (cubeEuclideanWspField_forceSobolevRegularity s (negCubeEuclideanWspField G)) s.2.1 s.2.2.le

/-- The library forcing seminorm of `-g` in terms of the paper seminorm of `g`. -/
theorem besovNeg_le {d : ℕ} [NeZero d] {Q : Homogenization.TriadicCube d} (s : FractionalOrder)
    (G : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s.1 (fun x => -G.toField x) ≤
      caccioppoliExactDatumConstant d * Real.rpow (cubeScaleFactor Q) s.1 *
        (cubeEuclideanWspESeminorm Q s FiniteLpExponent.two G.toField).toReal := by
  have := besovPos_le_datum_general d Q s (negCubeEuclideanWspField G)
  simpa only [negCubeEuclideanWspField_toField, cubeEuclideanWspESeminorm_neg] using this

theorem lambdaSq_two_pos {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {t : ℝ} (ht : 0 < t) :
    0 < Ch02.lambdaSq Q t (.finite 2) a :=
  Ch02.lambdaSq_pos Q a ht (by simp)

theorem LambdaSq_two_pos {d : ℕ} [NeZero d] (Q : Homogenization.TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) {t : ℝ} (ht : 0 < t) :
    0 < Ch02.LambdaSq Q t (.finite 2) a :=
  Ch02.LambdaSq_pos Q a ht (by simp)

/-- The gradient and flux displays, uniformly in the cube. -/
theorem coarsePoincare_flux_general (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Homogenization.TriadicCube d) (sF : FractionalOrder)
      (a : Ch02.TriadicCoeffFamily d)
      (G : CubeEuclideanWspField Q sF FiniteLpExponent.two)
      (u : H1Function (openCubeSet Q)),
      Ch03.ABK26.IsForcedEquation Q (a.coeffOn Q) u G.toField →
        (paperScaleNormalizedNegativeBesovVectorNorm Q sF.1 (.finite 2) u.grad ≤
          C * Real.rpow sF.1 (-(3 / 2 : ℝ)) *
              Real.rpow (lambda Q (sF.1 / 2) (.finite 2) a) (-(1 / 2 : ℝ)) *
              coefficientEnergyNorm Q a u.grad +
            C * Real.rpow sF.1 (-3 : ℝ) * (lambda Q (sF.1 / 2) (.finite 2) a)⁻¹ *
              (Real.rpow (cubeScaleFactor Q) sF.1 *
                (paperFractionalSeminorm Q sF FiniteLpExponent.two G.toField).toReal)) ∧
        (paperScaleNormalizedNegativeBesovVectorNorm Q sF.1 (.finite 2)
            (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) ≤
          C * Real.rpow sF.1 (-(3 / 2 : ℝ)) *
              Real.rpow (Lambda Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ) *
              coefficientEnergyNorm Q a u.grad +
            C * Real.rpow sF.1 (-(9 / 2 : ℝ)) *
              (Real.rpow (Lambda Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ) /
                Real.rpow (lambda Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ)) *
              (Real.rpow (cubeScaleFactor Q) sF.1 *
                (paperFractionalSeminorm Q sF FiniteLpExponent.two G.toField).toReal)) := by
  obtain ⟨Cp, hCp, hgrad, -⟩ := (Ch03.coarsePoincareRHSTheory (d := d)).exists_constant
  obtain ⟨Cw, hCw, hflux⟩ := (Ch03.weakFluxRHSTheory (d := d)).exists_constant
  let Kd : ℝ := caccioppoliExactDatumConstant d
  have hKd : 0 < Kd := caccioppoliExactDatumConstant_pos d
  refine ⟨(Cp + Cw) * (1 + Kd), by positivity, ?_⟩
  intro Q sF a G u hu
  have hs0 : 0 < sF.1 := sF.2.1
  have hs1 : sF.1 < 1 := sF.2.2
  have hs2 : 0 < sF.1 / 2 := by linarith
  let u' : Ch03.ForcedCubeSolution Q a (fun x => -G.toField x) := ⟨u, isForced_neg hu⟩
  have hreg := forceBesov_neg sF G
  have hE : Ch03.forcedSolutionEnergyNorm Q a u' = coefficientEnergyNorm Q a u.grad :=
    h1Energy_eq Q a u
  have hEnn : 0 ≤ coefficientEnergyNorm Q a u.grad := Real.sqrt_nonneg _
  have hBnn : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1
      (fun x => -G.toField x) :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hreg
  have hB := besovNeg_le sF G
  have hSnn : 0 ≤ (cubeEuclideanWspESeminorm Q sF FiniteLpExponent.two G.toField).toReal :=
    ENNReal.toReal_nonneg
  have hPS := paperSem_toReal Q sF G.toField
  have hcf : (0 : ℝ) < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  have hW : 0 ≤ Real.rpow (cubeScaleFactor Q) sF.1 := (Real.rpow_pos_of_pos hcf _).le
  have hL := lambdaSq_two_pos Q a hs2
  have hLam := LambdaSq_two_pos Q a hs2
  have hLinv : Real.rpow (Ch02.lambdaSq Q (sF.1 / 2) (.finite 2) a) (-1 : ℝ) =
      (Ch02.lambdaSq Q (sF.1 / 2) (.finite 2) a)⁻¹ := by simp [Real.rpow_neg_one]
  have hscale' : ∀ F : Homogenization.Vec d → Homogenization.Vec d,
      paperScaleNormalizedNegativeBesovVectorNorm Q sF.1 (.finite 2) F =
        Real.rpow sF.1 (1 / 2 : ℝ) *
          Ch03.scaleNormalizedNegativeBesovVectorNorm Q sF.1 (.finite 2) F :=
    fun F => rfl
  constructor
  · -- gradient display
    have hN := hgrad u' hs0 hs1 hreg
    simp only [Ch03.coarsePoincareWithRHSGradientRHS, hE, hLinv] at hN
    rw [hscale']
    have := scalar_grad (s := sF.1) (hs := hs0) (hs1 := hs1) (hCp := hCp.le) (hKd := hKd.le)
      (hlf := Real.rpow_nonneg hL.le _) (hE := hEnn) (hL := hL) (hW := hW) (hS0 := hSnn)
      (hN := hN) (hB := hB) (hS := hPS)
    refine this.trans ?_
    have hC : Cp * (1 + Kd) ≤ (Cp + Cw) * (1 + Kd) := by nlinarith
    have hL1 : 0 ≤ Ch03.poincareLowerEllipticityFactor Q a (sF.1 / 2) (.finite 2) :=
      Real.rpow_nonneg hL.le _
    have hp32 : 0 ≤ Real.rpow sF.1 (-(3 / 2 : ℝ)) := (Real.rpow_pos_of_pos hs0 _).le
    have hp3 : 0 ≤ Real.rpow sF.1 (-3 : ℝ) := (Real.rpow_pos_of_pos hs0 _).le
    have hLi : 0 ≤ (Ch02.lambdaSq Q (sF.1 / 2) (.finite 2) a)⁻¹ := inv_nonneg.mpr hL.le
    have hWP : 0 ≤ Real.rpow (cubeScaleFactor Q) sF.1 *
        (paperFractionalSeminorm Q sF FiniteLpExponent.two G.toField).toReal :=
      mul_nonneg hW ENNReal.toReal_nonneg
    change _ ≤ (Cp + Cw) * (1 + Kd) * Real.rpow sF.1 (-(3 / 2 : ℝ)) *
        Ch03.poincareLowerEllipticityFactor Q a (sF.1 / 2) (.finite 2) *
          coefficientEnergyNorm Q a u.grad +
      (Cp + Cw) * (1 + Kd) * Real.rpow sF.1 (-3 : ℝ) *
        (Ch02.lambdaSq Q (sF.1 / 2) (.finite 2) a)⁻¹ *
        (Real.rpow (cubeScaleFactor Q) sF.1 *
          (paperFractionalSeminorm Q sF FiniteLpExponent.two G.toField).toReal)
    gcongr
    exact le_rfl
  · -- flux display
    have hN := hflux u' hs0 hs1 hreg
    have hN' : Ch03.scaleNormalizedNegativeBesovVectorNorm Q sF.1 (.finite 2)
        (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) ≤
        Cw * (sF.1)⁻¹ * Real.rpow (Ch02.LambdaSq Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ) *
            coefficientEnergyNorm Q a u.grad +
          Cw * Real.rpow sF.1 (-(5 / 2 : ℝ)) *
            Real.rpow (Ch02.LambdaSq Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ) *
            Real.rpow (Ch02.lambdaSq Q (sF.1 / 2) (.finite 2) a) (-(1 / 2 : ℝ)) *
            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1
              (fun x => -G.toField x) := by
      have h := hN
      simp only [Ch03.weakFluxWithRHSRHS, hE] at h
      exact h
    rw [hscale']
    have hlf : Real.rpow (Ch02.lambdaSq Q (sF.1 / 2) (.finite 2) a) (-(1 / 2 : ℝ)) =
        (Real.rpow (Ch02.lambdaSq Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ))⁻¹ := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_neg hL.le]
    have := scalar_flux (s := sF.1) (hs := hs0) (hs1 := hs1) (hCw := hCw.le) (hKd := hKd.le)
      (hlf := (Real.rpow_nonneg hL.le _)) (hU := Real.rpow_nonneg hLam.le _) (hE := hEnn)
      (hW := hW) (hS0 := hSnn) (hB0 := hBnn) (hN := hN') (hB := hB) (hS := hPS)
    refine this.trans ?_
    simp only [Real.rpow_eq_pow] at hlf ⊢
    rw [hlf, ← div_eq_mul_inv]
    have hC : Cw * (1 + Kd) ≤ (Cp + Cw) * (1 + Kd) := by nlinarith
    have hU : 0 ≤ (Ch02.LambdaSq Q (sF.1 / 2) (.finite 2) a) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg hLam.le _
    have hlp : 0 ≤ (Ch02.lambdaSq Q (sF.1 / 2) (.finite 2) a) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg hL.le _
    have hp32 : 0 ≤ sF.1 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
    have hp92 : 0 ≤ sF.1 ^ (-(9 / 2 : ℝ)) := Real.rpow_nonneg hs0.le _
    have hWP : 0 ≤ (cubeScaleFactor Q) ^ sF.1 *
        (paperFractionalSeminorm Q sF FiniteLpExponent.two G.toField).toReal :=
      mul_nonneg (Real.rpow_nonneg hcf.le _) ENNReal.toReal_nonneg
    exact coeff_mono hC hp32 hU hEnn hp92 (div_nonneg hU hlp) hWP

end SubdiffusiveProcess.CoarseRHS
