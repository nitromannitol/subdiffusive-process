module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.OscillationPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryArbitraryH1Circ

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open Homogenization Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The dimension-only constant of the coarse-grained `L²` Poincare
inequality: the detachment constant of
`oscillationMultiscalePoincareConstant`, one factor `d` for the coordinate
sum, the `q = 1` geometric discount `(1 - 3^{-1})⁻¹` and one further factor
`d` from the componentwise multiscale gradient bound. -/
def coarseL2PoincareConst (d : ℕ) [NeZero d] : ℝ :=
  oscillationMultiscalePoincareConstant d *
    ((d : ℝ) * ((geometricDiscount 1 1)⁻¹ * (d : ℝ)))

theorem coarseL2PoincareConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ coarseL2PoincareConst d := by
  have hgd : 0 < geometricDiscount 1 1 := geometricDiscount_pos (by norm_num)
  have := oscillationMultiscalePoincareConstant_nonneg d
  unfold coarseL2PoincareConst
  positivity

omit [NeZero d] in
private theorem cubeBesovScaleWeight_neg_one (Q : TriadicCube d) :
    cubeBesovScaleWeight (-1) Q = cubeScaleFactor Q := by
  have hpos : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  unfold cubeBesovScaleWeight
  norm_num



theorem aCutoff_cubeFluctuation_lpNorm_le_of_lambdaSCap
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    {t sigma K : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hcap : (Ch02.lambdaS Q t (aCutoffFamily M L omega))⁻¹ ≤ K * sigma⁻¹) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u.toFun) ≤
      coarseL2PoincareConst d * Real.sqrt (K * sigma⁻¹) * cubeScaleFactor Q *
        Real.sqrt (cubeAverage Q
          (coefficientEnergyDensity
            (publicCoeffField Q (aCutoffFamily M L omega)) u.grad)) := by
  classical
  set A := aCutoffFamily M L omega with hA
  set E : ℝ := Real.sqrt (cubeAverage Q
    (coefficientEnergyDensity (publicCoeffField Q A) u.grad)) with hE
  set Bnd : ℝ :=
    (cubeScaleFactor Q *
      ((geometricDiscount 1 1)⁻¹ * ((d : ℝ) * Real.sqrt (K * sigma⁻¹)))) * E
    with hBnd
  have hcirc : ∀ i : Fin d,
      cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) ≤ Bnd := by
    intro i
    refine cubeBesovCircNorm_le_of_forall_partialNorm_le Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
      (fun x => u.grad x i) (by simp) ?_
    intro N
    have hraw := aCutoff_h1Gradient_circPartialNorm_le_of_lambdaSCap
      M L omega Q u (t := t) (r := 1) (sigma := sigma) (K := K) ht ht1 hcap i N
    simpa only [hA, hE, hBnd, cubeBesovScaleWeight_neg_one] using hraw
  have hsum :
      ∑ i : Fin d, cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x i) ≤ (d : ℝ) * Bnd := by
    calc
      ∑ i : Fin d, cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)
          ≤ ∑ _i : Fin d, Bnd := Finset.sum_le_sum fun i _ => hcirc i
      _ = (d : ℝ) * Bnd := by simp
  have hosc :=
    cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm
      Q u
  have hoscConst : 0 ≤ oscillationMultiscalePoincareConstant d :=
    oscillationMultiscalePoincareConstant_nonneg d
  have hfinal :
      cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x) ≤
        oscillationMultiscalePoincareConstant d * ((d : ℝ) * Bnd) :=
    hosc.trans (mul_le_mul_of_nonneg_left hsum hoscConst)
  have hcalc :
      oscillationMultiscalePoincareConstant d * ((d : ℝ) * Bnd) =
        coarseL2PoincareConst d * Real.sqrt (K * sigma⁻¹) * cubeScaleFactor Q * E := by
    unfold coarseL2PoincareConst
    rw [hBnd]
    ring
  rw [hcalc] at hfinal
  simpa only [cubeBesovOscillation, hE] using hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
