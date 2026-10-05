module

public import SubdiffusiveProcess.CoarseRHS.RHSBridge

@[expose] public section

/-!
# Datum norms in the paper normalization

Real-valued consequences, for a `CubeEuclideanWspField` datum `F` at the Hilbert exponent, of the
definition of the paper's additive full norm `paperFractionalFullNorm`: the seminorm is dominated by
the full norm, and the cube average, measured after the scale factor `3^{s m}`, is dominated by
`3^{s m}` times the full norm.
-/

namespace SubdiffusiveProcess.CoarseRHS

open Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec Mat TriadicCube

/-- The real seminorm is dominated by the real full norm. -/
theorem paperSem_le_full {d : ℕ} (Q : Homogenization.TriadicCube d) (s : FractionalOrder)
    (F : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    (paperFractionalSeminorm Q s FiniteLpExponent.two F.toField).toReal ≤
      (paperFractionalFullNorm Q s FiniteLpExponent.two F.toField).toReal := by
  refine ENNReal.toReal_mono (paperFull_finite Q s F) ?_
  exact le_self_add

/-- The cube average of a datum is dominated by `3^{s m}` times its paper full norm. -/
theorem avg_le_W_full (d : ℕ) [NeZero d] (Q : Homogenization.TriadicCube d) (s : FractionalOrder)
    (F : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    Real.sqrt (vecNormSq (cubeAverageVec Q F.toField)) ≤
      Real.rpow (cubeScaleFactor Q) s.1 *
        (paperFractionalFullNorm Q s FiniteLpExponent.two F.toField).toReal := by
  have hcf : (0 : ℝ) < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  let L2E : ℝ≥0∞ := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
    FiniteLpExponent.two.exponent F.toField
  have hL2E : L2E = eLpNorm (fun x => HilbertVec.ofVec (F.toField x)) 2 (normalizedCubeMeasure Q) := by
    simp only [L2E, cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec, eLpNorm_norm (fun x => HilbertVec.ofVec (F.toField x)) F.euclideanMemLp.aestronglyMeasurable]
    rfl
  have hL2top : L2E ≠ ⊤ := F.normalizedEuclideanLpENorm_lt_top.ne
  have hA0 := sqrt_vecNormSq_avg_le Q F.toField F.euclideanMemLp
  rw [← hL2E] at hA0
  have hA0' : Real.sqrt (vecNormSq (cubeAverageVec Q F.toField)) ≤ L2E.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hL2top).mp hA0
  have hfull : (paperFractionalFullNorm Q s FiniteLpExponent.two F.toField).toReal =
      (paperFractionalSeminorm Q s FiniteLpExponent.two F.toField).toReal +
        Real.rpow (cubeScaleFactor Q) (-s.1) * L2E.toReal := by
    unfold paperFractionalFullNorm
    have hsem : paperFractionalSeminorm Q s FiniteLpExponent.two F.toField ≠ ⊤ := by
      unfold paperFractionalSeminorm
      refine ENNReal.mul_ne_top ?_ F.eSeminorm_lt_top.ne
      exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    have hw : (ENNReal.ofReal (cubeScaleFactor Q)) ^ (-s.1) ≠ ⊤ := by
      rw [Ne, ENNReal.rpow_eq_top_iff]
      push Not
      refine ⟨fun h => absurd h ?_, fun h => absurd h ENNReal.ofReal_ne_top⟩
      exact (ENNReal.ofReal_pos.mpr hcf).ne'
    rw [ENNReal.toReal_add hsem (ENNReal.mul_ne_top hw hL2top), ENNReal.toReal_mul,
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hcf.le]
    rfl
  have hsem0 : 0 ≤ (paperFractionalSeminorm Q s FiniteLpExponent.two F.toField).toReal :=
    ENNReal.toReal_nonneg
  have hL0 : 0 ≤ L2E.toReal := ENNReal.toReal_nonneg
  have hcancel : Real.rpow (cubeScaleFactor Q) s.1 * Real.rpow (cubeScaleFactor Q) (-s.1) = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hcf]; simp
  have hW : 0 ≤ Real.rpow (cubeScaleFactor Q) s.1 := (Real.rpow_pos_of_pos hcf _).le
  calc Real.sqrt (vecNormSq (cubeAverageVec Q F.toField)) ≤ L2E.toReal := hA0'
    _ = Real.rpow (cubeScaleFactor Q) s.1 *
        (Real.rpow (cubeScaleFactor Q) (-s.1) * L2E.toReal) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ Real.rpow (cubeScaleFactor Q) s.1 *
        ((paperFractionalSeminorm Q s FiniteLpExponent.two F.toField).toReal +
          Real.rpow (cubeScaleFactor Q) (-s.1) * L2E.toReal) := by
        gcongr; linarith
    _ = _ := by rw [hfull]

/-- The cube average commutes with negation. -/
theorem cubeAverageVec_neg' {d : ℕ} (Q : Homogenization.TriadicCube d)
    (F : Homogenization.Vec d → Homogenization.Vec d) :
    cubeAverageVec Q (fun x => -F x) = -cubeAverageVec Q F := by
  funext i
  simp only [cubeAverageVec, Pi.neg_apply, cubeAverage_eq_integral_normalizedCubeMeasure,
    MeasureTheory.integral_neg]

end SubdiffusiveProcess.CoarseRHS
