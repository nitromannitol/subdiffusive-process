import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PaperDualReadout
import Homogenization.Book.Ch03.ABK26.FluxComparisonBridges




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- Subadditivity and homogeneity of the manuscript negative fractional dual.
The fields are kept bundled so that all local `L²` certificates remain
available to the coarse-graining API. -/
theorem paperNegativeFractionalDual_le_smul_add {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F G H : CubeEuclideanLpField Q FiniteLpExponent.two) (c : ℝ)
    (hG : G.toField = c • F.toField + H.toField) :
    paperNegativeFractionalDual Q s p G ≤
      ENNReal.ofReal |c| * paperNegativeFractionalDual Q s p F +
        paperNegativeFractionalDual Q s p H := by
  rw [paperNegativeFractionalDual]
  apply iSup_le
  rintro ⟨h, hh⟩
  let N := paperFractionalFullNorm Q s p.conjugate h.toField
  have hpair : cubeEuclideanNormalizedSmoothPairing G h =
      c * cubeEuclideanNormalizedSmoothPairing F h +
        cubeEuclideanNormalizedSmoothPairing H h := by
    unfold cubeEuclideanNormalizedSmoothPairing
    rw [hG]
    calc
      (∫ x, vecDot ((c • F.toField + H.toField) x) (h.toField x)
          ∂normalizedCubeMeasure Q) =
          ∫ x, (c * vecDot (F.toField x) (h.toField x) +
            vecDot (H.toField x) (h.toField x))
            ∂normalizedCubeMeasure Q := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [Pi.add_apply, Pi.smul_apply, vecDot_add_left,
          vecDot_smul_left]
      _ = c * ∫ x, vecDot (F.toField x) (h.toField x)
              ∂normalizedCubeMeasure Q +
            ∫ x, vecDot (H.toField x) (h.toField x)
              ∂normalizedCubeMeasure Q := by
        rw [integral_add
          ((cubeEuclideanNormalizedSmoothPairing_integrable F h).const_mul c)
          (cubeEuclideanNormalizedSmoothPairing_integrable H h),
          integral_const_mul]
  have hF : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| / N ≤
      paperNegativeFractionalDual Q s p F := by
    rw [paperNegativeFractionalDual]
    exact le_iSup (fun k : {k : CubeEuclideanWspSmoothTest Q s p.conjugate //
      paperFractionalFullNorm Q s p.conjugate k.toField ≠ 0} ↦
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F k.1| /
          paperFractionalFullNorm Q s p.conjugate k.1.toField) ⟨h, hh⟩
  have hH : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing H h| / N ≤
      paperNegativeFractionalDual Q s p H := by
    rw [paperNegativeFractionalDual]
    exact le_iSup (fun k : {k : CubeEuclideanWspSmoothTest Q s p.conjugate //
      paperFractionalFullNorm Q s p.conjugate k.toField ≠ 0} ↦
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing H k.1| /
          paperFractionalFullNorm Q s p.conjugate k.1.toField) ⟨h, hh⟩
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing G h| / N =
        ENNReal.ofReal |c * cubeEuclideanNormalizedSmoothPairing F h +
          cubeEuclideanNormalizedSmoothPairing H h| / N := by rw [hpair]
    _ ≤ (ENNReal.ofReal |c| *
          ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| +
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing H h|) / N := by
      gcongr
      calc
        ENNReal.ofReal |c * cubeEuclideanNormalizedSmoothPairing F h +
            cubeEuclideanNormalizedSmoothPairing H h| ≤
            ENNReal.ofReal (|c * cubeEuclideanNormalizedSmoothPairing F h| +
              |cubeEuclideanNormalizedSmoothPairing H h|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
        _ = ENNReal.ofReal |c| *
              ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| +
            ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing H h| := by
          rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), abs_mul,
            ENNReal.ofReal_mul (abs_nonneg _)]
    _ = ENNReal.ofReal |c| *
          (ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| / N) +
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing H h| / N := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ ENNReal.ofReal |c| * paperNegativeFractionalDual Q s p F +
        paperNegativeFractionalDual Q s p H := by
      exact add_le_add (mul_le_mul_right hF _) hH

/-- The local negative norm of the physical root flux is bounded by the exact
two-term left side exported by `general_coarse_graining`. -/
theorem paperNegativeFractionalDual_rootFluxDefect_le_comparison {d : ℕ}
    {m : ℤ}
    (a : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (u v : H1Function (openCubeSet (originCube d m)))
    (s : FractionalOrder) :
    paperNegativeFractionalDual (originCube d m) s FiniteLpExponent.two
        (centeredCubeRootFluxDefectL2Field m a alpha u) ≤
      ENNReal.ofReal alpha *
          paperNegativeFractionalDual (originCube d m) s FiniteLpExponent.two
            (centeredCubeGradientDifferenceL2Field m u v) +
        paperNegativeFractionalDual (originCube d m) s FiniteLpExponent.two
          (centeredCubeFluxDifferenceL2Field m a alpha u v) := by
  let gradNeg : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two :=
    { toField := fun x ↦ -(centeredCubeGradientDifferenceL2Field m u v).toField x
      euclideanMemLp := by
        simpa only [HilbertVec.ofVec, Pi.neg_apply] using
          (centeredCubeGradientDifferenceL2Field m u v).euclideanMemLp.neg }
  have hfield :
      (centeredCubeRootFluxDefectL2Field m a alpha u).toField =
        alpha • gradNeg.toField +
          (centeredCubeFluxDifferenceL2Field m a alpha u v).toField := by
    funext x
    simp only [gradNeg, Pi.add_apply, Pi.smul_apply,
      centeredCubeRootFluxDefectL2Field,
      centeredCubeGradientDifferenceL2Field,
      centeredCubeFluxDifferenceL2Field, sub_matVecMul,
      matVecMul_scalarMatrix]
    module
  have hraw := paperNegativeFractionalDual_le_smul_add
    (s := s) (p := FiniteLpExponent.two)
      gradNeg (centeredCubeRootFluxDefectL2Field m a alpha u)
      (centeredCubeFluxDifferenceL2Field m a alpha u v) alpha hfield
  let zeroField : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two :=
    { toField := fun _ ↦ 0
      euclideanMemLp := by simp }
  have hzero : paperNegativeFractionalDual (originCube d m) s
      FiniteLpExponent.two zeroField = 0 := by
    rw [paperNegativeFractionalDual]
    simp [cubeEuclideanNormalizedSmoothPairing, zeroField, vecDot]
  have hneg : paperNegativeFractionalDual (originCube d m) s
      FiniteLpExponent.two gradNeg =
      paperNegativeFractionalDual (originCube d m) s
        FiniteLpExponent.two (centeredCubeGradientDifferenceL2Field m u v) := by
    apply le_antisymm
    · refine (paperNegativeFractionalDual_le_smul_add
        (s := s) (p := FiniteLpExponent.two)
        (centeredCubeGradientDifferenceL2Field m u v) gradNeg
          zeroField (-1) ?_).trans ?_
      · funext x
        simp [gradNeg, zeroField]
      · rw [hzero]
        simp
    · refine (paperNegativeFractionalDual_le_smul_add
        (s := s) (p := FiniteLpExponent.two)
        gradNeg (centeredCubeGradientDifferenceL2Field m u v)
          zeroField (-1) ?_).trans ?_
      · funext x
        simp [gradNeg, zeroField]
      · rw [hzero]
        simp
  simpa only [hneg, abs_of_nonneg halpha] using hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
