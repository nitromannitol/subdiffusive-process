import SubdiffusiveProcess.CoarseGrainingVocab.PaperFractionalDualBridge
import Homogenization.Sobolev.Fractional.EuclideanWspSmoothDualFieldPairing

/-!
# Readout from the manuscript fractional dual

The manuscript uses an additive positive fractional norm, whereas the
completed-field pairing API is phrased with the power-aggregated norm.  This
file supplies the reverse dual comparison and then exposes the completed
pairing estimate directly in terms of the manuscript norm.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private theorem normalizedSmoothPairing_eq_zero_of_paperFullNorm_eq_zero
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p)
    (hh : paperFractionalFullNorm Q s p h.toField = 0) :
    cubeEuclideanNormalizedSmoothPairing F h = 0 := by
  have hscale :
      (ENNReal.ofReal (cubeScaleFactor Q)) ^ (-s.1) ≠ 0 := by
    exact ne_of_gt (ENNReal.rpow_pos
      (ENNReal.ofReal_pos.mpr (cubeScaleFactor_pos' Q)) ENNReal.ofReal_ne_top)
  have hLp :
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
          p.exponent h.toField = 0 := by
    rw [paperFractionalFullNorm, paperFractionalSeminorm] at hh
    have hterm := (add_eq_zero.mp hh).2
    exact (mul_eq_zero.mp hterm).resolve_left hscale
  have hLp' : eLpNorm (fun x ↦ euclideanNorm (h.toField x))
      p.exponent (normalizedCubeMeasure Q) = 0 := by
    rw [← cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    exact hLp
  have hmeas : AEStronglyMeasurable (fun x ↦ euclideanNorm (h.toField x))
      (normalizedCubeMeasure Q) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using
      (CubeEuclideanWspSmoothTest.euclideanMemLp_of_continuous Q
        p.exponent h.contDiff.continuous).1.norm
  have hp0 : p.exponent ≠ 0 := ne_of_gt (lt_trans zero_lt_one p.one_lt)
  have hnorm : (fun x ↦ euclideanNorm (h.toField x)) =ᵐ[
      normalizedCubeMeasure Q] 0 :=
    (eLpNorm_eq_zero_iff hmeas hp0).mp hLp'
  have hfield : h.toField =ᵐ[normalizedCubeMeasure Q] 0 := by
    filter_upwards [hnorm] with x hx
    exact euclideanNorm_eq_zero_iff.mp hx
  unfold cubeEuclideanNormalizedSmoothPairing
  apply integral_eq_zero_of_ae
  filter_upwards [hfield] with x hx
  simp [hx, vecDot]

/-- The power-norm smooth dual is controlled by twice the manuscript's
additive-norm dual.  The factor two is exactly the elementary comparison
between the two positive test norms. -/
theorem cubeEuclideanNegativeWspSmoothDualENorm_le_two_mul_paperNegativeFractionalDual
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    cubeEuclideanNegativeWspSmoothDualENorm Q s p F ≤
      2 * paperNegativeFractionalDual Q s p F := by
  rw [cubeEuclideanNegativeWspSmoothDualENorm]
  refine iSup_le fun h ↦ ?_
  let N : ℝ≥0∞ := paperFractionalFullNorm Q s p.conjugate h.1.toField
  let D : ℝ≥0∞ := paperNegativeFractionalDual Q s p F
  by_cases hN0 : N = 0
  · have hpair : cubeEuclideanNormalizedSmoothPairing F h.1 = 0 :=
      normalizedSmoothPairing_eq_zero_of_paperFullNorm_eq_zero
        Q s p.conjugate F h.1 (by simpa only [N] using hN0)
    simp [hpair]
  · have hNtop : N ≠ ∞ :=
      (paperFractionalFullNorm_lt_top_of_smooth h.1).ne
    let hp : {g : CubeEuclideanWspSmoothTest Q s p.conjugate //
        paperFractionalFullNorm Q s p.conjugate g.1 ≠ 0} := ⟨h.1, hN0⟩
    have hratio :
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1| / N ≤ D := by
      rw [show D = paperNegativeFractionalDual Q s p F by rfl,
        paperNegativeFractionalDual]
      exact le_iSup (fun g : {g : CubeEuclideanWspSmoothTest Q s p.conjugate //
        paperFractionalFullNorm Q s p.conjugate g.1 ≠ 0} ↦
          ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F g.1| /
            paperFractionalFullNorm Q s p.conjugate g.1.toField) hp
    have hpair :
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1| ≤ D * N := by
      exact (ENNReal.div_le_iff hN0 hNtop).mp hratio
    have hNle : N ≤ 2 := by
      calc
        N ≤ 2 * cubeEuclideanWspFullENorm Q s p.conjugate h.1.toField := by
          simpa only [N] using
            paperFractionalFullNorm_le_two_mul_cubeEuclideanWspFullENorm
              Q s p.conjugate h.1.toField
        _ ≤ 2 * 1 := mul_le_mul_right h.2 2
        _ = 2 := mul_one _
    calc
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1| ≤ D * N := hpair
      _ ≤ D * 2 := mul_le_mul_right hNle D
      _ = 2 * paperNegativeFractionalDual Q s p F := by
        simp only [D]
        ring

/-- Homogeneous pairing estimate for an arbitrary smooth manuscript test. -/
theorem ofReal_abs_normalizedSmoothPairing_le_paperNegativeFractionalDual_mul_fullNorm
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p.conjugate) :
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
      paperNegativeFractionalDual Q s p F *
        paperFractionalFullNorm Q s p.conjugate h.toField := by
  let N := paperFractionalFullNorm Q s p.conjugate h.toField
  let D := paperNegativeFractionalDual Q s p F
  by_cases hN0 : N = 0
  · have hpair := normalizedSmoothPairing_eq_zero_of_paperFullNorm_eq_zero
      Q s p.conjugate F h (by simpa only [N] using hN0)
    simp [hpair]
  · have hNtop : N ≠ ∞ :=
      (paperFractionalFullNorm_lt_top_of_smooth h).ne
    let hp : {g : CubeEuclideanWspSmoothTest Q s p.conjugate //
        paperFractionalFullNorm Q s p.conjugate g.1 ≠ 0} := ⟨h, hN0⟩
    have hratio :
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| / N ≤ D := by
      rw [show D = paperNegativeFractionalDual Q s p F by rfl,
        paperNegativeFractionalDual]
      exact le_iSup (fun g : {g : CubeEuclideanWspSmoothTest Q s p.conjugate //
        paperFractionalFullNorm Q s p.conjugate g.1 ≠ 0} ↦
          ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F g.1| /
            paperFractionalFullNorm Q s p.conjugate g.1.toField) hp
    simpa only [N, D] using (ENNReal.div_le_iff hN0 hNtop).mp hratio

/-- A completed fractional test field may be paired directly against a
field controlled in the manuscript negative dual, at the universal norm
comparison cost two. -/
theorem ofReal_abs_normalizedFieldPairing_le_two_mul_paperNegativeFractionalDual
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (G : CubeEuclideanWspL2Field Q s p.conjugate) :
    ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G| ≤
      2 * paperNegativeFractionalDual Q s p F *
        cubeEuclideanWspFullENorm Q s p.conjugate G.toField := by
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G| ≤
        cubeEuclideanNegativeWspSmoothDualENorm Q s p F *
          cubeEuclideanWspFullENorm Q s p.conjugate G.toField :=
      ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le F G
    _ ≤ (2 * paperNegativeFractionalDual Q s p F) *
          cubeEuclideanWspFullENorm Q s p.conjugate G.toField := by
      simpa only [mul_comm] using
        mul_le_mul_right
          (cubeEuclideanNegativeWspSmoothDualENorm_le_two_mul_paperNegativeFractionalDual
            Q s p F)
          (cubeEuclideanWspFullENorm Q s p.conjugate G.toField)
    _ = _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
