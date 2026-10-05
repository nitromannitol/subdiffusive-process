module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.HarmonicAnchoredPoincare

@[expose] public section

/-!
# Square-integral Poincare estimates for logarithmic tests

The coordinate-sum cube inequality is read as a bound by the Euclidean
gradient energy, then combined with the half-measure anchoring lemma.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The centered square integral is controlled by gradient energy with a
constant depending only on the dimension. -/
theorem harmonic_centered_sq_le_gradient {d : ℕ} (z : Vec d) {R : ℝ} (hR : 0 < R)
    (u : H1Function (centeredAxisCube z R)) :
    (∫ x in centeredAxisCube z R,
      (u.toFun x - integralAverage (centeredAxisCube z R) u.toFun) ^ 2) ≤
      (unitMeanZeroPoincareConst d * (d : ℝ)) ^ 2 * R ^ 2 *
        ∫ x in centeredAxisCube z R, vecNormSq (u.grad x) := by
  let U := centeredAxisCube z R
  let : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_axisCube (fun i => z i - R / 2) R).isFiniteMeasure_restrict_volume
  let E : ℝ := ∫ x in U, vecNormSq (u.grad x)
  have hE : 0 ≤ E := integral_nonneg fun x => vecNormSq_nonneg _
  have hcoord (i : Fin d) : (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn U)).toReal ≤ Real.sqrt E := by
    have hi : (∫ x in U, (u.grad x i) ^ 2) ≤ E :=
      integral_mono_ae (u.gradMemL2 i).integrable_sq (integrableOn_vecNormSq_h1Grad u)
        (Eventually.of_forall fun x => WeakPoissonEquationOn.coord_sq_le_vecNormSq (u.grad x) i)
    rw [← toReal_eLpNorm_two_sq_eq_integral_sq (u.gradMemL2 i)] at hi
    calc
      (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn U)).toReal =
          Real.sqrt ((eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn U)).toReal ^ 2) :=
        (Real.sqrt_sq ENNReal.toReal_nonneg).symm
      _ ≤ Real.sqrt E := Real.sqrt_le_sqrt hi
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hcoord i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hP := (scaled_meanZero_poincare (fun i => z i - R / 2) hR u).trans
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg (unitMeanZeroPoincareConst_nonneg d) hR.le))
  have hsquare := (sq_le_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg (mul_nonneg (unitMeanZeroPoincareConst_nonneg d) hR.le)
      (mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg E)))).mpr hP
  change (eLpNorm u.subAverage.toFun 2 (volume.restrict (centeredAxisCube z R))).toReal ^ 2 ≤
    (unitMeanZeroPoincareConst d * R * ((d : ℝ) * Real.sqrt E)) ^ 2 at hsquare
  rw [toReal_eLpNorm_two_sq_eq_integral_sq u.subAverage.memL2] at hsquare
  have hright : (unitMeanZeroPoincareConst d * R * ((d : ℝ) * Real.sqrt E)) ^ 2 =
      (unitMeanZeroPoincareConst d * (d : ℝ)) ^ 2 * R ^ 2 * E := by
    simp only [mul_pow, Real.sq_sqrt hE]
    ring
  rw [hright] at hsquare
  simpa only [H1Function.subAverage_apply] using hsquare

/-- Anchoring a Sobolev function on half the cube removes its mean from
the Poincare estimate. -/
theorem harmonic_sq_le_gradient_of_half_measure {d : ℕ} (z : Vec d) {R : ℝ} (hR : 0 < R)
    (u : H1Function (centeredAxisCube z R)) {E : Set (Vec d)} {B : ℝ}
    (hhalf : (volume (centeredAxisCube z R)).toReal / 2 ≤
      ((volume.restrict (centeredAxisCube z R)) E).toReal)
    (hgood : ∀ᵐ x ∂(volume.restrict (centeredAxisCube z R)).restrict E, |u.toFun x| ≤ B) :
    (∫ x in centeredAxisCube z R, u.toFun x ^ 2) ≤
      10 * (unitMeanZeroPoincareConst d * (d : ℝ)) ^ 2 * R ^ 2 *
          (∫ x in centeredAxisCube z R, vecNormSq (u.grad x)) +
        8 * B ^ 2 * (volume (centeredAxisCube z R)).toReal := by
  let : IsFiniteMeasure (volumeMeasureOn (centeredAxisCube z R)) :=
    (isOpenBoundedConvexDomain_axisCube (fun i => z i - R / 2) R).isFiniteMeasure_restrict_volume
  have hhalf' : ((volume.restrict (centeredAxisCube z R)) Set.univ).toReal / 2 ≤
      ((volume.restrict (centeredAxisCube z R)) E).toReal := by
    simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using hhalf
  have h := harmonic_integral_sq_le_centered_of_half_measure
    (m := integralAverage (centeredAxisCube z R) u.toFun) u.memL2 hhalf' hgood
  have hP := harmonic_centered_sq_le_gradient z hR u
  simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at h
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
