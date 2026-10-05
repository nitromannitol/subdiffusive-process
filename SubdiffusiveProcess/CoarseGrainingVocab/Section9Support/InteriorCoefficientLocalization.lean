module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicScaledContrast
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedPathDiscretizationGeometry

@[expose] public section

/-!
# Localization of the smooth factor in the coefficient

The unit-cube derivative input controls `log b` throughout the ambient cube.
On a sufficiently small interior cube, normalizing `b theta` by `b(z)` puts
it in `[1/4,4]`. Thus the local ratio is at most sixteen, independent of all
data. The factor `theta` is never differentiated.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Unit-cube supremum control gives a pointwise gradient bound on the
ambient domain, using only the global `C¹` regularity of the positive factor. -/
theorem interior_log_gradient_le_of_unit_control {d : ℕ} {U : Set (Vec d)}
    {b : Vec d → ℝ} (hb0 : ∀ x, 0 < b x) (hb : ContDiff ℝ 1 b)
    {G : ℝ} (hG : 0 ≤ G)
    (hcontrol : ∀ y, (centeredAxisCube y 1 ∩ U).Nonempty →
      supNormOn (centeredAxisCube y 2)
        (fun x => euclideanNorm (euclideanGradient (fun w => Real.log (b w)) x)) ^ 2 ≤ G ^ 2) :
    ∀ x ∈ U, euclideanNorm (euclideanGradient (fun w => Real.log (b w)) x) ≤ G := by
  have hlog : ContDiff ℝ 1 (fun w => Real.log (b w)) := hb.log fun x => (hb0 x).ne'
  let g := fun x => euclideanNorm (euclideanGradient (fun w => Real.log (b w)) x)
  have hg : Continuous g := by
    change Continuous (fun x => Real.sqrt (vecNormSq (euclideanGradient (fun w => Real.log (b w)) x)))
    apply Continuous.sqrt
    simp only [vecNormSq, vecDot]
    apply continuous_finsetSum
    intro i _
    have hi : Continuous (fun x => euclideanGradient (fun w => Real.log (b w)) x i) :=
      (hlog.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact hi.mul hi
  intro x hx
  have hx1 : x ∈ centeredAxisCube x 1 := self_mem_centeredAxisCube (by norm_num)
  have hx2 : x ∈ centeredAxisCube x 2 := self_mem_centeredAxisCube (by norm_num)
  have hsq := hcontrol x ⟨x, hx1, hx⟩
  have hbounded : Bornology.IsBounded (centeredAxisCube x 2) :=
    Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _
  obtain ⟨M, hM⟩ := hbounded.isCompact_closure.exists_bound_of_continuousOn hg.continuousOn
  have hsup : g x ≤ supNormOn (centeredAxisCube x 2) g := by
    have hbd : BddAbove {r : ℝ | ∃ y ∈ centeredAxisCube x 2, r = |g y|} := by
      refine ⟨M, ?_⟩
      rintro r ⟨y, hy, rfl⟩
      simpa only [Real.norm_eq_abs] using hM y (subset_closure hy)
    exact (le_abs_self _).trans (le_csSup hbd ⟨x, hx2, rfl⟩)
  have hsup0 : 0 ≤ supNormOn (centeredAxisCube x 2) g :=
    (euclideanNorm_nonneg _).trans hsup
  exact hsup.trans ((sq_le_sq₀ hsup0 hG).mp hsq)



theorem interior_log_gradient_le_of_frozen_input {d : ℕ} {zQ : Vec d} {L A C0 : ℝ}
    (hL : 0 < L) (hA : 2 ≤ A) (hC0 : 1 ≤ C0)
    {b : Vec d → ℝ} (hb0 : ∀ x, 0 < b x) (hb : ContDiff ℝ 1 b)
    (hcontrol : ∀ y, (centeredAxisCube y 1 ∩ centeredAxisCube zQ L).Nonempty →
      supNormOn (centeredAxisCube y 2)
        (fun x => euclideanNorm (euclideanGradient (fun w => Real.log (b w)) x)) ^ 2 ≤
          C0 * (Real.log A + Real.log (2 + L))) :
    ∀ x ∈ centeredAxisCube zQ L,
      euclideanNorm (euclideanGradient (fun w => Real.log (b w)) x) ≤
        Real.sqrt (C0 * (Real.log A + Real.log (2 + L))) := by
  have hnonneg : 0 ≤ C0 * (Real.log A + Real.log (2 + L)) :=
    mul_nonneg (by linarith) (add_nonneg (Real.log_nonneg (by linarith))
      (Real.log_nonneg (by linarith)))
  apply interior_log_gradient_le_of_unit_control hb0 hb (Real.sqrt_nonneg _)
  simpa only [Real.sq_sqrt hnonneg] using hcontrol

/-- A gradient bound on a convex set controls the logarithmic coefficient
ratio with the explicit norm-conversion factor `sqrt d`. -/
theorem interior_log_lipschitz {d : ℕ} {U : Set (Vec d)} (hU : Convex ℝ U)
    {b : Vec d → ℝ} (hb0 : ∀ x, 0 < b x) (hb : ContDiff ℝ 1 b)
    {G : ℝ} (hgrad : ∀ x ∈ U, euclideanNorm (euclideanGradient (fun w => Real.log (b w)) x) ≤ G)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    |Real.log (b y) - Real.log (b x)| ≤ Real.sqrt d * G * ‖y - x‖ := by
  have hlog : ContDiff ℝ 1 (fun w => Real.log (b w)) := hb.log fun z => (hb0 z).ne'
  have hder : ∀ z ∈ U, ‖fderiv ℝ (fun w => Real.log (b w)) z‖ ≤ Real.sqrt d * G := by
    intro z hz
    exact (WeightedLocalHarmonic.norm_fderiv_le_sqrt_card_mul_euclideanNorm _ z).trans
      (mul_le_mul_of_nonneg_left (hgrad z hz) (Real.sqrt_nonneg _))
  simpa only [Real.norm_eq_abs] using hU.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hlog.differentiable (by norm_num) z) hder hx hy

/-- Normalization on a cube where the logarithm changes by at most `log 2`
gives a fixed ellipticity band for the full measurable coefficient. -/
theorem interior_normalized_coefficient_band {d : ℕ} {U : Set (Vec d)}
    {b theta : Vec d → ℝ} (hb0 : ∀ x, 0 < b x)
    (htheta : ∀ x, 1 / 2 ≤ theta x ∧ theta x ≤ 2) {z : Vec d}
    (hlog : ∀ x ∈ U, |Real.log (b x) - Real.log (b z)| ≤ Real.log 2) :
    ∀ x ∈ U, 1 / 4 ≤ (b x * theta x) / b z ∧ (b x * theta x) / b z ≤ 4 := by
  intro x hx
  have hratio : b x / b z = Real.exp (Real.log (b x) - Real.log (b z)) := by
    rw [Real.exp_sub, Real.exp_log (hb0 x), Real.exp_log (hb0 z)]
  have hlow : 1 / 2 ≤ b x / b z := by
    rw [hratio]
    have h := Real.exp_le_exp.mpr (abs_le.mp (hlog x hx)).1
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using h
  have hhigh : b x / b z ≤ 2 := by
    rw [hratio]
    have h := Real.exp_le_exp.mpr (abs_le.mp (hlog x hx)).2
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
  have htheta0 : 0 ≤ theta x := by linarith [(htheta x).1]
  have hprodlo := mul_le_mul hlow (htheta x).1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by positivity : 0 ≤ b x / b z)
  have hprodhi := mul_le_mul hhigh (htheta x).2 htheta0 (by norm_num : (0 : ℝ) ≤ 2)
  constructor <;> nlinarith [show b x * theta x / b z = (b x / b z) * theta x by ring]

/-- On a cube of side at most `log 2 / (1 + sqrt d * G)`, the normalized
coefficient has a fixed dimensional band. This is the actual localization
scale, not a small-contrast hypothesis on the measurable factor. -/
theorem interior_normalized_coefficient_on_small_cube {d : ℕ} {U : Set (Vec d)}
    (hU : Convex ℝ U) {b theta : Vec d → ℝ}
    (hb0 : ∀ x, 0 < b x) (hb : ContDiff ℝ 1 b)
    (htheta : ∀ x, 1 / 2 ≤ theta x ∧ theta x ≤ 2)
    {G : ℝ} (hG : 0 ≤ G)
    (hgrad : ∀ x ∈ U, euclideanNorm (euclideanGradient (fun w => Real.log (b w)) x) ≤ G)
    {z : Vec d} {r : ℝ} (hr : 0 < r)
    (hsmall : r ≤ Real.log 2 / (1 + Real.sqrt d * G))
    (hsub : centeredAxisCube z r ⊆ U) :
    ∀ x ∈ centeredAxisCube z r,
      1 / 4 ≤ (b x * theta x) / b z ∧ (b x * theta x) / b z ≤ 4 := by
  apply interior_normalized_coefficient_band hb0 htheta
  intro x hx
  have hz : z ∈ U := hsub (self_mem_centeredAxisCube hr)
  have hdist : ‖x - z‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg hr.le).mpr
    intro i
    have hi := mem_centeredAxisCube.mp hx i
    change |x i - z i| ≤ r
    linarith
  have hG0 : 0 ≤ Real.sqrt d * G := mul_nonneg (Real.sqrt_nonneg _) hG
  have hprice : Real.sqrt d * G * r ≤ Real.log 2 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 1 + Real.sqrt d * G)).mp hsmall
    nlinarith
  exact (interior_log_lipschitz hU hb0 hb hgrad hz (hsub hx)).trans
    ((mul_le_mul_of_nonneg_left hdist hG0).trans hprice)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
