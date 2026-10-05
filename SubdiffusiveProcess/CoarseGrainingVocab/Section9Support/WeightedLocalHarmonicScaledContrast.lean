module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicCoefficientControl
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicRadialContrast
@[expose] public section

/-!
# What the scaled coefficient control actually buys

`LogCoefficientControlOn a H B` bounds `size^2 |grad log a|^2` and `size^2 [grad log a]_Lip`
scale-invariantly, and never mentions `sup a / inf a`. The main theorem here shows it
nevertheless forces an ellipticity ratio bound **on each cube separately**:

    a x <= exp (sqrt d * sqrt H) * a y     for x, y in cubeSet B.

So the coefficient is uniformly elliptic at every scale, with a ratio depending only on
`d` and `H`, even when the ratio is unbounded across scales globally. That is the precise
sense in which "the ellipticity blows up" is a statement about the family and not about
any single cube, and it is what lets interior estimates close with constants depending on
`d` and `H` alone — matching the `exp (C * H)` constants the manuscript's displays carry.
-/

set_option autoImplicit false
open Homogenization hiding cubeSet
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support (mem_centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic

variable {d : ℕ}

/-- On `Vec d = Fin d → ℝ` (sup norm) the dual norm of a linear functional is the
`ℓ¹` norm of its coordinates. -/
theorem norm_clm_le_sum_basisVec (L : Vec d →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i : Fin d, ‖L (basisVec i)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) ?_
  intro x
  have hx : L x = ∑ i : Fin d, x i * L (basisVec i) := by
    calc L x = ∑ i : Fin d, x i • L (fun j => if i = j then 1 else 0) := by
          simpa using (LinearMap.pi_apply_eq_sum_univ (f := L.toLinearMap) x)
      _ = ∑ i : Fin d, x i • L (basisVec i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hfun : (fun j => if i = j then 1 else 0) = basisVec i := by
            funext j; simp [basisVec_apply, eq_comm]
          rw [hfun]
      _ = ∑ i : Fin d, x i * L (basisVec i) := by simp [smul_eq_mul]
  rw [hx]
  calc ‖∑ i : Fin d, x i * L (basisVec i)‖
      ≤ ∑ i : Fin d, ‖x i * L (basisVec i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin d, ‖x i‖ * ‖L (basisVec i)‖ := by simp [norm_mul]
    _ ≤ ∑ i : Fin d, ‖x‖ * ‖L (basisVec i)‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (norm_nonneg _)
    _ = (∑ i : Fin d, ‖L (basisVec i)‖) * ‖x‖ := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The operator norm of `fderiv` is controlled by `√d` times the Euclidean norm
of the gradient. -/
theorem norm_fderiv_le_sqrt_card_mul_euclideanNorm (u : Vec d → ℝ) (x : Vec d) :
    ‖fderiv ℝ u x‖ ≤ Real.sqrt d * euclideanNorm (euclideanGradient u x) := by
  have hcoord : ∀ i : Fin d, (fderiv ℝ u x) (basisVec i) = euclideanGradient u x i := by
    intro i; rfl
  have h1 : ‖fderiv ℝ u x‖ ≤ ∑ i : Fin d, |euclideanGradient u x i| := by
    refine (norm_clm_le_sum_basisVec _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcoord i, Real.norm_eq_abs]
  have hcs : (∑ i : Fin d, |euclideanGradient u x i|) ^ 2
      ≤ (d : ℝ) * ∑ i : Fin d, |euclideanGradient u x i| ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => |euclideanGradient u x i|))
  have hsq : ∑ i : Fin d, |euclideanGradient u x i| ^ 2
      = vecNormSq (euclideanGradient u x) := by
    unfold vecNormSq vecDot
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sq_abs, sq]
  have hnn : (0:ℝ) ≤ ∑ i : Fin d, |euclideanGradient u x i| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hfinal : ∑ i : Fin d, |euclideanGradient u x i|
      ≤ Real.sqrt d * euclideanNorm (euclideanGradient u x) := by
    rw [hsq] at hcs
    calc ∑ i : Fin d, |euclideanGradient u x i|
        = Real.sqrt ((∑ i : Fin d, |euclideanGradient u x i|) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((d : ℝ) * vecNormSq (euclideanGradient u x)) :=
          Real.sqrt_le_sqrt hcs
      _ = Real.sqrt d * euclideanNorm (euclideanGradient u x) := by
          rw [euclideanNorm, Real.sqrt_mul (by positivity)]
  exact h1.trans hfinal

/-- A cube sits inside its double. -/
theorem cubeSet_subset_double {B : Cube d} (hB : 0 ≤ B.2) :
    cubeSet B ⊆ centeredAxisCube B.1 (2 * B.2) := by
  intro z hz
  rw [cubeSet] at hz
  refine mem_centeredAxisCube.mpr fun i => ?_
  have := mem_centeredAxisCube.mp hz i
  linarith

/-- Two points of a cube are within its side length in the ambient sup norm. -/
theorem norm_sub_le_side {B : Cube d} {x y : Vec d} (hB : 0 ≤ B.2)
    (hx : x ∈ cubeSet B) (hy : y ∈ cubeSet B) : ‖x - y‖ ≤ B.2 := by
  rw [cubeSet] at hx hy
  refine (pi_norm_le_iff_of_nonneg hB).mpr fun i => ?_
  have h1 := mem_centeredAxisCube.mp hx i
  have h2 := mem_centeredAxisCube.mp hy i
  rw [abs_lt] at h1 h2
  rw [Real.norm_eq_abs, Pi.sub_apply, abs_le]
  constructor <;> linarith

/-- **The scaled control bounds the ellipticity ratio on each cube of the family.**

`LogCoefficientControlOn a H B` bounds `size^2 |grad log a|^2` and does not mention
`sup a / inf a`. It nevertheless forces a ratio bound *on the cube itself*: the
log-coefficient varies by at most `sqrt d * sqrt H` across `B`, so
`a x <= exp (sqrt d * sqrt H) * a y` there. -/
theorem coefficientContrastOn_of_logCoefficientControlOn {a : Vec d → ℝ} {H : ℝ}
    {B : Cube d} (hB : 0 < B.2) (h : LogCoefficientControlOn a H B) :
    CoefficientContrastOn a (Real.exp (Real.sqrt d * Real.sqrt H)) B := by
  obtain ⟨hpos, G, K, hG, hK, hdiff, hgrad, _hholder, hscale⟩ := h
  have hsub := cubeSet_subset_double (d := d) (B := B) hB.le
  refine ⟨fun x hx => hpos x (hsub hx), ?_⟩
  intro x hx y hy
  have hconv : Convex ℝ (centeredAxisCube B.1 (2 * B.2)) := convex_axisCube _ _
  have hbd : ∀ z ∈ centeredAxisCube B.1 (2 * B.2),
      ‖fderiv ℝ (fun w => Real.log (a w)) z‖ ≤ Real.sqrt d * G := by
    intro z hz
    refine (norm_fderiv_le_sqrt_card_mul_euclideanNorm (fun w => Real.log (a w)) z).trans ?_
    exact mul_le_mul_of_nonneg_left (hgrad z hz) (Real.sqrt_nonneg _)
  have hmean := hconv.norm_image_sub_le_of_norm_fderiv_le
    (f := fun w => Real.log (a w)) (fun z hz => hdiff z hz) hbd (hsub hx) (hsub hy)
  have hxy : ‖y - x‖ ≤ B.2 := norm_sub_le_side hB.le hy hx
  have hGB : B.2 * G ≤ Real.sqrt H := by
    have hsq : (B.2 * G) ^ 2 ≤ H := by nlinarith [sq_nonneg (B.2 * G), mul_nonneg (sq_nonneg B.2) hK]
    calc B.2 * G = Real.sqrt ((B.2 * G) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt H := Real.sqrt_le_sqrt hsq
  have hkey : |Real.log (a y) - Real.log (a x)| ≤ Real.sqrt d * Real.sqrt H := by
    refine (Real.norm_eq_abs _ ▸ hmean).trans ?_
    calc Real.sqrt d * G * ‖y - x‖ ≤ Real.sqrt d * G * B.2 :=
          mul_le_mul_of_nonneg_left hxy (by positivity)
      _ = Real.sqrt d * (B.2 * G) := by ring
      _ ≤ Real.sqrt d * Real.sqrt H := mul_le_mul_of_nonneg_left hGB (Real.sqrt_nonneg _)
  have hax : 0 < a x := hpos x (hsub hx)
  have hay : 0 < a y := hpos y (hsub hy)
  have hlog : Real.log (a x) ≤ Real.log (a y) + Real.sqrt d * Real.sqrt H := by
    have := (abs_le.mp hkey).1
    linarith
  calc a x = Real.exp (Real.log (a x)) := (Real.exp_log hax).symm
    _ ≤ Real.exp (Real.log (a y) + Real.sqrt d * Real.sqrt H) := Real.exp_le_exp.mpr hlog
    _ = Real.exp (Real.sqrt d * Real.sqrt H) * a y := by
        rw [Real.exp_add, Real.exp_log hay]; ring



theorem not_uniform_radial_logCoefficientControl (H : ℝ) :
    ¬ (∀ n : ℕ, 3 < (3 : ℝ) ^ n →
      LogCoefficientControlOn WeightedLocalHarmonicRadial.radialCoefficient H
        (WeightedLocalHarmonicRadial.radialOuter ((3 : ℝ) ^ n))) := by
  intro h
  refine WeightedLocalHarmonicRadial.not_uniform_radial_contrast
    (Real.exp (Real.sqrt 2 * Real.sqrt H)) ?_
  intro n hn
  have hside : (0 : ℝ) < (WeightedLocalHarmonicRadial.radialOuter ((3 : ℝ) ^ n)).2 := by
    show (0 : ℝ) < (3 : ℝ) ^ n
    positivity
  simpa using coefficientContrastOn_of_logCoefficientControlOn hside (h n hn)

/-! ### The control makes the coefficient genuinely `C¹`

`LogCoefficientControlOn` asks for `log a` differentiable with a *Lipschitz* gradient on
the double cube. That is exactly `C^{1,1}`, so `log a` is `C¹` there and hence so is
`a = exp (log a)`. This is what feeds the Poisson reduction in
`Section9Support/PoissonReduction.lean`, which wants `ContDiffOn ℝ 1 a` and positivity.
-/

/-- A coordinate is bounded by the Euclidean norm. -/
theorem abs_le_euclideanNorm (v : Vec d) (i : Fin d) : |v i| ≤ euclideanNorm v := by
  rw [euclideanNorm]
  have hle : v i ^ 2 ≤ vecNormSq v := by
    unfold vecNormSq vecDot
    have : ∀ j ∈ (Finset.univ : Finset (Fin d)), 0 ≤ v j * v j :=
      fun j _ => mul_self_nonneg _
    calc v i ^ 2 = v i * v i := sq _
      _ ≤ ∑ j : Fin d, v j * v j := Finset.single_le_sum this (Finset.mem_univ i)
  calc |v i| = Real.sqrt (v i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (vecNormSq v) := Real.sqrt_le_sqrt hle

/-- The Euclidean norm is at most `√d` times the ambient sup norm. -/
theorem euclideanNorm_le_sqrt_card_mul_norm (v : Vec d) :
    euclideanNorm v ≤ Real.sqrt d * ‖v‖ := by
  have hsq : vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
    unfold vecNormSq vecDot
    calc ∑ i : Fin d, v i * v i ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : |v i| ≤ ‖v‖ := by
            simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
          nlinarith [abs_nonneg (v i), sq_abs (v i), norm_nonneg v]
      _ = (d : ℝ) * ‖v‖ ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]
  calc euclideanNorm v = Real.sqrt (vecNormSq v) := rfl
    _ ≤ Real.sqrt ((d : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt d * ‖v‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg v)]

/-- A Lipschitz bound on the Euclidean gradient makes `fderiv` Lipschitz, hence
continuous. -/
theorem continuousOn_fderiv_of_holderOne {W : Set (Vec d)} {f : Vec d → ℝ} {K : ℝ}
    (hK0 : 0 ≤ K) (hK : HolderSeminormBoundOn W 1 K (euclideanGradient f)) :
    ContinuousOn (fderiv ℝ f) W := by
  intro x hx
  refine Metric.continuousWithinAt_iff.mpr fun eps heps => ?_
  refine ⟨eps / ((d : ℝ) * K * Real.sqrt d + 1), by positivity, fun y hy hdist => ?_⟩
  have hbound : ‖fderiv ℝ f y - fderiv ℝ f x‖
      ≤ ∑ i : Fin d, ‖(fderiv ℝ f y - fderiv ℝ f x) (basisVec i)‖ :=
    norm_clm_le_sum_basisVec _
  have hcoord : ∀ i : Fin d, ‖(fderiv ℝ f y - fderiv ℝ f x) (basisVec i)‖
      ≤ K * euclideanNorm (y - x) := by
    intro i
    have hv : (fderiv ℝ f y - fderiv ℝ f x) (basisVec i)
        = euclideanGradient f y i - euclideanGradient f x i := rfl
    rw [hv, Real.norm_eq_abs]
    have h1 : |euclideanGradient f y i - euclideanGradient f x i|
        ≤ euclideanNorm (euclideanGradient f y - euclideanGradient f x) := by
      simpa using abs_le_euclideanNorm (euclideanGradient f y - euclideanGradient f x) i
    refine h1.trans ?_
    have := hK y hy x hx
    simpa using this
  have hsum : ∑ i : Fin d, ‖(fderiv ℝ f y - fderiv ℝ f x) (basisVec i)‖
      ≤ (d : ℝ) * (K * euclideanNorm (y - x)) := by
    calc ∑ i : Fin d, ‖(fderiv ℝ f y - fderiv ℝ f x) (basisVec i)‖
        ≤ ∑ _i : Fin d, K * euclideanNorm (y - x) :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * (K * euclideanNorm (y - x)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have heu : euclideanNorm (y - x) ≤ Real.sqrt d * ‖y - x‖ :=
    euclideanNorm_le_sqrt_card_mul_norm _
  have hdx : ‖y - x‖ < eps / ((d : ℝ) * K * Real.sqrt d + 1) := by
    simpa [dist_eq_norm] using hdist
  have hden : (0:ℝ) < (d : ℝ) * K * Real.sqrt d + 1 := by positivity
  have hchain : ‖fderiv ℝ f y - fderiv ℝ f x‖
      ≤ ((d : ℝ) * K * Real.sqrt d) * ‖y - x‖ := by
    refine hbound.trans (hsum.trans ?_)
    have hKnn : (0:ℝ) ≤ (d : ℝ) * K := by positivity
    nlinarith [heu, norm_nonneg (y - x), Real.sqrt_nonneg (d : ℝ)]
  rw [dist_eq_norm]
  calc ‖fderiv ℝ f y - fderiv ℝ f x‖
      ≤ ((d : ℝ) * K * Real.sqrt d) * ‖y - x‖ := hchain
    _ < eps := by
        rw [lt_div_iff₀ hden] at hdx
        nlinarith [norm_nonneg (y - x), Real.sqrt_nonneg (d:ℝ), hdx]

/-- **The anchor's coefficient hypothesis supplies a `C¹` coefficient.**

`LogCoefficientControlOn a H B` asks for `log a` differentiable with a Lipschitz gradient
on the double cube. That makes `log a` genuinely `C¹` there, hence `a = exp (log a)` too. -/
theorem contDiffOn_of_logCoefficientControlOn {a : Vec d → ℝ} {H : ℝ} {B : Cube d}
    (h : LogCoefficientControlOn a H B) :
    ContDiffOn ℝ 1 a (centeredAxisCube B.1 (2 * B.2)) := by
  obtain ⟨hpos, G, K, _hG, hK0, hdiff, _hgrad, hholder, _hscale⟩ := h
  set W : Set (Vec d) := centeredAxisCube B.1 (2 * B.2) with hWdef
  have hWopen : IsOpen W := isOpen_axisCube _ _
  have hlogdiff : DifferentiableOn ℝ (fun y => Real.log (a y)) W :=
    fun x hx => (hdiff x hx).differentiableWithinAt
  have hcont : ContinuousOn (fderiv ℝ (fun y => Real.log (a y))) W :=
    continuousOn_fderiv_of_holderOne hK0 hholder
  have hfw : ContinuousOn (fderivWithin ℝ (fun y => Real.log (a y)) W) W := by
    refine hcont.congr fun x hx => ?_
    exact fderivWithin_of_isOpen (f := fun y => Real.log (a y)) (𝕜 := ℝ) hWopen hx
  have hlogC1 : ContDiffOn ℝ 1 (fun y => Real.log (a y)) W := by
    have := contDiffOn_succ_of_fderivWithin (𝕜 := ℝ) (n := 0)
      (f := fun y => Real.log (a y)) (s := W) hlogdiff
      (fun hcon => absurd hcon (by simp))
      (by simpa [contDiffOn_zero] using hfw)
    simpa using this
  have hexp : ContDiffOn ℝ 1 (fun y => Real.exp (Real.log (a y))) W := hlogC1.exp
  exact hexp.congr fun x hx => (Real.exp_log (hpos x hx)).symm

/-- Positivity, in the form the Poisson reduction wants. -/
theorem pos_of_logCoefficientControlOn {a : Vec d → ℝ} {H : ℝ} {B : Cube d}
    (h : LogCoefficientControlOn a H B) :
    ∀ x ∈ centeredAxisCube B.1 (2 * B.2), 0 < a x := h.1

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
