module

public import Mathlib
public import SubdiffusiveProcess.CubeTrace.Scale

@[expose] public section

/-!
# Cube trace extension: mollification of a Hölder function

`ρ_h(y) = h^{-d} ρ(y/h)` with `ρ` a fixed smooth probability density supported in the unit sup-ball.
For a `K`-Hölder (`β`) function `G` on `ℝ^d` (sup norm) the mollification `A_h = ρ_h ⋆ G` is smooth with
`|A_h - G| ≤ K h^β`, `|∂_j A_h| ≤ c₁ K h^{β-1}`, `|∂_l ∂_j A_h| ≤ c₂ K h^{β-2}`.
All kernels are rescalings `h^{-(d+p)} κ(y/h)` of fixed smooth compactly supported kernels, and
derivatives of `G ⋆ k` are `G ⋆ ∂k`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology Convolution
noncomputable section
namespace SubdiffusiveProcess.CubeTrace

variable {d : ℕ}

/-- Convolution of a kernel with a function: `(k ⋆ G)(x) = ∫ k(x - t) G(t) dt`. -/
def ctConv (k G : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ := ∫ t, k (x - t) * G t

/-- The rescaled kernel `h^{-(d+p)} κ(h^{-1} y)`. -/
def ctScale (p : ℕ) (h : ℝ) (κ : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ :=
  ((h ^ (d + p))⁻¹) * κ (h⁻¹ • y)

/-- The fixed bump: inner radius `1/2`, outer radius `1`. -/
def ctBump : ContDiffBump (0 : Fin d → ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The fixed mollifier density (`∫ ρ = 1`, smooth, support the unit sup-ball). -/
def ctRho : (Fin d → ℝ) → ℝ := (ctBump (d := d)).normed volume

/-- The first-derivative kernel `κ_j = ∂_j ρ`. -/
def ctKap1 (j : Fin d) : (Fin d → ℝ) → ℝ := fun w => fderiv ℝ (ctRho (d := d)) w (Pi.single j 1)

/-- The second-derivative kernel `κ_{jl} = ∂_l ∂_j ρ`. -/
def ctKap2 (j l : Fin d) : (Fin d → ℝ) → ℝ :=
  fun w => fderiv ℝ (fun y => fderiv ℝ (ctRho (d := d)) y (Pi.single j 1)) w (Pi.single l 1)

/-- The rescaled density `ρ_h(y) = h^{-d} ρ(h^{-1} y)`. -/
def ctRhoH (h : ℝ) (y : Fin d → ℝ) : ℝ := (h ^ d)⁻¹ * ctRho (h⁻¹ • y)

/-- The mollification `A_h(x) = ∫ ρ_h(x - t) G(t) dt`. -/
def ctMoll (h : ℝ) (G : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ := ctConv (ctRhoH h) G x

theorem ctMoll_eq_conv (h : ℝ) (G : (Fin d → ℝ) → ℝ) : ctMoll h G = ctConv (ctRhoH h) G := by
  rfl

theorem ctRhoH_eq_scale (h : ℝ) : ctRhoH (d := d) h = ctScale 0 h ctRho := by
  funext y
  simp [ctRhoH, ctScale]

/-! ### The fixed kernel `ρ` -/

theorem ctRho_nonneg (y : Fin d → ℝ) : 0 ≤ ctRho y := by
  unfold ctRho
  exact ContDiffBump.nonneg_normed _ _

theorem ctRho_contDiff : ContDiff ℝ ∞ (ctRho (d := d)) := by
  unfold ctRho
  exact ContDiffBump.contDiff_normed _

theorem ctRho_integral : ∫ y, ctRho (d := d) y = 1 := by
  unfold ctRho
  exact ContDiffBump.integral_normed _

theorem ctRho_eq_zero_of_le {y : Fin d → ℝ} (hy : 1 ≤ ‖y‖) : ctRho y = 0 := by
  unfold ctRho
  have hsupp := ContDiffBump.support_normed_eq (ctBump (d := d)) (μ := volume)
  by_contra hne
  have : y ∈ Function.support ((ctBump (d := d)).normed volume) := hne
  rw [hsupp] at this
  simp only [ctBump, mem_ball_zero_iff] at this
  linarith

/-- A `C^∞` function with compact support has vanishing integral of every partial derivative. -/
theorem integral_fderiv_apply_eq_zero {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (j : Fin d) : ∫ y, fderiv ℝ f y (Pi.single j 1) = 0 := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hcont : Continuous (fun y => fderiv ℝ f y (Pi.single j 1)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsupp : HasCompactSupport (fun y => fderiv ℝ f y (Pi.single j 1)) :=
    hc.fderiv_apply ℝ (Pi.single j 1)
  have hint1 : Integrable (fun y => fderiv ℝ f y (Pi.single j 1)) := hcont.integrable_of_hasCompactSupport hsupp
  have hint2 : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (f := fun _ : Fin d → ℝ => (1 : ℝ)) (f' := fun _ => (0 : ℝ)) (g := f)
    (g' := fun y => fderiv ℝ f y (Pi.single j 1)) (v := Pi.single j 1)
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (by simp) (by simpa using hint1) (by simpa using hint2)
    (fun x _ => by simpa using (hasFDerivAt_const (1 : ℝ) x).hasLineDerivAt (Pi.single j 1))
    (fun x _ => (hd x).hasFDerivAt.hasLineDerivAt _)
  simpa using key

/-- If a smooth `f` vanishes for `‖y‖ > 1` then so do its partial derivatives for `‖y‖ ≥ 1`. -/
theorem fderiv_apply_eq_zero_of_vanishing {f : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hz : ∀ y, 1 < ‖y‖ → f y = 0) (j : Fin d) :
    ∀ y : Fin d → ℝ, 1 ≤ ‖y‖ → fderiv ℝ f y (Pi.single j 1) = 0 := by
  intro y hy
  have hcont : Continuous (fun w => fderiv ℝ f w (Pi.single j 1)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hzero : ∀ w : Fin d → ℝ, 1 < ‖w‖ → fderiv ℝ f w (Pi.single j 1) = 0 := by
    intro w hw
    have hev : f =ᶠ[𝓝 w] fun _ => (0 : ℝ) := by
      have hopen : IsOpen {w : Fin d → ℝ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hw] with u hu
      exact hz u hu
    rw [Filter.EventuallyEq.fderiv_eq hev]
    simp
  have hclos : y ∈ closure {w : Fin d → ℝ | 1 < ‖w‖} := by
    have : Nonempty (Fin d) := ⟨j⟩
    have hset : {w : Fin d → ℝ | 1 < ‖w‖} = (closedBall (0 : Fin d → ℝ) 1)ᶜ := by
      ext w; simp
    rw [hset, closure_compl, interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
    simpa using hy
  have := closure_minimal (fun w hw => hzero w hw) (isClosed_eq hcont continuous_const) hclos
  exact this

theorem hasCompactSupport_of_vanishing {f : (Fin d → ℝ) → ℝ} (hz : ∀ y, 1 ≤ ‖y‖ → f y = 0) :
    HasCompactSupport f := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℝ) 1)
  intro y hy
  apply hz
  simp only [mem_closedBall_zero_iff, not_le] at hy
  exact hy.le

theorem ctKap1_contDiff (j : Fin d) : ContDiff ℝ ∞ (ctKap1 j) := by
  unfold ctKap1
  exact (ctRho_contDiff.fderiv_right (by simp)).clm_apply contDiff_const

theorem ctKap1_eq_zero_of_le (j : Fin d) {y : Fin d → ℝ} (hy : 1 ≤ ‖y‖) : ctKap1 j y = 0 := by
  exact fderiv_apply_eq_zero_of_vanishing ctRho_contDiff
    (fun y hy => ctRho_eq_zero_of_le hy.le) j y hy

theorem ctKap2_contDiff (j l : Fin d) : ContDiff ℝ ∞ (ctKap2 j l) := by
  unfold ctKap2
  have h1 : ContDiff ℝ ∞ (fun y => fderiv ℝ (ctRho (d := d)) y (Pi.single j 1)) :=
    ctKap1_contDiff j
  exact (h1.fderiv_right (by simp)).clm_apply contDiff_const

theorem ctKap2_eq_zero_of_le (j l : Fin d) {y : Fin d → ℝ} (hy : 1 ≤ ‖y‖) : ctKap2 j l y = 0 := by
  exact fderiv_apply_eq_zero_of_vanishing (ctKap1_contDiff j)
    (fun y hy => ctKap1_eq_zero_of_le j hy.le) l y hy

theorem ctKap1_integral_zero (j : Fin d) : ∫ y, ctKap1 j y = 0 := by
  exact integral_fderiv_apply_eq_zero ctRho_contDiff
    (hasCompactSupport_of_vanishing (fun y hy => ctRho_eq_zero_of_le hy)) j

theorem ctKap2_integral_zero (j l : Fin d) : ∫ y, ctKap2 j l y = 0 := by
  exact integral_fderiv_apply_eq_zero (ctKap1_contDiff j)
    (hasCompactSupport_of_vanishing (fun y hy => ctKap1_eq_zero_of_le j hy)) l

theorem ctKap1_integrable (j : Fin d) : Integrable (ctKap1 j) := by
  exact (ctKap1_contDiff j).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_vanishing (fun y hy => ctKap1_eq_zero_of_le j hy))

theorem ctKap2_integrable (j l : Fin d) : Integrable (ctKap2 j l) := by
  exact (ctKap2_contDiff j l).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_vanishing (fun y hy => ctKap2_eq_zero_of_le j l hy))

/-! ### Rescaling -/

theorem ctScale_contDiff {p : ℕ} {h : ℝ} {κ : (Fin d → ℝ) → ℝ} (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ (ctScale p h κ) := by
  unfold ctScale
  exact contDiff_const.mul (hκ.comp (contDiff_const_smul h⁻¹))

theorem ctScale_eq_zero {p : ℕ} {h : ℝ} (hh : 0 < h) {κ : (Fin d → ℝ) → ℝ}
    (hκ : ∀ y, 1 ≤ ‖y‖ → κ y = 0) {y : Fin d → ℝ} (hy : h ≤ ‖y‖) : ctScale p h κ y = 0 := by
  unfold ctScale
  have hn : 1 ≤ ‖h⁻¹ • y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hh), ← div_eq_inv_mul, le_div_iff₀ hh]
    linarith
  rw [hκ _ hn, mul_zero]

theorem hasCompactSupport_ctScale {p : ℕ} {h : ℝ} (hh : 0 < h) {κ : (Fin d → ℝ) → ℝ}
    (hκ : ∀ y, 1 ≤ ‖y‖ → κ y = 0) : HasCompactSupport (ctScale p h κ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℝ) h)
  intro y hy
  apply ctScale_eq_zero hh hκ
  simp only [mem_closedBall_zero_iff, not_le] at hy
  exact hy.le

/-- `∫ h^{-(d+p)} κ(y/h) dy = h^{-p} ∫ κ`. -/
theorem integral_ctScale [NeZero d] {p : ℕ} {h : ℝ} (hh : 0 < h) (κ : (Fin d → ℝ) → ℝ) :
    ∫ y, ctScale p h κ y = (h ^ p)⁻¹ * ∫ y, κ y := by
  unfold ctScale
  rw [integral_const_mul]
  have key := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Fin d → ℝ)) κ h⁻¹
  rw [key, Module.finrank_fin_fun]
  have habs : |((h⁻¹) ^ d)⁻¹| = h ^ d := by
    rw [inv_pow, inv_inv, abs_of_pos (pow_pos hh d)]
  rw [habs, smul_eq_mul, pow_add]
  have hd : (h ^ d) ≠ 0 := (pow_pos hh d).ne'
  have hp : (h ^ p) ≠ 0 := (pow_pos hh p).ne'
  field_simp

theorem integrable_ctScale [NeZero d] {p : ℕ} {h : ℝ} (hh : 0 < h) {κ : (Fin d → ℝ) → ℝ}
    (hκ : Integrable κ) : Integrable (ctScale p h κ) := by
  unfold ctScale
  exact (hκ.comp_smul (inv_ne_zero hh.ne')).const_mul _

theorem abs_ctScale {p : ℕ} {h : ℝ} (hh : 0 < h) (κ : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) :
    |ctScale p h κ y| = ctScale p h (fun w => |κ w|) y := by
  unfold ctScale
  rw [abs_mul, abs_of_pos (by positivity : 0 < (h ^ (d + p))⁻¹)]

/-- The directional derivative of a rescaled kernel is the rescaled derivative kernel. -/
theorem fderiv_ctScale {p : ℕ} {h : ℝ} (_hh : 0 < h) {κ : (Fin d → ℝ) → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (y : Fin d → ℝ) (j : Fin d) :
    fderiv ℝ (ctScale p h κ) y (Pi.single j 1) =
      ctScale (p + 1) h (fun w => fderiv ℝ κ w (Pi.single j 1)) y := by
  have hκd : DifferentiableAt ℝ κ (h⁻¹ • y) := (hκ.differentiable (by simp)).differentiableAt
  have hA : HasFDerivAt (fun y : Fin d → ℝ => h⁻¹ • y) (h⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ)) y :=
    (hasFDerivAt_id y).const_smul h⁻¹
  have hcomp : HasFDerivAt (fun y : Fin d → ℝ => κ (h⁻¹ • y))
      ((fderiv ℝ κ (h⁻¹ • y)).comp (h⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ))) y :=
    hκd.hasFDerivAt.comp y hA
  have hF : HasFDerivAt (ctScale p h κ)
      ((h ^ (d + p))⁻¹ • (fderiv ℝ κ (h⁻¹ • y)).comp (h⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ))) y :=
    hcomp.const_mul ((h ^ (d + p))⁻¹)
  rw [hF.fderiv]
  simp only [ctScale, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, map_smul]
  have : (h ^ (d + (p + 1)))⁻¹ = (h ^ (d + p))⁻¹ * h⁻¹ := by
    rw [← add_assoc, pow_succ, mul_inv]
  rw [this]
  ring

/-- `∂_j ρ_h = ctScale 1 h κ_j` and `∂_l ∂_j ρ_h = ctScale 2 h κ_{jl}`. -/
theorem ctRhoH_fderiv_eq {h : ℝ} (hh : 0 < h) (j : Fin d) :
    (fun y => fderiv ℝ (ctRhoH (d := d) h) y (Pi.single j 1)) = ctScale 1 h (ctKap1 j) := by
  funext y
  rw [ctRhoH_eq_scale, fderiv_ctScale hh ctRho_contDiff]
  rfl

theorem ctRhoH_fderiv2_eq {h : ℝ} (hh : 0 < h) (j l : Fin d) :
    (fun y => fderiv ℝ (fun w => fderiv ℝ (ctRhoH (d := d) h) w (Pi.single j 1)) y (Pi.single l 1)) =
      ctScale 2 h (ctKap2 j l) := by
  have h1 : (fun y => fderiv ℝ (ctRhoH (d := d) h) y (Pi.single j 1)) = ctScale 1 h (ctKap1 j) :=
    ctRhoH_fderiv_eq hh j
  funext y
  rw [h1, fderiv_ctScale hh (ctKap1_contDiff j)]
  rfl

/-! ### Convolution -/

theorem ctConv_eq_convolution (k G : (Fin d → ℝ) → ℝ) :
    ctConv k G = G ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] k := by
  funext x
  simp [ctConv, convolution_def, mul_comm]

theorem ctConv_contDiff {k G : (Fin d → ℝ) → ℝ} (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (hG : Continuous G) : ContDiff ℝ ∞ (ctConv k G) := by
  rw [ctConv_eq_convolution]
  exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hG.locallyIntegrable hk

/-- `∂_j (k ⋆ G) = (∂_j k) ⋆ G`. -/
theorem ctConv_fderiv_apply {k G : (Fin d → ℝ) → ℝ} (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (hG : Continuous G) (x : Fin d → ℝ) (j : Fin d) :
    fderiv ℝ (ctConv k G) x (Pi.single j 1) = ctConv (fun y => fderiv ℝ k y (Pi.single j 1)) G x := by
  rw [ctConv_eq_convolution]
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by norm_cast)
  have hd := hc.hasFDerivAt_convolution_right (μ := volume) (ContinuousLinearMap.mul ℝ ℝ)
    (hG.locallyIntegrable (μ := volume)) hk1 x
  rw [hd.fderiv]
  have hex : ConvolutionExistsAt G (fderiv ℝ k) x
      ((ContinuousLinearMap.mul ℝ ℝ).precompR (Fin d → ℝ)) volume :=
    (hc.fderiv ℝ).convolutionExists_right _ (hG.locallyIntegrable (μ := volume))
      (hk.continuous_fderiv (by simp)) x
  rw [convolution_def, ContinuousLinearMap.integral_apply hex]
  simp [ctConv, mul_comm]


/-- Common core: the kernel against `G - G(x)`. -/
theorem ctConv_aux [NeZero d] {k G : (Fin d → ℝ) → ℝ} {K β r : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (_hr : 0 < r) (hG : ∀ x y, |G x - G y| ≤ K * ‖x - y‖ ^ β) (hk : Integrable k)
    (hsupp : ∀ y, r ≤ ‖y‖ → k y = 0) (x : Fin d → ℝ) :
    Integrable (fun t => k (x - t) * (G t - G x)) ∧
      |∫ t, k (x - t) * (G t - G x)| ≤ K * r ^ β * ∫ y, |k y| := by
  have hGc : Continuous G := holder_continuous hβ hG
  have hkx : Integrable (fun t => k (x - t)) := hk.comp_sub_left x
  have hbound : ∀ t, |k (x - t) * (G t - G x)| ≤ K * r ^ β * |k (x - t)| := by
    intro t
    by_cases ht : r ≤ ‖x - t‖
    · rw [hsupp _ ht]; simp
    · push Not at ht
      rw [abs_mul, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      calc |G t - G x| = |G x - G t| := abs_sub_comm _ _
        _ ≤ K * ‖x - t‖ ^ β := hG x t
        _ ≤ K * r ^ β := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) ht.le hβ.le) hK
  have hint : Integrable (fun t => k (x - t) * (G t - G x)) :=
    Integrable.mono' (hkx.norm.const_mul (K * r ^ β))
      (hkx.aestronglyMeasurable.mul (hGc.sub continuous_const).aestronglyMeasurable)
      (Eventually.of_forall (fun t => by simpa [Real.norm_eq_abs] using hbound t))
  refine ⟨hint, ?_⟩
  calc |∫ t, k (x - t) * (G t - G x)| = ‖∫ t, k (x - t) * (G t - G x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, K * r ^ β * |k (x - t)| :=
        norm_integral_le_of_norm_le (hkx.norm.const_mul (K * r ^ β))
          (Eventually.of_forall (fun t => by simpa [Real.norm_eq_abs] using hbound t))
    _ = K * r ^ β * ∫ t, |k (x - t)| := integral_const_mul _ _
    _ = K * r ^ β * ∫ y, |k y| := by
        rw [integral_sub_left_eq_self (fun y => |k y|) volume x]

theorem ctConv_eq_aux [NeZero d] {k G : (Fin d → ℝ) → ℝ} {K β r : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (hr : 0 < r) (hG : ∀ x y, |G x - G y| ≤ K * ‖x - y‖ ^ β) (hk : Integrable k)
    (hsupp : ∀ y, r ≤ ‖y‖ → k y = 0) (x : Fin d → ℝ) :
    ctConv k G x = (∫ t, k (x - t) * (G t - G x)) + G x * ∫ y, k y := by
  have h1 := (ctConv_aux hK hβ hr hG hk hsupp x).1
  have h2 : Integrable (fun t => k (x - t) * G x) := (hk.comp_sub_left x).mul_const _
  have h3 : ∫ t, k (x - t) * G x = G x * ∫ y, k y := by
    rw [integral_mul_const, integral_sub_left_eq_self (fun y => k y) volume x, mul_comm]
  unfold ctConv
  rw [← h3, ← integral_add h1 h2]
  congr 1
  funext t
  ring

/-- A kernel with mean zero supported in the ball of radius `r` gives `|k ⋆ G| ≤ K r^β ∫|k|`. -/
theorem abs_ctConv_le [NeZero d] {k G : (Fin d → ℝ) → ℝ} {K β r : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (hr : 0 < r) (hG : ∀ x y, |G x - G y| ≤ K * ‖x - y‖ ^ β) (hk : Integrable k)
    (hsupp : ∀ y, r ≤ ‖y‖ → k y = 0) (hint : ∫ y, k y = 0) (x : Fin d → ℝ) :
    |ctConv k G x| ≤ K * r ^ β * ∫ y, |k y| := by
  rw [ctConv_eq_aux hK hβ hr hG hk hsupp x, hint, mul_zero, add_zero]
  exact (ctConv_aux hK hβ hr hG hk hsupp x).2

/-- A probability density supported in the ball of radius `r` gives `|k ⋆ G - G| ≤ K r^β`. -/
theorem abs_ctConv_sub_le [NeZero d] {k G : (Fin d → ℝ) → ℝ} {K β r : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (hr : 0 < r) (hG : ∀ x y, |G x - G y| ≤ K * ‖x - y‖ ^ β) (hk : Integrable k)
    (hnn : ∀ y, 0 ≤ k y) (hsupp : ∀ y, r ≤ ‖y‖ → k y = 0) (hint : ∫ y, k y = 1)
    (x : Fin d → ℝ) : |ctConv k G x - G x| ≤ K * r ^ β := by
  have h := ctConv_aux hK hβ hr hG hk hsupp x
  have habs : ∫ y, |k y| = 1 := by
    simp_rw [abs_of_nonneg (hnn _)]
    exact hint
  rw [ctConv_eq_aux hK hβ hr hG hk hsupp x, hint, mul_one, add_sub_cancel_right]
  have := h.2
  rwa [habs, mul_one] at this

/-! ### The bounds for `A_h` -/

theorem ctMoll_contDiff [NeZero d] {h : ℝ} (hh : 0 < h) {G : (Fin d → ℝ) → ℝ} (hG : Continuous G) :
    ContDiff ℝ ∞ (ctMoll h G) := by
  rw [ctMoll_eq_conv]
  have hρ : ContDiff ℝ ∞ (ctRhoH (d := d) h) := by
    rw [ctRhoH_eq_scale]; exact ctScale_contDiff ctRho_contDiff
  have hc : HasCompactSupport (ctRhoH (d := d) h) := by
    rw [ctRhoH_eq_scale]; exact hasCompactSupport_ctScale hh (fun y hy => ctRho_eq_zero_of_le hy)
  exact ctConv_contDiff hρ hc hG

theorem ctRhoH_nonneg [NeZero d] {h : ℝ} (hh : 0 < h) (y : Fin d → ℝ) : 0 ≤ ctRhoH h y := by
  rw [ctRhoH_eq_scale]
  unfold ctScale
  exact mul_nonneg (by positivity) (ctRho_nonneg _)

theorem ctRhoH_integral [NeZero d] {h : ℝ} (hh : 0 < h) : ∫ y, ctRhoH (d := d) h y = 1 := by
  rw [ctRhoH_eq_scale, integral_ctScale hh, ctRho_integral]
  simp

theorem ctRhoH_eq_zero_of_le {h : ℝ} (hh : 0 < h) {y : Fin d → ℝ} (hy : h ≤ ‖y‖) :
    ctRhoH h y = 0 := by
  rw [ctRhoH_eq_scale]
  exact ctScale_eq_zero hh (fun y hy => ctRho_eq_zero_of_le hy) hy

theorem ctRhoH_integrable [NeZero d] {h : ℝ} (hh : 0 < h) : Integrable (ctRhoH (d := d) h) := by
  rw [ctRhoH_eq_scale]
  exact integrable_ctScale hh (ctRho_contDiff.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_vanishing (fun y hy => ctRho_eq_zero_of_le hy)))

/-- `A_h` is within `K h^β` of `G`. -/
theorem ctMoll_sub_le [NeZero d] {h : ℝ} (hh : 0 < h) {G : (Fin d → ℝ) → ℝ} {K β : ℝ}
    (hK : 0 ≤ K) (hβ : 0 < β) (hG : ∀ x y, |G x - G y| ≤ K * ‖x - y‖ ^ β)
    (x : Fin d → ℝ) : |ctMoll h G x - G x| ≤ K * h ^ β := by
  rw [ctMoll_eq_conv]
  exact abs_ctConv_sub_le hK hβ hh hG (ctRhoH_integrable hh) (fun y => ctRhoH_nonneg hh y)
    (fun y hy => ctRhoH_eq_zero_of_le hh hy) (ctRhoH_integral hh) x

/-- `|∂_j A_h| ≤ c₁ K h^{β-1}`. -/
theorem ctMoll_fderiv_bound [NeZero d] {β : ℝ} (hβ : 0 < β) :
    ∃ c1 : ℝ, 0 ≤ c1 ∧ ∀ {h : ℝ}, 0 < h → ∀ {G : (Fin d → ℝ) → ℝ} {K : ℝ}, 0 ≤ K →
      (∀ x y, |G x - G y| ≤ K * ‖x - y‖ ^ β) → ∀ (x : Fin d → ℝ) (j : Fin d),
      |fderiv ℝ (ctMoll h G) x (Pi.single j 1)| ≤ c1 * K * h ^ (β - 1) := by
  refine ⟨∑ j : Fin d, ∫ y, |ctKap1 j y|,
    Finset.sum_nonneg (fun j _ => integral_nonneg (fun y => abs_nonneg _)), ?_⟩
  intro h hh G K hK hG x j
  have hGc : Continuous G := holder_continuous hβ hG
  have hρ : ContDiff ℝ ∞ (ctRhoH (d := d) h) := by
    rw [ctRhoH_eq_scale]; exact ctScale_contDiff ctRho_contDiff
  have hc : HasCompactSupport (ctRhoH (d := d) h) := by
    rw [ctRhoH_eq_scale]; exact hasCompactSupport_ctScale hh (fun y hy => ctRho_eq_zero_of_le hy)
  have hform : fderiv ℝ (ctMoll h G) x (Pi.single j 1) = ctConv (ctScale 1 h (ctKap1 j)) G x := by
    rw [ctMoll_eq_conv, ctConv_fderiv_apply hρ hc hGc x j, ctRhoH_fderiv_eq hh j]
  rw [hform]
  have hb := abs_ctConv_le (k := ctScale 1 h (ctKap1 j)) hK hβ hh hG
    (integrable_ctScale hh (ctKap1_integrable j))
    (fun y hy => ctScale_eq_zero hh (fun y hy => ctKap1_eq_zero_of_le j hy) hy)
    (by rw [integral_ctScale hh, ctKap1_integral_zero, mul_zero]) x
  have habs : ∫ y, |ctScale 1 h (ctKap1 j) y| = (h ^ 1)⁻¹ * ∫ y, |ctKap1 j y| := by
    simp_rw [abs_ctScale hh]
    exact integral_ctScale hh (fun w => |ctKap1 j w|)
  rw [habs] at hb
  have hle : ∫ y, |ctKap1 j y| ≤ ∑ j : Fin d, ∫ y, |ctKap1 j y| :=
    Finset.single_le_sum (f := fun j : Fin d => ∫ y, |ctKap1 j y|)
      (fun j _ => integral_nonneg (fun y => abs_nonneg _)) (Finset.mem_univ j)
  have hrpow : h ^ (β - 1) = h ^ β / h := Real.rpow_sub_one hh.ne' β
  calc |ctConv (ctScale 1 h (ctKap1 j)) G x| ≤ K * h ^ β * ((h ^ 1)⁻¹ * ∫ y, |ctKap1 j y|) := hb
    _ = K * (h ^ β / h) * ∫ y, |ctKap1 j y| := by rw [pow_one]; field_simp
    _ ≤ K * (h ^ β / h) * ∑ j : Fin d, ∫ y, |ctKap1 j y| :=
        mul_le_mul_of_nonneg_left hle (mul_nonneg hK (div_nonneg (Real.rpow_nonneg hh.le _) hh.le))
    _ = (∑ j : Fin d, ∫ y, |ctKap1 j y|) * K * h ^ (β - 1) := by rw [hrpow]; ring

/-- `|∂_l ∂_j A_h| ≤ c₂ K h^{β-2}`. -/
theorem ctMoll_fderiv2_bound [NeZero d] {β : ℝ} (hβ : 0 < β) :
    ∃ c2 : ℝ, 0 ≤ c2 ∧ ∀ {h : ℝ}, 0 < h → ∀ {G : (Fin d → ℝ) → ℝ} {K : ℝ}, 0 ≤ K →
      (∀ x y, |G x - G y| ≤ K * ‖x - y‖ ^ β) → ∀ (x : Fin d → ℝ) (j l : Fin d),
      |fderiv ℝ (fun y => fderiv ℝ (ctMoll h G) y (Pi.single j 1)) x (Pi.single l 1)| ≤
        c2 * K * h ^ (β - 2) := by
  refine ⟨∑ j : Fin d, ∑ l : Fin d, ∫ y, |ctKap2 j l y|,
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun l _ =>
      integral_nonneg (fun y => abs_nonneg _))), ?_⟩
  intro h hh G K hK hG x j l
  have hGc : Continuous G := holder_continuous hβ hG
  have hρ : ContDiff ℝ ∞ (ctRhoH (d := d) h) := by
    rw [ctRhoH_eq_scale]; exact ctScale_contDiff ctRho_contDiff
  have hc : HasCompactSupport (ctRhoH (d := d) h) := by
    rw [ctRhoH_eq_scale]; exact hasCompactSupport_ctScale hh (fun y hy => ctRho_eq_zero_of_le hy)
  have hform1 : (fun y => fderiv ℝ (ctMoll h G) y (Pi.single j 1)) =
      ctConv (ctScale 1 h (ctKap1 j)) G := by
    funext y
    rw [ctMoll_eq_conv, ctConv_fderiv_apply hρ hc hGc y j, ctRhoH_fderiv_eq hh j]
  have hk1 : ContDiff ℝ ∞ (ctScale 1 h (ctKap1 j)) := ctScale_contDiff (ctKap1_contDiff j)
  have hkc : HasCompactSupport (ctScale 1 h (ctKap1 j)) :=
    hasCompactSupport_ctScale hh (fun y hy => ctKap1_eq_zero_of_le j hy)
  have hform : fderiv ℝ (fun y => fderiv ℝ (ctMoll h G) y (Pi.single j 1)) x (Pi.single l 1) =
      ctConv (ctScale 2 h (ctKap2 j l)) G x := by
    rw [hform1, ctConv_fderiv_apply hk1 hkc hGc x l]
    have := fderiv_ctScale (p := 1) hh (ctKap1_contDiff j)
    have h2 : (fun y => fderiv ℝ (ctScale 1 h (ctKap1 j)) y (Pi.single l 1)) =
        ctScale 2 h (ctKap2 j l) := by
      funext y
      rw [this y l]
      rfl
    rw [h2]
  rw [hform]
  have hb := abs_ctConv_le (k := ctScale 2 h (ctKap2 j l)) hK hβ hh hG
    (integrable_ctScale hh (ctKap2_integrable j l))
    (fun y hy => ctScale_eq_zero hh (fun y hy => ctKap2_eq_zero_of_le j l hy) hy)
    (by rw [integral_ctScale hh, ctKap2_integral_zero, mul_zero]) x
  have habs : ∫ y, |ctScale 2 h (ctKap2 j l) y| = (h ^ 2)⁻¹ * ∫ y, |ctKap2 j l y| := by
    simp_rw [abs_ctScale hh]
    exact integral_ctScale hh (fun w => |ctKap2 j l w|)
  rw [habs] at hb
  have hle : ∫ y, |ctKap2 j l y| ≤ ∑ j : Fin d, ∑ l : Fin d, ∫ y, |ctKap2 j l y| := by
    calc ∫ y, |ctKap2 j l y| ≤ ∑ l : Fin d, ∫ y, |ctKap2 j l y| :=
          Finset.single_le_sum (f := fun l : Fin d => ∫ y, |ctKap2 j l y|)
            (fun l _ => integral_nonneg (fun y => abs_nonneg _)) (Finset.mem_univ l)
      _ ≤ ∑ j : Fin d, ∑ l : Fin d, ∫ y, |ctKap2 j l y| :=
          Finset.single_le_sum (f := fun j : Fin d => ∑ l : Fin d, ∫ y, |ctKap2 j l y|)
            (fun j _ => Finset.sum_nonneg (fun l _ => integral_nonneg (fun y => abs_nonneg _)))
            (Finset.mem_univ j)
  have hrpow : h ^ (β - 2) = h ^ β / h ^ 2 := by
    rw [Real.rpow_sub hh, Real.rpow_two]
  calc |ctConv (ctScale 2 h (ctKap2 j l)) G x| ≤
        K * h ^ β * ((h ^ 2)⁻¹ * ∫ y, |ctKap2 j l y|) := hb
    _ = K * (h ^ β / h ^ 2) * ∫ y, |ctKap2 j l y| := by field_simp
    _ ≤ K * (h ^ β / h ^ 2) * ∑ j : Fin d, ∑ l : Fin d, ∫ y, |ctKap2 j l y| :=
        mul_le_mul_of_nonneg_left hle
          (mul_nonneg hK (div_nonneg (Real.rpow_nonneg hh.le _) (by positivity)))
    _ = (∑ j : Fin d, ∑ l : Fin d, ∫ y, |ctKap2 j l y|) * K * h ^ (β - 2) := by
        rw [hrpow]; ring

end SubdiffusiveProcess.CubeTrace
