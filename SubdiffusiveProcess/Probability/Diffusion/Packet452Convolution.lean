module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452PathLiftGoal

@[expose] public section




set_option autoImplicit false

open Function Homogenization MeasureTheory Filter Set Topology

open scoped ENNReal Convolution Pointwise

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-! ## The reflected kernel `z ↦ k (x − z)` -/

theorem hasCompactSupport_reflect (k : Vec d → ℝ) (hkc : HasCompactSupport k) (x : Vec d) :
    HasCompactSupport (fun y : Vec d => k (x - y)) :=
  HasCompactSupport.comp_homeomorph hkc (Homeomorph.subLeft x)

theorem contDiff_reflect {k : Vec d → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (x : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => k (x - y)) :=
  hk.comp (contDiff_const.sub contDiff_id)

theorem fderiv_reflect {k : Vec d → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (x y : Vec d) (v : Vec d) :
    fderiv ℝ (fun z : Vec d => k (x - z)) y v = -(fderiv ℝ k (x - y) v) := by
  have hd : HasFDerivAt (fun z : Vec d => k (x - z))
      ((fderiv ℝ k (x - y)).comp (-ContinuousLinearMap.id ℝ (Vec d))) y := by
    have h1 : HasFDerivAt (fun z : Vec d => x - z) (-ContinuousLinearMap.id ℝ (Vec d)) y :=
      (hasFDerivAt_id (𝕜 := ℝ) y).const_sub x
    have hdiff : Differentiable ℝ k := hk.differentiable (by simp)
    exact ((hdiff.differentiableAt).hasFDerivAt).comp y h1
  rw [hd.fderiv]
  simp

/-! ## Moving a derivative from the kernel onto the weak derivative -/

/-- The weak-derivative identity, read at the test function `z ↦ k (x − z)`.  Valid at every `x`. -/
theorem convolution_fderiv_transfer {f g : Vec d → ℝ} {i : Fin d}
    (hw : HasWeakPartialDerivOn Set.univ i f g)
    {k : Vec d → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k) (x : Vec d) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun a => fderiv ℝ k a (basisVec i))) x
      = (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) x := by
  have hw' := hw (fun z => k (x - z)) (contDiff_reflect hk x)
    (hasCompactSupport_reflect k hkc x) (subset_univ _)
  simp only [Measure.restrict_univ] at hw'
  simp only [fderiv_reflect hk x, mul_neg] at hw'
  rw [integral_neg] at hw'
  have hw'' : ∫ z, f z * fderiv ℝ k (x - z) (basisVec i) = ∫ z, g z * k (x - z) := by
    linarith [hw']
  simpa only [convolution_lsmul, smul_eq_mul] using! hw''

/-- **Step 4, the public re-derivation.**  The classical coordinate derivative of a mollification
is the mollification of the weak derivative -- at **every** point, not merely almost everywhere. -/
theorem fderiv_convolution_weak {f g : Vec d → ℝ} {i : Fin d}
    (hw : HasWeakPartialDerivOn Set.univ i f g)
    (hfloc : LocallyIntegrable f volume)
    {k : Vec d → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k) (x : Vec d) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) x (basisVec i)
      = (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) x := by
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by simp)
  have hd := hkc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hfloc hk1 x
  rw [hd.fderiv, convolution_precompR_apply _ hfloc (hkc.fderiv ℝ)
    (hk1.continuous_fderiv (by decide))]
  exact convolution_fderiv_transfer hw hk hkc x

/-- **Step 5.**  Differentiating a mollification again touches only the kernel: no second weak
derivative of `f` is invoked, which is essential since `f`'s weak gradient need not be weakly
differentiable. -/
theorem fderiv_convolution_kernel {f : Vec d → ℝ} (hfloc : LocallyIntegrable f volume)
    {k : Vec d → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k)
    (v : Vec d) (x : Vec d) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) x v
      = (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun a => fderiv ℝ k a v)) x := by
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by simp)
  have hd := hkc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hfloc hk1 x
  rw [hd.fderiv, convolution_precompR_apply _ hfloc (hkc.fderiv ℝ)
    (hk1.continuous_fderiv (by decide))]

/-! ## Commutativity, smoothness, support -/

theorem lsmul_flip : (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  ext
  simp

/-- The CoarseGraining mollifier API puts the kernel on the **left**; the Mathlib differentiation
API puts it on the right.  For real scalars the two agree. -/
theorem convolution_comm_lsmul (f g : Vec d → ℝ) :
    f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
      = g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  have h := convolution_flip (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure (Vec d))) (f := g) (g := f)
  rw [lsmul_flip] at h
  exact h

theorem contDiff_convolution_kernel {f : Vec d → ℝ} (hfloc : LocallyIntegrable f volume)
    {k : Vec d → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k) :
    ContDiff ℝ (⊤ : ℕ∞) (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) :=
  hkc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hfloc hk

theorem hasCompactSupport_convolution {f k : Vec d → ℝ} (hfc : HasCompactSupport f)
    (hkc : HasCompactSupport k) :
    HasCompactSupport (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] k) :=
  HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfc hkc

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
