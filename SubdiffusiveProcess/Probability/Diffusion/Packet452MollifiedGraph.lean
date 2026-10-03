module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452Mollifier
public import Homogenization.Sobolev.W1p.GlobalMollifierLp

@[expose] public section




set_option autoImplicit false

open Function Homogenization MeasureTheory Filter Set Topology

open scoped ENNReal Convolution Pointwise

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ} {U : Set (Vec d)}

/-! ## Compact support of the data -/

theorem hasCompactSupport_of_subset_bounded {g : Vec d → ℝ} (hUb : Bornology.IsBounded U)
    (hg : ∀ x, x ∉ U → g x = 0) : HasCompactSupport g :=
  HasCompactSupport.intro hUb.isCompact_closure fun x hx =>
    hg x fun hxU => hx (subset_closure hxU)

theorem hasCompactSupport_zeroExtension (hUb : Bornology.IsBounded U) (u : H10Function U) :
    HasCompactSupport u.zeroExtension :=
  hasCompactSupport_of_subset_bounded hUb fun _ hx => u.zeroExtension_apply_of_not_mem hx

theorem hasCompactSupport_zeroExtensionGrad (hUb : Bornology.IsBounded U) (u : H10Function U)
    (i : Fin d) : HasCompactSupport fun x => u.zeroExtensionGrad x i :=
  hasCompactSupport_of_subset_bounded hUb fun x hx => by
    rw [u.zeroExtensionGrad_apply_of_not_mem hx]; rfl

theorem hasCompactSupport_indicator (hUb : Bornology.IsBounded U) (f : Vec d → ℝ) :
    HasCompactSupport (U.indicator f) :=
  hasCompactSupport_of_subset_bounded hUb fun _ hx => Set.indicator_of_notMem hx f

/-! ## The mollified pair -/

/-- `φₙ = u⁰ ⋆ kₙ`. -/
def mollPhi (u : H10Function U) (n : ℕ) : Vec d → ℝ :=
  u.zeroExtension ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollKernel d n

/-- `fₙ = (1_U f) ⋆ kₙ`. -/
def mollForcing (U : Set (Vec d)) (f : Vec d → ℝ) (n : ℕ) : Vec d → ℝ :=
  U.indicator f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollKernel d n

theorem locallyIntegrable_zeroExtension (hU : IsOpen U) (u : H10Function U) :
    LocallyIntegrable u.zeroExtension volume :=
  (memLp_zeroExtension_two hU u).locallyIntegrable (by norm_num)

theorem locallyIntegrable_zeroExtensionGrad (hU : IsOpen U) (u : H10Function U) (i : Fin d) :
    LocallyIntegrable (fun x => u.zeroExtensionGrad x i) volume :=
  (memLp_zeroExtensionGrad_two hU u i).locallyIntegrable (by norm_num)

theorem memLp_indicator_two (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) : MemLp (U.indicator f) 2 volume :=
  (memLp_indicator_iff_restrict hU.measurableSet).mpr hf

theorem contDiff_mollPhi (hU : IsOpen U) (u : H10Function U) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollPhi u n) :=
  contDiff_convolution_kernel (locallyIntegrable_zeroExtension hU u)
    (mollKernel_contDiff n) (mollKernel_hasCompactSupport n)

theorem contDiff_mollForcing (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollForcing U f n) :=
  contDiff_convolution_kernel
    ((memLp_indicator_two hU hf).locallyIntegrable (by norm_num))
    (mollKernel_contDiff n) (mollKernel_hasCompactSupport n)

theorem hasCompactSupport_mollPhi (hUb : Bornology.IsBounded U) (u : H10Function U) (n : ℕ) :
    HasCompactSupport (mollPhi u n) :=
  hasCompactSupport_convolution (hasCompactSupport_zeroExtension hUb u)
    (mollKernel_hasCompactSupport n)

theorem hasCompactSupport_mollForcing (hUb : Bornology.IsBounded U) (f : Vec d → ℝ) (n : ℕ) :
    HasCompactSupport (mollForcing U f n) :=
  hasCompactSupport_convolution (hasCompactSupport_indicator hUb f)
    (mollKernel_hasCompactSupport n)

/-! ## Step 4 at `u.zeroExtension` -/

/-- The classical derivative of `φₙ` is the mollified weak gradient -- at every point. -/
theorem fderiv_mollPhi (hU : IsOpen U) (u : H10Function U) (n : ℕ) (i : Fin d) (x : Vec d) :
    fderiv ℝ (mollPhi u n) x (basisVec i)
      = ((fun y => u.zeroExtensionGrad y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          mollKernel d n) x :=
  fderiv_convolution_weak (u.hasWeakGradientOn_univ_zeroExtension hU.measurableSet i)
    (locallyIntegrable_zeroExtension hU u) (mollKernel_contDiff n)
    (mollKernel_hasCompactSupport n) x



theorem laplacian_mollPhi (hU : IsOpen U) (u : H10Function U) (n : ℕ) (x : Vec d) :
    ∑ i : Fin d, iteratedFDeriv ℝ 2 (mollPhi u n) x ![Pi.single i (1 : ℝ), Pi.single i (1 : ℝ)]
      = ∑ i : Fin d, ((fun y => u.zeroExtensionGrad y i)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            fun a => fderiv ℝ (mollKernel d n) a (basisVec i)) x := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ContDiff ℝ 2 (mollPhi u n) :=
    (contDiff_mollPhi hU u n).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  rw [show (Pi.single i (1 : ℝ) : Vec d) = basisVec i from rfl,
    iteratedFDeriv_two_eq h2 x (basisVec i)]
  have hfun : (fun y => fderiv ℝ (mollPhi u n) y (basisVec i))
      = (fun y => u.zeroExtensionGrad y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          mollKernel d n :=
    funext fun y => fderiv_mollPhi hU u n i y
  rw [hfun]
  exact fderiv_convolution_kernel (locallyIntegrable_zeroExtensionGrad hU u i)
    (mollKernel_contDiff n) (mollKernel_hasCompactSupport n) (basisVec i) x

/-! ## Step 3: the three graph-norm convergences -/

/-- The approximate-identity citation, in the kernel-on-the-right convention. -/
theorem tendsto_eLpNorm_moll {g : Vec d → ℝ} (hg : MemLp g 2 volume) :
    Tendsto (fun n => eLpNorm
      (fun x => (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollKernel d n) x - g x) 2 volume)
      atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)) (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num) hg
    (r := 1) one_pos (ε := unitConvexApproxScale) tendsto_unitConvexApproxScale
    (Eventually.of_forall unitConvexApproxScale_pos)
  simp only [mul_one] at h
  refine h.congr fun n => ?_
  rw [convolution_comm_lsmul]
  rfl

theorem tendsto_mollPhi (hU : IsOpen U) (u : H10Function U) :
    Tendsto (fun n => eLpNorm (fun x => mollPhi u n x - u.zeroExtension x) 2 volume)
      atTop (𝓝 0) :=
  tendsto_eLpNorm_moll (memLp_zeroExtension_two hU u)

theorem tendsto_mollPhi_grad (hU : IsOpen U) (u : H10Function U) (i : Fin d) :
    Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (mollPhi u n) x (Pi.single i 1) - u.zeroExtensionGrad x i) 2 volume)
      atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_moll (d := d) (memLp_zeroExtensionGrad_two hU u i)
  refine h.congr fun n => ?_
  refine eLpNorm_congr_ae (Eventually.of_forall fun x => ?_)
  have hx : fderiv ℝ (mollPhi u n) x (Pi.single i 1)
      = ((fun y => u.zeroExtensionGrad y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          mollKernel d n) x := fderiv_mollPhi hU u n i x
  simp only [hx]

theorem tendsto_mollForcing (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) :
    Tendsto (fun n => eLpNorm (fun x => mollForcing U f n x - U.indicator f x) 2 volume)
      atTop (𝓝 0) :=
  tendsto_eLpNorm_moll (memLp_indicator_two hU hf)

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
