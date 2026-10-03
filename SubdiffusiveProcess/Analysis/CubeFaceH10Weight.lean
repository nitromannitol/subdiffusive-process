module

public import SubdiffusiveProcess.Analysis.CubeFaceSmoothWeight
public import Homogenization.Sobolev.H1.Definitions
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

open MeasureTheory Filter Set Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess


/-- Weighted Fatou along an L2-convergent sequence. -/
theorem weighted_lintegral_le_of_tendsto_eLpNorm_two {d : ℕ}
    (w : SpatialCoordinates d → ℝ≥0∞) (hw : Measurable w)
    (g : SpatialCoordinates d → ℝ)
    (hg : AEStronglyMeasurable g (volume.restrict (cubeExtensionBox d)))
    (phi : ℕ → SpatialCoordinates d → ℝ) (hphi : ∀ n, Measurable (phi n))
    (hconv : Tendsto (fun n => eLpNorm (fun x => phi n x - g x) 2
      (volume.restrict (cubeExtensionBox d))) atTop (𝓝 0))
    (B : ℝ≥0∞) (hB : ∀ᶠ n in atTop,
      (∫⁻ x in cubeExtensionBox d, ENNReal.ofReal (phi n x ^ 2) * w x) ≤ B) :
    (∫⁻ x in cubeExtensionBox d, ENNReal.ofReal (g x ^ 2) * w x) ≤ B := by
  let mu := volume.restrict (cubeExtensionBox d)
  have hTIM : TendstoInMeasure mu phi atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (by simpa only [Pi.sub_apply] using! hconv)
  obtain ⟨ns, hns, hae⟩ := hTIM.exists_seq_tendsto_ae
  let H : ℕ → SpatialCoordinates d → ℝ≥0∞ := fun k x =>
    ENNReal.ofReal (phi (ns k) x ^ 2) * w x
  have hHm : ∀ k, Measurable (H k) := fun k =>
    ((hphi (ns k)).pow_const 2).ennreal_ofReal.mul hw
  have hpoint : ∀ᵐ x ∂mu,
      ENNReal.ofReal (g x ^ 2) * w x ≤ liminf (fun k => H k x) atTop := by
    filter_upwards [hae] with x hx
    have hn : Tendsto (fun k => ENNReal.ofReal (phi (ns k) x ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (g x ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hx.pow 2)
    have h := ENNReal.le_liminf_mul
      (u := fun k => ENNReal.ofReal (phi (ns k) x ^ 2))
      (v := fun _ : ℕ => w x) (f := atTop)
    simpa only [hn.liminf_eq, liminf_const] using! h
  have hB' : ∀ᶠ k in atTop, (∫⁻ x in cubeExtensionBox d, H k x) ≤ B :=
    hns.tendsto_atTop.eventually hB
  calc
    _ ≤ ∫⁻ x in cubeExtensionBox d, liminf (fun k => H k x) atTop :=
      lintegral_mono_ae hpoint
    _ ≤ liminf (fun k => ∫⁻ x in cubeExtensionBox d, H k x) atTop :=
      lintegral_liminf_le hHm
    _ ≤ B := liminf_le_of_frequently_le' hB'.frequently

theorem cubeFace_approx_gradient_bounded {d : ℕ}
    (u : H10Function (cubeExtensionBox d)) (i : Fin d) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ᶠ n in atTop,
      (∫⁻ x in cubeExtensionBox d,
        ENNReal.ofReal ((fderiv ℝ (u.approx n) x (basisVec i)) ^ 2)) ≤ B := by
  let mu := volume.restrict (cubeExtensionBox d)
  let w : SpatialCoordinates d → ℝ := fun x => u.toH1Function.grad x i
  let M := 1 + eLpNorm w 2 mu
  have hw : MemLp w 2 mu := u.toH1Function.gradMemL2 i
  have hMt : M ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hw.eLpNorm_ne_top⟩
  have he : ∀ᶠ n in atTop, eLpNorm
      (fun x => fderiv ℝ (u.approx n) x (basisVec i) - w x) 2 mu ≤ 1 :=
    (u.tendsto_approx_grad i).eventually (Iic_mem_nhds (by norm_num))
  refine ⟨M ^ 2, ENNReal.pow_ne_top hMt, ?_⟩
  filter_upwards [he] with n hn
  let f : SpatialCoordinates d → ℝ := fun x => fderiv ℝ (u.approx n) x (basisVec i)
  have hfm : AEStronglyMeasurable f mu :=
    ((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply
      continuous_const |>.aestronglyMeasurable
  have htri : eLpNorm f 2 mu ≤ M := by
    calc
      _ = eLpNorm ((fun x => f x - w x) + w) 2 mu := by
        congr 1; funext x; simp
      _ ≤ eLpNorm (fun x => f x - w x) 2 mu + eLpNorm w 2 mu :=
        eLpNorm_add_le (by norm_num)
      _ ≤ M := add_le_add hn le_rfl
  rw [← eLpNorm_two_sq_eq_lintegral_sq_of_aestronglyMeasurable mu f hfm]
  exact pow_le_pow_left₀ bot_le htri 2

/-- The boundary-weighted integral is finite on the native H1_0 carrier. -/
theorem cubeFaceWeightedIntegral_ne_top_of_H10Function {d : ℕ} (s : ℝ) (hs : s < 1)
    (u : H10Function (cubeExtensionBox d)) (upper : Bool) (i : Fin d) :
    cubeFaceWeightedIntegral s upper i (u : SpatialCoordinates d → ℝ) ≠ ⊤ := by
  obtain ⟨B, hBt, hB⟩ := cubeFace_approx_gradient_bounded u i
  let C := ENNReal.ofReal ((2 - 2 * s)⁻¹)
  have he : ∀ᶠ n in atTop,
      cubeFaceWeightedIntegral s upper i (u.approx n) ≤ C * B := by
    filter_upwards [hB] with n hn
    exact (cubeFaceWeightedIntegral_smooth_le s hs upper i (u.approx n)
      ((u.approx_smooth n).of_le (by simp)) (u.approx_support_subset n)).trans
        (mul_le_mul_of_nonneg_left hn bot_le)
  have hlim : cubeFaceWeightedIntegral s upper i (u : SpatialCoordinates d → ℝ) ≤ C * B :=
    weighted_lintegral_le_of_tendsto_eLpNorm_two
      (cubeFaceWeight s upper i) (measurable_cubeFaceWeight s upper i) u
      u.toH1Function.memL2.aestronglyMeasurable u.approx
      (fun n => (u.approx_smooth n).continuous.measurable) u.tendsto_approx (C * B) he
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBt) hlim

end SubdiffusiveProcess
