module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.OscillationPoincare

@[expose] public section

/-!
# Integration by parts of `H¹₀` functions of the unit cube against a coordinate

For `u ∈ H¹₀((-1/2,1/2)^d)` and every coordinate `i`: `∫ u = -∫ ∂_i u · x_i`.  This replaces the torsion-function
step of the paper's proof of `\eqref{e.CG.Poincare.trace.zero}` (`inputs_poincare_killed_endpoint`): it is proved
for smooth compactly supported functions by Mathlib's integration by parts on `ℝ^d` and passed to the limit through the
`L²` approximants of the `H¹₀` structure.
-/

open MeasureTheory
open Homogenization

namespace SubdiffusiveProcess.Besov.Detach

noncomputable section

theorem ibp_smooth {d : ℕ} (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (i : Fin d) :
    ∫ x, (fderiv ℝ φ x) (basisVec i) * x i = - ∫ x, φ x := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hg : Differentiable ℝ (fun x : Vec d => x i) := (differentiable_apply i)
  have hgd : ∀ x : Vec d, (fderiv ℝ (fun x : Vec d => x i) x) (basisVec i) = 1 := by
    intro x
    have : fderiv ℝ (fun x : Vec d => x i) x = ContinuousLinearMap.proj i := by
      exact (hasFDerivAt_apply i x).fderiv
    rw [this]
    simp [basisVec]
  have hcont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have h1 : Integrable (fun x => (fderiv ℝ φ x) (basisVec i) * x i) volume := by
    have hcs : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i) * x i) :=
      (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) (by simp) |>.mul_right
    exact (Continuous.integrable_of_hasCompactSupport
      ((hcont.clm_apply continuous_const).mul (continuous_apply i)) hcs)
  have h2 : Integrable (fun x => φ x * (fderiv ℝ (fun x : Vec d => x i) x) (basisVec i)) volume := by
    simp only [hgd, mul_one]
    exact hφ.continuous.integrable_of_hasCompactSupport hc
  have h3 : Integrable (fun x => φ x * x i) volume :=
    (hφ.continuous.mul (continuous_apply i)).integrable_of_hasCompactSupport hc.mul_right
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Vec d)))
    (f := φ) (g := fun x : Vec d => x i) (v := basisVec i) h1 h2 h3 (fun x _ => hd x) (fun x _ => hg x)
  simp only [hgd, mul_one] at this
  linarith

/-- `L²` convergence on a finite-measure set gives convergence of integrals against a bounded continuous weight. -/
theorem tendsto_integral_mul_of_L2 {d : ℕ} (U : Set (Vec d)) (hU : MeasurableSet U)
    (hfin : volume U < ⊤)
    (f : ℕ → Vec d → ℝ) (f0 g : Vec d → ℝ) (M : ℝ) (hg : Continuous g)
    (hgb : ∀ x ∈ U, |g x| ≤ M)
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict U)) (hf0 : MemLp f0 2 (volume.restrict U))
    (hlim : Filter.Tendsto (fun n => eLpNorm (fun x => f n x - f0 x) 2 (volume.restrict U))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x in U, f n x * g x) Filter.atTop
      (nhds (∫ x in U, f0 x * g x)) := by
  haveI : IsFiniteMeasure (volume.restrict U) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hM : ∀ᵐ x ∂(volume.restrict U), ‖g x‖ ≤ M := by
    filter_upwards [ae_restrict_mem hU] with x hx
    simpa [Real.norm_eq_abs] using hgb x hx
  have hgm : AEStronglyMeasurable g (volume.restrict U) := hg.aestronglyMeasurable
  have hint : ∀ h : Vec d → ℝ, MemLp h 2 (volume.restrict U) →
      Integrable (fun x => h x * g x) (volume.restrict U) := by
    intro h hh
    exact (hh.integrable one_le_two).mul_bdd hgm hM
  refine tendsto_integral_of_L1' (fun x => f0 x * g x)
    (Filter.Eventually.of_forall fun n => hint (f n) (hf n)) ?_
  have h1 : ∀ n, eLpNorm ((fun x => f n x * g x) - (fun x => f0 x * g x)) 1 (volume.restrict U) ≤
      ENNReal.ofReal M * (eLpNorm (fun x => f n x - f0 x) 2 (volume.restrict U) *
        (volume.restrict U) Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)) := by
    intro n
    have hA : eLpNorm ((fun x => f n x * g x) - (fun x => f0 x * g x)) 1 (volume.restrict U) ≤
        ENNReal.ofReal M * eLpNorm (fun x => f n x - f0 x) 1 (volume.restrict U) := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (f := (fun x => f n x * g x) - (fun x => f0 x * g x))
        (g := fun x => f n x - f0 x) (c := M)
        (((hf n).aestronglyMeasurable.mul hgm).sub (hf0.aestronglyMeasurable.mul hgm))
      filter_upwards [hM] with x hx
      simp only [Pi.sub_apply, Pi.mul_apply, ← sub_mul, norm_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg (f n x - f0 x))
    have hB : eLpNorm (fun x => f n x - f0 x) 1 (volume.restrict U) ≤
        eLpNorm (fun x => f n x - f0 x) 2 (volume.restrict U) *
          (volume.restrict U) Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num)
        (((hf n).sub hf0).aestronglyMeasurable)
    exact hA.trans (by gcongr)
  have h2 : Filter.Tendsto (fun n => ENNReal.ofReal M * (eLpNorm (fun x => f n x - f0 x) 2 (volume.restrict U) *
        (volume.restrict U) Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)))
      Filter.atTop (nhds 0) := by
    have hc : (volume.restrict U) Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
    have h2' := ENNReal.Tendsto.mul_const hlim (Or.inr hc)
    have h3 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M) h2' (Or.inr ENNReal.ofReal_ne_top)
    simpa using h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => bot_le) h1

theorem abs_coord_le_of_mem_openCubeSet {d : ℕ} (x : Vec d) (hx : x ∈ openCubeSet (originCube d 0))
    (i : Fin d) : |x i| ≤ 1 / 2 := by
  have h := hx i
  simp only [originCube, cubeScaleFactor, zpow_zero, Pi.zero_apply, Int.cast_zero, zero_sub,
    zero_add] at h
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

theorem volume_openCubeSet_lt_top {d : ℕ} (Q : TriadicCube d) : volume (openCubeSet Q) < ⊤ :=
  (isBounded_openCubeSet Q).measure_lt_top

/-- Integration by parts of an `H¹₀` function of the unit cube against a coordinate function. -/
theorem killed_ibp {d : ℕ} (u : H10Function (openCubeSet (originCube d 0))) (i : Fin d) :
    ∫ x in openCubeSet (originCube d 0), u.toFun x =
      - ∫ x in openCubeSet (originCube d 0), u.grad x i * x i := by
  let U : Set (Vec d) := openCubeSet (originCube d 0)
  have hUm : MeasurableSet U := (isOpen_openCubeSet _).measurableSet
  have hUf : volume U < ⊤ := volume_openCubeSet_lt_top _
  have hxb : ∀ x ∈ U, |x i| ≤ 1 / 2 := fun x hx => abs_coord_le_of_mem_openCubeSet x hx i
  have hone : ∀ x ∈ U, |(1 : ℝ)| ≤ 1 := fun x _ => by simp
  -- the approximants
  have hφc : ∀ n, Continuous (u.approx n) := fun n => (u.approx_smooth n).continuous
  have hφmem : ∀ n, MemLp (u.approx n) 2 (volume.restrict U) := fun n =>
    ((hφc n).memLp_of_hasCompactSupport (u.approx_hasCompactSupport n)).mono_measure Measure.restrict_le_self
  have hdcont : ∀ n, Continuous (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) := fun n =>
    ((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdcs : ∀ n, HasCompactSupport (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) := fun n =>
    ((u.approx_hasCompactSupport n).fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) (by simp)
  have hdmem : ∀ n, MemLp (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) 2 (volume.restrict U) :=
    fun n => ((hdcont n).memLp_of_hasCompactSupport (hdcs n)).mono_measure Measure.restrict_le_self
  -- the identity for each approximant
  have hid : ∀ n, ∫ x in U, u.approx n x * 1 =
      - ∫ x in U, (fderiv ℝ (u.approx n) x) (basisVec i) * x i := by
    intro n
    have h1 : ∫ x in U, u.approx n x * 1 = ∫ x, u.approx n x := by
      simp only [mul_one]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun h => hx (u.approx_support_subset n h))
    have h2 : ∫ x in U, (fderiv ℝ (u.approx n) x) (basisVec i) * x i =
        ∫ x, (fderiv ℝ (u.approx n) x) (basisVec i) * x i := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      have : x ∉ tsupport (u.approx n) := fun h => hx (u.approx_support_subset n h)
      have hz : fderiv ℝ (u.approx n) x = 0 := by
        by_contra hne
        exact this (support_fderiv_subset ℝ hne)
      simp [hz]
    rw [h1, h2, ibp_smooth _ (u.approx_smooth n) (u.approx_hasCompactSupport n) i]
    ring
  have hL := tendsto_integral_mul_of_L2 U hUm hUf u.approx u.toFun (fun _ => (1 : ℝ)) 1
    continuous_const hone hφmem u.memL2 u.tendsto_approx
  have hR := tendsto_integral_mul_of_L2 U hUm hUf
    (fun n x => (fderiv ℝ (u.approx n) x) (basisVec i)) (fun x => u.grad x i) (fun x => x i) (1 / 2)
    (continuous_apply i) hxb hdmem (u.gradMemL2 i) (u.tendsto_approx_grad i)
  have hR' := hR.neg
  have heq : (fun n => ∫ x in U, u.approx n x * (fun _ => (1 : ℝ)) x) =
      fun n => - ∫ x in U, (fderiv ℝ (u.approx n) x) (basisVec i) * x i := by
    funext n
    exact hid n
  rw [heq] at hL
  have h5 := tendsto_nhds_unique hL hR'
  simp only [mul_one] at h5
  exact h5

end

end SubdiffusiveProcess.Besov.Detach
