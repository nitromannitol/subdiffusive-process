module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserBoundedComposition
public import Homogenization.Sobolev.Truncation.H10Limit

@[expose] public section

/-!
# Zero-preserving compositions retain zero trace

The approximants come from the given H¹₀ function. A bounded derivative
controls the value and gradient errors; continuity of the derivative and
dominated convergence handle the remaining gradient term. The target may
use any almost-everywhere equal representative of the composite.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A zero-preserving C¹ composition with bounded derivative has zero trace. -/
theorem variational_memH10_comp {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H10Function U) (v : H1Function U)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0)
    {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv G t| ≤ M)
    (hval : v.toFun =ᵐ[volume.restrict U] fun x => G (u.toH1Function.toFun x))
    (hgrad : ∀ i, (fun x => v.grad x i) =ᵐ[volume.restrict U]
      fun x => deriv G (u.toH1Function.toFun x) * u.toH1Function.grad x i) :
    MemH10 U v.toFun := by
  letI : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  have hdiff : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hLip := lipschitzWith_of_abs_deriv_le hM hdiff hderiv
  have hDc : Continuous (deriv G) := hG.continuous_deriv (by norm_num)
  have hsmooth (n : ℕ) : ContDiff ℝ 1 (fun x => G (u.approx n x)) :=
    hG.comp ((u.approx_smooth n).of_le (by norm_num))
  let V : ℕ → H1Function U := fun n =>
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU (hsmooth n)
  have hVf (n : ℕ) (x : Vec d) : (V n).toFun x = G (u.approx n x) := rfl
  have hVg (n : ℕ) (x : Vec d) (i : Fin d) :
      (V n).grad x i = deriv G (u.approx n x) *
        (fderiv ℝ (u.approx n) x) (basisVec i) := by
    exact fderiv_comp_basisVec hdiff.differentiableAt
      ((u.approx_smooth n).differentiable (by norm_num)).differentiableAt
  have hmem (n : ℕ) : MemH10 U (V n).toFun := by
    refine memH10_of_compactSupport hU (V n) (u.approx_hasCompactSupport n)
      (u.approx_support_subset n) ?_
    intro x hx
    rw [hVf, image_eq_zero_of_notMem_tsupport hx, hG0]
  obtain ⟨sigma, hsigma, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      u.tendsto_approx).exists_seq_tendsto_ae
  apply memH10_of_tendsto_H1 hU v (fun n => V (sigma n)) (fun n => hmem (sigma n))
  · have hupper : Tendsto (fun n => ENNReal.ofReal M *
        eLpNorm (fun x => u.approx (sigma n) x - u.toH1Function.toFun x) 2
          (volume.restrict U)) atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M)
        (u.tendsto_approx.comp hsigma.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => zero_le) (fun n => ?_)
    rw [eLpNorm_sub_swap]
    calc
      _ = eLpNorm (fun x => G (u.approx (sigma n) x) -
          G (u.toH1Function.toFun x)) 2 (volume.restrict U) :=
        eLpNorm_congr_ae (hval.mono fun x hx => by rw [hVf, hx])
      _ ≤ _ := eLpNorm_comp_sub_le_of_lipschitz hM hLip _ _
        (u.approx_smooth (sigma n)).continuous.aestronglyMeasurable
        u.toH1Function.memL2.aestronglyMeasurable
  · intro i
    let TA : ℕ → Vec d → ℝ := fun n x => deriv G (u.approx (sigma n) x) *
      ((fderiv ℝ (u.approx (sigma n)) x) (basisVec i) - u.toH1Function.grad x i)
    let TB : ℕ → Vec d → ℝ := fun n x =>
      (deriv G (u.approx (sigma n) x) - deriv G (u.toH1Function.toFun x)) *
        u.toH1Function.grad x i
    have hmeasA (n : ℕ) : AEStronglyMeasurable (TA n) (volume.restrict U) :=
      (hDc.comp (u.approx_smooth (sigma n)).continuous).aestronglyMeasurable.mul
        ((((u.approx_smooth (sigma n)).continuous_fderiv (by norm_num)).clm_apply
          continuous_const).aestronglyMeasurable.sub (u.toH1Function.gradMemL2 i).aestronglyMeasurable)
    have hmeasB (n : ℕ) : AEStronglyMeasurable (TB n) (volume.restrict U) :=
      ((hDc.comp (u.approx_smooth (sigma n)).continuous).aestronglyMeasurable.sub
        (hDc.comp_aestronglyMeasurable u.toH1Function.memL2.aestronglyMeasurable)).mul
          (u.toH1Function.gradMemL2 i).aestronglyMeasurable
    have hTA : Tendsto (fun n => eLpNorm (TA n) 2 (volume.restrict U)) atTop (nhds 0) := by
      have hupper : Tendsto (fun n => ENNReal.ofReal M * eLpNorm
          (fun x => (fderiv ℝ (u.approx (sigma n)) x) (basisVec i) - u.toH1Function.grad x i)
          2 (volume.restrict U)) atTop (nhds 0) := by
        simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M)
          ((u.tendsto_approx_grad i).comp hsigma.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
        (fun _ => zero_le) (fun n => ?_)
      calc
        _ ≤ eLpNorm (M • fun x => (fderiv ℝ (u.approx (sigma n)) x) (basisVec i) -
            u.toH1Function.grad x i) 2 (volume.restrict U) := by
          apply eLpNorm_mono (hmeasA n)
          intro x
          simp only [TA, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
            abs_of_nonneg hM]
          exact mul_le_mul_of_nonneg_right (hderiv _) (abs_nonneg _)
        _ = _ := by rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hM]
    have hTB : Tendsto (fun n => eLpNorm (TB n) 2 (volume.restrict U)) atTop (nhds 0) := by
      have hdom := ((u.toH1Function.gradMemL2 i).const_mul (2 * M)).norm
      have hbound (n : ℕ) : ∀ᵐ x ∂volume.restrict U,
          ‖TB n x‖ ≤ ‖(2 * M) * u.toH1Function.grad x i‖ := by
        filter_upwards with x
        simp only [TB, norm_mul, Real.norm_eq_abs, abs_of_nonneg hM,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        calc
          _ ≤ |deriv G (u.approx (sigma n) x)| + |deriv G (u.toH1Function.toFun x)| := abs_sub _ _
          _ ≤ M + M := add_le_add (hderiv _) (hderiv _)
          _ = _ := by ring
      have hlim : ∀ᵐ x ∂volume.restrict U, Tendsto (fun n => TB n x) atTop (nhds 0) := by
        filter_upwards [hae] with x hx
        have h := (((hDc.tendsto _).comp hx).sub
          (tendsto_const_nhds (x := deriv G (u.toH1Function.toFun x)))).mul_const
          (u.toH1Function.grad x i)
        simpa only [TB, Function.comp_def, sub_self, zero_mul] using h
      simpa using tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hmeasB
        (memLp_const (0 : ℝ)) hdom hbound hlim
    have hsum : Tendsto (fun n => eLpNorm (TA n) 2 (volume.restrict U) +
        eLpNorm (TB n) 2 (volume.restrict U)) atTop (nhds 0) := by simpa using hTA.add hTB
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) (fun n => ?_)
    rw [eLpNorm_sub_swap]
    calc
      _ = eLpNorm (fun x => TA n x + TB n x) 2 (volume.restrict U) := by
        apply eLpNorm_congr_ae
        filter_upwards [hgrad i] with x hx
        rw [hVg, hx]
        dsimp only [TA, TB]
        ring
      _ ≤ _ := eLpNorm_add_le (f := TA n) (g := TB n) (by norm_num)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
