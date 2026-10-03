module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal RealInnerProductSpace BoundedContinuousFunction

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}

/-- **The killed resolvent as an operator on `L²(U, ρ dx)`.** -/
def killedResolventLp (hD : LocalDiffusion c rho law) [IsMarkovKernel law]
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] (s : ℝ) (hs : 0 < s) :
    Lp ℝ 2 ((weightedMeasure rho).restrict U) →L[ℝ]
      Lp ℝ 2 ((weightedMeasure rho).restrict U) :=
  kernelLpFinite ((weightedMeasure rho).restrict U) (resolventKernel law U hU s hs)
    (resolventKernel_subMarkov law U hU s hs)
    (resolventKernel_subinvariant hD hU hUb s hs) 2

variable {hD : LocalDiffusion c rho law} {hU : IsOpen U} {hUb : Bornology.IsBounded U}
  {s : ℝ} {hs : 0 < s}

/-- The operator is represented by the raw killed resolvent. -/
theorem killedResolventLp_coeFn [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (f : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    killedResolventLp hD hU hUb s hs f
      =ᵐ[(weightedMeasure rho).restrict U] killedResolvent law U s f := by
  refine (coeFn_kernelLpFinite _ _ _ _ 2 f).trans ?_
  exact resolventKernel_integral_ae law U hU s hs _
    (resolventKernel_subinvariant hD hU hUb s hs) _
    ((Lp.memLp f).integrable (by norm_num))

/-- **The `L²` pairing of the killed resolvent operator against bounded continuous data.**
Both sides unwind to the raw `Section9SupportInput.killedResolvent`. -/
theorem inner_killedResolventLp_toLp [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] (f g : Vec d →ᵇ ℝ) :
    ⟪killedResolventLp hD hU hUb s hs
        (BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ f),
      BoundedContinuousFunction.toLp 2 ((weightedMeasure rho).restrict U) ℝ g⟫
      = ∫ x, g x * killedResolvent law U s f x ∂((weightedMeasure rho).restrict U) := by
  set mu := (weightedMeasure rho).restrict U with hmu
  have hsubinv := resolventKernel_subinvariant hD hU hUb s hs
  have hfint : Integrable (f : Vec d → ℝ) mu :=
    Integrable.mono' (integrable_const ‖f‖) f.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall f.norm_coe_le_norm)
  have h1 := resolventKernel_integral_ae law U hU s hs mu hsubinv
    ((BoundedContinuousFunction.toLp 2 mu ℝ f : Lp ℝ 2 mu) : Vec d → ℝ)
    ((Lp.memLp (BoundedContinuousFunction.toLp 2 mu ℝ f)).integrable (by norm_num))
  have h2 := kernelIntegral_congr_ae hsubinv
    (BoundedContinuousFunction.coeFn_toLp 2 mu ℝ f)
  have h3 := resolventKernel_integral_ae law U hU s hs mu hsubinv (f : Vec d → ℝ) hfint
  rw [inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [killedResolventLp_coeFn (hD := hD) (hU := hU) (hUb := hUb)
      (s := s) (hs := hs) (BoundedContinuousFunction.toLp 2 mu ℝ f),
    h1, h2, h3, BoundedContinuousFunction.coeFn_toLp 2 mu ℝ g] with x hx hx1 hx2 hx3 hxg
  rw [hx, ← hx1, hx2, hx3, hxg, mul_comm]

theorem norm_killedResolventLp_le [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] :
    ‖killedResolventLp hD hU hUb s hs‖ ≤ 1 :=
  norm_kernelLpFinite_le _ _ _ _ 2

/-- **`R` is symmetric.** -/
theorem isSymmetricOp_killedResolventLp [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)] :
    IsSymmetricOp (killedResolventLp hD hU hUb s hs) := by
  intro F G
  rw [inner_eq_integral, inner_eq_integral]
  have hF : (∫ x, (killedResolventLp hD hU hUb s hs F) x * G x
        ∂((weightedMeasure rho).restrict U))
      = ∫ x, G x * killedResolvent law U s F x ∂((weightedMeasure rho).restrict U) := by
    refine integral_congr_ae ?_
    filter_upwards [killedResolventLp_coeFn (hD := hD) (hU := hU) (hUb := hUb)
      (s := s) (hs := hs) F] with x hx
    rw [hx, mul_comm]
  have hG : (∫ x, F x * (killedResolventLp hD hU hUb s hs G) x
        ∂((weightedMeasure rho).restrict U))
      = ∫ x, F x * killedResolvent law U s G x ∂((weightedMeasure rho).restrict U) := by
    refine integral_congr_ae ?_
    filter_upwards [killedResolventLp_coeFn (hD := hD) (hU := hU) (hUb := hUb)
      (s := s) (hs := hs) G] with x hx
    rw [hx]
  rw [hF, hG]
  exact killedResolvent_pairing_eq hD hU hUb hs (Lp.memLp G) (Lp.memLp F)


/-- `vecDot v v` is nonnegative. -/
theorem vecDot_self_nonneg (v : Vec d) : 0 ≤ vecDot v v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- **`R` is positive.**

Testing the massive weak formulation `s⁻¹ ρ u - ∇·(c∇u) = s⁻¹ ρ f` against `u = R f`
itself gives `⟪R f, f⟫ = ∫_U ρ u² + s ∫_U c |∇u|²`, and `ρ, c` are bounded below by a
positive constant on `U` by `LocalDiffusion`'s local coefficient clause. -/
theorem inner_killedResolventLp_nonneg [IsMarkovKernel law]
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (F : Lp ℝ 2 ((weightedMeasure rho).restrict U)) :
    0 ≤ ⟪killedResolventLp hD hU hUb s hs F, F⟫ := by
  have hr : CoefficientOn U rho := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).2
  have hc : CoefficientOn U c := coefficientOn_mono subset_closure
    (hD.2.1 (closure U) hUb.isCompact_closure).1
  obtain ⟨u, hueq, hu⟩ := hD.2.2 U hU hUb s hs (F : Vec d → ℝ) (Lp.memLp F)
  have hAc := volume_restrict_absolutelyContinuous_weightedMeasure_restrict hU.measurableSet hr
  have hRu : (fun x => (killedResolventLp hD hU hUb s hs F) x)
      =ᵐ[volume.restrict U] fun x => u.toH1Function.toFun x := by
    refine Filter.EventuallyEq.filter_mono ?_ hAc.ae_le
    filter_upwards [killedResolventLp_coeFn (hD := hD) (hU := hU) (hUb := hUb)
      (s := s) (hs := hs) F, hueq] with x hx hx2
    rw [hx, hx2]
  have hkey : ⟪killedResolventLp hD hU hUb s hs F, F⟫
      = ∫ x in U, rho x * F x * u.toH1Function.toFun x := by
    rw [inner_eq_integral, integral_weightedMeasure_restrict_eq hU.measurableSet rho _ hr]
    refine integral_congr_ae ?_
    filter_upwards [hRu] with x hx
    rw [hx]
    ring
  have hweak := hu u
  rw [integral_mass_scaled_forcing U rho (F : Vec d → ℝ) u.toH1Function.toFun s⁻¹] at hweak
  have hA : 0 ≤ ∫ x in U, rho x * u.toH1Function.toFun x * u.toH1Function.toFun x := by
    obtain ⟨-, lo, hi, hlo, hb⟩ := hr
    refine integral_nonneg_of_ae ?_
    filter_upwards [hb] with x hx
    have hrx : 0 ≤ rho x := hlo.le.trans hx.1
    simp only [Pi.zero_apply]
    nlinarith [mul_self_nonneg (u.toH1Function.toFun x)]
  have hB : 0 ≤ ∫ x in U,
      vecDot (c x • u.toH1Function.grad x) (u.toH1Function.grad x) := by
    obtain ⟨-, lo, hi, hlo, hb⟩ := hc
    refine integral_nonneg_of_ae ?_
    filter_upwards [hb] with x hx
    simp only [Pi.zero_apply]
    rw [vecDot_smul_left]
    exact mul_nonneg (hlo.le.trans hx.1) (vecDot_self_nonneg _)
  have hsinv : 0 < s⁻¹ := inv_pos.2 hs
  rw [hkey]
  nlinarith [hweak, hA, hB, hsinv]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledResolventLp
