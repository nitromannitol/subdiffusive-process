module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationContinuity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationLaplace
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationMixture
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationResolventOperator
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

@[expose] public section

/-!
# Symmetry of the killed semigroup

The local diffusion datum only provides the weak resolvent realisation, hence
symmetry of the killed resolvent.  Since the resolvent is the Laplace transform
of the killed semigroup and the semigroup pairings are right-continuous in time,
uniqueness of Laplace transforms transfers symmetry to every killed transition
kernel.
-/

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal ProbabilityTheory Topology BoundedContinuousFunction
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration

variable {d : ℕ}

/-- The killed resolvent is the exponential time average of the killed semigroup. -/
theorem killedResolvent_eq_expMeasure_integral (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s) (g : Vec d → ℝ) (hg : Measurable g)
    (x : Vec d) :
    killedResolvent law U s g x =
      ∫ t, kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x ∂(expMeasure s⁻¹) := by
  rw [integral_expMeasure s hs
    (fun t => kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x)]
  unfold killedResolvent
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [killedKernel_integral law U hU (Real.toNNReal t) g hg x,
    show ((Real.toNNReal t : NNReal) : ℝ≥0∞) = ENNReal.ofReal t from rfl]

/-- The killed semigroup pairing against a finite measure. -/
def killedPairing (law : Kernel (Vec d) (Path d)) (U : Set (Vec d)) (hU : IsOpen U)
    (mu : Measure (Vec d)) (f g : Vec d → ℝ) (t : ℝ) : ℝ :=
  ∫ x, f x * kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x ∂mu

/-- The killed semigroup pairing is jointly measurable in time. -/
theorem measurable_killedPairing (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (mu : Measure (Vec d)) [SFinite mu]
    (f g : Vec d → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (killedPairing law U hU mu f g) := by
  have hjoint : Measurable
      (fun q : NNReal × Vec d => ∫ y, g y ∂(killedJointKernel law U hU q)) :=
    measurable_kernelIntegral_function (killedJointKernel law U hU) g hg
  have hjoint' : StronglyMeasurable
      (fun q : ℝ × Vec d => f q.2 *
        kernelIntegral (killedKernel law U hU (Real.toNNReal q.1)) g q.2) := by
    refine ((hf.comp measurable_snd).mul ?_).stronglyMeasurable
    exact hjoint.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  exact (hjoint'.integral_prod_right').measurable

/-- The killed semigroup pairing is bounded. -/
theorem norm_killedPairing_le (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (mu : Measure (Vec d)) [IsFiniteMeasure mu]
    (f g : Vec d →ᵇ ℝ) (t : ℝ) :
    |killedPairing law U hU mu f g t| ≤ ‖f‖ * ‖g‖ * (mu Set.univ).toReal := by
  have hb : ∀ x, ‖f x * kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x‖
      ≤ ‖f‖ * ‖g‖ := by
    intro x
    rw [norm_mul]
    exact mul_le_mul (f.norm_coe_le_norm x)
      (norm_killedKernel_integral_le law U hU g t x) (norm_nonneg _) (norm_nonneg _)
  have := norm_integral_le_of_norm_le_const (μ := mu) (C := ‖f‖ * ‖g‖)
    (Filter.Eventually.of_forall hb)
  rw [Real.norm_eq_abs] at this
  simpa only [killedPairing, mul_comm, Measure.real] using! this


/-- Joint strong measurability of the killed pairing integrand. -/
theorem stronglyMeasurable_killedPairFun (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (f g : Vec d → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    StronglyMeasurable (fun q : Vec d × ℝ =>
      f q.1 * kernelIntegral (killedKernel law U hU (Real.toNNReal q.2)) g q.1) := by
  have hjoint : Measurable
      (fun q : NNReal × Vec d => ∫ y, g y ∂(killedJointKernel law U hU q)) :=
    measurable_kernelIntegral_function (killedJointKernel law U hU) g hg
  refine ((hf.comp measurable_fst).mul ?_).stronglyMeasurable
  exact hjoint.comp (measurable_snd.real_toNNReal.prodMk measurable_fst)

/-- The resolvent pairing is the exponential time average of the semigroup pairings. -/
theorem killedResolvent_pairing_eq_expMeasure (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law]
    (U : Set (Vec d)) (hU : IsOpen U) (mu : Measure (Vec d)) [IsFiniteMeasure mu]
    (f g : Vec d →ᵇ ℝ) (s : ℝ) (hs : 0 < s) :
    (∫ x, f x * killedResolvent law U s g x ∂mu)
      = ∫ t, killedPairing law U hU mu f g t ∂(expMeasure s⁻¹) := by
  letI := exponential_probability s hs
  have hstep : ∀ x, f x * killedResolvent law U s g x
      = ∫ t, f x * kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x
          ∂(expMeasure s⁻¹) := by
    intro x
    rw [killedResolvent_eq_expMeasure_integral law U hU s hs g g.continuous.measurable x,
      integral_const_mul]
  have hsm := stronglyMeasurable_killedPairFun law U hU f g
    f.continuous.measurable g.continuous.measurable
  have hint : Integrable (Function.uncurry
      (fun (x : Vec d) (t : ℝ) =>
        f x * kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x))
      (mu.prod (expMeasure s⁻¹)) := by
    refine Integrable.mono' (integrable_const (‖f‖ * ‖g‖)) hsm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    show ‖f q.1 * kernelIntegral (killedKernel law U hU (Real.toNNReal q.2)) g q.1‖ ≤ ‖f‖ * ‖g‖
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (by simpa only [← Real.norm_eq_abs] using f.norm_coe_le_norm q.1)
      (by simpa only [← Real.norm_eq_abs] using
        norm_killedKernel_integral_le law U hU g q.2 q.1)
      (abs_nonneg _) (norm_nonneg _)
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep)]
  exact integral_integral_swap hint


/-- The killed semigroup pairings are symmetric at every nonnegative time. -/
theorem killedPairing_symm {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law] {U : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (f g : Vec d →ᵇ ℝ) (t : ℝ) (ht : 0 ≤ t) :
    killedPairing law U hU ((weightedMeasure rho).restrict U) f g t
      = killedPairing law U hU ((weightedMeasure rho).restrict U) g f t := by
  set mu := (weightedMeasure rho).restrict U with hmudef
  have hmemf : MemLp (f : Vec d → ℝ) 2 mu :=
    MemLp.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall f.norm_coe_le_norm)
  have hmemg : MemLp (g : Vec d → ℝ) 2 mu :=
    MemLp.of_bound g.continuous.measurable.aestronglyMeasurable ‖g‖
      (Filter.Eventually.of_forall g.norm_coe_le_norm)
  refine eq_of_forall_integral_exp_neg_mul_eq_of_rightContinuous
    (measurable_killedPairing law U hU mu f g f.continuous.measurable g.continuous.measurable)
    (measurable_killedPairing law U hU mu g f g.continuous.measurable f.continuous.measurable)
    (fun r _ => continuousWithinAt_killedKernel_pairing law U hU mu f g r)
    (fun r _ => continuousWithinAt_killedKernel_pairing law U hU mu g f r)
    (C := ‖f‖ * ‖g‖ * (mu Set.univ).toReal)
    (fun r _ => norm_killedPairing_le law U hU mu f g r)
    (fun r _ => by
      simpa only [mul_comm ‖g‖ ‖f‖] using norm_killedPairing_le law U hU mu g f r)
    ?_ t ht
  intro r hr
  have hs : (0:ℝ) < r⁻¹ := inv_pos.mpr hr
  have hpair := killedResolvent_pairing_eq hD hU hUb hs hmemf hmemg
  rw [killedResolvent_pairing_eq_expMeasure law U hU mu f g r⁻¹ hs,
    killedResolvent_pairing_eq_expMeasure law U hU mu g f r⁻¹ hs,
    integral_expMeasure r⁻¹ hs, integral_expMeasure r⁻¹ hs, inv_inv] at hpair
  have hexp : ∀ u : ℝ, Real.exp (-u / r⁻¹) = Real.exp (-(r * u)) := by
    intro u
    congr 1
    field_simp
  simp only [hexp] at hpair
  exact mul_left_cancel₀ hr.ne' hpair


section Abstract

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X]

/-- Symmetry of all bounded continuous pairings is rectangle symmetry. -/
theorem rectangle_symmetry_of_bcnn {mu : Measure X} [IsFiniteMeasure mu]
    {kap : Kernel X X} (hsub : IsSubMarkovKernel kap)
    (hsym : ∀ f g : X →ᵇ ℝ≥0,
      (∫⁻ x, (f x : ℝ≥0∞) * (∫⁻ y, (g y : ℝ≥0∞) ∂kap x) ∂mu)
        = ∫⁻ x, (g x : ℝ≥0∞) * (∫⁻ y, (f y : ℝ≥0∞) ∂kap x) ∂mu)
    (C D : Set X) (hC : MeasurableSet C) (hD : MeasurableSet D) :
    (∫⁻ x in C, kap x D ∂mu) = ∫⁻ x in D, kap x C ∂mu := by
  letI : IsFiniteKernel kap := hsub.isFiniteKernel
  have hcoe : ∀ f : X →ᵇ ℝ≥0, Measurable (fun x : X => (f x : ℝ≥0∞)) :=
    fun f => f.continuous.measurable.coe_nnreal_ennreal
  have hker : ∀ f : X →ᵇ ℝ≥0, Measurable (fun x : X => ∫⁻ y, (f y : ℝ≥0∞) ∂kap x) :=
    fun f => (hcoe f).lintegral_kernel
  have hrow : ∀ E : Set X, MeasurableSet E → Measurable (fun x : X => kap x E) :=
    fun E hE => kap.measurable_coe hE
  -- Round 1: bounded continuous against an arbitrary measurable set
  have hround1 : ∀ (f : X →ᵇ ℝ≥0) (E : Set X), MeasurableSet E →
      (∫⁻ x, (f x : ℝ≥0∞) * kap x E ∂mu)
        = ∫⁻ x in E, (∫⁻ y, (f y : ℝ≥0∞) ∂kap x) ∂mu := by
    intro f E hE
    set nu1 : Measure X := kap ∘ₘ (mu.withDensity (fun x => (f x : ℝ≥0∞))) with hnu1def
    set nu2 : Measure X := mu.withDensity (fun x => ∫⁻ y, (f y : ℝ≥0∞) ∂kap x) with hnu2def
    have hnu1apply : ∀ E : Set X, MeasurableSet E →
        nu1 E = ∫⁻ x, (f x : ℝ≥0∞) * kap x E ∂mu := by
      intro E hE
      rw [hnu1def, Measure.bind_apply hE (Kernel.aemeasurable kap),
        lintegral_withDensity_eq_lintegral_mul _ (hcoe f) (hrow E hE)]
      rfl
    have hnu2apply : ∀ E : Set X, MeasurableSet E →
        nu2 E = ∫⁻ x in E, (∫⁻ y, (f y : ℝ≥0∞) ∂kap x) ∂mu := by
      intro E hE
      rw [hnu2def, withDensity_apply _ hE]
    have hfinite1 : IsFiniteMeasure nu1 := by
      refine ⟨?_⟩
      rw [hnu1apply Set.univ MeasurableSet.univ]
      refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (BoundedContinuousFunction.lintegral_lt_top_of_nnreal mu f)
      simpa only [mul_one] using mul_le_mul_right (hsub.measure_le_one x Set.univ) _
    have heq : nu1 = nu2 := by
      refine @ext_of_forall_lintegral_eq_of_IsFiniteMeasure X _ _ _ _ nu1 nu2 hfinite1 ?_
      intro g
      rw [hnu1def, Measure.lintegral_bind (Kernel.aemeasurable kap) (hcoe g).aemeasurable,
        lintegral_withDensity_eq_lintegral_mul _ (hcoe f) (hker g), hnu2def,
        lintegral_withDensity_eq_lintegral_mul _ (hker f) (hcoe g)]
      simp only [Pi.mul_apply]
      calc
        (∫⁻ x, (f x : ℝ≥0∞) * (∫⁻ y, (g y : ℝ≥0∞) ∂kap x) ∂mu)
            = ∫⁻ x, (g x : ℝ≥0∞) * (∫⁻ y, (f y : ℝ≥0∞) ∂kap x) ∂mu := hsym f g
        _ = ∫⁻ x, (∫⁻ y, (f y : ℝ≥0∞) ∂kap x) * (g x : ℝ≥0∞) ∂mu :=
            lintegral_congr fun x => mul_comm _ _
    rw [← hnu1apply E hE, heq, hnu2apply E hE]
  -- Round 2: two arbitrary measurable sets
  set nu1 : Measure X := mu.withDensity (fun x => kap x D) with hnu1def
  set nu2 : Measure X := kap ∘ₘ (mu.restrict D) with hnu2def
  have hnu1apply : ∀ E : Set X, MeasurableSet E → nu1 E = ∫⁻ x in E, kap x D ∂mu :=
    fun E hE => by rw [hnu1def, withDensity_apply _ hE]
  have hnu2apply : ∀ E : Set X, MeasurableSet E → nu2 E = ∫⁻ x in D, kap x E ∂mu :=
    fun E hE => by rw [hnu2def, Measure.bind_apply hE (Kernel.aemeasurable kap)]
  have hfinite1 : IsFiniteMeasure nu1 := by
    refine ⟨?_⟩
    rw [hnu1apply Set.univ MeasurableSet.univ]
    refine lt_of_le_of_lt (lintegral_mono fun x => hsub.measure_le_one x D) ?_
    simpa only [Measure.restrict_univ, lintegral_one] using measure_lt_top mu Set.univ
  have heq : nu1 = nu2 := by
    refine @ext_of_forall_lintegral_eq_of_IsFiniteMeasure X _ _ _ _ nu1 nu2 hfinite1 ?_
    intro g
    rw [hnu1def, lintegral_withDensity_eq_lintegral_mul _ (hrow D hD) (hcoe g), hnu2def,
      Measure.lintegral_bind (Kernel.aemeasurable kap) (hcoe g).aemeasurable]
    simp only [Pi.mul_apply]
    calc
      (∫⁻ x, kap x D * (g x : ℝ≥0∞) ∂mu) = ∫⁻ x, (g x : ℝ≥0∞) * kap x D ∂mu := by
        exact lintegral_congr fun x => mul_comm _ _
      _ = ∫⁻ x in D, (∫⁻ y, (g y : ℝ≥0∞) ∂kap x) ∂mu := hround1 g D hD
  rw [← hnu1apply C hC, heq, hnu2apply C hC]

end Abstract


/-- The real bounded continuous function attached to a nonnegative one. -/
def toRealBcf {X : Type*} [TopologicalSpace X] (f : X →ᵇ ℝ≥0) : X →ᵇ ℝ :=
  ⟨⟨fun x => ((f x : ℝ≥0) : ℝ), Continuous.comp' NNReal.continuous_coe f.continuous⟩,
    f.map_bounded'⟩

theorem toRealBcf_nonneg {X : Type*} [TopologicalSpace X] (f : X →ᵇ ℝ≥0) (x : X) :
    0 ≤ toRealBcf f x := (f x).coe_nonneg

theorem ofReal_toRealBcf {X : Type*} [TopologicalSpace X] (f : X →ᵇ ℝ≥0) (x : X) :
    ENNReal.ofReal (toRealBcf f x) = (f x : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-- Rectangle symmetry of every killed transition kernel. -/
theorem killedKernel_rectangle_symmetry {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusion c rho law) [IsMarkovKernel law] {U : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure ((weightedMeasure rho).restrict U)]
    (t : NNReal) (C D : Set (Vec d)) (hC : MeasurableSet C) (hDs : MeasurableSet D) :
    (∫⁻ x in C, killedKernel law U hU t x D ∂((weightedMeasure rho).restrict U))
      = ∫⁻ x in D, killedKernel law U hU t x C ∂((weightedMeasure rho).restrict U) := by
  set mu := (weightedMeasure rho).restrict U with hmudef
  set kap := killedKernel law U hU t with hkapdef
  have hsub : IsSubMarkovKernel kap := killedKernel_subMarkov law U hU t
  letI : IsFiniteKernel kap := hsub.isFiniteKernel
  refine rectangle_symmetry_of_bcnn hsub ?_ C D hC hDs
  intro f g
  have hkerint : ∀ (h : Vec d →ᵇ ℝ≥0) (x : Vec d),
      (∫⁻ y, (h y : ℝ≥0∞) ∂kap x) = ENNReal.ofReal (kernelIntegral kap (toRealBcf h) x) := by
    intro h x
    have hint : Integrable (toRealBcf h) (kap x) :=
      Integrable.mono' (integrable_const ‖toRealBcf h‖)
        (toRealBcf h).continuous.measurable.aestronglyMeasurable
        (Filter.Eventually.of_forall (toRealBcf h).norm_coe_le_norm)
    rw [show kernelIntegral kap (toRealBcf h) x = ∫ y, toRealBcf h y ∂(kap x) from rfl,
      ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (toRealBcf_nonneg h))]
    exact lintegral_congr fun y => (ofReal_toRealBcf h y).symm
  have hpairing : ∀ h k : Vec d →ᵇ ℝ≥0,
      (∫⁻ x, (h x : ℝ≥0∞) * (∫⁻ y, (k y : ℝ≥0∞) ∂kap x) ∂mu)
        = ENNReal.ofReal (killedPairing law U hU mu (toRealBcf h) (toRealBcf k) (t : ℝ)) := by
    intro h k
    have hnn : ∀ x : Vec d, 0 ≤ toRealBcf h x *
        kernelIntegral (killedKernel law U hU (Real.toNNReal (t : ℝ))) (toRealBcf k) x := by
      intro x
      refine mul_nonneg (toRealBcf_nonneg h x) ?_
      rw [Real.toNNReal_coe]
      exact integral_nonneg fun y => toRealBcf_nonneg k y
    have hint : Integrable (fun x => toRealBcf h x *
        kernelIntegral (killedKernel law U hU (Real.toNNReal (t : ℝ))) (toRealBcf k) x) mu := by
      refine Integrable.mono' (integrable_const (‖toRealBcf h‖ * ‖toRealBcf k‖))
        (((toRealBcf h).continuous.measurable.mul (measurable_kernelIntegral_function
          (killedKernel law U hU (Real.toNNReal (t : ℝ))) (toRealBcf k)
          (toRealBcf k).continuous.measurable)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (by simpa only [← Real.norm_eq_abs] using (toRealBcf h).norm_coe_le_norm x)
        (by simpa only [← Real.norm_eq_abs] using
          norm_killedKernel_integral_le law U hU (toRealBcf k) (t : ℝ) x)
        (abs_nonneg _) (norm_nonneg _)
    rw [killedPairing, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall hnn)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (toRealBcf_nonneg h x), ofReal_toRealBcf h x, Real.toNNReal_coe,
      ← hkerint k x]
  rw [hpairing f g, hpairing g f,
    killedPairing_symm hD hU hUb (toRealBcf f) (toRealBcf g) (t : ℝ) (t : ℝ≥0).coe_nonneg]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
