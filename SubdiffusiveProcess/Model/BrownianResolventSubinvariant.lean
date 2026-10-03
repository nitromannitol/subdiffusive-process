module

public import SubdiffusiveProcess.Model.KilledBrownian
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationMixture
@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Model

/-- **Subinvariance passes from the killed kernels to the resolvent kernel.**  The resolvent
kernel is an exponential mixture of the killed kernels, so Tonelli transfers the bound with
no symmetry hypothesis and no `LocalDiffusion`. -/
theorem resolventKernel_subinvariant_of_killed {d : ℕ} (law : Kernel (Vec d) (Path d))
    [IsMarkovKernel law] (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ) (hs : 0 < s)
    (mu : Measure (Vec d)) [SFinite mu]
    (hkilled : ∀ t : NNReal, killedKernel law U hU t ∘ₘ mu ≤ mu) :
    resolventKernel law U hU s hs ∘ₘ mu ≤ mu := by
  letI := exponential_probability s hs
  refine Measure.le_iff.mpr fun B hB => ?_
  rw [Measure.bind_apply hB (resolventKernel law U hU s hs).aemeasurable]
  have hmix : ∀ x : Vec d, resolventKernel law U hU s hs x B
      = ∫⁻ t : ℝ, killedKernel law U hU (Real.toNNReal t) x B ∂expMeasure s⁻¹ :=
    fun x => resolventKernel_apply_mixture law U hU s hs x B hB
  have hjoint : Measurable (Function.uncurry
      (fun (x : Vec d) (t : ℝ) => killedKernel law U hU (Real.toNNReal t) x B)) := by
    change Measurable (fun p : Vec d × ℝ =>
      killedKernel law U hU (Real.toNNReal p.2) p.1 B)
    have hmap : Measurable
        (fun p : Vec d × ℝ => ((Real.toNNReal p.2, p.1) : NNReal × Vec d)) :=
      measurable_snd.real_toNNReal.prodMk measurable_fst
    exact Measurable.comp
      (g := fun q : NNReal × Vec d => killedKernel law U hU q.1 q.2 B)
      (f := fun p : Vec d × ℝ => ((Real.toNNReal p.2, p.1) : NNReal × Vec d))
      (killedKernel_joint_measurable law U hU B hB) hmap
  have hstep : ∀ t : ℝ,
      (∫⁻ x, killedKernel law U hU (Real.toNNReal t) x B ∂mu) ≤ mu B := by
    intro t
    have hb := (Measure.le_iff.mp (hkilled (Real.toNNReal t))) B hB
    rwa [Measure.bind_apply hB (killedKernel law U hU (Real.toNNReal t)).aemeasurable] at hb
  calc (∫⁻ x, resolventKernel law U hU s hs x B ∂mu)
      = ∫⁻ x, (∫⁻ t : ℝ, killedKernel law U hU (Real.toNNReal t) x B ∂expMeasure s⁻¹) ∂mu :=
        lintegral_congr hmix
    _ = ∫⁻ t : ℝ, (∫⁻ x, killedKernel law U hU (Real.toNNReal t) x B ∂mu)
          ∂expMeasure s⁻¹ := lintegral_lintegral_swap hjoint.aemeasurable
    _ ≤ ∫⁻ _t : ℝ, mu B ∂expMeasure s⁻¹ := lintegral_mono hstep
    _ = mu B := by rw [lintegral_const, measure_univ, mul_one]

open SubdiffusiveProcess.Model.BrownianDiffusion SubdiffusiveProcess.Model.LifetimeProcess

/-- **The Brownian resolvent kernel is subinvariant for restricted Lebesgue measure**, with
no `LocalDiffusion` hypothesis anywhere in its proof. -/
theorem resolventKernel_brownian_subinvariant (d : ℕ) (U : Set (Vec d)) (hU : IsOpen U)
    (s : ℝ) (hs : 0 < s) :
    resolventKernel (brownianLifetimeProcess d) U hU s hs ∘ₘ (volume.restrict U) ≤
      volume.restrict U :=
  resolventKernel_subinvariant_of_killed _ U hU s hs _
    (killedKernel_brownian_subinvariant d U hU)

/-- Restricted Lebesgue measure on a bounded set is finite. -/
theorem isFiniteMeasure_volume_restrict {d : ℕ} {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) : IsFiniteMeasure (volume.restrict U : Measure (Vec d)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact hUb.measure_lt_top



def brownianResolventLp (d : ℕ) (U : Set (Vec d)) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (s : ℝ) (hs : 0 < s) :
    Lp ℝ 2 (volume.restrict U : Measure (Vec d)) →L[ℝ]
      Lp ℝ 2 (volume.restrict U : Measure (Vec d)) :=
  letI := isFiniteMeasure_volume_restrict hUb
  kernelLpFinite (volume.restrict U) (resolventKernel (brownianLifetimeProcess d) U hU s hs)
    (resolventKernel_subMarkov _ U hU s hs)
    (resolventKernel_brownian_subinvariant d U hU s hs) 2

/-- The killed Brownian resolvent operator is a contraction on `L²`. -/
theorem norm_brownianResolventLp_le (d : ℕ) (U : Set (Vec d)) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (s : ℝ) (hs : 0 < s) :
    ‖brownianResolventLp d U hU hUb s hs‖ ≤ 1 :=
  letI := isFiniteMeasure_volume_restrict hUb
  norm_kernelLpFinite_le _ _ _ _ 2

/-- The operator is represented by the raw killed resolvent of Section 9's input layer. -/
theorem brownianResolventLp_coeFn (d : ℕ) (U : Set (Vec d)) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (s : ℝ) (hs : 0 < s)
    (f : Lp ℝ 2 (volume.restrict U : Measure (Vec d))) :
    brownianResolventLp d U hU hUb s hs f
      =ᵐ[volume.restrict U] killedResolvent (brownianLifetimeProcess d) U s f := by
  letI := isFiniteMeasure_volume_restrict hUb
  refine (coeFn_kernelLpFinite _ _ _ _ 2 f).trans ?_
  exact resolventKernel_integral_ae (brownianLifetimeProcess d) U hU s hs _
    (resolventKernel_brownian_subinvariant d U hU s hs) _
    ((Lp.memLp f).integrable (by norm_num))

end SubdiffusiveProcess.Model
