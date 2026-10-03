module

public import SubdiffusiveProcess.Model.BrownianDiffusion
public import SubdiffusiveProcess.Model.HeatSemigroupInvariant
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp
public import MarkovProcess.Killed.Semigroup
public import MarkovProcess.Trajectory.Dynkin

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.Model.LifetimeProcess

/-- The two killed-kernel constructions agree under the lifetime-path embedding. -/
theorem killedKernel_lifetimeProcess {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d))
    (hP : P.IsConservative) (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) :
    killedKernel (lifetimeProcess P hP) U hU t
      = SubMarkovKernelSemigroup.IsConservative.killedKernel P hP U hU t := by
  apply Kernel.ext_iff'.2
  intro x B hB
  have hEvent : MeasurableSet
      ((position t) ⁻¹' B ∩
        {p : Path d | (t : ENNReal) < LifetimePath.exitTime U p}) :=
    ((position_fixed_measurable t) hB).inter
      (measurableSet_lt
        (show Measurable (fun _ : Path d => (t : ENNReal)) from measurable_const)
        (LifetimePath.isStoppingTime_exitTime U hU).measurable')
  unfold killedKernel
  rw [map_restrict_apply _ _ _ _ (position_fixed_measurable t) x B hB, lifetimeProcess_apply]
  rw [Measure.map_apply LifetimePath.measurable_ofContinuousPath hEvent,
    SubMarkovKernelSemigroup.IsConservative.killedKernel_apply P hP U hU t x hB]
  congr 1
  ext w
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq,
    position_ofContinuousPath, LifetimePath.exitTime_ofContinuousPath,
    ContinuousPath.mem_killedEvent_iff, and_comm]

/-- Domination and support transfer subinvariance to the restricted measure. -/
theorem kernel_comp_restrict_le_of_domination {α : Type*} [MeasurableSpace α]
    (K P : Kernel α α) (μ : Measure α) (U : Set α) (hU : MeasurableSet U)
    (hdom : ∀ x, K x ≤ P x) (hsupport : ∀ x, ∀ᵐ y ∂K x, y ∈ U)
    (hμ : P ∘ₘ μ ≤ μ) : K ∘ₘ μ.restrict U ≤ μ.restrict U := by
  have h1 : K ∘ₘ μ.restrict U ≤ P ∘ₘ μ.restrict U := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.bind_apply hs K.aemeasurable,
      Measure.bind_apply hs P.aemeasurable]
    exact lintegral_mono' le_rfl fun x => hdom x s
  have h2 : P ∘ₘ μ.restrict U ≤ P ∘ₘ μ := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.bind_apply hs P.aemeasurable,
      Measure.bind_apply hs P.aemeasurable]
    exact lintegral_mono' (Measure.restrict_le_self) fun _ => le_rfl
  have h3 : K ∘ₘ μ.restrict U ≤ μ := h1.trans (h2.trans hμ)
  have hae : ∀ᵐ y ∂(K ∘ₘ μ.restrict U), y ∈ U :=
    Measure.ae_comp_of_ae_ae hU (Filter.Eventually.of_forall hsupport)
  have h4 : (K ∘ₘ μ.restrict U).restrict U = K ∘ₘ μ.restrict U :=
    Measure.restrict_eq_self_of_ae_mem hae
  calc K ∘ₘ μ.restrict U = (K ∘ₘ μ.restrict U).restrict U := h4.symm
    _ ≤ μ.restrict U := Measure.restrict_mono_measure h3 U

/-- Killing only removes paths from the transition law. -/
theorem killedKernel_le_transition {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d))
    (hP : P.IsConservative) (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal)
    (x : Vec d) :
    SubMarkovKernelSemigroup.IsConservative.killedKernel P hP U hU t x ≤ P t x := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [SubMarkovKernelSemigroup.IsConservative.killedKernel_apply P hP U hU t x hB]
  have heval : Measurable (fun w : ContinuousPath (Vec d) => w t) :=
    ContinuousPath.measurable_coordinateProcess (alpha := Vec d) t
  calc
    ((SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP) x)
        (ContinuousPath.killedEvent U t B)
        ≤ (SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP) x
            ((fun w : ContinuousPath (Vec d) => w t) ⁻¹' B) :=
      measure_mono (fun w hw =>
        (ContinuousPath.mem_killedEvent_iff U t B w).mp hw |>.2)
    _ = P t x B := by
      rw [← Kernel.map_apply'
          (SubMarkovKernelSemigroup.IsConservative.continuousProcess P hP) heval x hB,
        hFeller.continuousProcess_map_eval_nnreal P hP hK t]

/-- A subinvariant measure remains subinvariant for the process killed on an open set. -/
theorem killedKernel_subinvariant {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d))
    (hP : P.IsConservative) (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (mu : Measure (Vec d)) (hmu : P.IsSubInvariant mu)
    (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) :
    SubMarkovKernelSemigroup.IsConservative.killedKernel P hP U hU t ∘ₘ mu.restrict U ≤
      mu.restrict U :=
  kernel_comp_restrict_le_of_domination _ (P t) mu U hU.measurableSet
    (killedKernel_le_transition P hP hFeller hK U hU t)
    (SubMarkovKernelSemigroup.IsConservative.ae_mem_killedKernel P hP U hU t) (hmu t)

end SubdiffusiveProcess.Model.LifetimeProcess

namespace SubdiffusiveProcess.Model.BrownianDiffusion

open SubdiffusiveProcess.Model.LifetimeProcess SubdiffusiveProcess.Model.HeatSemigroupVec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledSemigroupLp

/-- The killed Brownian kernel is subinvariant for restricted Lebesgue measure. -/
theorem killedKernel_brownian_subinvariant (d : ℕ) (U : Set (Vec d)) (hU : IsOpen U)
    (t : NNReal) :
    killedKernel (brownianLifetimeProcess d) U hU t ∘ₘ (volume.restrict U) ≤
      volume.restrict U := by
  change killedKernel (lifetimeProcess (heatSemigroupVec d)
    isConservative_heatSemigroupVec) U hU t ∘ₘ (volume.restrict U) ≤ volume.restrict U
  rw [killedKernel_lifetimeProcess]
  exact killedKernel_subinvariant (heatSemigroupVec d) isConservative_heatSemigroupVec
    isFellerKernelSemigroup_heatSemigroupVec kolmogorovRegular_heatSemigroupVec volume
    (isSubInvariant_volume_heatSemigroupVec d) U hU t



theorem isSubInvariant_brownianKilledSMKS (d : ℕ) (U : Set (Vec d)) (hU : IsOpen U) :
    (killedSMKS (brownianLifetimeProcess d) (strongMarkov_brownianLifetimeProcess d)
      U hU).IsSubInvariant (volume.restrict U) := by
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [killedSMKS_apply, killedFamily_zero, Measure.id_comp]
  · rw [killedSMKS_apply, killedFamily_of_ne _ _ _ ht]
    exact killedKernel_brownian_subinvariant d U hU t

/-- The killed Brownian transition operators on L² of restricted Lebesgue measure. -/
def brownianKilledLp (d : ℕ) (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) :
    Lp ℝ 2 (volume.restrict U) →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
  (killedSMKS (brownianLifetimeProcess d) (strongMarkov_brownianLifetimeProcess d)
    U hU).operatorFinite (volume.restrict U) (isSubInvariant_brownianKilledSMKS d U hU) 2 t

/-- The L² output represents the integral against the killed transition kernel. -/
theorem brownianKilledLp_coeFn (d : ℕ) (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal)
    (f : Lp ℝ 2 (volume.restrict U)) :
    brownianKilledLp d U hU t f =ᵐ[volume.restrict U]
      kernelIntegral (killedFamily (brownianLifetimeProcess d) U hU t) f :=
  (killedSMKS (brownianLifetimeProcess d) (strongMarkov_brownianLifetimeProcess d)
    U hU).isAssociatedFinite_operatorFinite _ (isSubInvariant_brownianKilledSMKS d U hU) 2 t f

/-- The killed Brownian L² operators are contractions. -/
theorem norm_brownianKilledLp_le (d : ℕ) (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) :
    ‖brownianKilledLp d U hU t‖ ≤ 1 :=
  (killedSMKS (brownianLifetimeProcess d) (strongMarkov_brownianLifetimeProcess d)
    U hU).norm_operatorFinite_le _ (isSubInvariant_brownianKilledSMKS d U hU) 2 t

end SubdiffusiveProcess.Model.BrownianDiffusion
