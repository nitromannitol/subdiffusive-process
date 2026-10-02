import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationKernelIntegral
import SubdiffusiveProcess.CoarseGrainingVocab.Section10.WholeSpaceKilledDensity
import MarkovProcess.Kernel.Integral

/-! Positive killed-kernel domination on arbitrary nested open carriers.
The a.e. integral comparison retains actual subinvariant measures, so no
pointwise integrability is inferred from an Lp representative. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory MarkovProcess Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal
namespace SubdiffusiveProcess.Section10

/-- Enlarging the open carrier increases the actual killed endpoint measure. -/
theorem killedKernel_le_of_subset {d : ℕ}
    (law : Kernel (Vec d) (Path d)) {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) (t : NNReal) (x : Vec d) :
    killedKernel law U hU t x ≤ killedKernel law V hV t x := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [killedKernel, killedKernel, map_restrict_apply _ _ _ _
    (position_fixed_measurable t) x B hB,
    map_restrict_apply _ _ _ _ (position_fixed_measurable t) x B hB]
  apply measure_mono
  intro w hw
  exact ⟨hw.1, lt_of_lt_of_le hw.2
    (SubdiffusiveProcess.CoarseGrainingVocab.Section10.exitTime_mono_set hUV w)⟩

/-- Enlarging the open carrier increases the actual positive occupation kernel. -/
theorem resolventKernel_le_of_subset {d : ℕ}
    (law : Kernel (Vec d) (Path d)) [IsMarkovKernel law] {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (s : ℝ) (hs : 0 < s) (x : Vec d) :
    resolventKernel law U hU s hs x ≤ resolventKernel law V hV s hs x := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [resolventKernel, resolventKernel,
    map_restrict_apply _ _ _ _ joint_position x B hB,
    map_restrict_apply _ _ _ _ joint_position x B hB]
  apply measure_mono
  intro q hq
  exact ⟨hq.1, lt_of_lt_of_le hq.2
    (SubdiffusiveProcess.CoarseGrainingVocab.Section10.exitTime_mono_set hUV q.2)⟩

/-- Dominated positive kernels compare raw integrals a.e. under their own
subinvariant measures. Row integrability is obtained from subinvariance. -/
theorem ae_abs_kernelIntegral_le_of_kernel_le {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) (kappa eta : Kernel X X)
    (hmn : mu ≤ nu) (hke : ∀ x, kappa x ≤ eta x)
    (hk : kappa ∘ₘ mu ≤ mu) (he : eta ∘ₘ nu ≤ nu)
    (f g : X → ℝ) (hf : Integrable f mu) (hg : Integrable g nu)
    (hfg : ∀ᵐ y ∂mu, |f y| ≤ g y) (hg0 : ∀ᵐ y ∂nu, 0 ≤ g y) :
    ∀ᵐ x ∂mu, |kernelIntegral kappa f x| ≤ kernelIntegral eta g x := by
  have hfrow : ∀ᵐ x ∂mu, Integrable f (kappa x) :=
    Measure.ae_integrable_of_integrable_comp (hf.mono_measure hk)
  have hgrow : ∀ᵐ x ∂nu, Integrable g (eta x) :=
    Measure.ae_integrable_of_integrable_comp (hg.mono_measure he)
  have hposrow : ∀ᵐ x ∂nu, ∀ᵐ y ∂eta x, 0 ≤ g y :=
    ae_ae_kernel_of_comp_le he hg0
  filter_upwards [hfrow, hgrow.filter_mono (Measure.absolutelyContinuous_of_le hmn).ae_le,
    hposrow.filter_mono (Measure.absolutelyContinuous_of_le hmn).ae_le,
    ae_ae_kernel_of_comp_le hk hfg]
    with x hfx hgx hpos hcomp
  have hgk : Integrable g (kappa x) := hgx.mono_measure (hke x)
  change |∫ y, f y ∂kappa x| ≤ ∫ y, g y ∂eta x
  calc
    |∫ y, f y ∂kappa x| ≤ ∫ y, |f y| ∂kappa x := abs_integral_le_integral_abs
    _ ≤ ∫ y, g y ∂kappa x := integral_mono_ae hfx.abs hgk hcomp
    _ ≤ ∫ y, g y ∂eta x := integral_mono_measure (hke x) hpos hgx

end SubdiffusiveProcess.Section10
