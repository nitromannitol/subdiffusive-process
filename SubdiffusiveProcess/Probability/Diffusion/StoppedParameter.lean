module

public import MarkovProcess.Trajectory.StoppingLtTop
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-!
# Restart with a parameter measurable at the stopping time

A restricted restart identity determines the joint law of any stopped-measurable
parameter and the future path. This permits observables with a random remaining
time in the fixed-horizon Hunt formula.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {Ω α β : Type*} {m mΩ : MeasurableSpace Ω}
  [MeasurableSpace α] [MeasurableSpace β]

/-- A restricted restart identity also identifies the joint law of a parameter
measurable at the conditioning sigma-algebra and the restarted variable. -/
theorem map_stoppedParameter_eq_comp
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (κ : @Kernel Ω β mΩ _) [IsSFiniteKernel κ]
    (Y : Ω → β) (hY : @Measurable Ω β mΩ _ Y)
    (hm : m ≤ mΩ) (S : Set Ω)
    (hJoint : ∀ A : Set Ω, MeasurableSet[m] A →
      (μ.restrict (A ∩ S)).map Y = κ ∘ₘ μ.restrict (A ∩ S))
    (θ : Ω → α) (hθ : Measurable[m] θ) :
    (μ.restrict S).map (fun ω => (θ ω, Y ω)) =
      (Kernel.deterministic θ (hθ.mono hm le_rfl) ×ₖ κ) ∘ₘ μ.restrict S := by
  have hθ' : @Measurable Ω α mΩ _ θ := hθ.mono hm le_rfl
  apply Measure.ext_prod
  intro A B hA hB
  have h := congrArg (fun ν : Measure β => ν B) (hJoint (θ ⁻¹' A) (hθ hA))
  rw [Measure.map_apply hY hB, Measure.bind_apply hB κ.aemeasurable] at h
  rw [Measure.map_apply (hθ'.prodMk hY) (hA.prod hB),
    Measure.bind_apply (hA.prod hB) (Kernel.aemeasurable _)]
  have heval : (fun ω => (Kernel.deterministic θ hθ' ×ₖ κ) ω (A ×ˢ B)) =
      (θ ⁻¹' A).indicator (fun ω => κ ω B) := by
    funext ω
    rw [Kernel.prod_apply_prod, Kernel.deterministic_apply]
    by_cases hω : θ ω ∈ A
    · simp only [Measure.dirac_apply' _ hA, hω, Pi.one_apply, one_mul,
        mem_preimage, indicator_of_mem]
    · simp only [Measure.dirac_apply' _ hA, hω, zero_mul,
        mem_preimage, indicator_of_notMem, not_false_eq_true]
  rw [heval, lintegral_indicator (hθ' hA), Measure.restrict_restrict (hθ' hA)]
  rw [Measure.restrict_apply ((hθ'.prodMk hY) (hA.prod hB))]
  rw [Measure.restrict_apply (hY hB)] at h
  convert h using 1
  congr 1
  ext ω
  simp only [mem_inter_iff, mem_preimage, mem_prod, and_assoc, and_left_comm]

/-- Restart applies to a jointly measurable observable of the stopped parameter
and the future variable, with no simple-function approximation left as a premise. -/
theorem setLIntegral_stoppedParameter_eq
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (κ : @Kernel Ω β mΩ _) [IsSFiniteKernel κ]
    (Y : Ω → β) (hY : @Measurable Ω β mΩ _ Y)
    (hm : m ≤ mΩ) (S : Set Ω)
    (hJoint : ∀ A : Set Ω, MeasurableSet[m] A →
      (μ.restrict (A ∩ S)).map Y = κ ∘ₘ μ.restrict (A ∩ S))
    (θ : Ω → α) (hθ : Measurable[m] θ)
    (F : α × β → ENNReal) (hF : Measurable F) :
    (∫⁻ ω in S, F (θ ω, Y ω) ∂μ) =
      ∫⁻ ω in S, ∫⁻ η, F (θ ω, η) ∂κ ω ∂μ := by
  rw [← lintegral_map hF ((hθ.mono hm le_rfl).prodMk hY),
    map_stoppedParameter_eq_comp μ κ Y hY hm S hJoint θ hθ]
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hF.aemeasurable]
  exact lintegral_congr fun ω => Kernel.lintegral_deterministic_prod
    (hθ.mono hm le_rfl) κ ω hF

end SubdiffusiveProcess.Probability.Diffusion
