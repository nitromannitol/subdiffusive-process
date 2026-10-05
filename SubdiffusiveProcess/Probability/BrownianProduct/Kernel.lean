module

public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.GiryMonad

@[expose] public section

/-!
# Finite products of probability kernels

The factors may depend measurably on a common parameter. Measurability follows
from the product formula on measurable rectangles, which generate the product
sigma algebra. Only Mathlib objects are used in this construction.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Probability.BrownianProduct

variable {ι α : Type*} {β : ι → Type*} [Fintype ι]
  [MeasurableSpace α] [∀ i, MeasurableSpace (β i)]

/-- The independent finite product of probability kernels with a common input. -/
def piKernel (κ : ∀ i, Kernel α (β i)) [∀ i, IsMarkovKernel (κ i)] :
    Kernel α (∀ i, β i) where
  toFun x := Measure.pi (fun i => κ i x)
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_pi.symm isPiSystem_pi
    rintro _ ⟨s, hs, rfl⟩
    simp only [Measure.pi_pi]
    exact Finset.measurable_prod _ fun i _ => (κ i).measurable_coe (hs i (mem_univ i))

/-- Evaluation of the product kernel is the finite product measure. -/
theorem piKernel_apply (κ : ∀ i, Kernel α (β i)) [∀ i, IsMarkovKernel (κ i)] (x : α) :
    piKernel κ x = Measure.pi (fun i => κ i x) := rfl

instance isMarkovKernel_piKernel (κ : ∀ i, Kernel α (β i)) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (piKernel κ) where
  isProbabilityMeasure x := by
    rw [piKernel_apply]
    infer_instance

/-- The probability of a rectangle factors into the probabilities of its sides. -/
theorem piKernel_apply_pi (κ : ∀ i, Kernel α (β i)) [∀ i, IsMarkovKernel (κ i)]
    (x : α) (A : ∀ i, Set (β i)) :
    piKernel κ x (pi univ A) = ∏ i, κ i x (A i) :=
  Measure.pi_pi _ _

end SubdiffusiveProcess.Probability.BrownianProduct
