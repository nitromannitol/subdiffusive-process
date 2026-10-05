module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeFailureTail

@[expose] public section

/-!
# Simultaneous finiteness of countably many failure heights

After proving summability for each lattice-site and cutoff-index failure family, the source
intersects the resulting countably many full-measure events.  This file formalizes that
countable intersection step.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Omega I : Type*} [MeasurableSpace Omega] [Countable I]

/-- If every indexed failure family has summable probabilities, then all corresponding
failure heights are finite simultaneously almost surely.

The source applies this with the countable index `(m, z) ∈ ℕ × ℤ^d`.

-/
theorem ae_forall_failureHeightAt_ne_top_of_tsum_measure_ne_top
    (mu : Measure Omega) (failure : I → ℕ → Set Omega)
    (hsum : ∀ i, (∑' h, mu (failure i h)) ≠ ∞) :
    ∀ᵐ omega ∂mu, ∀ i, failureHeightAt (failure i) omega ≠ (⊤ : WithTop ℕ) :=
  eventually_countable_forall.mpr fun i ↦
    ae_failureHeightAt_ne_top_of_tsum_measure_ne_top mu (failure i) (hsum i)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
