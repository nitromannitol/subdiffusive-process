import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeFailureHeight
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Failure-height tails

The stopping construction takes one plus the last failed level.  This file connects that
height to the union of all later failure events, proves the corresponding countable union
bound, and records the almost-sure finiteness consequence of summable failure probabilities.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {Omega : Type*}



def failureHeightAt (failure : ℕ → Set Omega) (omega : Omega) : WithTop ℕ :=
  extendedFailureHeight {h | omega ∈ failure h}



theorem failureHeightTail_subset_iUnion (failure : ℕ → Set Omega) (N : ℕ) :
    {omega | (N : WithTop ℕ) < failureHeightAt failure omega} ⊆
      ⋃ h : {h : ℕ // N ≤ h}, failure h := by
  intro omega hheight
  by_contra hnot
  have hle : failureHeightAt failure omega ≤ (N : WithTop ℕ) := by
    apply iSup_le
    rintro ⟨h, hh⟩
    have hlt : h < N := by
      apply Nat.lt_of_not_ge
      intro hNh
      apply hnot
      exact mem_iUnion_of_mem ⟨h, hNh⟩ hh
    exact_mod_cast Nat.succ_le_iff.mpr hlt
  exact (not_lt_of_ge hle) hheight

variable [MeasurableSpace Omega]



theorem measure_failureHeightTail_le_tsum (mu : Measure Omega)
    (failure : ℕ → Set Omega) (bound : ℕ → ENNReal) (N : ℕ)
    (hmeasure : ∀ h, mu (failure h) ≤ bound h) :
    mu {omega | (N : WithTop ℕ) < failureHeightAt failure omega} ≤
      ∑' h : {h : ℕ // N ≤ h}, bound h := by
  calc
    mu {omega | (N : WithTop ℕ) < failureHeightAt failure omega} ≤
        mu (⋃ h : {h : ℕ // N ≤ h}, failure h) :=
      measure_mono (failureHeightTail_subset_iUnion failure N)
    _ ≤ ∑' h : {h : ℕ // N ≤ h}, mu (failure h) := measure_iUnion_le _
    _ ≤ ∑' h : {h : ℕ // N ≤ h}, bound h :=
      ENNReal.tsum_le_tsum fun h ↦ hmeasure h



theorem ae_failureHeightAt_ne_top_of_tsum_measure_ne_top
    (mu : Measure Omega) (failure : ℕ → Set Omega)
    (hsum : (∑' h, mu (failure h)) ≠ ∞) :
    ∀ᵐ omega ∂mu, failureHeightAt failure omega ≠ (⊤ : WithTop ℕ) := by
  filter_upwards [ae_finite_setOf_mem hsum] with omega hfinite
  rw [failureHeightAt, ← hfinite.coe_toFinset,
    extendedFailureHeight_coe_finset]
  exact WithTop.coe_ne_top

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
