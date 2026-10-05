module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFixedCode

@[expose] public section

/-!
# Measurability of triadic failure heights and stopping candidates

The failure height is rewritten as a supremum over the fixed countable level
carrier.  This removes the sample-dependent subtype in its defining supremum
and exposes the measurable stopping-depth fibres used by the fixed cell code.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- Fixed-index expression for the extended height. -/
theorem failureHeightAt_eq_iSup_indicator
    (failure : ℕ → Set Omega) (omega : Omega) :
    failureHeightAt failure omega =
      ⨆ h : ℕ, if omega ∈ failure h then ((h + 1 : ℕ) : WithTop ℕ) else 0 := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨h, hh⟩
    change omega ∈ failure h at hh
    exact le_iSup_of_le h (by rw [ite_eq_left hh])
  · apply iSup_le
    intro h
    by_cases hh : omega ∈ failure h
    · simp only [ite_eq_left hh]
      exact le_iSup_of_le ⟨h, hh⟩ le_rfl
    · simp only [ite_eq_right hh]
      exact bot_le

/-- If no failure occurs at or above level `B`, the extended height is at
most `B`. -/
theorem failureHeightAt_le_of_forall_ge
    (failure : ℕ → Set Omega) (omega : Omega) (B : ℕ)
    (hB : ∀ j : ℕ, B ≤ j → omega ∉ failure j) :
    failureHeightAt failure omega ≤ (B : WithTop ℕ) := by
  rw [failureHeightAt_eq_iSup_indicator]
  apply iSup_le
  intro h
  by_cases hh : omega ∈ failure h
  · have hnot : ¬ B ≤ h := fun hb => hB h hb hh
    have hlt : h + 1 ≤ B := by omega
    rw [ite_eq_left hh]
    exact_mod_cast hlt
  · rw [ite_eq_right hh]
    exact zero_le

/-- The stopping depth of a base cube is bounded by any level above which no
ancestor of that cube fails. -/
theorem triadicStoppingDepth_le_of_forall_ge
    (failure : TriadicCube d → Set Omega) (omega : Omega) (B : ℕ)
    (Q : StoppingBaseCube d base)
    (hB : ∀ j : ℕ, B ≤ j → omega ∉ failure (ancestorCube j Q.1)) :
    triadicStoppingDepth failure omega Q ≤ B := by
  have hheight : triadicFailureHeight failure omega Q ≤ (B : WithTop ℕ) :=
    failureHeightAt_le_of_forall_ge (fun j ↦ failure (ancestorCube j Q.1)) omega B hB
  rw [triadicStoppingDepth]
  cases hcase : triadicFailureHeight failure omega Q with
  | top =>
      rw [hcase] at hheight
      exact absurd (top_le_iff.mp hheight) (by simp)
  | coe n =>
      rw [hcase] at hheight
      simpa only [WithTop.untopD_coe] using (Nat.cast_le (α := WithTop ℕ)).mp hheight

variable [MeasurableSpace Omega]

/-- Measurability of the last-failure height from measurable failure events. -/
theorem measurable_failureHeightAt
    (failure : ℕ → Set Omega) (hfailure : ∀ h, MeasurableSet (failure h)) :
    Measurable (failureHeightAt failure) := by
  rw [show failureHeightAt failure = fun omega ↦
      ⨆ h : ℕ, if omega ∈ failure h then
        ((h + 1 : ℕ) : WithTop ℕ) else 0 by
    funext omega
    exact failureHeightAt_eq_iSup_indicator failure omega]
  exact Measurable.iSup fun h ↦
    (measurable_const.ite (hfailure h) measurable_const)

/-- Measurability of a triadic failure height along a fixed ancestor chain. -/
theorem measurable_triadicFailureHeight
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (P : StoppingBaseCube d base) :
    Measurable (fun omega ↦ triadicFailureHeight failure omega P) := by
  exact measurable_failureHeightAt
    (fun j ↦ failure (ancestorCube j P.1))
    (fun j ↦ hfailure (ancestorCube j P.1))

/-- Measurability of the natural stopping depth, including its specified junk
value on infinite-height samples. -/
theorem measurable_triadicStoppingDepth
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (P : StoppingBaseCube d base) :
    Measurable (fun omega ↦ triadicStoppingDepth failure omega P) := by
  have huntop : Measurable (fun h : WithTop ℕ ↦ h.untopD 0) :=
    measurable_of_countable _
  exact huntop.comp (measurable_triadicFailureHeight failure hfailure P)

/-- Each fibre of the random stopping candidate is measurable. -/
theorem measurableSet_triadicStoppingCandidate_eq
    (failure : TriadicCube d → Set Omega)
    (hfailure : ∀ Q, MeasurableSet (failure Q))
    (P : StoppingBaseCube d base) (Q : TriadicCube d) :
    MeasurableSet
      {omega | triadicStoppingCandidate failure omega P = Q} := by
  let depth : Omega → ℕ := fun omega ↦ triadicStoppingDepth failure omega P
  have hdepth : Measurable depth :=
    measurable_triadicStoppingDepth failure hfailure P
  have heq : {omega | triadicStoppingCandidate failure omega P = Q} =
      ⋃ n : {n : ℕ // ancestorCube n P.1 = Q},
        {omega | depth omega = n.1} := by
    ext omega
    simp only [mem_ofPred_eq, mem_iUnion, depth, triadicStoppingCandidate]
    constructor
    · intro h
      exact ⟨⟨triadicStoppingDepth failure omega P, h⟩, rfl⟩
    · rintro ⟨n, hdepthn⟩
      rw [hdepthn]
      exact n.2
  rw [heq]
  apply MeasurableSet.iUnion
  intro n
  exact hdepth (MeasurableSet.singleton n.1)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
