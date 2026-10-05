module

public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridStabilityGrid
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionFailureHeight
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeFailureTailSummability

@[expose] public section

/-!
# Failure heights along triadic ancestor chains

The repaired whole-space stopping partition starts with one candidate above
the last failed ancestor of every base-scale triadic cube.  This file defines
that candidate directly from a failure event indexed by `TriadicCube d` and
records its containment and goodness properties.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-- A base-scale triadic cube. -/
def StoppingBaseCube (d : ℕ) (base : ℤ) :=
  {Q : TriadicCube d // Q.scale = base}

instance (base : ℤ) : Countable (StoppingBaseCube d base) :=
  by
    dsimp only [StoppingBaseCube]
    infer_instance

/-- The extended height of failures along the ancestor chain of a base cube. -/
def triadicFailureHeight (failure : TriadicCube d → Set Omega)
    (omega : Omega) (Q : StoppingBaseCube d base) : WithTop ℕ :=
  failureHeightAt (fun j ↦ failure (ancestorCube j Q.1)) omega

/-- One plus the last failed ancestor level, with a junk value off the
finite-height event. -/
def triadicStoppingDepth (failure : TriadicCube d → Set Omega)
    (omega : Omega) (Q : StoppingBaseCube d base) : ℕ :=
  (triadicFailureHeight failure omega Q).untopD 0

/-- The initial candidate selected above the last failed ancestor. -/
def triadicStoppingCandidate (failure : TriadicCube d → Set Omega)
    (omega : Omega) (Q : StoppingBaseCube d base) : TriadicCube d :=
  ancestorCube (triadicStoppingDepth failure omega Q) Q.1

@[simp]
theorem triadicStoppingCandidate_scale
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (Q : StoppingBaseCube d base) :
    (triadicStoppingCandidate failure omega Q).scale =
      base + (triadicStoppingDepth failure omega Q : ℤ) := by
  rw [triadicStoppingCandidate, ancestorCube_scale, Q.2]

theorem base_le_triadicStoppingCandidate_scale
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (Q : StoppingBaseCube d base) :
    base ≤ (triadicStoppingCandidate failure omega Q).scale := by
  rw [triadicStoppingCandidate_scale]
  exact le_add_of_nonneg_right (Int.natCast_nonneg _)

/-- The initial candidate contains its base cube. -/
theorem cubeSet_subset_triadicStoppingCandidate
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (Q : StoppingBaseCube d base) :
    cubeSet Q.1 ⊆ cubeSet (triadicStoppingCandidate failure omega Q) :=
  cubeSet_subset_cubeSet_ancestorCube _ _

/-- A failure along the ancestor chain lies strictly below the selected
candidate whenever the height is finite. -/
theorem lt_triadicStoppingDepth_of_mem_failure
    (failure : TriadicCube d → Set Omega) {omega : Omega}
    {Q : StoppingBaseCube d base}
    (hfinite : triadicFailureHeight failure omega Q ≠ (⊤ : WithTop ℕ))
    {j : ℕ} (hfail : omega ∈ failure (ancestorCube j Q.1)) :
    j < triadicStoppingDepth failure omega Q := by
  have hcontribution : ((j + 1 : ℕ) : WithTop ℕ) ≤
      triadicFailureHeight failure omega Q :=
    coe_succ_le_extendedFailureHeight hfail
  generalize hheight : triadicFailureHeight failure omega Q = height
    at hcontribution
  cases height with
  | top => exact (hfinite hheight).elim
  | coe H =>
      have hnat : j + 1 ≤ H := WithTop.coe_le_coe.mp hcontribution
      simpa only [triadicStoppingDepth, hheight, WithTop.untopD_coe,
        Nat.lt_iff_add_one_le] using hnat

/-- No ancestor at or above the candidate level fails. -/
theorem not_mem_failure_ancestor_of_triadicStoppingDepth_le
    (failure : TriadicCube d → Set Omega) {omega : Omega}
    {Q : StoppingBaseCube d base}
    (hfinite : triadicFailureHeight failure omega Q ≠ (⊤ : WithTop ℕ))
    {j : ℕ} (hlevel : triadicStoppingDepth failure omega Q ≤ j) :
    omega ∉ failure (ancestorCube j Q.1) := by
  intro hfail
  exact (not_lt_of_ge hlevel)
    (lt_triadicStoppingDepth_of_mem_failure failure hfinite hfail)

/-- In particular, the initial candidate itself is good. -/
theorem not_mem_failure_triadicStoppingCandidate
    (failure : TriadicCube d → Set Omega) {omega : Omega}
    {Q : StoppingBaseCube d base}
    (hfinite : triadicFailureHeight failure omega Q ≠ (⊤ : WithTop ℕ)) :
    omega ∉ failure (triadicStoppingCandidate failure omega Q) := by
  simpa only [triadicStoppingCandidate] using
    not_mem_failure_ancestor_of_triadicStoppingDepth_le failure hfinite le_rfl

/-- Every further ancestor of an initial candidate is also good. -/
theorem not_mem_failure_ancestor_triadicStoppingCandidate
    (failure : TriadicCube d → Set Omega) {omega : Omega}
    {Q : StoppingBaseCube d base}
    (hfinite : triadicFailureHeight failure omega Q ≠ (⊤ : WithTop ℕ))
    (k : ℕ) :
    omega ∉ failure (ancestorCube k (triadicStoppingCandidate failure omega Q)) := by
  change omega ∉ failure
    ((parentCube^[k]) ((parentCube^[triadicStoppingDepth failure omega Q]) Q.1))
  rw [← Function.iterate_add_apply, Nat.add_comm]
  exact not_mem_failure_ancestor_of_triadicStoppingDepth_le failure hfinite
    (Nat.le_add_right _ _)

variable [MeasurableSpace Omega]

/-- Uniform geometric bounds for cube failures give simultaneous finite
ancestor-chain heights for every base cube. -/
theorem ae_forall_triadicFailureHeight_ne_top_of_le_geometric
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (C q : ENNReal) (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ (Q : StoppingBaseCube d base) j,
      mu (failure (ancestorCube j Q.1)) ≤ C * q ^ j) :
    ∀ᵐ omega ∂mu, ∀ Q : StoppingBaseCube d base,
      triadicFailureHeight failure omega Q ≠ (⊤ : WithTop ℕ) := by
  simpa only [triadicFailureHeight] using
    (ae_forall_failureHeightAt_ne_top_of_le_geometric
      (I := StoppingBaseCube d base) mu
      (fun Q j ↦ failure (ancestorCube j Q.1)) C q hC hq hmeasure)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
