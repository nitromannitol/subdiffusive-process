module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeSimultaneousFailureFiniteness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeFailureTailExact
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Summability of geometric failure tails

The Section 9 construction first proves a level-by-level exponentially decreasing failure
bound and then sums over the level. This file supplies that summability step directly in
`ENNReal`, both for one failure family and simultaneously for a countable family.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

omit [MeasurableSpace Omega] in
/-- The failure-height tail is the union of the failure events indexed as `N + k`.

This uses the level summation.
-/
theorem failureHeightTail_eq_iUnion_nat_add (failure : ℕ → Set Omega) (N : ℕ) :
    {omega | (N : WithTop ℕ) < failureHeightAt failure omega} =
      ⋃ k : ℕ, failure (N + k) := by
  rw [failureHeightTail_eq_iUnion]
  ext omega
  constructor
  · intro homega
    rw [Set.mem_iUnion] at homega
    obtain ⟨h, homega⟩ := homega
    rw [Set.mem_iUnion]
    refine ⟨h.1 - N, ?_⟩
    rwa [Nat.add_sub_of_le h.2]
  · intro homega
    rw [Set.mem_iUnion] at homega
    obtain ⟨k, homega⟩ := homega
    rw [Set.mem_iUnion]
    exact ⟨⟨N + k, Nat.le_add_right N k⟩, homega⟩

/-- A geometric level-failure estimate sums to the corresponding geometric bound for the
failure-height tail.

-/
theorem measure_failureHeightTail_le_geometric (mu : Measure Omega)
    (failure : ℕ → Set Omega) (C q : ENNReal)
    (hmeasure : ∀ h, mu (failure h) ≤ C * q ^ h) (N : ℕ) :
    mu {omega | (N : WithTop ℕ) < failureHeightAt failure omega} ≤
      C * q ^ N * (1 - q)⁻¹ := by
  rw [failureHeightTail_eq_iUnion_nat_add]
  calc
    mu (⋃ k : ℕ, failure (N + k)) ≤ ∑' k : ℕ, mu (failure (N + k)) :=
      measure_iUnion_le _
    _ ≤ ∑' k : ℕ, C * q ^ (N + k) :=
      ENNReal.tsum_le_tsum fun k ↦ hmeasure (N + k)
    _ = C * q ^ N * (1 - q)⁻¹ := by
      simp_rw [pow_add, ← mul_assoc]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- An `ENNReal`-valued sequence dominated by a finite geometric sequence has finite total
sum.

This uses the summation of level failures.
-/
theorem tsum_measure_ne_top_of_le_geometric (mu : Measure Omega)
    (failure : ℕ → Set Omega) (C q : ENNReal) (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ h, mu (failure h) ≤ C * q ^ h) :
    (∑' h, mu (failure h)) ≠ ∞ := by
  have hsum : (∑' h, mu (failure h)) ≤ ∑' h : ℕ, C * q ^ h :=
    ENNReal.tsum_le_tsum hmeasure
  have hgeom : (∑' h : ℕ, q ^ h) ≠ ∞ := (tsum_geometric_lt_top.mpr hq).ne
  have hmajorant : (∑' h : ℕ, C * q ^ h) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hC hgeom
  exact ne_top_of_le_ne_top hmajorant hsum

/-- A geometric probability bound makes one extended failure height finite almost
everywhere.

-/
theorem ae_failureHeightAt_ne_top_of_le_geometric (mu : Measure Omega)
    (failure : ℕ → Set Omega) (C q : ENNReal) (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ h, mu (failure h) ≤ C * q ^ h) :
    ∀ᵐ omega ∂mu, failureHeightAt failure omega ≠ (⊤ : WithTop ℕ) :=
  ae_failureHeightAt_ne_top_of_tsum_measure_ne_top mu failure
    (tsum_measure_ne_top_of_le_geometric mu failure C q hC hq hmeasure)

/-- Uniform geometric bounds for a countable family yield one full-measure event on which
all failure heights are finite.

The source applies this with the countable index set of cutoff levels and lattice sites.

-/
theorem ae_forall_failureHeightAt_ne_top_of_le_geometric
    {I : Type*} [Countable I] (mu : Measure Omega)
    (failure : I → ℕ → Set Omega) (C q : ENNReal) (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ i h, mu (failure i h) ≤ C * q ^ h) :
    ∀ᵐ omega ∂mu, ∀ i, failureHeightAt (failure i) omega ≠ (⊤ : WithTop ℕ) := by
  apply ae_forall_failureHeightAt_ne_top_of_tsum_measure_ne_top mu failure
  intro i
  exact tsum_measure_ne_top_of_le_geometric mu (failure i) C q hC hq (hmeasure i)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
