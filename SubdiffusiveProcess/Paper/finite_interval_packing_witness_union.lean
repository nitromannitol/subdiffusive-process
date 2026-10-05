module

public import SubdiffusiveProcess.Paper.lem_finite_good_cell
public import SubdiffusiveProcess.Paper.finite_response_ramp
public import SubdiffusiveProcess.Paper.lem_rare_tests
public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

/-- The finite witness-union estimate, with the displayed counting hypotheses. -/

private lemma aux_finite_interval_packing_witness_union_measurable
    {Om : Type*} [MeasurableSpace Om]
    (blockSigma : Set ℤ → MeasurableSpace Om)
    (blocks : ℕ+ → Set ℤ)
    (W : Fin 3 → ℕ+ → Set Om)
    (hWmeas : ∀ i h, @MeasurableSet Om (blockSigma (blocks h)) (W i h))
    (h : ℕ+) :
    @MeasurableSet Om (blockSigma (blocks h)) (⋃ i : Fin 3, W i h) :=
  MeasurableSet.iUnion (fun i => hWmeas i h)

private lemma aux_finite_interval_packing_witness_union_prob_bound
    {Om : Type*} [MeasurableSpace Om]
    (P : Measure Om)
    (rate : ℝ)
    (W : Fin 3 → ℕ+ → Set Om)
    (hWprob : ∀ i h, P (W i h) ≤ ENNReal.ofReal (Real.exp (-(rate * (h : ℝ)))))
    (h : ℕ+) :
    P (⋃ i : Fin 3, W i h) ≤ 3 * ENNReal.ofReal (Real.exp (-(rate * (h : ℝ)))) := by
  calc
    P (⋃ i : Fin 3, W i h) ≤ ∑' i : Fin 3, P (W i h) := measure_iUnion_le _
    _ = ∑ i : Fin 3, P (W i h) := by rw [tsum_fintype]
    _ ≤ ∑ i : Fin 3, ENNReal.ofReal (Real.exp (-(rate * (h : ℝ)))) :=
      Finset.sum_le_sum (fun i _ => hWprob i h)
    _ = 3 * ENNReal.ofReal (Real.exp (-(rate * (h : ℝ)))) := by simp

private lemma aux_finite_interval_packing_witness_union_cover_ae
    {Om : Type*} [MeasurableSpace Om]
    (P : Measure Om) [IsProbabilityMeasure P]
    (W : Fin 3 → ℕ+ → Set Om)
    (failure : Fin 3 → Set Om)
    (hcover : ∀ i, ∀ᵐ omega ∂P, omega ∈ failure i → omega ∈ ⋃ h : ℕ+, W i h) :
    ∀ᵐ omega ∂P, (∃ i : Fin 3, omega ∈ failure i) → omega ∈ ⋃ h : ℕ+, (⋃ i : Fin 3, W i h) := by
  have h_all : ∀ᵐ omega ∂P, ∀ i : Fin 3, omega ∈ failure i → omega ∈ ⋃ h : ℕ+, W i h :=
    Filter.eventually_all.mpr (fun i => hcover i)
  filter_upwards [h_all] with omega homega
  intro hex
  rcases hex with ⟨i, hi⟩
  rcases Set.mem_iUnion.1 (homega i hi) with ⟨hh, hmem⟩
  exact Set.mem_iUnion.2 ⟨hh, Set.mem_iUnion.2 ⟨i, hmem⟩⟩

theorem finite_interval_packing_witness_union
    {Om : Type*} [MeasurableSpace Om]
    (P : Measure Om) [IsProbabilityMeasure P]
    (blockSigma : Set ℤ → MeasurableSpace Om)
    (blocks : ℕ+ → Set ℤ)
    (rate : ℝ)
    (failure : Fin 3 → Set Om)
    (W : Fin 3 → ℕ+ → Set Om)
    (hWmeas : ∀ i h, @MeasurableSet Om (blockSigma (blocks h)) (W i h))
    (hWprob : ∀ i h,
      P (W i h) ≤ ENNReal.ofReal (Real.exp (-(rate * (h : ℝ)))))
    (hcover : ∀ i, ∀ᵐ omega ∂P,
      omega ∈ failure i → omega ∈ ⋃ h : ℕ+, W i h) :
    ∃ Wunion : ℕ+ → Set Om,
      (∀ h, @MeasurableSet Om (blockSigma (blocks h)) (Wunion h)) ∧
      (∀ h, P (Wunion h) ≤
        3 * ENNReal.ofReal (Real.exp (-(rate * (h : ℝ))))) ∧
      (∀ᵐ omega ∂P,
        (∃ i : Fin 3, omega ∈ failure i) →
          omega ∈ ⋃ h : ℕ+, Wunion h) := by
  refine ⟨fun h => ⋃ i : Fin 3, W i h, ?_, ?_, ?_⟩
  · exact aux_finite_interval_packing_witness_union_measurable blockSigma blocks W hWmeas
  · exact aux_finite_interval_packing_witness_union_prob_bound P rate W hWprob
  · exact aux_finite_interval_packing_witness_union_cover_ae P W failure hcover

end SubdiffusiveProcess.Paper
