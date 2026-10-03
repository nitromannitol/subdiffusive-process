module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Finite families of eventual comparison events admit one future threshold.
The bound is the sum of the individual outer-measure bounds; no independence
or measurability is required.
-/
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace SubdiffusiveProcess

/-- A finite family of eventual event bounds has one common threshold. -/
theorem finite_event_comparison {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    (mu : Measure Omega) (bad : I → ℕ → Set Omega) (N : ℕ) (B : I → ℝ≥0∞)
    (hbad : ∀ i, ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M → mu (bad i M) ≤ B i) :
    ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
      mu {omega | ∃ i, omega ∈ bad i M} ≤ ∑ i : I, B i := by
  classical
  choose M0 hNM0 hM0 using hbad
  refine ⟨max N (Finset.univ.sup M0), le_max_left _ _, ?_⟩
  intro M hM
  calc
    mu {omega | ∃ i, omega ∈ bad i M} = mu (⋃ i : I, bad i M) := by
      congr 1
      ext omega
      exact (mem_iUnion).symm
    _ ≤ ∑ i : I, mu (bad i M) := measure_iUnion_fintype_le mu _
    _ ≤ ∑ i : I, B i := Finset.sum_le_sum (fun i _ => hM0 i M
      ((Finset.le_sup (f := M0) (Finset.mem_univ i)).trans ((le_max_right _ _).trans hM)))

/-- A common lower bound on the remaining index gives one geometric tail for a finite family. -/
theorem finite_event_comparison_geometric {Omega I : Type*}
    [MeasurableSpace Omega] [Fintype I]
    (mu : Measure Omega) (bad : I → ℕ → Set Omega) (N K : ℕ)
    (remaining : I → ℕ) (C c : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hK : ∀ i, K ≤ remaining i)
    (hbad : ∀ i, ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
      mu (bad i M) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-c * (remaining i : ℝ)))) :
    ∃ M0 : ℕ, N ≤ M0 ∧ ∀ M : ℕ, M0 ≤ M →
      mu {omega | ∃ i, omega ∈ bad i M} ≤
        ENNReal.ofReal ((Fintype.card I : ℝ) * (C * (3 : ℝ) ^ (-c * (K : ℝ)))) := by
  have hstep i : C * (3 : ℝ) ^ (-c * (remaining i : ℝ)) ≤
      C * (3 : ℝ) ^ (-c * (K : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonpos_left (by exact_mod_cast hK i) (neg_nonpos.mpr hc)
  obtain ⟨M0, hNM0, hM0⟩ := finite_event_comparison mu bad N
    (fun i => ENNReal.ofReal (C * (3 : ℝ) ^ (-c * (remaining i : ℝ)))) hbad
  refine ⟨M0, hNM0, fun M hM => (hM0 M hM).trans ?_⟩
  calc
    (∑ i : I, ENNReal.ofReal (C * (3 : ℝ) ^ (-c * (remaining i : ℝ)))) ≤
        ∑ _i : I, ENNReal.ofReal (C * (3 : ℝ) ^ (-c * (K : ℝ))) :=
      Finset.sum_le_sum (fun i _ => ENNReal.ofReal_le_ofReal (hstep i))
    _ = ENNReal.ofReal (∑ _i : I, C * (3 : ℝ) ^ (-c * (K : ℝ))) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
        mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))).symm
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end SubdiffusiveProcess
