module

public import SubdiffusiveProcess.Probability.OneSidedLimitComparison
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

@[expose] public section

/-! Summable two-cutoff comparison tails transfer a growing finite catalogue
to a common limit. The catalogue and its summable bound remain explicit;
the result does not infer a rate from qualitative convergence alone.
-/
open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology
namespace SubdiffusiveProcess

/-- Summable eventual comparison tails give an almost-sure upper comparison on a growing mesh. -/
theorem ae_eventually_growing_mesh_le_limit {Omega I : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (V : ℕ → I → Omega → ℝ) (L : I → Omega → ℝ)
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop)
    (hconv : ∀ i, TendstoInMeasure mu (fun j => V (phi j) i) atTop (L i))
    (k : ℕ → ℕ) (entry : ∀ n, Fin (k n) → I)
    (a b : ℝ) (hab : a < b) (B : ℕ → ℝ≥0∞) (N0 : ℕ)
    (hbound : ∀ n, N0 ≤ n → ∀ i : Fin (k n),
      ∀ᶠ m in atTop, mu {omega | a < V n (entry n i) omega - V m (entry n i) omega} ≤ B n)
    (hsum : (∑' n, (k n : ℝ≥0∞) * B n) ≠ ⊤) :
    ∀ᵐ omega ∂mu, ∀ᶠ n in atTop, ∀ i : Fin (k n),
      V n (entry n i) omega ≤ L (entry n i) omega + b := by
  classical
  let bad : ℕ → Set Omega := fun n => {omega | N0 ≤ n ∧
    ∃ i : Fin (k n), b < V n (entry n i) omega - L (entry n i) omega}
  have ht n : mu (bad n) ≤ (k n : ℝ≥0∞) * B n := by
    by_cases hn : N0 ≤ n
    · have hi (i : Fin (k n)) :
          mu {omega | b < V n (entry n i) omega - L (entry n i) omega} ≤ B n :=
        measure_sub_limit_gt_le mu (fun j => V (phi j) (entry n i))
          (V n (entry n i)) (L (entry n i)) (hconv (entry n i)) a b hab (B n)
          (hphi.eventually (hbound n hn i))
      have heq : bad n = ⋃ i : Fin (k n),
          {omega | b < V n (entry n i) omega - L (entry n i) omega} := by
        ext omega
        simp only [bad, hn, true_and, mem_ofPred_eq, mem_iUnion]
      rw [heq]
      calc mu (⋃ i : Fin (k n),
          {omega | b < V n (entry n i) omega - L (entry n i) omega}) ≤
          ∑ i : Fin (k n), mu {omega | b < V n (entry n i) omega - L (entry n i) omega} :=
            measure_iUnion_fintype_le mu _
        _ ≤ ∑ _i : Fin (k n), B n := Finset.sum_le_sum (fun i _ => hi i)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · have heq : bad n = ∅ := by
        ext omega
        simp only [bad, hn, false_and, mem_ofPred_eq, mem_empty_iff_false]
      rw [heq, measure_empty]
      exact zero_le
  have hae := ae_eventually_notMem
    (ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum ht))
  filter_upwards [hae] with omega homega
  filter_upwards [homega, eventually_ge_atTop N0] with n hn hN
  intro i
  have hle : V n (entry n i) omega - L (entry n i) omega ≤ b :=
    le_of_not_gt (fun h => hn ⟨hN, i, h⟩)
  linarith only [hle]

end SubdiffusiveProcess
