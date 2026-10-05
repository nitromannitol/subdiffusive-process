module

public import Mathlib

@[expose] public section

/-!
# Stampacchia: a common almost everywhere convergent subsequence for finitely many `L²` limits
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Stampacchia

theorem exists_seq_tendsto_ae_pi {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ι : Type*} [Fintype ι] (F : ι → ℕ → α → ℝ) (G : ι → α → ℝ)
    (hF : ∀ i n, AEStronglyMeasurable (F i n) μ) (hG : ∀ i, AEStronglyMeasurable (G i) μ)
    (h : ∀ i, Tendsto (fun n => eLpNorm (fun x => F i n x - G i x) 2 μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, ∀ i, Tendsto (fun j => F i (ns j) x) atTop (𝓝 (G i x)) := by
  classical
  set D : ℕ → α → ℝ := fun n x => ∑ i, ‖F i n x - G i x‖ with hD
  have hDm : ∀ n, AEStronglyMeasurable (D n) μ := fun n =>
    (Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => ((hF i n).sub (hG i)).norm))
  have hDn : ∀ n, D n = ∑ i, (fun x => ‖F i n x - G i x‖) := by
    intro n; funext x; simp [hD]
  have hD0 : Tendsto (fun n => eLpNorm (D n - 0) 2 μ) atTop (𝓝 0) := by
    have hbound : ∀ n, eLpNorm (D n - 0) 2 μ ≤ ∑ i, eLpNorm (fun x => F i n x - G i x) 2 μ := by
      intro n
      rw [sub_zero, hDn n]
      refine (eLpNorm_sum_le (by norm_num)).trans ?_
      refine Finset.sum_le_sum fun i _ => le_of_eq ?_
      exact eLpNorm_norm _ ((hF i n).sub (hG i))
    have hsum : Tendsto (fun n => ∑ i, eLpNorm (fun x => F i n x - G i x) 2 μ) atTop (𝓝 0) := by
      have := tendsto_finsetSum Finset.univ (fun i _ => h i)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun n => bot_le)
      hbound
  have hmeas : TendstoInMeasure μ D atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hD0
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hae] with x hx i
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hx
  show ‖F i (ns j) x - G i x‖ ≤ D (ns j) x
  exact Finset.single_le_sum (f := fun i => ‖F i (ns j) x - G i x‖) (fun i _ => norm_nonneg _)
    (Finset.mem_univ i)

end SubdiffusiveProcess.Stampacchia
