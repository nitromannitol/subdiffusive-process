module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

/-! `eLpNorm` of an a.e.-convergent series is at most the `tsum` of the terms' `eLpNorm`s. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SubdiffusiveProcess

/-- The `Lp`-seminorm of an a.e.-convergent series is at most the `tsum` of the `Lp`-seminorms of
its terms: Fatou (`Lp.eLpNorm_lim_le_liminf_eLpNorm`) applied to the partial sums, bounded termwise
by the finite triangle inequality (`eLpNorm_sum_le`), then `liminf` of a monotone `ℝ≥0∞` sequence of
partial sums is its `tsum`. Used to turn `lem_infrared`'s per-layer geometric `Lp` bound into a
geometric bound on the infrared field's truncation tail. -/
theorem eLpNorm_tsum_le_tsum_eLpNorm {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    {f : ℕ → Ω → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {F : Ω → E} (hF : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ i ∈ Finset.range n, f i ω) atTop (𝓝 (F ω))) :
    eLpNorm F p μ ≤ ∑' i, eLpNorm (f i) p μ := by
  have hmeas : ∀ n, AEStronglyMeasurable (fun ω => ∑ i ∈ Finset.range n, f i ω) μ := by
    intro n
    induction n with
    | zero => simpa using aestronglyMeasurable_const (b := (0 : E))
    | succ n ih =>
        simp only [Finset.sum_range_succ]
        exact ih.add (hf n)
  have hpartial : ∀ n, eLpNorm (fun ω => ∑ i ∈ Finset.range n, f i ω) p μ ≤
      ∑ i ∈ Finset.range n, eLpNorm (f i) p μ := by
    intro n
    have heq : (fun ω => ∑ i ∈ Finset.range n, f i ω) =
        (∑ i ∈ Finset.range n, f i : Ω → E) := by
      funext ω; simp
    rw [heq]
    exact eLpNorm_sum_le hp1
  have hFmeas : AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas hF
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p) hmeas F hFmeas hF
  refine hfatou.trans ?_
  have hsup : Tendsto (fun n => ∑ i ∈ Finset.range n, eLpNorm (f i) p μ) atTop
      (𝓝 (∑' i, eLpNorm (f i) p μ)) :=
    (ENNReal.summable (f := fun i => eLpNorm (f i) p μ)).hasSum.tendsto_sum_nat
  have hliminfeq : atTop.liminf (fun n => ∑ i ∈ Finset.range n, eLpNorm (f i) p μ) =
      ∑' i, eLpNorm (f i) p μ := hsup.liminf_eq
  calc atTop.liminf (fun n => eLpNorm (fun ω => ∑ i ∈ Finset.range n, f i ω) p μ)
      ≤ atTop.liminf (fun n => ∑ i ∈ Finset.range n, eLpNorm (f i) p μ) :=
        liminf_le_liminf (Eventually.of_forall hpartial)
    _ = ∑' i, eLpNorm (f i) p μ := hliminfeq

end SubdiffusiveProcess
