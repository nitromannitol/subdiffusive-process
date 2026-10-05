module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Nash

/-- Fatou's bound in measure, with a convergent sequence of upper bounds. -/
theorem eLpNorm_le_of_tendstoInMeasure_bounds {X : Type*} [MeasurableSpace X]
    {mu : Measure X} {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {f : ι → X → ℝ} {g : X → ℝ} (p : ℝ≥0∞)
    (hf : ∀ i, AEStronglyMeasurable (f i) mu) (hconv : TendstoInMeasure mu f l g)
    (A : ι → ℝ≥0∞) (C : ℝ≥0∞) (hA : Tendsto A l (𝓝 C))
    (hbound : ∀ᶠ i in l, eLpNorm (f i) p mu ≤ A i) : eLpNorm g p mu ≤ C := by
  obtain ⟨v, hv, hvAE⟩ := hconv.exists_seq_tendsto_ae'
  calc
    _ ≤ atTop.liminf (fun n => eLpNorm (f (v n)) p mu) :=
      Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => hf (v n)) g
        (aestronglyMeasurable_of_tendsto_ae atTop (fun n => hf (v n)) hvAE) hvAE
    _ ≤ atTop.liminf (fun n => A (v n)) := liminf_le_liminf (hv.eventually hbound)
    _ = C := (hA.comp hv).liminf_eq

end SubdiffusiveProcess.Nash
