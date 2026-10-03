module

public import SubdiffusiveProcess.Probability.SameLawComposition
public import SubdiffusiveProcess.Probability.ConvergenceInProbability
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-! The given original-space quadratic inverse limit identifies every represented
unweighted operator, on one event and for every load. -/

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace SubdiffusiveProcess.AuditRepairs

/-- Scalar base convergence transfers through cutoff-dependent same-law environments.
A dense countable set makes the quadratic identification simultaneous for all loads. -/
theorem coupled_base_quadratic_identification
    {S Ωh H : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace.PseudoMetrizableSpace S] [MeasurableSpace Ωh]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [SeparableSpace H]
    (P : Measure S) [IsProbabilityMeasure P]
    (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
    (env : ℕ → Ωh → S) (field : Ωh → S)
    (henv : ∀ n, MeasurePreserving (env n) Ph P)
    (hfield : MeasurePreserving field Ph P)
    (hfieldconv : ∀ᵐ ω ∂Ph, Tendsto (fun n => env n ω) atTop (𝓝 (field ω)))
    (X : ℕ → S → H → ℝ) (hX : ∀ n f, AEStronglyMeasurable (fun s => X n s f) P)
    (Gbase : S → H →L[ℝ] H)
    (hbaseconv : ∀ f, TendstoInMeasure P (fun n s => X n s f) atTop
      (fun s => inner ℝ f (Gbase s f)))
    (ns : ℕ → ℕ) (hns : StrictMono ns)
    (GN : ℕ → Ωh → H →L[ℝ] H) (GE : Ωh → H →L[ℝ] H)
    (hfinite : ∀ᵐ ω ∂Ph, ∀ n f, inner ℝ f (GN n ω f) = X (ns n) (env n ω) f)
    (hlimit : ∀ᵐ ω ∂Ph, Tendsto (fun n => GN n ω) atTop (𝓝 (GE ω))) :
    ∀ᵐ ω ∂Ph, ∀ f, inner ℝ f (GE ω f) = inner ℝ f (Gbase (field ω) f) := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq H
  have heq : ∀ k, (fun ω => inner ℝ (e k) (GE ω (e k))) =ᵐ[Ph]
      fun ω => inner ℝ (e k) (Gbase (field ω) (e k)) := by
    intro k
    have hmeas : AEStronglyMeasurable (fun s => inner ℝ (e k) (Gbase s (e k))) P :=
      TendstoInMeasure.aestronglyMeasurable (fun n => hX n (e k)) (hbaseconv (e k))
    have htransfer :=
      SubdiffusiveProcess.tendstoInMeasure_comp_of_sameLaw_of_tendstoInMeasure
        henv hfield hfieldconv hmeas (fun n => hX (ns n) (e k))
        ((hbaseconv (e k)).comp hns.tendsto_atTop)
    have hpath : ∀ᵐ ω ∂Ph,
        Tendsto (fun n => X (ns n) (env n ω) (e k)) atTop
          (𝓝 (inner ℝ (e k) (GE ω (e k)))) := by
      filter_upwards [hfinite, hlimit] with ω hω hlim
      have hc : Continuous (fun T : H →L[ℝ] H => inner ℝ (e k) (T (e k))) :=
        continuous_const.inner ((ContinuousLinearMap.apply ℝ H (e k)).continuous)
      have ht : Tendsto (fun n => inner ℝ (e k) (GN n ω (e k))) atTop
          (𝓝 (inner ℝ (e k) (GE ω (e k)))) := (hc.tendsto (GE ω)).comp hlim
      simpa only [hω] using ht
    exact (SubdiffusiveProcess.Probability.ae_eq_of_tendstoInMeasure_of_subseq_tendsto_ae
      htransfer tendsto_id hpath).symm
  filter_upwards [ae_all_iff.mpr heq] with ω hω
  have hfun : (fun f : H => inner ℝ f (GE ω f)) =
      fun f : H => inner ℝ f (Gbase (field ω) f) := by
    apply he.equalizer
    · exact continuous_id.inner ((GE ω).continuous)
    · exact continuous_id.inner ((Gbase (field ω)).continuous)
    · exact funext hω
  exact fun f => congrFun hfun f

end SubdiffusiveProcess.AuditRepairs
