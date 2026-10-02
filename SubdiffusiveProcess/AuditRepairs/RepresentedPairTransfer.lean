import SubdiffusiveProcess.Probability.SubseqUniquenessInProbability
import SubdiffusiveProcess.Probability.ConvergenceInProbability
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Equal cluster limits on auxiliary spaces imply convergence in probability on the
original space. The finite-index environments preserve the entire original law. -/

open Filter MeasureTheory Topology
open scoped ENNReal

namespace SubdiffusiveProcess.AuditRepairs

/-- Auxiliary representations may depend on the pair of subsequences. Only their finite
joint laws and the equality of the two represented limits are needed. -/
theorem cauchy_in_probability_of_represented_pairs
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n))
    (hpair : ∀ u v : ℕ → ℕ, StrictMono u → StrictMono v →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh),
          IsProbabilityMeasure Ph ∧
          ∃ (env : ℕ → Ωh → Ω) (L : Ωh → ℝ),
            (∀ n, MeasurePreserving (env n) Ph P) ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => X (u (σ n)) (env n ω)) atTop (𝓝 (L ω))) ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => X (v (σ n)) (env n ω)) atTop (𝓝 (L ω)))) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ,
      ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
        P {ω | eps ≤ dist (X N ω) (X N' ω)} ≤ ENNReal.ofReal rho := by
  by_contra h
  push_neg at h
  obtain ⟨eps, heps, rho, hrho, hbad⟩ := h
  choose u v huv using hbad
  have hutop : Tendsto u atTop atTop := tendsto_atTop.2 fun M =>
    eventually_atTop.2 ⟨M, fun n hn => hn.trans (huv n).1⟩
  have hvtop : Tendsto v atTop atTop := tendsto_atTop.2 fun M =>
    eventually_atTop.2 ⟨M, fun n hn => hn.trans (huv n).2.1⟩
  obtain ⟨φ, hφ, huφ⟩ := Filter.strictMono_subseq_of_tendsto_atTop hutop
  obtain ⟨ψ, hψ, hvψ⟩ :=
    Filter.strictMono_subseq_of_tendsto_atTop (hvtop.comp hφ.tendsto_atTop)
  let u' : ℕ → ℕ := u ∘ φ ∘ ψ
  let v' : ℕ → ℕ := v ∘ φ ∘ ψ
  have hu' : StrictMono u' := huφ.comp hψ
  have hv' : StrictMono v' := hvψ
  have hbad' : ∀ n, ENNReal.ofReal rho <
      P {ω | eps ≤ dist (X (u' n) ω) (X (v' n) ω)} :=
    fun n => (huv (φ (ψ n))).2.2
  obtain ⟨σ, hσ, Ωh, mΩh, Ph, hPh, env, L, henv, hL1, hL2⟩ := hpair u' v' hu' hv'
  haveI : IsProbabilityMeasure Ph := hPh
  let A : ℕ → Set Ωh := fun n =>
    {ω | eps ≤ dist (X (u' (σ n)) (env n ω)) (X (v' (σ n)) (env n ω))}
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le measurable_const
      (((hX _).comp (henv n).measurable).dist ((hX _).comp (henv n).measurable))
  have hae : ∀ᵐ ω ∂Ph, ∀ᶠ n in atTop, ω ∉ A n := by
    filter_upwards [hL1, hL2] with ω h1 h2
    have hd : Tendsto
        (fun n => dist (X (u' (σ n)) (env n ω)) (X (v' (σ n)) (env n ω)))
        atTop (𝓝 0) := by
      simpa using h1.dist h2
    refine ((Metric.tendsto_nhds.1 hd) eps heps).mono fun n hn => ?_
    have hlt : dist (X (u' (σ n)) (env n ω)) (X (v' (σ n)) (env n ω)) < eps := by
      simpa only [Real.dist_eq, sub_zero, abs_abs] using hn
    exact not_le.mpr hlt
  obtain ⟨N0, hN0⟩ :=
    SubdiffusiveProcess.Probability.aux_eventually_measure_le_of_ae_eventually_notMem Ph
      (fun n => (hA n).nullMeasurableSet) hrho hae
  have hlaw : ∀ n, Ph (A n) =
      P {ω | eps ≤ dist (X (u' (σ n)) ω) (X (v' (σ n)) ω)} := by
    intro n
    exact (henv n).measure_preimage
      (measurableSet_le measurable_const ((hX _).dist (hX _))).nullMeasurableSet
  have hsmall := hN0 N0 le_rfl
  rw [hlaw N0] at hsmall
  exact (not_le.mpr (hbad' (σ N0))) hsmall

/-- The previous finite-joint-law criterion constructs a measurable original-space limit. -/
theorem exists_measurable_limit_of_represented_pairs
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n))
    (hpair : ∀ u v : ℕ → ℕ, StrictMono u → StrictMono v →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh),
          IsProbabilityMeasure Ph ∧
          ∃ (env : ℕ → Ωh → Ω) (L : Ωh → ℝ),
            (∀ n, MeasurePreserving (env n) Ph P) ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => X (u (σ n)) (env n ω)) atTop (𝓝 (L ω))) ∧
            (∀ᵐ ω ∂Ph, Tendsto (fun n => X (v (σ n)) (env n ω)) atTop (𝓝 (L ω)))) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ TendstoInMeasure P X atTop Y ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∀ᵐ ω ∂P, Tendsto (fun n => X (σ n) ω) atTop (𝓝 (Y ω)) :=
  SubdiffusiveProcess.Probability.exists_measurable_limit_in_measure_of_cauchy_in_probability
    P X hX (cauchy_in_probability_of_represented_pairs P X hX hpair)

end SubdiffusiveProcess.AuditRepairs
