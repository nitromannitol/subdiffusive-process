module

public import SubdiffusiveProcess.Probability.OpNormCauchyInProbability
public import SubdiffusiveProcess.Probability.SubseqInProbability

@[expose] public section

/-!
# Convergence in probability through Mathlib's convergence-in-measure API

The process-convergence proofs use explicit error and probability tolerances.
These lemmas connect that formulation to `MeasureTheory.TendstoInMeasure`, so
consumers can reuse Mathlib's subsequence and uniqueness theorems. The target
may be a nonseparable complete pseudometric space, as in operator-norm convergence.
-/

open Filter MeasureTheory Topology

namespace SubdiffusiveProcess.Probability

/-- The two-tolerance formulation of convergence in probability is convergence in measure.
No measurability of the distance events is required for this equivalence. -/
theorem tendstoInMeasure_iff_probability_bounds
    {Ω F : Type*} [MeasurableSpace Ω] [PseudoMetricSpace F]
    (P : Measure Ω) (X : ℕ → Ω → F) (Y : Ω → F) :
    TendstoInMeasure P X atTop Y ↔
      ∀ ε : ℝ, 0 < ε → ∀ ρ : ℝ, 0 < ρ → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        P {ω | ε ≤ dist (X N ω) (Y ω)} ≤ ENNReal.ofReal ρ := by
  rw [tendstoInMeasure_iff_dist]
  constructor
  · intro h ε hε
    exact (SubdiffusiveProcess.tendsto_zero_ennreal_iff_real _).mp (h ε hε)
  · intro h ε hε
    exact (SubdiffusiveProcess.tendsto_zero_ennreal_iff_real _).mpr (h ε hε)

/-- A measurable sequence that is Cauchy in probability has a measurable limit in measure,
and a strictly increasing subsequence converges almost everywhere to that same limit. -/
theorem exists_measurable_limit_in_measure_of_cauchy_in_probability
    {Ω F : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    [PseudoMetricSpace F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    (X : ℕ → Ω → F) (hX : ∀ N, Measurable (X N))
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∀ ρ : ℝ, 0 < ρ → ∃ N₀ : ℕ,
      ∀ N N', N₀ ≤ N → N₀ ≤ N' →
        P {ω | ε ≤ dist (X N ω) (X N' ω)} ≤ ENNReal.ofReal ρ) :
    ∃ Y : Ω → F, Measurable Y ∧ TendstoInMeasure P X atTop Y ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ ω ∂P, Tendsto (fun n => X (φ n) ω) atTop (𝓝 (Y ω)) := by
  obtain ⟨Y, hY, φ, hφ, hae, hprob⟩ :=
    exists_limit_of_cauchy_in_probability P X hX hCauchy
  exact ⟨Y, hY, (tendstoInMeasure_iff_probability_bounds P X Y).mpr hprob,
    φ, hφ, hae⟩

/-- An almost-everywhere subsequential limit agrees with the limit in probability.
Neither separability nor measurability of the distance events is needed: extract
a further almost-everywhere convergent subsequence using Mathlib. -/
theorem ae_eq_of_tendstoInMeasure_of_subseq_tendsto_ae
    {Ω F : Type*} [MeasurableSpace Ω] [MetricSpace F]
    {P : Measure Ω} {X : ℕ → Ω → F} {Y Z : Ω → F}
    (hY : TendstoInMeasure P X atTop Y)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hZ : ∀ᵐ ω ∂P, Tendsto (fun n => X (φ n) ω) atTop (𝓝 (Z ω))) :
    Y =ᵐ[P] Z := by
  obtain ⟨ψ, hψ, hψY⟩ := (hY.comp hφ).exists_seq_tendsto_ae
  filter_upwards [hψY, hZ] with ω hYω hZω
  exact tendsto_nhds_unique hYω (hZω.comp hψ.tendsto_atTop)

end SubdiffusiveProcess.Probability
