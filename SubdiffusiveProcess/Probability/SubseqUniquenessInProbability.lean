module

public import Mathlib
public import SubdiffusiveProcess.Probability.OpNormCauchyInProbability

@[expose] public section




open Filter MeasureTheory Topology
open scoped ENNReal

namespace SubdiffusiveProcess.Probability

/-! ## Eventual smallness of almost-surely vanishing bad events -/

/-- **Almost-sure eventuality makes null-measurable bad events eventually small.**  If almost every
point is eventually outside the bad sets `A n`, then the outer measures `P (A n)` are eventually
below any prescribed positive bound.  The proof takes the antitone unions `⋃_{k ≥ n} A k`, whose
intersection is the limsup of the bad sets and is null by hypothesis; continuity from above for
null-measurable antitone families gives the limit. -/
theorem aux_eventually_measure_le_of_ae_eventually_notMem
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A : ℕ → Set Ω} (hA : ∀ n, NullMeasurableSet (A n) P)
    {rho : ℝ} (hrho : 0 < rho)
    (hae : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ A n) :
    ∃ N0 : ℕ, ∀ n ≥ N0, P (A n) ≤ ENNReal.ofReal rho := by
  let C : ℕ → Set Ω := fun n => ⋃ k : ℕ, A (k + n)
  have hCmeas : ∀ n, NullMeasurableSet (C n) P := fun n =>
    NullMeasurableSet.iUnion fun k => hA (k + n)
  have hCanti : Antitone C := by
    refine antitone_nat_of_succ_le fun n ω hω => ?_
    rcases Set.mem_iUnion.1 hω with ⟨k, hk⟩
    refine Set.mem_iUnion.2 ⟨k + 1, ?_⟩
    have h : k + (n + 1) = (k + 1) + n := by omega
    rwa [h] at hk
  have hfull : ∀ᵐ ω ∂P, ∃ n, ω ∉ C n := by
    filter_upwards [hae] with ω hω
    obtain ⟨n, hn⟩ := eventually_atTop.1 hω
    exact ⟨n, fun hmem => by
      rcases Set.mem_iUnion.1 hmem with ⟨k, hk⟩
      exact hn (k + n) (Nat.le_add_left n k) hk⟩
  have hnull : P (⋂ n, C n) = 0 := by
    have h := ae_iff.1 hfull
    have hset : {ω | ¬ ∃ n, ω ∉ C n} = ⋂ n, C n := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, not_exists, not_not]
    rwa [hset] at h
  have hlim : Tendsto (fun n => P (C n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop hCmeas hCanti ⟨0, measure_ne_top P (C 0)⟩
    simpa only [Function.comp_def, hnull] using h
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    ((ENNReal.tendsto_nhds_zero.1 hlim) (ENNReal.ofReal rho) (ENNReal.ofReal_pos.2 hrho))
  refine ⟨N0, fun n hn => ?_⟩
  have hsub : A n ⊆ C N0 := by
    intro ω hω
    exact Set.mem_iUnion.2 ⟨n - N0, by rwa [Nat.sub_add_cancel hn]⟩
  exact (measure_mono hsub).trans (hN0 N0 le_rfl)

/-! ## Main lemma: Cauchy in probability -/

/-- **Subsequential compactness plus uniqueness of subsequential limits implies Cauchy in
probability.**  Failure of Cauchy-in-probability produces pairs of arbitrarily large indices with
bad events of outer measure `≥ ρ`; those index maps are refined simultaneously to strictly monotone
subsequences (`Filter.strictMono_subseq_of_tendsto_atTop` twice, with one common refinement), the
uniqueness hypothesis gives a common further subsequence along which both converge almost surely to
one limit, and the triangle inequality makes almost every sample eventually avoid those bad events.
Their probabilities then tend to zero, contradicting the positive lower bound.  No fixed candidate limit is assumed. -/
theorem cauchy_in_probability_of_forall_strictMono_pair_subseq_common_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Type*} [PseudoMetricSpace F] (X : ℕ → Ω → F)
    (hdmeas : ∀ (m m' : ℕ) (eps : ℝ), 0 < eps →
      NullMeasurableSet {ω | eps ≤ dist (X m ω) (X m' ω)} P)
    (hpair : ∀ u v : ℕ → ℕ, StrictMono u → StrictMono v →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ L : Ω → F,
        (∀ᵐ ω ∂P, Tendsto (fun n => X (u (ρ n)) ω) atTop (𝓝 (L ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => X (v (ρ n)) ω) atTop (𝓝 (L ω)))) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
      P {ω | eps ≤ dist (X N ω) (X N' ω)} ≤ ENNReal.ofReal rho := by
  by_contra h
  push_neg at h
  obtain ⟨eps, heps, rho, hrho, hbad⟩ := h
  choose u v huv using hbad
  have hutop : Tendsto u atTop atTop := tendsto_atTop.2 fun M =>
    eventually_atTop.2 ⟨M, fun n hn => hn.trans (huv n).1⟩
  have hvtap : Tendsto v atTop atTop := tendsto_atTop.2 fun M =>
    eventually_atTop.2 ⟨M, fun n hn => hn.trans (huv n).2.1⟩
  -- one common strictly monotone refinement carrying the badness
  obtain ⟨φ, hφ, huφ⟩ := Filter.strictMono_subseq_of_tendsto_atTop hutop
  obtain ⟨ψ, hψ, hvψ⟩ := Filter.strictMono_subseq_of_tendsto_atTop (hvtap.comp hφ.tendsto_atTop)
  set u' : ℕ → ℕ := u ∘ φ ∘ ψ with hu'def
  set v' : ℕ → ℕ := v ∘ φ ∘ ψ with hv'def
  have hu' : StrictMono u' := huφ.comp hψ
  have hv' : StrictMono v' := hvψ
  have hbad' : ∀ n : ℕ, ENNReal.ofReal rho < P {ω | eps ≤ dist (X (u' n) ω) (X (v' n) ω)} :=
    fun n => (huv (φ (ψ n))).2.2
  obtain ⟨ρ, hρ, L, hL1, hL2⟩ := hpair u' v' hu' hv'
  have hae : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∉ {ω | eps ≤ dist (X (u' (ρ n)) ω) (X (v' (ρ n)) ω)} := by
    filter_upwards [hL1, hL2] with ω h1 h2
    have hd : Tendsto (fun n => dist (X (u' (ρ n)) ω) (X (v' (ρ n)) ω)) atTop (𝓝 0) := by
      simpa using h1.dist h2
    refine ((Metric.tendsto_nhds.1 hd) eps heps).mono fun n hn => ?_
    have h' := hn
    rw [Real.dist_eq, sub_zero] at h'
    exact not_le.2 (abs_lt.1 h').2
  obtain ⟨N0, hN0⟩ := aux_eventually_measure_le_of_ae_eventually_notMem P
    (A := fun n => {ω | eps ≤ dist (X (u' (ρ n)) ω) (X (v' (ρ n)) ω)})
    (fun n => hdmeas (u' (ρ n)) (v' (ρ n)) eps heps) hrho hae
  exact absurd (hN0 N0 le_rfl) (not_le.2 (hbad' (ρ N0)))

/-- Index-sequence form of `cauchy_in_probability_of_forall_strictMono_pair_subseq_common_ae`:
the uniqueness hypothesis is assumed for all pairs of index maps tending to infinity. -/
theorem cauchy_in_probability_of_forall_pair_subseq_common_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Type*} [PseudoMetricSpace F] (X : ℕ → Ω → F)
    (hdmeas : ∀ (m m' : ℕ) (eps : ℝ), 0 < eps →
      NullMeasurableSet {ω | eps ≤ dist (X m ω) (X m' ω)} P)
    (hpair : ∀ u v : ℕ → ℕ, Tendsto u atTop atTop → Tendsto v atTop atTop →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ L : Ω → F,
        (∀ᵐ ω ∂P, Tendsto (fun n => X (u (ρ n)) ω) atTop (𝓝 (L ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => X (v (ρ n)) ω) atTop (𝓝 (L ω)))) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
      P {ω | eps ≤ dist (X N ω) (X N' ω)} ≤ ENNReal.ofReal rho :=
  cauchy_in_probability_of_forall_strictMono_pair_subseq_common_ae P X hdmeas
    (fun u v hu hv => hpair u v hu.tendsto_atTop hv.tendsto_atTop)

/-! ## Identified-limit (subsequence criterion) form -/

/-- **Subsequence criterion with an identified limit.**  If every subsequence has a further
subsequence along which `X` converges almost surely to one fixed function `R` (the "every cluster
value is identified with `R`" output of the model-level comparison argument), then the full sequence
converges to `R` in probability.  Elementary contradiction: a bad subsequence of large tail events,
further refined to an almost-surely convergent one, contradicts
`aux_eventually_measure_le_of_ae_eventually_notMem`. -/
theorem tendstoInMeasure_of_forall_strictMono_subseq_exists_subseq_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Type*} [PseudoMetricSpace F] (X : ℕ → Ω → F) (R : Ω → F)
    (hdmeas : ∀ (m : ℕ) (eps : ℝ), 0 < eps →
      NullMeasurableSet {ω | eps ≤ dist (X m ω) (R ω)} P)
    (hsub : ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
        ∀ᵐ ω ∂P, Tendsto (fun n => X (ψ (ψ' n)) ω) atTop (𝓝 (R ω))) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N ≥ N0,
      P {ω | eps ≤ dist (X N ω) (R ω)} ≤ ENNReal.ofReal rho := by
  by_contra h
  push_neg at h
  obtain ⟨eps, heps, rho, hrho, hbad⟩ := h
  have hfreq : ∃ᶠ N in atTop, ENNReal.ofReal rho < P {ω | eps ≤ dist (X N ω) (R ω)} :=
    frequently_atTop.2 fun N0 => hbad N0
  obtain ⟨φ, hφ, hφbad⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨φ', hφ', hae⟩ := hsub φ hφ
  have hae' : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∉ {ω | eps ≤ dist (X (φ (φ' n)) ω) (R ω)} := by
    filter_upwards [hae] with ω hω
    exact ((Metric.tendsto_nhds.1 hω) eps heps).mono fun n hn => not_le.2 hn
  obtain ⟨N0, hN0⟩ := aux_eventually_measure_le_of_ae_eventually_notMem P
    (A := fun n => {ω | eps ≤ dist (X (φ (φ' n)) ω) (R ω)})
    (fun n => hdmeas (φ (φ' n)) eps heps) hrho hae'
  exact absurd (hN0 N0 le_rfl) (not_le.2 (hφbad (φ' N0)))

/-- Cauchy-in-probability form of
`tendstoInMeasure_of_forall_strictMono_subseq_exists_subseq_ae`, obtained by deriving the
pair-of-subsequences interface: for `u` and `v` strict monotone, take the extraction of `u`, then
the extraction of `v` along the first refinement. -/
theorem cauchy_in_probability_of_forall_strictMono_subseq_exists_subseq_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Type*} [PseudoMetricSpace F] (X : ℕ → Ω → F) (R : Ω → F)
    (hdmeas : ∀ (m m' : ℕ) (eps : ℝ), 0 < eps →
      NullMeasurableSet {ω | eps ≤ dist (X m ω) (X m' ω)} P)
    (hsub : ∀ ψ : ℕ → ℕ, StrictMono ψ →
      ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧
        ∀ᵐ ω ∂P, Tendsto (fun n => X (ψ (ψ' n)) ω) atTop (𝓝 (R ω))) :
    ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N N' : ℕ, N0 ≤ N → N0 ≤ N' →
      P {ω | eps ≤ dist (X N ω) (X N' ω)} ≤ ENNReal.ofReal rho := by
  refine cauchy_in_probability_of_forall_strictMono_pair_subseq_common_ae P X hdmeas ?_
  intro u v hu hv
  obtain ⟨u', hu', hu'conv⟩ := hsub u hu
  obtain ⟨w', hw', hw'conv⟩ := hsub (v ∘ u') (hv.comp hu')
  refine ⟨u' ∘ w', hu'.comp hw', R, ?_, ?_⟩
  · filter_upwards [hu'conv] with ω hω
    exact hω.comp hw'.tendsto_atTop
  · filter_upwards [hw'conv] with ω hω
    exact hω

/-! ## Completeness wrapper -/



theorem exists_limit_of_forall_strictMono_pair_subseq_common_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F : Type*} [PseudoMetricSpace F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    (X : ℕ → Ω → F) (hX : ∀ N : ℕ, Measurable (X N))
    (hdmeas : ∀ (m m' : ℕ) (eps : ℝ), 0 < eps →
      NullMeasurableSet {ω | eps ≤ dist (X m ω) (X m' ω)} P)
    (hpair : ∀ u v : ℕ → ℕ, StrictMono u → StrictMono v →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ L : Ω → F,
        (∀ᵐ ω ∂P, Tendsto (fun n => X (u (ρ n)) ω) atTop (𝓝 (L ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => X (v (ρ n)) ω) atTop (𝓝 (L ω)))) :
    ∃ Xlim : Ω → F, Measurable Xlim ∧
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho → ∃ N0 : ℕ, ∀ N ≥ N0,
        P {ω | eps ≤ dist (X N ω) (Xlim ω)} ≤ ENNReal.ofReal rho := by
  have hcauchy := cauchy_in_probability_of_forall_strictMono_pair_subseq_common_ae P X hdmeas hpair
  obtain ⟨Xlim, hmeas, φ, hφ, hφae, hconvLim⟩ :=
    SubdiffusiveProcess.Probability.exists_limit_of_cauchy_in_probability P X hX hcauchy
  exact ⟨Xlim, hmeas, hconvLim⟩

end SubdiffusiveProcess.Probability
