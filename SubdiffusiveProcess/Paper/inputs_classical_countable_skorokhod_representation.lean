module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Topology.MetricSpace.Polish
public import SubdiffusiveProcess.Paper.classical_prokhorov_sequential
public import SubdiffusiveProcess.Paper.classical_skorokhod_representation

@[expose] public section

/-! Countable Polish joint representation from coordinate tightness.
Follows from the two exact classical leaves `classical_prokhorov_sequential` (Kallenberg 2002, Thm 16.3;
Billingsley 1999, Thm 5.1) and `classical_skorokhod_representation` (Kallenberg 2002, Thm 4.30; Billingsley 1999,
Thm 6.7), by tightness of countable products (Tychonoff) and the canonical-space push-forward. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory
open scoped Topology ENNReal
universe u v
namespace SubdiffusiveProcess.Paper

/-- Tightness of every coordinate family of marginals gives tightness of the family on the countable product. -/
theorem aux_inputs_classical_countable_skorokhod_representation_tight
    {I : Type u} [Countable I] (S : I → Type v)
    [∀ i, TopologicalSpace (S i)] [∀ i, PolishSpace (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (mu : ℕ → Measure ((i : I) → S i))
    (htight : ∀ i, IsTightMeasureSet
      (Set.range (fun n => Measure.map (fun x : (i : I) → S i => x i) (mu n)))) :
    IsTightMeasureSet (Set.range mu) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨e, he⟩ := Countable.exists_injective_nat I
  have hpos : ∀ i : I, 0 < ε / 2 ^ (e i + 1) := fun i =>
    ENNReal.div_pos hε.ne' (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  choose K hKc hK using fun i =>
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 (htight i)) _ (hpos i)
  refine ⟨Set.pi Set.univ K, isCompact_univ_pi hKc, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hset : (Set.pi Set.univ K)ᶜ = ⋃ i, {x : (i : I) → S i | x i ∈ (K i)ᶜ} := by
    ext x
    simp [Set.mem_pi]
  calc mu n (Set.pi Set.univ K)ᶜ = mu n (⋃ i, {x : (i : I) → S i | x i ∈ (K i)ᶜ}) := by rw [hset]
    _ ≤ ∑' i, mu n {x : (i : I) → S i | x i ∈ (K i)ᶜ} := measure_iUnion_le _
    _ ≤ ∑' i, ε / 2 ^ (e i + 1) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        have h1 := hK i (Measure.map (fun x : (i : I) → S i => x i) (mu n)) ⟨n, rfl⟩
        rwa [Measure.map_apply (measurable_pi_apply i) (hKc i).isClosed.measurableSet.compl] at h1
    _ ≤ ∑' k : ℕ, ε / 2 ^ (k + 1) := ENNReal.tsum_comp_le_tsum_of_injective he (fun k => ε / 2 ^ (k + 1))
    _ = ε := by
        have : ∀ k : ℕ, ε / 2 ^ (k + 1) = ε * (2⁻¹) ^ (k + 1) := by
          intro k
          rw [div_eq_mul_inv, ENNReal.inv_pow]
        simp_rw [this]
        rw [ENNReal.tsum_mul_left]
        have hg : ∑' k : ℕ, (2⁻¹ : ℝ≥0∞) ^ (k + 1) = 1 := by
          simp_rw [pow_succ]
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
          rw [ENNReal.one_sub_inv_two, inv_inv]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [hg, mul_one]

/-- At every index, preserves the joint law of the entire coordinate vector.
The probability space is the canonical space of sequences and their limits. -/
theorem inputs_classical_countable_skorokhod_representation
    {I : Type*} [Countable I] (S : I → Type*)
    [∀ i, TopologicalSpace (S i)] [∀ i, PolishSpace (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (mu : ℕ → Measure ((i : I) → S i))
    (hprob : ∀ n, IsProbabilityMeasure (mu n))
    (htight : ∀ i, IsTightMeasureSet
      (Set.range (fun n => Measure.map (fun x : (i : I) → S i => x i) (mu n)))) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∃ P : Measure ((ℕ → (i : I) → S i) × ((i : I) → S i)),
        IsProbabilityMeasure P ∧
        (∀ n, Measure.map
          (fun omega : (ℕ → (i : I) → S i) × ((i : I) → S i) => omega.1 n) P =
            mu (seq n)) ∧
        (∀ᵐ omega ∂P, Tendsto (fun n => omega.1 n) atTop (𝓝 omega.2)) := by
  classical
  have hjoint := aux_inputs_classical_countable_skorokhod_representation_tight S mu htight
  let muP : ℕ → ProbabilityMeasure ((i : I) → S i) := fun n => ⟨mu n, hprob n⟩
  have htight' : IsTightMeasureSet (Set.range (fun n => (muP n : Measure ((i : I) → S i)))) := hjoint
  obtain ⟨seq, nu, hseq, hconv⟩ := classical_prokhorov_sequential muP htight'
  obtain ⟨Ω, hΩ, P, Xn, X0, hP, hXn, hX0, hlaw, hlaw0, hae⟩ :=
    classical_skorokhod_representation (fun n => muP (seq n)) nu hconv
  let Φ : Ω → (ℕ → (i : I) → S i) × ((i : I) → S i) := fun ω => (fun n => Xn n ω, X0 ω)
  have hΦ : Measurable Φ := (measurable_pi_iff.2 hXn).prodMk hX0
  have hmeasT : MeasurableSet
      {ω : (ℕ → (i : I) → S i) × ((i : I) → S i) | Tendsto (fun n => ω.1 n) atTop (𝓝 ω.2)} := by
    let : MetricSpace ((i : I) → S i) := TopologicalSpace.metrizableSpaceMetric _
    have hset : {ω : (ℕ → (i : I) → S i) × ((i : I) → S i) | Tendsto (fun n => ω.1 n) atTop (𝓝 ω.2)} =
        {ω | Tendsto (fun n => dist (ω.1 n) ω.2) atTop (𝓝 (0 : ℝ))} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      exact tendsto_iff_dist_tendsto_zero
    rw [hset]
    exact measurableSet_tendsto (𝓝 (0 : ℝ)) (fun n =>
      ((measurable_pi_apply n).comp measurable_fst).dist measurable_snd)
  have : IsProbabilityMeasure P := hP
  have : IsProbabilityMeasure (P.map Φ) := inferInstance
  refine ⟨seq, hseq, P.map Φ, inferInstance, ?_, ?_⟩
  · intro n
    have hg : Measurable (fun omega : (ℕ → (i : I) → S i) × ((i : I) → S i) => omega.1 n) :=
      (measurable_pi_apply n).comp measurable_fst
    rw [Measure.map_map hg hΦ]
    exact hlaw n
  · exact (ae_map_iff hΦ.aemeasurable hmeasT).2 hae

end SubdiffusiveProcess.Paper
