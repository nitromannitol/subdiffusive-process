module

public import SubdiffusiveProcess.Probability.ProkhorovCompact
public import SubdiffusiveProcess.Probability.ProkhorovEmbedding
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

@[expose] public section

/-! Sequential Prokhorov compactness. Embed the Polish source into a compact countable
cube, extract a limit there, and use tightness and Portmanteau to pull the limit back. -/

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

noncomputable section

namespace SubdiffusiveProcess.Probability

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [PolishSpace X] in
/-- A tight weak limit in an ambient space gives full mass to the embedded source. -/
theorem measure_range_eq_one_of_tight (e : X → Y) (he : IsEmbedding e)
    (mu : ℕ → ProbabilityMeasure X) (nu : ProbabilityMeasure Y)
    (htight : IsTightMeasureSet (Set.range (fun n => (mu n : Measure X))))
    (hlim : Tendsto (fun n => (mu n).map e)
      atTop (𝓝 nu)) :
    (nu : Measure Y) (Set.range e) = 1 := by
  apply le_antisymm prob_le_one
  apply ENNReal.le_of_forall_pos_le_add
  intro eps heps _
  obtain ⟨K, hK, htail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (eps : ℝ≥0∞) (by exact_mod_cast heps)
  have hclosed : IsClosed (e '' K) := (hK.image he.continuous).isClosed
  have htail' : ∀ n,
      ((mu n).map e : Measure Y) (e '' K)ᶜ ≤ eps := by
    intro n
    rw [ProbabilityMeasure.map_apply' _ he.continuous.measurable.aemeasurable hclosed.measurableSet.compl,
      Set.preimage_compl, Set.preimage_image_eq _ he.injective]
    exact htail _ (Set.mem_range_self n)
  have hlimit_tail : (nu : Measure Y) (e '' K)ᶜ ≤ eps :=
    (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hclosed.isOpen_compl).trans
      ((liminf_le_limsup (u := fun n =>
        ((mu n).map e : Measure Y) (e '' K)ᶜ)).trans
        (limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall htail')))
  calc
    1 = (nu : Measure Y) (e '' K) + (nu : Measure Y) (e '' K)ᶜ := by
      simpa using (measure_add_measure_compl (μ := (nu : Measure Y))
        hclosed.measurableSet).symm
    _ ≤ (nu : Measure Y) (Set.range e) + eps :=
      add_le_add (measure_mono (Set.image_subset_range e K)) hlimit_tail

/-- Tightness allows closed-set Portmanteau estimates to be transported through an embedding. -/
theorem tendsto_comap_of_tight (e : X → Y) (he : IsEmbedding e)
    (mu : ℕ → ProbabilityMeasure X) (nu : ProbabilityMeasure Y)
    (htight : IsTightMeasureSet (Set.range (fun n => (mu n : Measure X))))
    (hlim : Tendsto (fun n => (mu n).map e)
      atTop (𝓝 nu)) :
    ∃ rho : ProbabilityMeasure X, Tendsto mu atTop (𝓝 rho) := by
  have hem : MeasurableEmbedding e := he.continuous.measurableEmbedding he.injective
  let rho : Measure X := (nu : Measure Y).comap e
  have hrho : IsProbabilityMeasure rho := by
    constructor
    rw [Measure.comap_apply e he.injective (fun S hS => hem.measurableSet_image.mpr hS)
      (nu : Measure Y) MeasurableSet.univ, Set.image_univ]
    exact measure_range_eq_one_of_tight e he mu nu htight hlim
  let P : ProbabilityMeasure X := ⟨rho, hrho⟩
  refine ⟨P, tendsto_of_forall_isClosed_limsup_le' ?_⟩
  intro F hF
  apply ENNReal.le_of_forall_pos_le_add
  intro eps heps _
  obtain ⟨K, hK, htail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (eps : ℝ≥0∞) (by exact_mod_cast heps)
  have hclosed : IsClosed (e '' (F ∩ K)) :=
    ((hK.inter_left hF).image he.continuous).isClosed
  have hbound (n : ℕ) : (mu n : Measure X) F ≤
      ((mu n).map e : Measure Y) (e '' (F ∩ K)) + eps := by
    rw [ProbabilityMeasure.map_apply' _ he.continuous.measurable.aemeasurable hclosed.measurableSet,
      Set.preimage_image_eq _ he.injective]
    calc
      (mu n : Measure X) F ≤ (mu n : Measure X) ((F ∩ K) ∪ Kᶜ) := by
        apply measure_mono
        intro x hx
        by_cases hxK : x ∈ K
        · exact Or.inl ⟨hx, hxK⟩
        · exact Or.inr hxK
      _ ≤ (mu n : Measure X) (F ∩ K) + (mu n : Measure X) Kᶜ := measure_union_le _ _
      _ ≤ (mu n : Measure X) (F ∩ K) + eps :=
        add_le_add le_rfl (htail _ (Set.mem_range_self n))
  have hsub : (nu : Measure Y) (e '' (F ∩ K)) ≤ (P : Measure X) F := by
    change (nu : Measure Y) (e '' (F ∩ K)) ≤ rho F
    rw [Measure.comap_apply e he.injective (fun S hS => hem.measurableSet_image.mpr hS)
      (nu : Measure Y) hF.measurableSet]
    exact measure_mono (Set.image_mono Set.inter_subset_left)
  calc
    limsup (fun n => (mu n : Measure X) F) atTop ≤
        limsup (fun n =>
          ((mu n).map e : Measure Y) (e '' (F ∩ K)) + eps)
          atTop := limsup_le_limsup (Eventually.of_forall hbound)
    _ = limsup (fun n =>
          ((mu n).map e : Measure Y) (e '' (F ∩ K)))
          atTop + eps := limsup_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault)
    _ ≤ (nu : Measure Y) (e '' (F ∩ K)) + eps :=
      add_le_add (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hclosed) le_rfl
    _ ≤ (P : Measure X) F + eps := add_le_add hsub le_rfl

/-- Sequential Prokhorov compactness on a Polish space. -/
theorem prokhorov_sequential (mu : ℕ → ProbabilityMeasure X)
    (htight : IsTightMeasureSet (Set.range (fun n => (mu n : Measure X)))) :
    ∃ (seq : ℕ → ℕ) (nu : ProbabilityMeasure X), StrictMono seq ∧
      Tendsto (fun n => mu (seq n)) atTop (𝓝 nu) := by
  obtain ⟨e, he⟩ := exists_polish_embedding_cube X
  letI : MeasurableSpace (ℕ → unitInterval) := borel _
  letI : BorelSpace (ℕ → unitInterval) := ⟨rfl⟩
  let pushed : ℕ → ProbabilityMeasure (ℕ → unitInterval) :=
    fun n => (mu n).map e
  obtain ⟨seq, nu, hseq, hlim⟩ := probability_subsequence_compact pushed
  have hsubtight : IsTightMeasureSet (Set.range (fun n => (mu (seq n) : Measure X))) :=
    htight.subset (by rintro _ ⟨n, rfl⟩; exact ⟨seq n, rfl⟩)
  obtain ⟨rho, hrho⟩ := tendsto_comap_of_tight e he (fun n => mu (seq n)) nu hsubtight hlim
  exact ⟨seq, rho, hseq, hrho⟩

end SubdiffusiveProcess.Probability
