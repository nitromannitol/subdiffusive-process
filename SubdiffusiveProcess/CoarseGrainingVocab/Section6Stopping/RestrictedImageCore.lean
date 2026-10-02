import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Order.IsLUB
/-!
# Restricted events from a sufficient ambient event

A measurable observation of a standard Borel sample admits a measurable
subset of the image of any ambient good event, with pullback measure at
least that of the good event. Compact approximation supplies this subset.
Any analytic property constant on observation fibres therefore transfers to
a restricted-measurable good event without increasing its failure bound.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory Filter Topology Set
noncomputable section

theorem restricted_property_of_mem_image {X Y : Type*} (f : X → Y) (P : X → Prop) (G : Set X) (hG : ∀ x ∈ G, P x) (hf : ∀ x y, f x = f y → (P x ↔ P y)) {x : X} (hx : f x ∈ f '' G) : P x := by
  obtain ⟨y, hyG, hfy⟩ := hx
  exact (hf y x hfy).mp (hG y hyG)


theorem restricted_bad_preimage_measurable {X Y : Type*} [MeasurableSpace Y] (f : X → Y) (H : Set Y) (hH : MeasurableSet H) : MeasurableSet[MeasurableSpace.comap f inferInstance] (f ⁻¹' H)ᶜ := by
  have h : MeasurableSet[MeasurableSpace.comap f inferInstance] (f ⁻¹' H) := by
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨H, hH, rfl⟩
  exact h.compl


theorem restricted_good_of_not_mem_bad {X Y : Type*} (f : X → Y) (G : Set X) (H : Set Y) (hH : H ⊆ f '' G) {x : X} (hx : x ∉ (f ⁻¹' H)ᶜ) : ∃ y ∈ G, f y = f x := by
  have hfx : f x ∈ H := by
    by_contra h
    exact hx (by simp [h])
  obtain ⟨y, hyG, hy⟩ := hH hfx
  exact ⟨y, hyG, hy⟩


theorem restricted_compact_image_subset {X Y : Type*} (f : X → Y) (G : Set X) (K : ℕ → Set X) (hK : ∀ n, K n ⊆ G) : (⋃ n, f '' K n) ⊆ f '' G := by
  intro y hy
  rcases Set.mem_iUnion.mp hy with ⟨n, hn⟩
  rcases hn with ⟨x, hxK, rfl⟩
  exact ⟨x, hK n hxK, rfl⟩

theorem restricted_image_measurable_union {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y] (f : X → Y) (hf : Continuous f) (K : ℕ → Set X) (hK : ∀ n, IsCompact (K n)) : MeasurableSet (⋃ n, f '' K n) := by
  apply MeasurableSet.iUnion
  intro n
  exact ((hK n).image hf).isClosed.measurableSet


theorem restricted_compl_measure_le {X : Type*} [MeasurableSpace X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure mu]
    (G H : Set X) (hG : MeasurableSet G) (hH : MeasurableSet H)
    (h : mu G ≤ mu H) : mu Hᶜ ≤ mu Gᶜ := by
  rw [MeasureTheory.measure_compl hH (measure_ne_top mu H),
      MeasureTheory.measure_compl hG (measure_ne_top mu G)]
  exact tsub_le_tsub_left h _


theorem restricted_compact_measure_isLUB {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (mu : Measure X) [mu.InnerRegular] (G : Set X) (hG : MeasurableSet G) : IsLUB {r | ∃ K : Set X, K ⊆ G ∧ IsCompact K ∧ r = mu K} (mu G) := by
  constructor
  · intro r hr
    obtain ⟨K, hKG, hK, rfl⟩ := hr
    exact measure_mono hKG
  · intro r hr
    rw [hG.measure_eq_iSup_isCompact mu]
    apply iSup_le
    · intro K
      apply iSup_le
      · intro hKG
        apply iSup_le
        · intro hK
          exact hr ⟨K, hKG, hK, rfl⟩

theorem restricted_image_core_measure {X Y : Type*} [MeasurableSpace X] (mu : Measure X) (f : X → Y) (G : Set X) (K : ℕ → Set X) (ht : Tendsto (fun n => mu (K n)) atTop (𝓝 (mu G))) : mu G ≤ mu (f ⁻¹' (⋃ n, f '' K n)) := by
  refine le_of_tendsto ht (Filter.Eventually.of_forall fun n => ?_)
  apply measure_mono
  intro x hx
  exact Set.mem_iUnion.mpr ⟨n, x, hx, rfl⟩


theorem restricted_exists_image_core_continuous
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (mu : Measure X) [mu.InnerRegular] (f : X → Y) (hf : Continuous f)
    (G : Set X) (hG : MeasurableSet G) :
    ∃ H : Set Y, MeasurableSet H ∧ H ⊆ f '' G ∧ mu G ≤ mu (f ⁻¹' H) := by
  have hLub := restricted_compact_measure_isLUB mu G hG
  have hnonempty : {r | ∃ K : Set X, K ⊆ G ∧ IsCompact K ∧ r = mu K}.Nonempty :=
    ⟨mu ∅, ∅, empty_subset G, isCompact_empty, rfl⟩
  obtain ⟨u, _hmono, _hle, htend, hmem⟩ :=
    hLub.exists_seq_monotone_tendsto hnonempty
  choose K hKG hK hval using hmem
  have hu : u = fun n => mu (K n) := funext hval
  rw [hu] at htend
  exact ⟨⋃ n, f '' K n, restricted_image_measurable_union f hf K hK,
    restricted_compact_image_subset f G K hKG,
    restricted_image_core_measure mu f G K htend⟩

theorem restricted_exists_image_core
    {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (mu : Measure X) [IsFiniteMeasure mu] (f : X → Y) (hf : Measurable f)
    (G : Set X) (hG : MeasurableSet G) :
    ∃ H : Set Y, MeasurableSet H ∧ H ⊆ f '' G ∧ mu G ≤ mu (f ⁻¹' H) := by
  letI := upgradeStandardBorel X
  obtain ⟨t, hle, hcont, hpolish⟩ := hf.exists_continuous
  have hborel : @BorelSpace X t inferInstance := by
    constructor
    rw [eq_borel_upgradeStandardBorel X,
      borel_eq_borel_of_le hpolish (by infer_instance) hle]
  letI := t
  letI := hpolish
  letI := hborel
  exact restricted_exists_image_core_continuous mu f hcont G hG

theorem restricted_exists_bad_event
    {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (mu : Measure X) [IsFiniteMeasure mu] (f : X → Y) (hf : Measurable f)
    (P : X → Prop) (G : Set X) (hG : MeasurableSet G)
    (hGP : ∀ x ∈ G, P x) (hP : ∀ x y, f x = f y → (P x ↔ P y)) :
    ∃ bad : Set X, MeasurableSet[MeasurableSpace.comap f inferInstance] bad ∧
      mu bad ≤ mu Gᶜ ∧ ∀ x ∉ bad, P x := by
  obtain ⟨H, hH, hHG, hmu⟩ := restricted_exists_image_core mu f hf G hG
  refine ⟨(f ⁻¹' H)ᶜ, restricted_bad_preimage_measurable f H hH,
    restricted_compl_measure_le mu G (f ⁻¹' H) hG (hH.preimage hf) hmu, ?_⟩
  intro x hx
  obtain ⟨y, hy, heq⟩ := restricted_good_of_not_mem_bad f G H hHG hx
  exact (hP y x heq).mp (hGP y hy)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
