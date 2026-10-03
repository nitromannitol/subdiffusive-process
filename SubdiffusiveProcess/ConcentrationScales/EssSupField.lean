module

public import Mathlib

@[expose] public section

/-!
# Essential suprema of jointly measurable random fields

`Y : Ω → T → ℝ` is a random field which is jointly measurable in `(ω, x)`; `ν` is a measure on the
index space `T`.  The functional `ω ↦ essSup_x G(Y ω x)` is measurable in `ω`, and it agrees `μ`-almost surely
with a supremum over a *countable* set `S` of indices, which may be prescribed to lie in any `ν`-conull set.
Consequently the essential-supremum functional is (almost surely) a measurable functional of the
product-σ-algebra law of the field, and it is invariant, in the one-sided sense used below, under
equality of laws of fields.
-/

namespace SubdiffusiveProcess.ConcentrationScales

open MeasureTheory
open scoped ENNReal

noncomputable section

section EssSup

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]

theorem lt_essSup_iff_measure_ne_zero {ν : Measure T} {f : T → ℝ≥0∞} {c : ℝ≥0∞} :
    c < essSup f ν ↔ ν {x | c < f x} ≠ 0 := by
  constructor
  · intro h h0
    refine absurd (essSup_le_of_ae_le c ?_) (not_le.mpr h)
    rw [Filter.EventuallyLE, ae_iff]
    simpa using h0
  · intro h
    by_contra hle
    push_neg at hle
    refine h (measure_mono_null (fun x hx => ?_) (ae_iff.mp (ENNReal.ae_le_essSup (μ := ν) f)))
    exact not_le.mpr (lt_of_le_of_lt hle hx)

/-- The essential supremum of a jointly measurable family is a measurable function of the parameter. -/
theorem measurable_essSup_uncurry {g : Ω → T → ℝ≥0∞} (hg : Measurable (Function.uncurry g))
    (ν : Measure T) [SFinite ν] : Measurable (fun ω => essSup (g ω) ν) := by
  refine measurable_of_Ioi fun c => ?_
  have hset : (fun ω => essSup (g ω) ν) ⁻¹' Set.Ioi c = {ω | ν {x | c < g ω x} ≠ 0} := by
    ext ω
    simp [lt_essSup_iff_measure_ne_zero]
  rw [hset]
  have hs : MeasurableSet {p : Ω × T | c < Function.uncurry g p} :=
    measurableSet_lt measurable_const hg
  have hm : Measurable fun ω => ν {x | c < g ω x} :=
    measurable_measure_prodMk_left (ν := ν) hs
  exact (hm (measurableSet_singleton 0)).compl


/-- Countable exhaustion up to null sets: a countable subfamily whose union contains every member up to a null set. -/
theorem exists_countable_ae_subset_biUnion {ι : Type*} (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    ∃ S : Set ι, S.Countable ∧ ∀ i, μ (A i \ ⋃ j ∈ S, A j) = 0 := by
  classical
  let F : {S : Set ι // S.Countable} → ℝ≥0∞ := fun S => μ (⋃ j ∈ S.1, A j)
  let m : ℝ≥0∞ := ⨆ S, F S
  have hmfin : m ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
      (iSup_le fun S => measure_mono (Set.subset_univ _))
  have happrox : ∀ n : ℕ, ∃ S : {S : Set ι // S.Countable}, m ≤ F S + ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    by_cases hm0 : m = 0
    · exact ⟨⟨∅, Set.countable_empty⟩, by simp [hm0]⟩
    · have hε : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := by simp
      have hlt : m - ((n : ℝ≥0∞) + 1)⁻¹ < m := ENNReal.sub_lt_self hmfin hm0 hε
      obtain ⟨S, hS⟩ := lt_iSup_iff.mp hlt
      exact ⟨S, tsub_le_iff_right.mp hS.le⟩
  choose S hS using happrox
  let S₀ : Set ι := ⋃ n, (S n).1
  have hS₀ : S₀.Countable := Set.countable_iUnion fun n => (S n).2
  have hle : μ (⋃ j ∈ S₀, A j) ≤ m := le_iSup F ⟨S₀, hS₀⟩
  have hge : m ≤ μ (⋃ j ∈ S₀, A j) := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by simpa using hε.ne')
    have hsub : F (S n) ≤ μ (⋃ j ∈ S₀, A j) :=
      measure_mono (Set.biUnion_subset_biUnion_left (Set.subset_iUnion (fun n => (S n).1) n))
    calc m ≤ F (S n) + ((n : ℝ≥0∞) + 1)⁻¹ := hS n
      _ ≤ μ (⋃ j ∈ S₀, A j) + (ε : ℝ≥0∞) := by
        gcongr
        exact le_trans (ENNReal.inv_le_inv.mpr (by simp)) hn.le
  have heq : μ (⋃ j ∈ S₀, A j) = m := le_antisymm hle hge
  refine ⟨S₀, hS₀, fun i => ?_⟩
  by_contra hne
  have hmeas : MeasurableSet (⋃ j ∈ S₀, A j) := MeasurableSet.biUnion hS₀ fun j _ => hA j
  have h1 : F ⟨insert i S₀, hS₀.insert i⟩ ≤ m := le_iSup F ⟨insert i S₀, hS₀.insert i⟩
  have h2 : F ⟨insert i S₀, hS₀.insert i⟩ = μ (⋃ j ∈ S₀, A j) + μ (A i \ ⋃ j ∈ S₀, A j) := by
    change μ (⋃ j ∈ insert i S₀, A j) = _
    rw [Set.biUnion_insert, measure_add_diff hmeas.nullMeasurableSet, Set.union_comm]
  rw [h2, heq] at h1
  have : μ (A i \ ⋃ j ∈ S₀, A j) ≤ 0 :=
    (ENNReal.add_le_add_iff_left hmfin).mp (by simpa using h1)
  exact hne (le_antisymm this bot_le)

/-- Almost every index `x` is *good*: `g · x` is dominated by `essSup (g ω) ν` for `μ`-almost every `ω`. -/
theorem ae_forall_ae_le_essSup {μ : Measure Ω} [SFinite μ] {ν : Measure T} [SFinite ν]
    {g : Ω → T → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) :
    ∀ᵐ x ∂ν, ∀ᵐ ω ∂μ, g ω x ≤ essSup (g ω) ν := by
  have hmeasEss := measurable_essSup_uncurry hg ν
  have hset : MeasurableSet {p : Ω × T | g p.1 p.2 ≤ essSup (g p.1) ν} :=
    measurableSet_le hg (hmeasEss.comp measurable_fst)
  exact (Measure.ae_ae_comm hset).mp (Filter.Eventually.of_forall fun ω => ENNReal.ae_le_essSup _)

/-- **Countable representation of the essential supremum.**  For a jointly measurable family
`g : Ω → T → ℝ≥0∞` there is a countable set `S` of indices, which may be taken inside any prescribed
`ν`-conull set `𝒢`, with `essSup (g ω) ν = ⨆ x ∈ S, g ω x` for `μ`-almost every `ω`. -/
theorem exists_countable_essSup_eq {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure T} [SFinite ν]
    {g : Ω → T → ℝ≥0∞} (hg : Measurable (Function.uncurry g)) (𝒢 : Set T)
    (h𝒢 : ∀ᵐ x ∂ν, x ∈ 𝒢) :
    ∃ S : Set T, S.Countable ∧ S ⊆ 𝒢 ∧ ∀ᵐ ω ∂μ, essSup (g ω) ν = ⨆ x ∈ S, g ω x := by
  classical
  have hgood := ae_forall_ae_le_essSup (μ := μ) hg (ν := ν)
  let 𝒢' : Set T := {x | x ∈ 𝒢 ∧ ∀ᵐ ω ∂μ, g ω x ≤ essSup (g ω) ν}
  have h𝒢' : ∀ᵐ x ∂ν, x ∈ 𝒢' := by
    filter_upwards [h𝒢, hgood] with x h1 h2 using ⟨h1, h2⟩
  let A : ℚ → 𝒢' → Set Ω := fun q x => {ω | (Real.toNNReal q : ℝ≥0∞) < g ω (x : T)}
  have hA : ∀ q x, MeasurableSet (A q x) := fun q x =>
    measurableSet_lt measurable_const (hg.comp (measurable_id.prodMk measurable_const))
  have hex : ∀ q : ℚ, ∃ S : Set 𝒢', S.Countable ∧ ∀ x, μ (A q x \ ⋃ y ∈ S, A q y) = 0 :=
    fun q => exists_countable_ae_subset_biUnion μ (A q) (hA q)
  choose Sq hSq hmax using hex
  let S : Set T := ⋃ q : ℚ, (Subtype.val '' Sq q)
  have hSc : S.Countable := Set.countable_iUnion fun q => (hSq q).image _
  have hS𝒢' : S ⊆ 𝒢' := by
    intro x hx
    simp only [S, Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨q, y, _, rfl⟩ := hx
    exact y.2
  have hmeasEss := measurable_essSup_uncurry hg ν
  have hup : ∀ᵐ ω ∂μ, ⨆ x ∈ S, g ω x ≤ essSup (g ω) ν := by
    have hall : ∀ᵐ ω ∂μ, ∀ x ∈ S, g ω x ≤ essSup (g ω) ν := by
      rw [ae_ball_iff hSc]
      intro x hx
      exact (hS𝒢' hx).2
    filter_upwards [hall] with ω hω
    exact iSup₂_le hω
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂μ, ω ∈ (⋃ y ∈ Sq q, A q y)ᶜ →
      ν {x | (Real.toNNReal q : ℝ≥0∞) < g ω x} = 0 := by
    intro q
    have hN : MeasurableSet ((⋃ y ∈ Sq q, A q y)ᶜ) :=
      (MeasurableSet.biUnion (hSq q) fun y _ => hA q y).compl
    have hset : MeasurableSet
        {p : Ω × T | ¬ (p.1 ∈ (⋃ y ∈ Sq q, A q y)ᶜ ∧ (Real.toNNReal q : ℝ≥0∞) < g p.1 p.2)} :=
      ((hN.preimage measurable_fst).inter (measurableSet_lt measurable_const hg)).compl
    have h1 : ∀ᵐ x ∂ν, ∀ᵐ ω ∂μ,
        ¬ (ω ∈ (⋃ y ∈ Sq q, A q y)ᶜ ∧ (Real.toNNReal q : ℝ≥0∞) < g ω x) := by
      filter_upwards [h𝒢'] with x hx
      have h0 := hmax q ⟨x, hx⟩
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) h0
      have hω' := not_not.mp hω
      exact ⟨hω'.2, hω'.1⟩
    have h2 := (Measure.ae_ae_comm (μ := μ) (ν := ν)
      (p := fun ω x => ¬ (ω ∈ (⋃ y ∈ Sq q, A q y)ᶜ ∧ (Real.toNNReal q : ℝ≥0∞) < g ω x)) hset).mpr h1
    filter_upwards [h2] with ω hω hωN
    rw [ae_iff] at hω
    exact measure_mono_null (fun x hx => not_not.mpr ⟨hωN, hx⟩) hω
  have hdown : ∀ᵐ ω ∂μ, essSup (g ω) ν ≤ ⨆ x ∈ S, g ω x := by
    filter_upwards [ae_all_iff.mpr hq] with ω hω
    by_contra hlt
    push_neg at hlt
    obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt
    have hωN : ω ∈ (⋃ y ∈ Sq q, A q y)ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      intro y hy hlt'
      have hyS : (y : T) ∈ S := by
        simp only [S, Set.mem_iUnion, Set.mem_image]
        exact ⟨q, y, hy, rfl⟩
      have : g ω (y : T) ≤ ⨆ x ∈ S, g ω x := le_iSup₂ (f := fun x _ => g ω x) (y : T) hyS
      exact absurd (lt_of_lt_of_le hlt' this) (not_lt.mpr hq1.le)
    have h0 := hω q hωN
    exact (lt_essSup_iff_measure_ne_zero.mp hq2) h0
  refine ⟨S, hSc, fun x hx => (hS𝒢' hx).1, ?_⟩
  filter_upwards [hup, hdown] with ω h1 h2 using le_antisymm h2 h1

theorem measurable_field_of_uncurry {Y : Ω → T → ℝ} (hY : Measurable fun p : Ω × T => Y p.1 p.2) :
    Measurable Y :=
  measurable_pi_iff.mpr fun _ => hY.comp (measurable_id.prodMk measurable_const)

/-- The essential supremum of `G (Y ω ·)` is, almost surely, a measurable functional of the field
`Y ω : T → ℝ`, measurable for the product σ-algebra of the function space. -/
theorem exists_measurable_functional_ae_eq_essSup {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : Measure T} [SFinite ν] {Y : Ω → T → ℝ} (hY : Measurable fun p : Ω × T => Y p.1 p.2)
    {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∃ ρ : (T → ℝ) → ℝ≥0∞, Measurable ρ ∧
      ∀ᵐ ω ∂μ, essSup (fun x => G (Y ω x)) ν = ρ (Y ω) := by
  obtain ⟨S, hSc, -, hS⟩ := exists_countable_essSup_eq (μ := μ) (ν := ν)
    (g := fun ω x => G (Y ω x)) (hG.comp hY) Set.univ (Filter.Eventually.of_forall fun _ => trivial)
  refine ⟨fun f => ⨆ x ∈ S, G (f x), ?_, hS⟩
  haveI : Countable S := hSc.to_subtype
  have : (fun f : T → ℝ => ⨆ x ∈ S, G (f x)) = fun f => ⨆ x : S, G (f x) := by
    funext f
    exact iSup_subtype' (p := fun x => x ∈ S) (f := fun x _ => G (f x))
  rw [this]
  exact Measurable.iSup fun x => hG.comp (measurable_pi_apply (x : T))

/-- One-sided invariance of `∫⁻ essSup` under equality of the laws of the fields in the function space. -/
theorem lintegral_essSup_le_of_map_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : Measure T} [SFinite ν] {Y Y' : Ω → T → ℝ}
    (hY : Measurable fun p : Ω × T => Y p.1 p.2) (hY' : Measurable fun p : Ω × T => Y' p.1 p.2)
    (hlaw : μ.map Y' = μ.map Y) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, essSup (fun x => G (Y' ω x)) ν ∂μ ≤ ∫⁻ ω, essSup (fun x => G (Y ω x)) ν ∂μ := by
  have hgood : ∀ᵐ x ∂ν, ∀ᵐ ω ∂μ, G (Y ω x) ≤ essSup (fun x => G (Y ω x)) ν :=
    ae_forall_ae_le_essSup (μ := μ) (ν := ν) (g := fun ω x => G (Y ω x)) (hG.comp hY)
  obtain ⟨S, hSc, hS𝒢, hS⟩ := exists_countable_essSup_eq (μ := μ) (ν := ν)
    (g := fun ω x => G (Y' ω x)) (hG.comp hY')
    {x | ∀ᵐ ω ∂μ, G (Y ω x) ≤ essSup (fun x => G (Y ω x)) ν} hgood
  set ρ : (T → ℝ) → ℝ≥0∞ := fun f => ⨆ x ∈ S, G (f x) with hρdef
  haveI : Countable S := hSc.to_subtype
  have hρ : Measurable ρ := by
    have : ρ = fun f => ⨆ x : S, G (f x) := by
      funext f
      exact iSup_subtype' (p := fun x => x ∈ S) (f := fun x _ => G (f x))
    rw [this]
    exact Measurable.iSup fun x => hG.comp (measurable_pi_apply (x : T))
  calc ∫⁻ ω, essSup (fun x => G (Y' ω x)) ν ∂μ = ∫⁻ ω, ρ (Y' ω) ∂μ := lintegral_congr_ae hS
    _ = ∫⁻ f, ρ f ∂(μ.map Y') := (lintegral_map hρ (measurable_field_of_uncurry hY')).symm
    _ = ∫⁻ f, ρ f ∂(μ.map Y) := by rw [hlaw]
    _ = ∫⁻ ω, ρ (Y ω) ∂μ := lintegral_map hρ (measurable_field_of_uncurry hY)
    _ ≤ ∫⁻ ω, essSup (fun x => G (Y ω x)) ν ∂μ := by
      refine lintegral_mono_ae ?_
      have hall : ∀ᵐ ω ∂μ, ∀ x ∈ S, G (Y ω x) ≤ essSup (fun x => G (Y ω x)) ν := by
        rw [ae_ball_iff hSc]
        intro x hx
        exact hS𝒢 hx
      filter_upwards [hall] with ω hω
      exact iSup₂_le hω

end EssSup

end

end SubdiffusiveProcess.ConcentrationScales
