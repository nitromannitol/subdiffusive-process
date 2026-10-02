import Mathlib.Probability.Independence.Basic

/-!
# Independence support for finite-cutoff restriction laws

This file contains two purely measure-theoretic transports used by the
finite-cutoff range proof: independence through a pushforward, and aggregation
of independently paired local sigma fields across mutually independent shell
coordinates.

PROVENANCE: adapted verbatim in mathematical content from
`Algsuperdiff/Probability/IndependenceMap.lean` and
`Algsuperdiff/Probability/RefinedIndependence.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Independence of two pullback sigma fields is equivalent to independence
under the pushforward measure. -/
theorem indep_comap_iff_indep_map
    {alpha beta : Type*} [mAlpha : MeasurableSpace alpha]
    {m₁ m₂ : MeasurableSpace beta} [mBeta : MeasurableSpace beta]
    {mu : Measure alpha} {f : alpha → beta} (hf : AEMeasurable f mu)
    (hm₁ : m₁ ≤ mBeta) (hm₂ : m₂ ≤ mBeta) :
    Indep (m₁.comap f) (m₂.comap f) mu ↔ Indep m₁ m₂ (mu.map f) := by
  constructor
  · intro h
    rw [Indep_iff] at h ⊢
    intro s t hs ht
    have hsBeta : MeasurableSet[mBeta] s := hm₁ s hs
    have htBeta : MeasurableSet[mBeta] t := hm₂ t ht
    have hsf : MeasurableSet[m₁.comap f] (f ⁻¹' s) :=
      MeasurableSpace.measurableSet_comap.2 ⟨s, hs, rfl⟩
    have htf : MeasurableSet[m₂.comap f] (f ⁻¹' t) :=
      MeasurableSpace.measurableSet_comap.2 ⟨t, ht, rfl⟩
    calc
      mu.map f (s ∩ t) = mu (f ⁻¹' (s ∩ t)) :=
        Measure.map_apply_of_aemeasurable hf (hsBeta.inter htBeta)
      _ = mu (f ⁻¹' s ∩ f ⁻¹' t) := by rw [Set.preimage_inter]
      _ = mu (f ⁻¹' s) * mu (f ⁻¹' t) := h _ _ hsf htf
      _ = mu.map f s * mu.map f t := by
        rw [Measure.map_apply_of_aemeasurable hf hsBeta,
          Measure.map_apply_of_aemeasurable hf htBeta]
  · intro h
    rw [Indep_iff] at h ⊢
    intro s t hs ht
    rcases MeasurableSpace.measurableSet_comap.1 hs with ⟨s', hs', rfl⟩
    rcases MeasurableSpace.measurableSet_comap.1 ht with ⟨t', ht', rfl⟩
    have hsBeta : MeasurableSet[mBeta] s' := hm₁ s' hs'
    have htBeta : MeasurableSet[mBeta] t' := hm₂ t' ht'
    calc
      mu (f ⁻¹' s' ∩ f ⁻¹' t') = mu (f ⁻¹' (s' ∩ t')) := by
        rw [Set.preimage_inter]
      _ = mu.map f (s' ∩ t') :=
        (Measure.map_apply_of_aemeasurable hf (hsBeta.inter htBeta)).symm
      _ = mu.map f s' * mu.map f t' := h s' t' hs' ht'
      _ = mu (f ⁻¹' s') * mu (f ⁻¹' t') := by
        rw [Measure.map_apply_of_aemeasurable hf hsBeta,
          Measure.map_apply_of_aemeasurable hf htBeta]

variable {Omega : Type*} [mOmega : MeasurableSpace Omega]
  {mu : Measure Omega}

private def refinedSigma {iota : Type*}
    (a b : iota → MeasurableSpace Omega) :
    iota × Bool → MeasurableSpace Omega :=
  fun p => cond p.2 (b p.1) (a p.1)

private theorem meas_biInter_fiber [IsProbabilityMeasure mu]
    {iota : Type*} {a b : iota → MeasurableSpace Omega}
    (i : iota) (hab : Indep (a i) (b i) mu)
    {F : Finset (iota × Bool)} (hF : ∀ p ∈ F, p.1 = i)
    {g : iota × Bool → Set Omega}
    (hg : ∀ p ∈ F, MeasurableSet[refinedSigma a b p] (g p)) :
    mu (⋂ p ∈ F, g p) = ∏ p ∈ F, mu (g p) := by
  classical
  have hFsub : F ⊆ ({(i, false), (i, true)} : Finset (iota × Bool)) := by
    intro p hp
    obtain ⟨p1, p2⟩ := p
    have hp1 : p1 = i := hF _ hp
    subst hp1
    cases p2 <;> simp
  by_cases hu : (i, false) ∈ F <;> by_cases hv : (i, true) ∈ F
  · have hFeq : F = ({(i, false), (i, true)} : Finset (iota × Bool)) := by
      apply Finset.Subset.antisymm hFsub
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with h | h <;> subst h <;> assumption
    subst hFeq
    have hne : (i, false) ≠ (i, true) := by simp
    rw [Finset.prod_insert (Finset.notMem_singleton.mpr hne),
      Finset.prod_singleton, Finset.set_biInter_insert,
      Finset.set_biInter_singleton]
    have h1 : MeasurableSet[a i] (g (i, false)) := hg (i, false) hu
    have h2 : MeasurableSet[b i] (g (i, true)) := hg (i, true) hv
    exact (Indep_iff (a i) (b i) mu).1 hab _ _ h1 h2
  · have hFeq : F = ({(i, false)} : Finset (iota × Bool)) := by
      apply Finset.Subset.antisymm _ (by simpa using hu)
      intro p hp
      have hsub := hFsub hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsub ⊢
      rcases hsub with h | h
      · exact h
      · exact absurd (h ▸ hp) hv
    subst hFeq
    simp
  · have hFeq : F = ({(i, true)} : Finset (iota × Bool)) := by
      apply Finset.Subset.antisymm _ (by simpa using hv)
      intro p hp
      have hsub := hFsub hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsub ⊢
      rcases hsub with h | h
      · exact absurd (h ▸ hp) hu
      · exact h
    subst hFeq
    simp
  · have hFeq : F = (∅ : Finset (iota × Bool)) := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      have hsub := hFsub hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsub
      rcases hsub with h | h
      · exact hu (h ▸ hp)
      · exact hv (h ▸ hp)
    subst hFeq
    simp

private theorem iIndep_refinedSigma [IsProbabilityMeasure mu]
    {iota : Type*} {kappa a b : iota → MeasurableSpace Omega}
    (hkappa : iIndep kappa mu) (ha : ∀ i, a i ≤ kappa i)
    (hb : ∀ i, b i ≤ kappa i) (hab : ∀ i, Indep (a i) (b i) mu) :
    iIndep (refinedSigma a b) mu := by
  classical
  rw [iIndep_iff]
  intro S' g hg
  have hnkappa : ∀ p : iota × Bool,
      refinedSigma a b p ≤ kappa p.1 := by
    rintro ⟨i, c⟩
    cases c
    · simpa using ha i
    · simpa using hb i
  set L := S'.image Prod.fst with hL
  set fib : iota → Finset (iota × Bool) :=
    fun i => S'.filter (fun q => q.1 = i) with hfib
  have hInter : (⋂ p ∈ S', g p) = ⋂ i ∈ L, ⋂ p ∈ fib i, g p := by
    ext x
    simp only [Set.mem_iInter, hfib, Finset.mem_filter, hL,
      Finset.mem_image]
    constructor
    · intro h i _ p hp
      exact h p hp.1
    · intro h p hp
      exact h p.1 ⟨p, hp, rfl⟩ p ⟨hp, rfl⟩
  have hGmeas : ∀ i ∈ L,
      MeasurableSet[kappa i] (⋂ p ∈ fib i, g p) := by
    intro i _
    refine @Finset.measurableSet_biInter _ _ (kappa i) _ _
      (fun p hp => ?_)
    have hpi : p.1 = i := (Finset.mem_filter.1 hp).2
    have hmeas := (hnkappa p) _ (hg p (Finset.mem_filter.1 hp).1)
    rwa [hpi] at hmeas
  have hfiber : ∀ i ∈ L,
      mu (⋂ p ∈ fib i, g p) = ∏ p ∈ fib i, mu (g p) := by
    intro i _
    refine meas_biInter_fiber i (hab i)
      (fun p hp => (Finset.mem_filter.1 hp).2) ?_
    intro p hp
    exact hg p (Finset.mem_filter.1 hp).1
  rw [hInter, hkappa.meas_biInter hGmeas]
  rw [Finset.prod_congr rfl hfiber]
  have hmaps : ∀ p ∈ S', Prod.fst p ∈ L := fun p hp =>
    hL ▸ Finset.mem_image_of_mem Prod.fst hp
  exact Finset.prod_fiberwise_of_maps_to hmaps (fun p => mu (g p))

/-- Aggregate two local sigma-field families from independent shell
coordinates, given independence of the two views within every coordinate. -/
theorem indep_iSup_of_indep_of_iIndep [IsProbabilityMeasure mu]
    {iota : Type*} {kappa a b : iota → MeasurableSpace Omega}
    (hkappa : iIndep kappa mu) (hle : ∀ i, kappa i ≤ mOmega)
    (ha : ∀ i, a i ≤ kappa i) (hb : ∀ i, b i ≤ kappa i)
    (hab : ∀ i, Indep (a i) (b i) mu) :
    Indep (⨆ i, a i) (⨆ i, b i) mu := by
  classical
  have hind : iIndep (refinedSigma a b) mu :=
    iIndep_refinedSigma hkappa ha hb hab
  have hnle : ∀ p : iota × Bool,
      refinedSigma a b p ≤ mOmega := by
    rintro ⟨i, c⟩
    cases c
    · exact le_trans (by simpa using ha i) (hle i)
    · exact le_trans (by simpa using hb i) (hle i)
  have hdisj : Disjoint ({p : iota × Bool | p.2 = false})
      ({p : iota × Bool | p.2 = true}) := by
    rw [Set.disjoint_left]
    rintro ⟨i, c⟩ hs ht
    simp only [Set.mem_setOf_eq] at hs ht
    rw [hs] at ht
    exact absurd ht (by decide)
  have hmain := indep_iSup_of_disjoint hnle hind hdisj
  have hSa : (⨆ p ∈ ({p : iota × Bool | p.2 = false}),
      refinedSigma a b p) = ⨆ i, a i := by
    apply le_antisymm
    · refine iSup₂_le ?_
      rintro ⟨i, c⟩ (hc : c = false)
      subst hc
      exact le_iSup a i
    · refine iSup_le fun i => ?_
      exact le_iSup₂_of_le (i, false) rfl le_rfl
  have hSb : (⨆ p ∈ ({p : iota × Bool | p.2 = true}),
      refinedSigma a b p) = ⨆ i, b i := by
    apply le_antisymm
    · refine iSup₂_le ?_
      rintro ⟨i, c⟩ (hc : c = true)
      subst hc
      exact le_iSup b i
    · refine iSup_le fun i => ?_
      exact le_iSup₂_of_le (i, true) rfl le_rfl
  rwa [hSa, hSb] at hmain

end SubdiffusiveProcess.CoarseGrainingVocab
