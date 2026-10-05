module

public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace SubdiffusiveProcess.Paper



theorem in_source_independence
    (Y : Int → Type) [∀ j, MeasurableSpace (Y j)]
    (laws : (j : Int) → Measure (Y j)) [∀ j, IsProbabilityMeasure (laws j)]
    (I : Type) [Fintype I]
    (blocks : I → Set Int)
    (hdisj : Pairwise (fun i j => Disjoint (blocks i) (blocks j)))
    (events : I → Set ((j : Int) → Y j))
    (hmeas : ∀ i, MeasurableSet[
      (inferInstance : MeasurableSpace ((j : {j : Int // j ∈ blocks i}) → Y j.val)).comap
        (fun (omega : (j : Int) → Y j) =>
          fun j : {j : Int // j ∈ blocks i} => omega j.val)] (events i)) :
    iIndepSet events (Measure.infinitePi laws) := by
  classical
  let mcoord : Int → MeasurableSpace ((j : Int) → Y j) := fun j =>
    (inferInstance : MeasurableSpace (Y j)).comap (fun omega : (j : Int) → Y j => omega j)
  let mblock : I → MeasurableSpace ((j : Int) → Y j) := fun i =>
    ⨆ j ∈ blocks i, mcoord j
  let piCoord : Int → Set (Set ((j : Int) → Y j)) := fun j =>
    {s | MeasurableSet[mcoord j] s}
  let piBlock : I → Set (Set ((j : Int) → Y j)) := fun i =>
    piiUnionInter piCoord (blocks i)
  have hcoord : iIndep mcoord (Measure.infinitePi laws) := by
    simpa [mcoord] using
      (iIndepFun_infinitePi (P := laws) (X := fun _ x => x)
        (fun _ => measurable_id)).iIndep
  have hpiBlock : iIndepSets piBlock (Measure.infinitePi laws) := by
    rw [iIndepSets_iff]
    intro s f hf
    have hf' : ∀ i : s, f i ∈ piBlock i.1 := fun i => hf i.1 i.2
    choose t ht g hg hfg using hf'
    let u : Finset Int := s.attach.biUnion (fun i => t i)
    have huniq {i i' : s} {j : Int} (hij : j ∈ t i) (hij' : j ∈ t i') : i = i' := by
      apply Subtype.ext
      by_contra hne
      exact Set.disjoint_left.mp (hdisj (by
        intro hEq
        exact hne hEq)) (ht i hij) (ht i' hij')
    let q : Int → Set ((j : Int) → Y j) := fun j =>
      if hj : ∃ i : s, j ∈ t i then g (Classical.choose hj) j else Set.univ
    have hq : ∀ j, j ∈ u → MeasurableSet[mcoord j] (q j) := by
      intro j hj
      have hj' : ∃ i : s, j ∈ t i := by
        rcases Finset.mem_biUnion.mp hj with ⟨i, _, hij⟩
        exact ⟨i, hij⟩
      have hqeq : q j = g (Classical.choose hj') j := by
        dsimp [q]
        rw [dite_eq_left hj']
      rw [hqeq]
      exact hg (Classical.choose hj') j (Classical.choose_spec hj')
    have ht_disj : (↑s.attach : Set s).PairwiseDisjoint t := by
      intro i hi i' hi' hne
      apply Finset.disjoint_left.2
      intro j hij hij'
      exact hne (huniq hij hij')
    have hleft : (⋂ i ∈ s, f i) = ⋂ i : s, f i := by
      ext omega
      simp
    have hinter : (⋂ i ∈ s, f i) = ⋂ j ∈ u, q j := by
      rw [hleft]
      simp_rw [hfg]
      ext omega
      simp only [Set.mem_iInter]
      constructor
      · intro h j hj
        rcases Finset.mem_biUnion.mp hj with ⟨i, _, hij⟩
        have hj' : ∃ i : s, j ∈ t i := ⟨i, hij⟩
        have hqeq : q j = g (Classical.choose hj') j := by
          dsimp [q]
          rw [dite_eq_left hj']
        rw [hqeq]
        exact h (Classical.choose hj') j (Classical.choose_spec hj')
      · intro h i j hij
        have hj : j ∈ u := by
          apply Finset.mem_biUnion.mpr
          exact ⟨i, by simp, hij⟩
        have hj' : ∃ i' : s, j ∈ t i' := ⟨i, hij⟩
        have hqmem := h j hj
        have hqeq : q j = g i j := by
          have hchoose : Classical.choose hj' = i := huniq (Classical.choose_spec hj') hij
          dsimp [q]
          rw [dite_eq_left hj', hchoose]
        rw [hqeq] at hqmem
        exact hqmem
    have hmeasure :
        (Measure.infinitePi laws) (⋂ j ∈ u, q j) =
          ∏ j ∈ u, (Measure.infinitePi laws) (q j) :=
      ProbabilityTheory.iIndep.meas_biInter hcoord (S := u) (s := q) hq
    have hprod_q :
        ∏ j ∈ u, (Measure.infinitePi laws) (q j) =
          ∏ i : s, ∏ j ∈ t i, (Measure.infinitePi laws) (g i j) := by
      rw [Finset.prod_biUnion ht_disj]
      refine Finset.prod_congr rfl fun i _ => ?_
      refine Finset.prod_congr rfl fun j hij => ?_
      have hj' : ∃ i' : s, j ∈ t i' := ⟨i, hij⟩
      have hqeq : q j = g i j := by
        have hchoose : Classical.choose hj' = i := huniq (Classical.choose_spec hj') hij
        dsimp [q]
        rw [dite_eq_left hj', hchoose]
      rw [hqeq]
    have hprod_f :
        ∏ i ∈ s, (Measure.infinitePi laws) (f i) =
          ∏ i : s, ∏ j ∈ t i, (Measure.infinitePi laws) (g i j) := by
      rw [← s.prod_coe_sort]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hfg i]
      exact ProbabilityTheory.iIndep.meas_biInter hcoord (S := t i) (s := g i)
        (fun j hj => hg i j hj)
    rw [hinter, hmeasure, hprod_q, ← hprod_f]
  have hblock : iIndep mblock (Measure.infinitePi laws) := by
    refine ProbabilityTheory.iIndepSets.iIndep (m := mblock) ?_ piBlock ?_ ?_ hpiBlock
    · intro i
      dsimp [mblock]
      exact iSup₂_le fun j _ => by
        simpa [mcoord] using (measurable_pi_apply j).comap_le
    · intro i
      exact isPiSystem_piiUnionInter piCoord
        (fun j => @MeasurableSpace.isPiSystem_measurableSet _ (mcoord j)) (blocks i)
    · intro i
      simpa [mblock, piBlock, piCoord] using
        (generateFrom_piiUnionInter_measurableSet mcoord (blocks i)).symm
  have hevent_meas : ∀ i, MeasurableSet[mblock i] (events i) := by
    intro i
    have hi : MeasurableSet[
        ⨆ j ∈ blocks i,
          (inferInstance : MeasurableSpace (Y j)).comap
            (fun omega : (j : Int) → Y j => omega j)] (events i) := by
      rw [← SubdiffusiveProcess.comap_restrict_eq_iSup (X := Y) (S := blocks i)]
      exact hmeas i
    simpa [mblock, mcoord] using hi
  have hevent_le : ∀ i,
      (⊤ : MeasurableSpace Prop).comap (fun omega : (j : Int) → Y j => omega ∈ events i) ≤
        mblock i := by
    intro i
    have hm : @Measurable ((j : Int) → Y j) Prop (mblock i) ⊤
        (fun omega : (j : Int) → Y j => omega ∈ events i) :=
      (@measurable_mem ((j : Int) → Y j) (events i) (mblock i)).2 (hevent_meas i)
    exact hm.comap_le
  have hsmall : iIndep (fun i =>
      (⊤ : MeasurableSpace Prop).comap (fun omega : (j : Int) → Y j => omega ∈ events i))
      (Measure.infinitePi laws) := by
    rw [iIndep_iff]
    intro s f hf
    exact ProbabilityTheory.iIndep.meas_biInter hblock
      (fun i hi => hevent_le i (f i) (hf i hi))
  exact (iIndep_comap_mem_iff (f := events) (μ := Measure.infinitePi laws)).mp hsmall

end SubdiffusiveProcess.Paper
