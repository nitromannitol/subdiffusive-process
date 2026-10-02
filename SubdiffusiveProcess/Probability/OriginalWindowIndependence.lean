import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

namespace SubdiffusiveProcess

/-- Independent original-layer blocks give the exact probability product for a fixed disjoint family of witness windows. -/
theorem measure_biInter_eq_prod_of_disjoint_measurable_original_windows
    {ι Ω X : Type*} [DecidableEq ι]
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (g : ℤ → Ω → X)
    (hg_meas : ∀ j : ℤ, Measurable (g j))
    (hg_indep : iIndepFun g P)
    (s : Finset ι) (window : ι → Finset ℤ)
    (hwindow : ∀ ⦃i⦄, i ∈ s → ∀ ⦃k⦄, k ∈ s → i ≠ k →
      Disjoint (window i) (window k))
    (E : ι → Set Ω)
    (hE : ∀ i, i ∈ s →
      @MeasurableSet Ω
        (⨆ j : ℤ, ⨆ (_ : j ∈ window i),
          MeasurableSpace.comap (g (-j)) (inferInstance : MeasurableSpace X))
        (E i)) :
    P (⋂ i ∈ s, E i) = ∏ i ∈ s, P (E i) := by
  classical
  letI := hg_indep.isProbabilityMeasure
  let m : ℤ → MeasurableSpace Ω := fun j =>
    MeasurableSpace.comap (g (-j)) (inferInstance : MeasurableSpace X)
  have hbase : iIndep m P := by
    dsimp [m]
    exact hg_indep.iIndep.precomp neg_injective
  have hm_le : ∀ j : ℤ, m j ≤ (inferInstance : MeasurableSpace Ω) := by
    intro j
    exact (hg_meas (-j)).comap_le
  have hprod : ∀ (t : Finset ι), t ⊆ s →
      P (⋂ i ∈ t, E i) = ∏ i ∈ t, P (E i) := by
    intro t ht
    induction t using Finset.induction_on with
    | empty => simp [measure_univ]
    | @insert i t hi ih =>
        have hi_s : i ∈ s := ht (Finset.mem_insert_self i t)
        have ht_s : t ⊆ s := fun k hk => ht (Finset.mem_insert_of_mem hk)
        have hdisj :
            Disjoint (window i : Set ℤ)
              (⋃ k ∈ (t : Set ι), (window k : Set ℤ)) := by
          refine Set.disjoint_left.2 ?_
          intro j hji hjt
          simp only [Set.mem_iUnion] at hjt
          obtain ⟨k, hk, hjk⟩ := hjt
          exact Finset.disjoint_left.1
            (hwindow hi_s (ht_s hk) (fun hik => hi (hik ▸ hk))) hji hjk
        have hblock_le : ∀ k ∈ t,
            (⨆ j : ℤ, ⨆ (_ : j ∈ window k), m j) ≤
              (⨆ j : ℤ, ⨆ (_ : j ∈ ⋃ k ∈ (t : Set ι), (window k : Set ℤ)), m j) := by
          intro k hk
          refine iSup_le fun j => iSup_le fun hj => ?_
          have hjt : j ∈ ⋃ k ∈ (t : Set ι), (window k : Set ℤ) := by
            simp only [Set.mem_iUnion]
            exact ⟨k, hk, hj⟩
          exact le_iSup_of_le j (le_iSup_of_le hjt le_rfl)
        have hEi : MeasurableSet[(⨆ j : ℤ, ⨆ (_ : j ∈ window i), m j)] (E i) := by
          simpa [m] using hE i hi_s
        have hEt :
            MeasurableSet[
              (⨆ j : ℤ, ⨆ (_ : j ∈ ⋃ k ∈ (t : Set ι), (window k : Set ℤ)), m j)]
              (⋂ k ∈ t, E k) := by
          exact t.measurableSet_biInter (fun k hk =>
            hblock_le k hk (E k) (hE k (ht_s hk)))
        have hind :
            Indep (⨆ j : ℤ, ⨆ (_ : j ∈ window i), m j)
              (⨆ j : ℤ, ⨆ (_ : j ∈ ⋃ k ∈ (t : Set ι), (window k : Set ℤ)), m j) P :=
          indep_iSup_of_disjoint hm_le hbase hdisj
        calc
          P (⋂ k ∈ insert i t, E k) = P (E i ∩ ⋂ k ∈ t, E k) := by
            rw [Finset.set_biInter_insert]
          _ = P (E i) * P (⋂ k ∈ t, E k) :=
            (Indep_iff _ _ P).1 hind _ _ hEi hEt
          _ = ∏ k ∈ insert i t, P (E k) := by
            rw [ih ht_s, Finset.prod_insert hi]
  exact hprod s (by intro i hi; exact hi)

end SubdiffusiveProcess
