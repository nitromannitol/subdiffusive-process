import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.IntervalPacking
import Mathlib.Probability.Independence.Basic

/-!
# Independence transport for fixed packed interval configurations

The greedy packing is chosen pointwise, but probability factorization is used
only after a configuration is fixed.  This module supplies that second step:
events measurable with respect to disjoint finite joins of mutually independent
primitive sigma-fields factorize.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Density

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Finite events supported on pairwise-disjoint blocks of a mutually
independent family factorize. -/
theorem measure_biInter_eq_prod_of_iIndep_finsetBlocks
    {Omega iota kappa : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {m : iota → MeasurableSpace Omega}
    (hind : iIndep m mu)
    (hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace Omega))
    (K : Finset kappa) (block : kappa → Finset iota)
    (hblock : (K : Set kappa).PairwiseDisjoint block)
    (E : kappa → Set Omega)
    (hE : ∀ k ∈ K, MeasurableSet[⨆ i ∈ block k, m i] (E k)) :
    mu (⋂ k ∈ K, E k) = ∏ k ∈ K, mu (E k) := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | @insert a K ha ih =>
      have hpairK : (K : Set kappa).PairwiseDisjoint block :=
        fun x hx y hy hxy ↦ hblock (by simp [hx]) (by simp [hy]) hxy
      have hdisj : Disjoint (block a) (K.biUnion block) := by
        rw [Finset.disjoint_left]
        intro i hia hiK
        obtain ⟨b, hbK, hib⟩ := Finset.mem_biUnion.mp hiK
        exact Finset.disjoint_left.mp
          (hblock (by simp) (by simp [hbK]) (by intro hab; subst b; exact ha hbK)) hia hib
      have hindBlocks : Indep (⨆ i ∈ block a, m i)
          (⨆ i ∈ K.biUnion block, m i) mu := by
        apply indep_iSup_of_disjoint hm hind
        change Disjoint (↑(block a) : Set iota) (↑(K.biUnion block) : Set iota)
        exact Finset.disjoint_coe.mpr hdisj
      have hrestMeas : MeasurableSet[⨆ i ∈ K.biUnion block, m i]
          (⋂ k ∈ K, E k) := by
        apply Finset.measurableSet_biInter
        intro k hk
        have hle : (⨆ i ∈ block k, m i) ≤
            (⨆ i ∈ K.biUnion block, m i) := by
          refine iSup₂_le ?_
          intro i hi
          exact le_iSup₂_of_le i (Finset.mem_biUnion.mpr ⟨k, hk, hi⟩) le_rfl
        exact hle _ (hE k (Finset.mem_insert_of_mem hk))
      have hfactor : mu (E a ∩ ⋂ k ∈ K, E k) =
          mu (E a) * mu (⋂ k ∈ K, E k) :=
        (Indep_iff _ _ _).mp hindBlocks _ _ (hE a (by simp)) hrestMeas
      calc
        mu (⋂ k ∈ insert a K, E k) = mu (E a ∩ ⋂ k ∈ K, E k) := by simp
        _ = mu (E a) * mu (⋂ k ∈ K, E k) := hfactor
        _ = mu (E a) * ∏ k ∈ K, mu (E k) := by
          rw [ih hpairK (fun k hk ↦ hE k (Finset.mem_insert_of_mem hk))]
        _ = ∏ k ∈ insert a K, mu (E k) := by rw [Finset.prod_insert ha]

/-- Fixed packed centered intervals satisfy the block hypothesis above. -/
theorem measure_biInter_eq_prod_of_iIndep_centeredIntervals
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {m : ℤ → MeasurableSpace Omega}
    (hind : iIndep m mu)
    (hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace Omega))
    (K : Finset ℤ) (radius : ℤ → ℕ)
    (hsep : ∀ a ∈ K, ∀ b ∈ K, a ≠ b →
      centeredIntIntervalsSeparated a (radius a) b (radius b))
    (E : ℤ → Set Omega)
    (hE : ∀ k ∈ K,
      MeasurableSet[⨆ i ∈ centeredIntInterval k (radius k), m i] (E k)) :
    mu (⋂ k ∈ K, E k) = ∏ k ∈ K, mu (E k) := by
  apply measure_biInter_eq_prod_of_iIndep_finsetBlocks hind hm K
    (fun k ↦ centeredIntInterval k (radius k))
  · intro a ha b hb hab
    change Disjoint (centeredIntInterval a (radius a))
      (centeredIntInterval b (radius b))
    rw [Finset.disjoint_left]
    intro i hia hib
    exact Finset.disjoint_left.mp (hsep a ha b hb hab).1 hia
      (centeredIntInterval_subset_separatedIntInterval b (radius b) hib)
  · exact hE

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
