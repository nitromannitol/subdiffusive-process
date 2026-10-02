import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GoodStoppingTail
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.HolderScale

/-!
# Tail event for the good-scale stopping depth

This file connects the frozen `Finset.min'`/`sInf` first-failure carrier to
the spatial bad-count event controlled by the good-scale density estimate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

def goodScaleSpatialFailure {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (lambda epsilon s : ℝ)
    (n m : ℕ) : Set (Sample d) :=
  {omega | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
    lambda * (m - n) < ∑ j ∈ Finset.Icc n m,
      (1 - if omega ∈ goodEvent M none j z epsilon s then (1 : ℝ) else 0)}

/-- A large frozen good-scale depth forces a bad spatial count at one of the
starting scales allowed by that depth. -/
theorem goodStoppingDepth_tail_subset_iUnion {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (lambda epsilon s : ℝ)
    (q m : ℕ) :
    {omega | q < goodStoppingDepth M lambda epsilon s m omega} ⊆
      ⋃ n ∈ Finset.range (m - q + 1),
        goodScaleSpatialFailure M lambda epsilon s n m := by
  intro omega homega
  change q < goodStoppingDepth M lambda epsilon s m omega at homega
  let candidates := insert (m + 1) ((Finset.range (m + 1)).filter fun n ↦
      sInf {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m,
          if omega ∈ goodEvent M none j z epsilon s then 1 else 0} <=
        (1 - lambda) * ((m : ℝ) - (n : ℝ)))
  have hm : m + 1 ∈ candidates := by simp [candidates]
  let first := candidates.min' ⟨m + 1, hm⟩
  have hfirst_mem : first ∈ candidates := Finset.min'_mem candidates ⟨m + 1, hm⟩
  have hfirst_le : first <= m + 1 := Finset.min'_le candidates (m + 1) hm
  have hindex : (goodStoppingIndex M none lambda epsilon s m omega : Int) =
      (first : Int) - 1 := by
    rfl
  have hdepth : goodStoppingDepth M lambda epsilon s m omega =
      m + 1 - first := by
    unfold goodStoppingDepth
    rw [hindex]
    have hnonneg : 0 <= (m : Int) - ((first : Int) - 1) := by omega
    apply Nat.cast_injective (R := Int)
    rw [Int.toNat_of_nonneg hnonneg, Nat.cast_sub hfirst_le]
    push_cast
    ring
  rw [hdepth] at homega
  have hfirst_m : first <= m := by omega
  have hfirst_range : first ∈ Finset.range (m - q + 1) := by
    rw [Finset.mem_range]
    omega
  have hfilter : first ∈ (Finset.range (m + 1)).filter fun n ↦
      sInf {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m,
          if omega ∈ goodEvent M none j z epsilon s then 1 else 0} <=
        (1 - lambda) * ((m : ℝ) - (n : ℝ)) := by
    simp only [candidates, Finset.mem_insert] at hfirst_mem
    rcases hfirst_mem with htop | hfilter
    · omega
    · exact hfilter
  have hfail := (Finset.mem_filter.1 hfilter).2
  have hwitness := exists_gridCenter_badScaleCount_of_sInf_le
    M lambda epsilon s first m hfirst_m omega hfail
  exact Set.mem_iUnion₂.2 ⟨first, hfirst_range, hwitness⟩

/-- Outer-measure union bound for the good-scale stopping depth. -/
theorem measure_goodStoppingDepth_tail_le_sum {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (lambda epsilon s : ℝ)
    (q m : ℕ) :
    M.P.toMeasure {omega | q < goodStoppingDepth M lambda epsilon s m omega} <=
      ∑ n ∈ Finset.range (m - q + 1),
        M.P.toMeasure (goodScaleSpatialFailure M lambda epsilon s n m) := by
  calc
    M.P.toMeasure {omega | q < goodStoppingDepth M lambda epsilon s m omega} <=
        M.P.toMeasure (⋃ n ∈ Finset.range (m - q + 1),
          goodScaleSpatialFailure M lambda epsilon s n m) :=
      measure_mono (goodStoppingDepth_tail_subset_iUnion M lambda epsilon s q m)
    _ <= ∑ n ∈ Finset.range (m - q + 1),
        M.P.toMeasure (goodScaleSpatialFailure M lambda epsilon s n m) :=
      measure_biUnion_finset_le _ _

/-- The density input gives the manuscript's pre-geometric-series bound for
the full good-scale stopping depth. -/
theorem measure_goodStoppingDepth_tail_le_sum_exp {d : ℕ}
    (hDensity : DensityOfGoodScalesInput d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s lambda epsilon : ℝ),
        s ∈ Set.Ioc (0 : ℝ) 1 -> lambda ∈ Set.Ioc (0 : ℝ) 1 ->
        epsilon ∈ Set.Ioc (0 : ℝ) 1 ->
        C * s ^ (-6 : Int) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta| <= lambda / 2 ->
        ∀ q m : ℕ,
          M.P.toMeasure {omega |
              q < goodStoppingDepth M lambda epsilon s m omega} <=
            ∑ n ∈ Finset.range (m - q + 1),
              (3 ^ (d * (m - n)) : ℕ) *
                ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)) *
                    (m - n + 1))) := by
  obtain ⟨C, hC, hspatial⟩ :=
    measure_exists_gridCenter_badScaleCount_large_le hDensity
  refine ⟨C, hC, ?_⟩
  intro M s lambda epsilon hs hlambda hepsilon hsmall q m
  calc
    M.P.toMeasure {omega |
        q < goodStoppingDepth M lambda epsilon s m omega} <=
      ∑ n ∈ Finset.range (m - q + 1),
        M.P.toMeasure (goodScaleSpatialFailure M lambda epsilon s n m) :=
      measure_goodStoppingDepth_tail_le_sum M lambda epsilon s q m
    _ <= ∑ n ∈ Finset.range (m - q + 1),
        (3 ^ (d * (m - n)) : ℕ) *
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
            (C * M.delta ^ 2 * |Real.log M.delta|)) *
              (m - n + 1))) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnm : n <= m := by
        rw [Finset.mem_range] at hn
        omega
      simpa only [goodScaleSpatialFailure] using
        hspatial M s lambda epsilon hs hlambda hepsilon hsmall n m hnm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
