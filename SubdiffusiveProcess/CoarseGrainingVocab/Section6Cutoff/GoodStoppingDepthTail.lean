import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodEventDensity
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.CutoffHolderScale
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GridCenters

/-!
# Finite-cutoff good-scale stopping tail
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

theorem exists_gridCenter_cutoffBadScaleCount_of_sInf_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (lambda epsilon s : ℝ) (n m : ℕ) (hnm : n ≤ m)
    (omega : Sample d)
    (hfail : sInf {r : ℝ | ∃ z : Vec d,
        OnTriadicGrid n z ∧ z ∈ cube d m ∧
          r = ∑ j ∈ Finset.Icc n m,
            if omega ∈ goodEvent M (some L) j z epsilon s then 1 else 0} ≤
      (1 - lambda) * ((m : ℝ) - (n : ℝ))) :
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
      lambda * (m - n) < ∑ j ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) j z epsilon s then
          (1 : ℝ) else 0) := by
  let centers := gridCentersInCube d n m
  let goodCount : {z : Vec d // z ∈ centers} → ℝ := fun z =>
    ∑ j ∈ Finset.Icc n m,
      if omega ∈ goodEvent M (some L) j z.1 epsilon s then 1 else 0
  let values : Set ℝ := {r : ℝ | ∃ z : Vec d,
    OnTriadicGrid n z ∧ z ∈ cube d m ∧
      r = ∑ j ∈ Finset.Icc n m,
        if omega ∈ goodEvent M (some L) j z epsilon s then 1 else 0}
  have hvalues : values = Set.range goodCount := by
    ext r
    constructor
    · rintro ⟨z, hzgrid, hzmem, rfl⟩
      exact ⟨⟨z, (mem_gridCentersInCube_iff hnm).2 ⟨hzgrid, hzmem⟩⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨hzgrid, hzmem⟩ := (mem_gridCentersInCube_iff hnm).1 z.2
      exact ⟨z.1, hzgrid, hzmem, rfl⟩
  have hcenters : centers.Nonempty := by
    rw [← Finset.card_pos, card_gridCentersInCube hnm]
    positivity
  letI : Nonempty {z : Vec d // z ∈ centers} :=
    Finset.nonempty_coe_sort.mpr hcenters
  have hfinite : values.Finite := by
    rw [hvalues]
    exact Set.finite_range goodCount
  have hnonempty : values.Nonempty := by
    rw [hvalues]
    exact Set.range_nonempty goodCount
  by_contra hcontra
  push_neg at hcontra
  have hall : ∀ r ∈ values,
      (1 - lambda) * ((m : ℝ) - (n : ℝ)) < r := by
    rintro r ⟨z, hzgrid, hzmem, rfl⟩
    have hbad := hcontra z hzgrid hzmem
    have hcard : ((Finset.Icc n m).card : ℝ) =
        (m : ℝ) - (n : ℝ) + 1 := by
      rw [Nat.card_Icc, Nat.cast_sub (by omega : n ≤ m + 1), Nat.cast_add]
      norm_num
      ring
    have hpartition :
        (∑ j ∈ Finset.Icc n m,
            if omega ∈ goodEvent M (some L) j z epsilon s then
              (1 : ℝ) else 0) +
          (∑ j ∈ Finset.Icc n m,
            (1 - if omega ∈ goodEvent M (some L) j z epsilon s then
              (1 : ℝ) else 0)) =
          (m : ℝ) - (n : ℝ) + 1 := by
      rw [← hcard, ← Finset.sum_add_distrib]
      calc
        (∑ j ∈ Finset.Icc n m,
            ((if omega ∈ goodEvent M (some L) j z epsilon s then
                (1 : ℝ) else 0) +
              (1 - if omega ∈ goodEvent M (some L) j z epsilon s then
                (1 : ℝ) else 0))) =
            ∑ _j ∈ Finset.Icc n m, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _hj
          split_ifs <;> norm_num
        _ = ((Finset.Icc n m).card : ℝ) := by simp
    push_cast at hbad
    nlinarith
  have hlower : (1 - lambda) * ((m : ℝ) - (n : ℝ)) < sInf values :=
    (hfinite.lt_csInf_iff hnonempty).2 hall
  exact (not_lt_of_ge (by simpa only [values] using hfail)) hlower

def cutoffGoodScaleSpatialFailure {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (lambda epsilon s : ℝ) (n m : ℕ) : Set (Sample d) :=
  {omega | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
    lambda * (m - n) < ∑ j ∈ Finset.Icc n m,
      (1 - if omega ∈ goodEvent M (some L) j z epsilon s then
        (1 : ℝ) else 0)}

theorem cutoffGoodStoppingDepth_tail_subset_iUnion {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (lambda epsilon s : ℝ) (q m : ℕ) :
    {omega | q < cutoffGoodStoppingDepth M L lambda epsilon s m omega} ⊆
      ⋃ n ∈ Finset.range (m - q + 1),
        cutoffGoodScaleSpatialFailure M L lambda epsilon s n m := by
  intro omega homega
  change q < cutoffGoodStoppingDepth M L lambda epsilon s m omega at homega
  let candidates := insert (m + 1) ((Finset.range (m + 1)).filter fun n ↦
      sInf {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m,
          if omega ∈ goodEvent M (some L) j z epsilon s then 1 else 0} ≤
        (1 - lambda) * ((m : ℝ) - (n : ℝ)))
  have hm : m + 1 ∈ candidates := by simp [candidates]
  let first := candidates.min' ⟨m + 1, hm⟩
  have hfirst_mem : first ∈ candidates :=
    Finset.min'_mem candidates ⟨m + 1, hm⟩
  have hfirst_le : first ≤ m + 1 := Finset.min'_le candidates (m + 1) hm
  have hindex :
      (goodStoppingIndex M (some L) lambda epsilon s m omega : Int) =
        (first : Int) - 1 := by rfl
  have hdepth : cutoffGoodStoppingDepth M L lambda epsilon s m omega =
      m + 1 - first := by
    unfold cutoffGoodStoppingDepth
    rw [hindex]
    have hnonneg : 0 ≤ (m : Int) - ((first : Int) - 1) := by omega
    apply Nat.cast_injective (R := Int)
    rw [Int.toNat_of_nonneg hnonneg, Nat.cast_sub hfirst_le]
    push_cast
    ring
  rw [hdepth] at homega
  have hfirst_m : first ≤ m := by omega
  have hfirst_range : first ∈ Finset.range (m - q + 1) := by
    rw [Finset.mem_range]
    omega
  have hfilter : first ∈ (Finset.range (m + 1)).filter fun n ↦
      sInf {r : ℝ | ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
        r = ∑ j ∈ Finset.Icc n m,
          if omega ∈ goodEvent M (some L) j z epsilon s then 1 else 0} ≤
        (1 - lambda) * ((m : ℝ) - (n : ℝ)) := by
    simp only [candidates, Finset.mem_insert] at hfirst_mem
    rcases hfirst_mem with htop | hfilter
    · omega
    · exact hfilter
  have hfail := (Finset.mem_filter.1 hfilter).2
  have hwitness := exists_gridCenter_cutoffBadScaleCount_of_sInf_le
    M L lambda epsilon s first m hfirst_m omega hfail
  exact Set.mem_iUnion₂.2 ⟨first, hfirst_range, hwitness⟩

theorem measure_cutoffGoodStoppingDepth_tail_le_sum_exp {d : ℕ}
    (hDensity : CutoffDensityOfGoodScalesInput d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (s lambda epsilon : ℝ),
        s ∈ Set.Ioc (0 : ℝ) 1 → lambda ∈ Set.Ioc (0 : ℝ) 1 →
        epsilon ∈ Set.Ioc (0 : ℝ) 1 →
        C * s ^ (-6 : Int) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta| ≤ lambda / 2 →
        ∀ q m : ℕ,
          M.P.toMeasure {omega |
              q < cutoffGoodStoppingDepth M L lambda epsilon s m omega} ≤
            ∑ n ∈ Finset.range (m - q + 1),
              (3 ^ (d * (m - n)) : ℕ) *
                ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)) *
                    (m - n + 1))) := by
  obtain ⟨C, hC, hone⟩ :=
    measure_translated_cutoffBadScaleCount_large_le hDensity
  refine ⟨C, hC, ?_⟩
  intro M L s lambda epsilon hs hlambda hepsilon hsmall q m
  have hsubset := cutoffGoodStoppingDepth_tail_subset_iUnion
    M L lambda epsilon s q m
  calc
    M.P.toMeasure {omega |
        q < cutoffGoodStoppingDepth M L lambda epsilon s m omega} ≤
      M.P.toMeasure (⋃ n ∈ Finset.range (m - q + 1),
        cutoffGoodScaleSpatialFailure M L lambda epsilon s n m) :=
      measure_mono hsubset
    _ ≤ ∑ n ∈ Finset.range (m - q + 1),
        M.P.toMeasure
          (cutoffGoodScaleSpatialFailure M L lambda epsilon s n m) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.range (m - q + 1),
        (3 ^ (d * (m - n)) : ℕ) *
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
            (C * M.delta ^ 2 * |Real.log M.delta|)) *
              (m - n + 1))) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnm : n ≤ m := by
        rw [Finset.mem_range] at hn
        omega
      let centers := gridCentersInCube d n m
      let E : Vec d → Set (Sample d) := fun z =>
        {omega | lambda * (m - n) < ∑ j ∈ Finset.Icc n m,
          (1 - if omega ∈ goodEvent M (some L) j z epsilon s then
            (1 : ℝ) else 0)}
      have hevent : cutoffGoodScaleSpatialFailure M L lambda epsilon s n m =
          ⋃ z ∈ centers, E z := by
        ext omega
        constructor
        · rintro ⟨z, hzgrid, hzmem, hzbad⟩
          exact Set.mem_iUnion₂.2 ⟨z,
            (mem_gridCentersInCube_iff hnm).2 ⟨hzgrid, hzmem⟩, hzbad⟩
        · rintro homega
          obtain ⟨z, hz, hzbad⟩ := Set.mem_iUnion₂.1 homega
          obtain ⟨hzgrid, hzmem⟩ := (mem_gridCentersInCube_iff hnm).1 hz
          exact ⟨z, hzgrid, hzmem, hzbad⟩
      rw [hevent]
      calc
        M.P.toMeasure (⋃ z ∈ centers, E z) ≤
            ∑ z ∈ centers, M.P.toMeasure (E z) :=
          measure_biUnion_finset_le centers E
        _ ≤ ∑ _z ∈ centers,
            ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
              (C * M.delta ^ 2 * |Real.log M.delta|)) *
                (m - n + 1))) := by
          apply Finset.sum_le_sum
          intro z _hz
          simpa only [E, Nat.cast_sub hnm, Nat.add_sub_of_le hnm] using
            hone M L s lambda epsilon hs hlambda hepsilon hsmall z n (m - n)
        _ = (3 ^ (d * (m - n)) : ℕ) *
            ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
              (C * M.delta ^ 2 * |Real.log M.delta|)) *
                (m - n + 1))) := by
          rw [Finset.sum_const, nsmul_eq_mul, card_gridCentersInCube hnm]

/-- The translated cutoff good-stopping tail with its density input discharged
by the finite-cutoff response and the two unchanged shell-field arrays. -/
theorem exists_measure_cutoffGoodStoppingDepth_tail_le_sum_exp (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (s lambda epsilon : ℝ),
        s ∈ Set.Ioc (0 : ℝ) 1 → lambda ∈ Set.Ioc (0 : ℝ) 1 →
        epsilon ∈ Set.Ioc (0 : ℝ) 1 →
        C * s ^ (-6 : Int) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta| ≤ lambda / 2 →
        ∀ q m : ℕ,
          M.P.toMeasure {omega |
              q < cutoffGoodStoppingDepth M L lambda epsilon s m omega} ≤
            ∑ n ∈ Finset.range (m - q + 1),
              (3 ^ (d * (m - n)) : ℕ) *
                ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
                  (C * M.delta ^ 2 * |Real.log M.delta|)) *
                    (m - n + 1))) :=
  measure_cutoffGoodStoppingDepth_tail_le_sum_exp
    (exists_measure_cutoffGoodEvent_badDensity_le d)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
