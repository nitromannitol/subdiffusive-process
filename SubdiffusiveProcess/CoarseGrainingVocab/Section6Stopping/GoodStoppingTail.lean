module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GoodDensityTranslation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.GridCenters

@[expose] public section

/-!
# Spatial union bound for the good-scale stopping argument

This file performs the exact `3^{d(m-n)}` union in
`l.min.scale.good.scale`.  No measurability of the literal good event is used:
the density input already supplies the outer-measure estimate for each centre.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- A frozen `sInf` candidate is witnessed by an actual grid centre.  The
extra one in the cardinality of `Icc n m` turns the weak good-count failure
into the strict bad-count event used by the density estimate. -/
theorem exists_gridCenter_badScaleCount_of_sInf_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (lambda epsilon s : ℝ)
    (n m : ℕ) (hnm : n <= m)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hfail : sInf {r : ℝ | ∃ z : Vec d,
        OnTriadicGrid n z ∧ z ∈ cube d m ∧
          r = ∑ j ∈ Finset.Icc n m,
            if omega ∈ goodEvent M none j z epsilon s then 1 else 0} <=
      (1 - lambda) * ((m : ℝ) - (n : ℝ))) :
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
      lambda * (m - n) < ∑ j ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M none j z epsilon s then
          (1 : ℝ) else 0) := by
  let centers := gridCentersInCube d n m
  let goodCount : {z : Vec d // z ∈ centers} -> ℝ := fun z =>
    ∑ j ∈ Finset.Icc n m,
      if omega ∈ goodEvent M none j z.1 epsilon s then 1 else 0
  let values : Set ℝ := {r : ℝ | ∃ z : Vec d,
    OnTriadicGrid n z ∧ z ∈ cube d m ∧
      r = ∑ j ∈ Finset.Icc n m,
        if omega ∈ goodEvent M none j z epsilon s then 1 else 0}
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
  let : Nonempty {z : Vec d // z ∈ centers} :=
    Finset.nonempty_coe_sort.mpr hcenters
  have hfinite : values.Finite := by
    rw [hvalues]
    exact Set.finite_range goodCount
  have hnonempty : values.Nonempty := by
    rw [hvalues]
    exact Set.range_nonempty goodCount
  by_contra hcontra
  push Not at hcontra
  have hall : ∀ r ∈ values,
      (1 - lambda) * ((m : ℝ) - (n : ℝ)) < r := by
    rintro r ⟨z, hzgrid, hzmem, rfl⟩
    have hbad := hcontra z hzgrid hzmem
    have hcard : ((Finset.Icc n m).card : ℝ) =
        (m : ℝ) - (n : ℝ) + 1 := by
      rw [Nat.card_Icc, Nat.cast_sub (by omega : n <= m + 1), Nat.cast_add]
      norm_num
      ring
    have hpartition :
        (∑ j ∈ Finset.Icc n m,
            if omega ∈ goodEvent M none j z epsilon s then (1 : ℝ) else 0) +
          (∑ j ∈ Finset.Icc n m,
            (1 - if omega ∈ goodEvent M none j z epsilon s then
              (1 : ℝ) else 0)) =
          (m : ℝ) - (n : ℝ) + 1 := by
      rw [← hcard, ← Finset.sum_add_distrib]
      calc
        (∑ j ∈ Finset.Icc n m,
            ((if omega ∈ goodEvent M none j z epsilon s then (1 : ℝ) else 0) +
              (1 - if omega ∈ goodEvent M none j z epsilon s then
                (1 : ℝ) else 0))) =
            ∑ _j ∈ Finset.Icc n m, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _hj
          split_ifs <;> norm_num
        _ = ((Finset.Icc n m).card : ℝ) := by simp
    nlinarith
  have hlower : (1 - lambda) * ((m : ℝ) - (n : ℝ)) < sInf values :=
    (hfinite.lt_csInf_iff hnonempty).2 hall
  exact (not_lt_of_ge (by simpa only [values] using hfail)) hlower

/-- The one-centre density estimate, unioned over every literal scale-`n`
grid centre in `□_m`. -/
theorem measure_exists_gridCenter_badScaleCount_large_le {d : ℕ}
    (hDensity : DensityOfGoodScalesInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s lambda epsilon : ℝ,
      s ∈ Set.Ioc 0 1 → lambda ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| ≤ lambda / 2 →
      ∀ n m : ℕ, n ≤ m →
        M.P.toMeasure {omega | ∃ z : Vec d,
            OnTriadicGrid n z ∧ z ∈ cube d m ∧
              lambda * (m - n) < ∑ j ∈ Finset.Icc n m,
                (1 - if omega ∈ goodEvent M none j z epsilon s then
                  (1 : ℝ) else 0)} ≤
          (3 ^ (d * (m - n)) : ℕ) *
            ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
              (C * M.delta ^ 2 * |Real.log M.delta|)) * (m - n + 1))) := by
  obtain ⟨C, hC, hone⟩ :=
    measure_translated_badScaleCount_large_le hDensity
  refine ⟨C, hC, ?_⟩
  intro M s lambda epsilon hs hlambda hepsilon hsmall n m hnm
  let centers := gridCentersInCube d n m
  let E : Vec d → Set (_root_.SubdiffusiveProcess.Model.PotentialSample d) := fun z =>
    {omega | lambda * (m - n) < ∑ j ∈ Finset.Icc n m,
      (1 - if omega ∈ goodEvent M none j z epsilon s then
        (1 : ℝ) else 0)}
  have hevent : {omega | ∃ z : Vec d,
      OnTriadicGrid n z ∧ z ∈ cube d m ∧
        lambda * (m - n) < ∑ j ∈ Finset.Icc n m,
          (1 - if omega ∈ goodEvent M none j z epsilon s then
            (1 : ℝ) else 0)} = ⋃ z ∈ centers, E z := by
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
    M.P.toMeasure (⋃ z ∈ centers, E z) ≤ ∑ z ∈ centers, M.P.toMeasure (E z) :=
      measure_biUnion_finset_le centers E
    _ ≤ ∑ _z ∈ centers,
        ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
          (C * M.delta ^ 2 * |Real.log M.delta|)) * (m - n + 1))) := by
      apply Finset.sum_le_sum
      intro z _hz
      simpa only [E, Nat.cast_sub hnm, Nat.add_sub_of_le hnm] using
        hone M s lambda epsilon hs hlambda hepsilon hsmall z n (m - n)
    _ = (3 ^ (d * (m - n)) : ℕ) *
        ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
          (C * M.delta ^ 2 * |Real.log M.delta|)) * (m - n + 1))) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_gridCentersInCube hnm]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
