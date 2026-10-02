import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ParameterizedResponseMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorResponseWindow

/-!
# Parameterized finite-cutoff response-window rearrangement

This module performs the deterministic response part of the general-`s`
accumulated-error rearrangement.  It reduces the literal nested supremum to
the parameterized capped rows and sums the resulting triangular convolution
over a finite scale window.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open Filter MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The literal finite-cutoff response supremum at an arbitrary exponent. -/
noncomputable def cutoffParameterizedAccumulatedResponseSup {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) (k : ℕ)
    (omega : Sample d) : ℝ :=
  sSup {r : ℝ | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid l z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
        Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
          vecNormSq e = 1 ∧
            t = section6Response M l (min l L) omega z e}) 1)}

/-- The same response supremum based at an arbitrary spatial center. -/
noncomputable def translatedCutoffParameterizedAccumulatedResponseSup
    {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) (k : ℕ)
    (z : Vec d) (omega : Sample d) : ℝ :=
  sSup {r : ℝ | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
    ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
      z' - z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
        Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
          vecNormSq e = 1 ∧
            t = section6Response M l (min l L) omega z' e}) 1)}

theorem translatedCutoffParameterizedAccumulatedResponseSup_eq_origin_translate
    {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) (k : ℕ)
    (z : Vec d) (omega : Sample d) :
    translatedCutoffParameterizedAccumulatedResponseSup M L s k z omega =
      cutoffParameterizedAccumulatedResponseSup M L s k
        (translatePotentialSample z omega) := by
  unfold translatedCutoffParameterizedAccumulatedResponseSup
    cutoffParameterizedAccumulatedResponseSup
  congr 1
  ext r
  constructor
  · rintro ⟨j, l, hjk, hlj, z', hzgrid, hzann, rfl⟩
    refine ⟨j, l, hjk, hlj, z' - z, hzgrid, hzann, ?_⟩
    have hsets : {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M l (min l L)
          (translatePotentialSample z omega) (z' - z) e} =
        {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          t = section6Response M l (min l L) omega z' e} := by
      ext t
      constructor
      · rintro ⟨e, he, rfl⟩
        refine ⟨e, he, ?_⟩
        rw [Section6Covariance.section6Response_translatePotentialSample,
          add_sub_cancel]
      · rintro ⟨e, he, rfl⟩
        refine ⟨e, he, ?_⟩
        rw [Section6Covariance.section6Response_translatePotentialSample,
          add_sub_cancel]
    rw [hsets]
  · rintro ⟨j, l, hjk, hlj, y, hygrid, hyann, rfl⟩
    refine ⟨j, l, hjk, hlj, z + y, ?_, ?_, ?_⟩
    · simpa only [add_sub_cancel_left] using hygrid
    · simpa only [add_sub_cancel_left] using hyann
    · have hsets : {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          t = section6Response M l (min l L) omega (z + y) e} =
          {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            t = section6Response M l (min l L)
              (translatePotentialSample z omega) y e} := by
        ext t
        constructor
        · rintro ⟨e, he, rfl⟩
          refine ⟨e, he, ?_⟩
          exact (Section6Covariance.section6Response_translatePotentialSample
            M l (min l L) omega z y e).symm
        · rintro ⟨e, he, rfl⟩
          exact ⟨e, he,
            Section6Covariance.section6Response_translatePotentialSample
              M l (min l L) omega z y e⟩
      rw [hsets]

/-- Pointwise reduction of the literal general-`s` response supremum to the
parameterized row convolution. -/
theorem cutoffParameterizedAccumulatedResponseSup_le_row_convolution_of_localNet
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (omega : Sample d)
    (hall : ∀ j l : ℕ, l + 2 ≤ j →
      ∀ z : Vec d, OnTriadicGrid l z →
        z ∈ cube d j \ cube d (j - 1) →
          sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
              t = section6Response M l (min l L) omega z e} ≤
            2 * (cutoffLocalResponseScaleAtom M L j l omega).toReal)
    (k : ℕ) :
    cutoffParameterizedAccumulatedResponseSup M L s k omega ≤
      2 * ∑ j ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
          cutoffParameterizedResponseRow M L s j omega := by
  let values : Set ℝ := {r : ℝ | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid l z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
        Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
          vecNormSq e = 1 ∧
            t = section6Response M l (min l L) omega z e}) 1)}
  by_cases hvalues : values.Nonempty
  · unfold cutoffParameterizedAccumulatedResponseSup
    apply csSup_le hvalues
    rintro r ⟨j, l, hjk, hlj, z, hzgrid, hzann, rfl⟩
    let R : ℝ := sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
      t = section6Response M l (min l L) omega z e}
    let A : ℝ := (cutoffLocalResponseScaleAtom M L j l omega).toReal
    have hRA : R ≤ 2 * A := by
      simpa only [R, A] using hall j l hlj z hzgrid hzann
    have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
    have hminA0 : 0 ≤ min A 1 := le_min hA0 zero_le_one
    have hmin : min R 1 ≤ 2 * min A 1 := by
      by_cases hA1 : A ≤ 1
      · rw [min_eq_left hA1]
        exact (min_le_left R 1).trans hRA
      · rw [min_eq_right (le_of_not_ge hA1)]
        exact (min_le_right R 1).trans (by norm_num)
    have hsqrt : Real.sqrt (min R 1) ≤ 2 * Real.sqrt (min A 1) := by
      calc
        Real.sqrt (min R 1) ≤ Real.sqrt (2 * min A 1) :=
          Real.sqrt_le_sqrt hmin
        _ = Real.sqrt 2 * Real.sqrt (min A 1) :=
          Real.sqrt_mul (by norm_num) _
        _ ≤ 2 * Real.sqrt (min A 1) := by
          gcongr
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
            Real.sqrt_nonneg 2]
    have hweight :
        (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) ≤
          (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
            (3 : ℝ) ^ (-(s / 4) * ((j : ℝ) - (l : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hlk : (l : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (by omega : l ≤ k)
      nlinarith
    have hatom := cutoffParameterizedResponseAtom_le_row
      M L hs hs1 hlj omega
    have hterm :
        (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
            Real.sqrt (min R 1) ≤
          2 * ((3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
            cutoffParameterizedResponseRow M L s j omega) := by
      calc
        _ ≤ (3 : ℝ) ^ (-(s / 2) * ((k : ℝ) - (l : ℝ))) *
            (2 * Real.sqrt (min A 1)) := by gcongr
        _ ≤ ((3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
              (3 : ℝ) ^ (-(s / 4) * ((j : ℝ) - (l : ℝ)))) *
            (2 * Real.sqrt (min A 1)) := by gcongr
        _ ≤ 2 * ((3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
            cutoffParameterizedResponseRow M L s j omega) := by
          calc
            _ = 2 * (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
                ((3 : ℝ) ^ (-(s / 4) * ((j : ℝ) - (l : ℝ))) *
                  Real.sqrt (min A 1)) := by ring
            _ ≤ 2 * (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
                cutoffParameterizedResponseRow M L s j omega := by
              gcongr
            _ = _ := by ring
    have hjmem : j ∈ Finset.range (k + 1) :=
      Finset.mem_range.mpr (by omega)
    calc
      _ ≤ 2 * ((3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
          cutoffParameterizedResponseRow M L s j omega) := by
        simpa only [R, A] using hterm
      _ ≤ 2 * ∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
            cutoffParameterizedResponseRow M L s j omega := by
        gcongr
        exact Finset.single_le_sum
          (f := fun i : ℕ =>
            (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (i : ℝ))) *
              cutoffParameterizedResponseRow M L s i omega)
          (fun i _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (cutoffParameterizedResponseRow_nonneg M L s i omega)) hjmem
  · have hempty : values = ∅ := Set.not_nonempty_iff_eq_empty.mp hvalues
    have hright : 0 ≤ 2 * ∑ j ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
          cutoffParameterizedResponseRow M L s j omega := by
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ =>
        mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (cutoffParameterizedResponseRow_nonneg M L s j omega))
    unfold cutoffParameterizedAccumulatedResponseSup
    change sSup values ≤ _
    rw [hempty, Real.sSup_empty]
    exact hright

theorem ae_forall_cutoffParameterizedAccumulatedResponseSup_le_row_convolution
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ k : ℕ,
      cutoffParameterizedAccumulatedResponseSup M L s k omega ≤
        2 * ∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
            cutoffParameterizedResponseRow M L s j omega := by
  filter_upwards
    [ae_forall_sSup_section6Response_cutoff_le_two_mul_localResponseScaleAtom_toReal
      M L] with omega hall
  intro k
  exact cutoffParameterizedAccumulatedResponseSup_le_row_convolution_of_localNet
    M L hs hs1 omega hall k

/-- The triangular parameterized response convolution over a scale window. -/
noncomputable def cutoffParameterizedAccumulatedResponseWindowConvolution
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (s : ℝ) (n m : ℕ)
    (omega : Sample d) : ℝ :=
  ∑ k ∈ Finset.Icc n m, ∑ j ∈ Finset.range (k + 1),
    (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
      cutoffParameterizedResponseRow M L s j omega

theorem ae_sum_cutoffParameterizedAccumulatedResponseSup_le_windowConvolution
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (n m : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m,
        cutoffParameterizedAccumulatedResponseSup M L s k omega) ≤
        2 * cutoffParameterizedAccumulatedResponseWindowConvolution
          M L s n m omega := by
  filter_upwards
    [ae_forall_cutoffParameterizedAccumulatedResponseSup_le_row_convolution
      M L hs hs1] with omega hall
  unfold cutoffParameterizedAccumulatedResponseWindowConvolution
  calc
    (∑ k ∈ Finset.Icc n m,
        cutoffParameterizedAccumulatedResponseSup M L s k omega) ≤
        ∑ k ∈ Finset.Icc n m,
          2 * ∑ j ∈ Finset.range (k + 1),
            (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
              cutoffParameterizedResponseRow M L s j omega := by
      exact Finset.sum_le_sum fun k _ => hall k
    _ = 2 * ∑ k ∈ Finset.Icc n m, ∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(s / 4) * ((k : ℝ) - (j : ℝ))) *
            cutoffParameterizedResponseRow M L s j omega := by
      rw [Finset.mul_sum]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
