import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.AccumulatedErrorCovariance

/-!
# Good-scale carriers below a finite cutoff

When the observation scale `m` is at most the deterministic cutoff `L`, every
response scale read by the Section 6 good event and accumulated error is also
at most `L`.  The finite-cutoff carriers therefore agree literally with their
uncutoff counterparts.  This module records that deterministic saturation
step separately from the annular `m > L` argument.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-- Below the cutoff, the response clause reads the same coefficient at every
admissible inner scale. -/
theorem goodResponse_some_iff_none_of_scale_le_cutoff
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (y : Vec d) (epsilon s : ℝ) (omega : Sample d) :
    GoodResponse M (some L) m y epsilon s omega ↔
      GoodResponse M none m y epsilon s omega := by
  unfold GoodResponse
  constructor
  · intro h j n hjm hnj z hgrid hann e he
    have hnL : n ≤ L := by omega
    simpa only [Option.getD_some, Option.getD_none, min_self, min_eq_left hnL]
      using h j n hjm hnj z hgrid hann e he
  · intro h j n hjm hnj z hgrid hann e he
    have hnL : n ≤ L := by omega
    simpa only [Option.getD_some, Option.getD_none, min_self, min_eq_left hnL]
      using h j n hjm hnj z hgrid hann e he

/-- The full good event is unchanged below the cutoff; its two field clauses
never depended on the cutoff and the response clause saturates by the previous
lemma. -/
theorem mem_goodEvent_some_iff_none_of_scale_le_cutoff
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (y : Vec d) (epsilon s : ℝ) (omega : Sample d) :
    omega ∈ goodEvent M (some L) m y epsilon s ↔
      omega ∈ goodEvent M none m y epsilon s := by
  unfold goodEvent
  change (GoodFieldOne m y epsilon s omega ∧ GoodFieldTwo m y s omega ∧
      GoodResponse M (some L) m y epsilon s omega) ↔
    (GoodFieldOne m y epsilon s omega ∧ GoodFieldTwo m y s omega ∧
      GoodResponse M none m y epsilon s omega)
  rw [goodResponse_some_iff_none_of_scale_le_cutoff M hmL y epsilon s omega]

private theorem accumulatedError_responseSet_some_eq_none_of_scale_le_cutoff
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (z : Vec d) (s : ℝ) (omega : Sample d) :
    {r : ℝ | ∃ j l : ℕ, j ≤ m ∧ l + 2 ≤ j ∧
        ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
          z' - z ∈ cube d j \ cube d (j - 1) ∧
          r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
            Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
              vecNormSq e = 1 ∧
              t = section6Response M l (min l ((some L).getD l)) omega z' e}) 1)} =
      {r : ℝ | ∃ j l : ℕ, j ≤ m ∧ l + 2 ≤ j ∧
        ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
          z' - z ∈ cube d j \ cube d (j - 1) ∧
          r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
            Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
              vecNormSq e = 1 ∧
              t = section6Response M l (min l (none.getD l)) omega z' e}) 1)} := by
  ext r
  constructor
  · rintro ⟨j, l, hjm, hlj, z', hgrid, hann, rfl⟩
    have hlL : l ≤ L := by omega
    refine ⟨j, l, hjm, hlj, z', hgrid, hann, ?_⟩
    simp only [Option.getD_some, Option.getD_none, min_self, min_eq_left hlL]
  · rintro ⟨j, l, hjm, hlj, z', hgrid, hann, rfl⟩
    have hlL : l ≤ L := by omega
    refine ⟨j, l, hjm, hlj, z', hgrid, hann, ?_⟩
    simp only [Option.getD_some, Option.getD_none, min_self, min_eq_left hlL]

/-- The literal accumulated error is unchanged below the cutoff. -/
theorem accumulatedError_some_eq_none_of_scale_le_cutoff
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (z : Vec d) (s : ℝ) (omega : Sample d) :
    accumulatedError M (some L) m z s omega =
      accumulatedError M none m z s omega := by
  unfold accumulatedError
  rw [accumulatedError_responseSet_some_eq_none_of_scale_le_cutoff
    M hmL z s omega]

/-- The translated refined good-scale estimate transfers verbatim to the
finite-cutoff carrier below `L`.  The separate epsilon cap follows from the
same minimum estimate, so both conclusions use one dimension-only constant. -/
theorem exists_section6HomogenizationError_le_cutoff_min_of_scale_le_cutoff
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      ∀ L m : ℕ, m ≤ L → ∀ omega z,
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
          omega ∈ goodEvent M (some L) m z epsilon s →
            section6HomogenizationError M s L m omega z ≤
                C * min epsilon
                  (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                    accumulatedError M (some L) m z s omega) ∧
              section6HomogenizationError M s L m omega z ≤ C * epsilon := by
  obtain ⟨C, hC, hbound⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.exists_section6HomogenizationError_le_min_accumulatedError_local d
  refine ⟨C, hC, ?_⟩
  intro M s hs L m hmL omega z epsilon hepsilon hgood
  have hgoodNone : omega ∈ goodEvent M none m z epsilon s :=
    (mem_goodEvent_some_iff_none_of_scale_le_cutoff
      M hmL z epsilon s omega).1 hgood
  have h := hbound M s hs L m hmL omega z epsilon hepsilon hgoodNone
  rw [← accumulatedError_some_eq_none_of_scale_le_cutoff
    M hmL z s omega] at h
  refine ⟨h, h.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (min_le_left _ _) hC.le

/-- Indicator-form low-scale branch, matching the final clause of the frozen
cutoff good-scale proposition. -/
theorem exists_indicator_section6HomogenizationError_le_cutoff_min_of_scale_le_cutoff
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      ∀ L m : ℕ, m ≤ L → ∀ z omega,
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
          indicatorValue (goodEvent M (some L) m z epsilon s)
              (fun omega' ↦ section6HomogenizationError M s L m omega' z) omega ≤
              C * min epsilon
                (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                  accumulatedError M (some L) m z s omega) ∧
            indicatorValue (goodEvent M (some L) m z epsilon s)
              (fun omega' ↦ section6HomogenizationError M s L m omega' z) omega ≤
              C * epsilon := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_section6HomogenizationError_le_cutoff_min_of_scale_le_cutoff d
  refine ⟨C, hC, ?_⟩
  intro M s hs L m hmL z omega epsilon hepsilon
  by_cases hgood : omega ∈ goodEvent M (some L) m z epsilon s
  · simpa only [indicatorValue, if_pos hgood] using
      hbound M s hs L m hmL omega z epsilon hepsilon hgood
  · have hs0 : 0 ≤ s :=
      (mul_nonneg (by norm_num) (sq_nonneg M.delta)).trans hs.1
    have hD0 : 0 ≤ s⁻¹ * M.delta ^ 2 :=
      mul_nonneg (inv_nonneg.mpr hs0) (sq_nonneg _)
    have hepsilon0 : 0 ≤ epsilon := hD0.trans hepsilon.1
    have hE0 : 0 ≤ accumulatedError M (some L) m z s omega :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.accumulatedError_nonneg
        M (some L) s m z omega
    simp only [indicatorValue, if_neg hgood]
    constructor
    · exact mul_nonneg hC.le <| le_min hepsilon0 (by positivity)
    · exact mul_nonneg hC.le hepsilon0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
