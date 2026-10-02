import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.ResidueWindow
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.AccumulatedErrorFieldWindow

/-!
# Literal response-window rearrangement

This is the deterministic `k/j/l` part of
`e.split.J.for.minimal.scale` at the fixed Hölder exponent.  It connects the
literal nested supremum in `accumulatedError` to the landed capped annular
rows, on the single common quarter-net event.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The first `sSup` in the frozen accumulated-error definition, at the
origin and at the fixed Hölder stopping exponent. -/
noncomputable def accumulatedResponseSup {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ)
    (omega : Sample d) : ℝ :=
  sSup {r : ℝ | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid l z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(holderStoppingS / 2) * ((k : ℝ) - (l : ℝ))) *
        Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
        vecNormSq e = 1 ∧ t = section6Response M l l omega z e}) 1)}

/-- The literal first summand of `accumulatedError` at an arbitrary base
centre and with no cutoff. -/
noncomputable def translatedAccumulatedResponseSup {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d)
    (omega : Sample d) : ℝ :=
  sSup {r : ℝ | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
    ∃ z' : Vec d, OnTriadicGrid l (z' - z) ∧
      z' - z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(holderStoppingS / 2) * ((k : ℝ) - (l : ℝ))) *
        Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
          vecNormSq e = 1 ∧ t = section6Response M l l omega z' e}) 1)}

/-- Stationarity identifies the arbitrary-centre literal response carrier
with the origin carrier evaluated on the translated sample. -/
theorem translatedAccumulatedResponseSup_eq_origin_translate {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (z : Vec d)
    (omega : Sample d) :
    translatedAccumulatedResponseSup M k z omega =
      accumulatedResponseSup M k (translatePotentialSample z omega) := by
  unfold translatedAccumulatedResponseSup accumulatedResponseSup
  congr 1
  ext r
  constructor
  · rintro ⟨j, l, hjk, hlj, z', hzgrid, hzann, rfl⟩
    refine ⟨j, l, hjk, hlj, z' - z, hzgrid, hzann, ?_⟩
    have hsets : {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
        t = section6Response M l l (translatePotentialSample z omega) (z' - z) e} =
        {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
          t = section6Response M l l omega z' e} := by
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
          t = section6Response M l l omega (z + y) e} =
          {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
            t = section6Response M l l (translatePotentialSample z omega) y e} := by
        ext t
        constructor
        · rintro ⟨e, he, rfl⟩
          refine ⟨e, he, ?_⟩
          exact (Section6Covariance.section6Response_translatePotentialSample
            M l l omega z y e).symm
        · rintro ⟨e, he, rfl⟩
          exact ⟨e, he,
            Section6Covariance.section6Response_translatePotentialSample
              M l l omega z y e⟩
      rw [hsets]

/-- The literal response supremum at scale `k` is bounded by the geometric
convolution of the annular response rows. -/
theorem accumulatedResponseSup_le_row_convolution_of_localNet
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : Sample d)
    (hall : ∀ j l : ℕ, l + 2 ≤ j →
      ∀ z : Vec d, OnTriadicGrid l z →
        z ∈ cube d j \ cube d (j - 1) →
          sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
              t = section6Response M l l omega z e} ≤
            2 * (localResponseScaleAtom M j l omega).toReal)
    (k : ℕ) :
    accumulatedResponseSup M k omega ≤
      2 * ∑ j ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
          holderResponseRow M j omega := by
  let values : Set ℝ := {r : ℝ | ∃ j l : ℕ, j ≤ k ∧ l + 2 ≤ j ∧
    ∃ z : Vec d, OnTriadicGrid l z ∧ z ∈ cube d j \ cube d (j - 1) ∧
      r = (3 : ℝ) ^ (-(holderStoppingS / 2) * ((k : ℝ) - (l : ℝ))) *
        Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
          vecNormSq e = 1 ∧ t = section6Response M l l omega z e}) 1)}
  by_cases hvalues : values.Nonempty
  · unfold accumulatedResponseSup
    apply csSup_le hvalues
    rintro r ⟨j, l, hjk, hlj, z, hzgrid, hzann, rfl⟩
    let R : ℝ := sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
      t = section6Response M l l omega z e}
    let A : ℝ := (localResponseScaleAtom M j l omega).toReal
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
        (3 : ℝ) ^ (-(holderStoppingS / 2) * ((k : ℝ) - (l : ℝ))) ≤
          (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
            (3 : ℝ) ^ (-(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hlk : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : l ≤ k)
      have hs := holderStoppingS_pos
      nlinarith
    have hatom := holderResponseAtom_le_row M hlj omega
    have hterm :
        (3 : ℝ) ^ (-(holderStoppingS / 2) * ((k : ℝ) - (l : ℝ))) *
            Real.sqrt (min R 1) ≤
          2 * ((3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
            holderResponseRow M j omega) := by
      calc
        _ ≤ (3 : ℝ) ^ (-(holderStoppingS / 2) * ((k : ℝ) - (l : ℝ))) *
            (2 * Real.sqrt (min A 1)) := by gcongr
        _ ≤ ((3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
              (3 : ℝ) ^ (-(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ)))) *
            (2 * Real.sqrt (min A 1)) := by gcongr
        _ ≤ 2 * ((3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
              holderResponseRow M j omega) := by
          calc
            _ = 2 * (3 : ℝ) ^
                (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
                ((3 : ℝ) ^
                  (-(holderStoppingS / 4) * ((j : ℝ) - (l : ℝ))) *
                    Real.sqrt (min A 1)) := by ring
            _ ≤ 2 * (3 : ℝ) ^
                (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
                holderResponseRow M j omega := by
              gcongr
            _ = _ := by ring
    have hjmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    calc
      _ ≤ 2 * ((3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
          holderResponseRow M j omega) := by simpa only [R, A] using hterm
      _ ≤ 2 * ∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
            holderResponseRow M j omega := by
        gcongr
        exact Finset.single_le_sum
          (f := fun i : ℕ ↦
            (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (i : ℝ))) *
              holderResponseRow M i omega)
          (fun i _ ↦ mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (holderResponseRow_nonneg M i omega)) hjmem
  · have hempty : values = ∅ := Set.not_nonempty_iff_eq_empty.mp hvalues
    have hright : 0 ≤ 2 * ∑ j ∈ Finset.range (k + 1),
        (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
          holderResponseRow M j omega := by
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ ↦
        mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (holderResponseRow_nonneg M j omega))
    unfold accumulatedResponseSup
    change sSup values ≤ _
    rw [hempty, Real.sSup_empty]
    exact hright

/-- Almost surely, all scale-`k` literal response suprema are controlled by
the same row convolution. -/
theorem ae_forall_accumulatedResponseSup_le_row_convolution
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ k : ℕ,
      accumulatedResponseSup M k omega ≤
        2 * ∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
            holderResponseRow M j omega := by
  filter_upwards
    [ae_forall_sSup_section6Response_le_two_mul_localResponseScaleAtom_toReal M]
      with omega hall
  intro k
  exact accumulatedResponseSup_le_row_convolution_of_localNet M omega hall k

/-- The exact finite triangular convolution produced after summing the
literal response suprema over a scale window. -/
noncomputable def accumulatedResponseWindowConvolution
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ)
    (omega : Sample d) : ℝ :=
  ∑ k ∈ Finset.Icc n m, ∑ j ∈ Finset.range (k + 1),
    (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
      holderResponseRow M j omega

/-- Summed form of the literal `e.split.J.for.minimal.scale` reduction. -/
theorem ae_sum_accumulatedResponseSup_le_windowConvolution
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ) :
    ∀ᵐ omega ∂M.P.toMeasure,
      (∑ k ∈ Finset.Icc n m, accumulatedResponseSup M k omega) ≤
        2 * accumulatedResponseWindowConvolution M n m omega := by
  filter_upwards [ae_forall_accumulatedResponseSup_le_row_convolution M]
    with omega hall
  unfold accumulatedResponseWindowConvolution
  calc
    (∑ k ∈ Finset.Icc n m, accumulatedResponseSup M k omega) ≤
        ∑ k ∈ Finset.Icc n m,
          2 * ∑ j ∈ Finset.range (k + 1),
            (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
              holderResponseRow M j omega := by
      exact Finset.sum_le_sum fun k _ ↦ hall k
    _ = 2 * ∑ k ∈ Finset.Icc n m, ∑ j ∈ Finset.range (k + 1),
          (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
            holderResponseRow M j omega := by
      rw [Finset.mul_sum]

/-- The `j`th annular row after interchanging the literal `k/j` triangle. -/
noncomputable def accumulatedResponseColumn {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m j : ℕ) : Sample d → ℝ :=
  fun omega ↦ ∑ k ∈ (Finset.Icc n m).filter (fun k ↦ j ≤ k),
    (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
      holderResponseRow M j omega

noncomputable def accumulatedResponseColumnWeight (n m j : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc n m).filter (fun k ↦ j ≤ k),
    (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ)))

theorem accumulatedResponseColumn_eq_weight_mul {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m j : ℕ) (omega : Sample d) :
    accumulatedResponseColumn M n m j omega =
      accumulatedResponseColumnWeight n m j * holderResponseRow M j omega := by
  unfold accumulatedResponseColumn accumulatedResponseColumnWeight
  rw [Finset.sum_mul]

noncomputable def accumulatedResponseLowWindow {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ) : Sample d → ℝ :=
  fun omega ↦ ∑ j ∈ Finset.range n, accumulatedResponseColumn M n m j omega

noncomputable def accumulatedResponseActiveWindow {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ) : Sample d → ℝ :=
  fun omega ↦ ∑ j ∈ Finset.Icc n m, accumulatedResponseColumn M n m j omega

/-- The inner `k`-sum costs only the fixed geometric constant. -/
theorem accumulatedResponseColumnWeight_le (n m j : ℕ) :
    accumulatedResponseColumnWeight n m j ≤ 8 / holderStoppingS := by
  let S : Finset ℕ := (Finset.Icc n m).filter (fun k ↦ j ≤ k)
  have hquarter : holderStoppingS / 2 / 2 = holderStoppingS / 4 := by ring
  have hsummable : Summable (fun q : ℤ ↦
      SubdiffusiveProcess.Concentration.wt (holderStoppingS / 4) (j : ℤ) q) := by
    simpa only [hquarter] using SubdiffusiveProcess.Concentration.summable_wt_half
      (show 0 < holderStoppingS / 2 by norm_num [holderStoppingS])
      (show holderStoppingS / 2 ≤ 1 by norm_num [holderStoppingS]) (j : ℤ)
  have hfinite : (∑ q ∈ S.map ⟨Int.ofNat, Int.ofNat_injective⟩,
      SubdiffusiveProcess.Concentration.wt (holderStoppingS / 4) (j : ℤ) q) ≤
      ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (holderStoppingS / 4) (j : ℤ) q :=
    hsummable.sum_le_tsum
    (s := S.map ⟨Int.ofNat, Int.ofNat_injective⟩)
    (fun q _ ↦ SubdiffusiveProcess.Concentration.wt_nonneg (holderStoppingS / 4) (j : ℤ) q)
  have hsum : accumulatedResponseColumnWeight n m j ≤
      ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (holderStoppingS / 4) (j : ℤ) q := by
    unfold accumulatedResponseColumnWeight
    rw [Finset.sum_map] at hfinite
    apply (Finset.sum_le_sum fun k hk ↦ ?_).trans hfinite
    obtain ⟨_hk, hjk⟩ := Finset.mem_filter.mp hk
    simp only [Function.Embedding.coeFn_mk, SubdiffusiveProcess.Concentration.wt,
      SubdiffusiveProcess.Concentration.idist_eq]
    have habs : ((j : ℤ) - Int.ofNat k).natAbs = k - j := by
      rw [show (j : ℤ) - Int.ofNat k = -(Int.ofNat k - (j : ℤ)) by ring,
        Int.natAbs_neg]
      simpa only [Int.ofNat_eq_natCast] using
        Int.natAbs_natCast_sub_natCast_of_ge hjk
    rw [habs, Nat.cast_sub hjk]
    apply le_of_eq
    congr 2
    ring
  calc
    _ ≤ ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (holderStoppingS / 4) (j : ℤ) q := hsum
    _ ≤ 4 / (holderStoppingS / 2) := by
      simpa only [hquarter] using SubdiffusiveProcess.Concentration.sum_wt_half_le
        (show 0 < holderStoppingS / 2 by norm_num [holderStoppingS])
        (show holderStoppingS / 2 ≤ 1 by norm_num [holderStoppingS]) (j : ℤ)
    _ = 8 / holderStoppingS := by ring

theorem accumulatedResponseActiveWindow_le_rows {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ)
    (omega : Sample d) :
    accumulatedResponseActiveWindow M n m omega ≤
      (8 / holderStoppingS) *
        ∑ j ∈ Finset.Icc n m, holderResponseRow M j omega := by
  unfold accumulatedResponseActiveWindow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [accumulatedResponseColumn_eq_weight_mul]
  exact mul_le_mul_of_nonneg_right
    (accumulatedResponseColumnWeight_le n m j)
    (holderResponseRow_nonneg M j omega)

/-- A row born before `n` retains its geometric distance from the window. -/
theorem accumulatedResponseColumnWeight_eq_low_decay {n m j : ℕ}
    (hj : j ≤ n) :
    accumulatedResponseColumnWeight n m j =
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
        accumulatedResponseColumnWeight n m n := by
  unfold accumulatedResponseColumnWeight
  have hfilter : (Finset.Icc n m).filter (fun k ↦ j ≤ k) =
      (Finset.Icc n m).filter (fun k ↦ n ≤ k) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

theorem accumulatedResponseLowWindow_le_decay_rows {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ) (omega : Sample d) :
    accumulatedResponseLowWindow M n m omega ≤
      (8 / holderStoppingS) * ∑ j ∈ Finset.range n,
        (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
          holderResponseRow M j omega := by
  unfold accumulatedResponseLowWindow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [accumulatedResponseColumn_eq_weight_mul,
    accumulatedResponseColumnWeight_eq_low_decay (Finset.mem_range.mp hj).le]
  have hw := accumulatedResponseColumnWeight_le n m n
  have hdecay : 0 ≤
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hrow := holderResponseRow_nonneg M j omega
  calc
    _ ≤ ((3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
          (8 / holderStoppingS)) * holderResponseRow M j omega := by
      gcongr
    _ = (8 / holderStoppingS) *
        ((3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
          holderResponseRow M j omega) := by ring

theorem sum_responseQuarterWeight_range_le (n : ℕ) :
    (∑ j ∈ Finset.range n,
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ)))) ≤
        8 / holderStoppingS := by
  have hquarter : holderStoppingS / 2 / 2 = holderStoppingS / 4 := by ring
  have hsummable : Summable (fun q : ℤ ↦
      SubdiffusiveProcess.Concentration.wt (holderStoppingS / 4) (n : ℤ) q) := by
    simpa only [hquarter] using SubdiffusiveProcess.Concentration.summable_wt_half
      (show 0 < holderStoppingS / 2 by norm_num [holderStoppingS])
      (show holderStoppingS / 2 ≤ 1 by norm_num [holderStoppingS]) (n : ℤ)
  have hfinite := hsummable.sum_le_tsum
    (s := (Finset.range n).map ⟨Int.ofNat, Int.ofNat_injective⟩)
    (fun q _ ↦ SubdiffusiveProcess.Concentration.wt_nonneg (holderStoppingS / 4) (n : ℤ) q)
  have hsum : (∑ j ∈ Finset.range n,
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ)))) ≤
      ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (holderStoppingS / 4) (n : ℤ) q := by
    rw [Finset.sum_map] at hfinite
    apply (Finset.sum_le_sum fun j hj ↦ ?_).trans hfinite
    have hjn := (Finset.mem_range.mp hj).le
    simp only [Function.Embedding.coeFn_mk, SubdiffusiveProcess.Concentration.wt,
      SubdiffusiveProcess.Concentration.idist_eq]
    have habs : ((n : ℤ) - Int.ofNat j).natAbs = n - j := by
      simpa only [Int.ofNat_eq_natCast] using
        Int.natAbs_natCast_sub_natCast_of_ge hjn
    rw [habs, Nat.cast_sub hjn]
    apply le_of_eq
    congr 2
    ring
  calc
    _ ≤ ∑' q : ℤ, SubdiffusiveProcess.Concentration.wt (holderStoppingS / 4) (n : ℤ) q := hsum
    _ ≤ 4 / (holderStoppingS / 2) := by
      simpa only [hquarter] using SubdiffusiveProcess.Concentration.sum_wt_half_le
        (show 0 < holderStoppingS / 2 by norm_num [holderStoppingS])
        (show holderStoppingS / 2 ≤ 1 by norm_num [holderStoppingS]) (n : ℤ)
    _ = 8 / holderStoppingS := by ring

noncomputable def accumulatedResponseLowRows {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) : Sample d → ℝ :=
  fun omega ↦ ∑ j ∈ Finset.range n,
    (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
      holderResponseRow M j omega

theorem isBigO_accumulatedResponseLowRows {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ)
    {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2)
      (holderResponseRow M j) A) :
    IndependentSums.IsBigO M.P.toMeasure (IndependentSums.gammaSigma 2)
      (accumulatedResponseLowRows M n)
      (Ch04.gammaTriangleConst 2 * ((8 / holderStoppingS) * A)) := by
  by_cases hn : n = 0
  · subst n
    have hzero := (hrow 0).const_mul (c := 0) (by norm_num)
    have hzero' : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2)
        (fun _ : Sample d ↦ (0 : ℝ)) 0 := by
      simpa [IndependentSums.IsBigO] using hzero
    have hfun : accumulatedResponseLowRows M 0 =
        (fun _ : Sample d ↦ (0 : ℝ)) := by
      funext omega
      simp [accumulatedResponseLowRows]
    rw [hfun]
    exact hzero'.mono_scale (by
      have htri := IndependentSums.gammaTriangleConst_pos (σ := 2)
      have hs : 0 < holderStoppingS := holderStoppingS_pos
      positivity)
  · let X : ℕ → Sample d → ℝ := fun j omega ↦
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) *
        holderResponseRow M j omega
    let a : ℕ → ℝ := fun j ↦
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ))) * A
    have hsum := Ch04.isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := M.P.toMeasure) (Finset.range n) (X := X) (a := a) (σ := 2)
      (by norm_num) (Finset.nonempty_range_iff.mpr hn)
      (fun j _ ↦ mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hA)
      (fun j _ ↦ by
        let w : ℝ := (3 : ℝ) ^
          (-(holderStoppingS / 4) * ((n : ℝ) - (j : ℝ)))
        have hw : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
        have hscaled := (hrow j).const_mul (c := w) hw
        simpa only [X, a, w, IndependentSums.IsBigO,
          abs_of_nonneg (mul_nonneg hw (holderResponseRow_nonneg M j _))]
          using hscaled)
      (fun j _ ↦ measurable_const.mul (measurable_holderResponseRow M j))
    have hsum' : IndependentSums.IsBigO M.P.toMeasure
        (IndependentSums.gammaSigma 2) (accumulatedResponseLowRows M n)
        (Ch04.gammaTriangleConst 2 * ∑ j ∈ Finset.range n, a j) := by
      simpa only [accumulatedResponseLowRows, X] using hsum
    refine hsum'.mono_scale ?_
    have hweights := sum_responseQuarterWeight_range_le n
    have hnonneg : 0 ≤ Ch04.gammaTriangleConst 2 :=
      (IndependentSums.gammaTriangleConst_pos (σ := 2)).le
    unfold a
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hweights hA.le) hnonneg

/-- Reinsert the retained row means after the residue-class centered sum. -/
theorem sum_holderResponseRow_le_centered_add_mean_bound
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ)
    {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (holderResponseRow M j) A)
    (omega : Sample d) :
    (∑ j ∈ Finset.Icc n m, holderResponseRow M j omega) ≤
      centeredHolderResponseWindow M n m omega +
        ((m + 1 - n : ℕ) : ℝ) *
          (IndependentSums.gammaMomentConst 2 * A) := by
  have hmean : ∀ j : ℕ,
      ∫ eta, holderResponseRow M j eta ∂M.P.toMeasure ≤
        IndependentSums.gammaMomentConst 2 * A := by
    intro j
    exact (integral_nonneg_le_gammaMomentConst_mul_of_isBigOWith_gammaTwo
      hA (measurable_holderResponseRow M j)
      (holderResponseRow_nonneg M j) (hrow j)).2.2
  have hcard : (Finset.Icc n m).card = m + 1 - n := by
    rw [Nat.card_Icc]
  calc
    (∑ j ∈ Finset.Icc n m, holderResponseRow M j omega) =
        centeredHolderResponseWindow M n m omega +
          ∑ j ∈ Finset.Icc n m,
            ∫ eta, holderResponseRow M j eta ∂M.P.toMeasure := by
      unfold centeredHolderResponseWindow centeredHolderResponseRow
      rw [Finset.sum_sub_distrib]
      ring
    _ ≤ centeredHolderResponseWindow M n m omega +
          ∑ _j ∈ Finset.Icc n m,
            IndependentSums.gammaMomentConst 2 * A := by
      gcongr with j hj
      exact hmean j
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- Complete active response bound: centered fluctuation plus the retained
linear mean from Step 3. -/
theorem accumulatedResponseActiveWindow_le_centered_add_mean
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n m : ℕ)
    {A : ℝ} (hA : 0 < A)
    (hrow : ∀ j : ℕ, IndependentSums.IsBigOWith M.P.toMeasure
      (IndependentSums.gammaSigma 2) (holderResponseRow M j) A)
    (omega : Sample d) :
    accumulatedResponseActiveWindow M n m omega ≤
      (8 / holderStoppingS) *
        (centeredHolderResponseWindow M n m omega +
          ((m + 1 - n : ℕ) : ℝ) *
            (IndependentSums.gammaMomentConst 2 * A)) := by
  exact (accumulatedResponseActiveWindow_le_rows M n m omega).trans
    (mul_le_mul_of_nonneg_left
      (sum_holderResponseRow_le_centered_add_mean_bound M n m hA hrow omega)
      (by positivity [holderStoppingS_pos]))

/-- Exact `j<n`/`n≤j≤m` split in `e.split.J.for.minimal.scale`. -/
theorem accumulatedResponseWindowConvolution_eq_low_add_active
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {n m : ℕ} (hnm : n ≤ m)
    (omega : Sample d) :
    accumulatedResponseWindowConvolution M n m omega =
      accumulatedResponseLowWindow M n m omega +
        accumulatedResponseActiveWindow M n m omega := by
  unfold accumulatedResponseWindowConvolution accumulatedResponseLowWindow
    accumulatedResponseActiveWindow accumulatedResponseColumn
  rw [sum_Icc_sum_range_eq_sum_range_sum_filter]
  rw [show Finset.Icc n m = Finset.Ico n (m + 1) by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  exact (Finset.sum_range_add_sum_Ico (f := fun j ↦
    ∑ k ∈ (Finset.Icc n m).filter (fun k ↦ j ≤ k),
      (3 : ℝ) ^ (-(holderStoppingS / 4) * ((k : ℝ) - (j : ℝ))) *
        holderResponseRow M j omega) (by omega : n ≤ m + 1)).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
