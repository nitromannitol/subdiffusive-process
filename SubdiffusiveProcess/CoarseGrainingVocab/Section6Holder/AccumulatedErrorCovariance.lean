import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.RefinedLocalMathcalE

/-!
# Translation covariance of the accumulated error

The frozen `accumulatedError` carries its spatial centre explicitly.  This
module identifies that carrier with the origin-centred error of the translated
sample, so the origin-centred good-scale proposition can be used at every
Hölder iteration centre.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open Homogenization hiding Vec
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem vectorSupNormOn_comp_add {d : ℕ}
    (z : Vec d) (W : Set (Vec d)) (f : Vec d → Vec d) :
    vectorSupNormOn W (fun x ↦ f (x + z)) =
      vectorSupNormOn ((fun p ↦ z + p) '' W) f := by
  unfold vectorSupNormOn
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x + z, ⟨x, hx, add_comm z x⟩, rfl⟩
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    congr 2
    exact add_comm z x

private theorem vectorSupNormOn_translatedCube_comp_add {d : ℕ}
    (z y : Vec d) (k : ℤ) (f : Vec d → Vec d) :
    vectorSupNormOn (translatedCube d k y) (fun x ↦ f (x + z)) =
      vectorSupNormOn (translatedCube d k (z + y)) f := by
  rw [vectorSupNormOn_comp_add,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.image_add_left_translatedCube]

private theorem responseSet_translate {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    {r : ℝ | ∃ j l : ℕ, j ≤ m ∧ l + 2 ≤ j ∧
      ∃ y : Vec d, OnTriadicGrid l (y - 0) ∧
        y - 0 ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
          Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
            vecNormSq e = 1 ∧ t = section6Response M l
              (min l (cutoff.getD l)) (translatePotentialSample z omega) y e}) 1)} =
    {r : ℝ | ∃ j l : ℕ, j ≤ m ∧ l + 2 ≤ j ∧
      ∃ y : Vec d, OnTriadicGrid l (y - z) ∧
        y - z ∈ cube d j \ cube d (j - 1) ∧
        r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (l : ℝ))) *
          Real.sqrt (min (sSup {t : ℝ | ∃ e : Vec d,
            vecNormSq e = 1 ∧ t = section6Response M l
              (min l (cutoff.getD l)) omega y e}) 1)} := by
  ext r
  constructor
  · rintro ⟨j, l, hjm, hlj, y, hygrid, hyann, rfl⟩
    refine ⟨j, l, hjm, hlj, z + y, ?_, ?_, ?_⟩
    · simpa only [add_sub_cancel_left, sub_zero] using hygrid
    · simpa only [add_sub_cancel_left, sub_zero] using hyann
    · congr 3
      congr 1
      ext t
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, he, rfl⟩
        exact ⟨e, he, by
          rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.section6Response_translatePotentialSample]⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨e, he, by
          rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.section6Response_translatePotentialSample]⟩
  · rintro ⟨j, l, hjm, hlj, y, hygrid, hyann, rfl⟩
    refine ⟨j, l, hjm, hlj, y - z, ?_, ?_, ?_⟩
    · simpa only [sub_zero] using hygrid
    · simpa only [sub_zero] using hyann
    · congr 3
      congr 1
      ext t
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨e, he, rfl⟩
        refine ⟨e, he, ?_⟩
        rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.section6Response_translatePotentialSample]
        congr 2
        abel
      · rintro ⟨e, he, rfl⟩
        refine ⟨e, he, ?_⟩
        rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.section6Response_translatePotentialSample]
        congr 2
        abel

/-- Exact covariance of the literal accumulated error. -/
theorem accumulatedError_translatePotentialSample {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : Sample d) :
    accumulatedError M cutoff m 0 s (translatePotentialSample z omega) =
      accumulatedError M cutoff m z s omega := by
  unfold accumulatedError
  rw [responseSet_translate M cutoff s m z omega]
  have hshell :
      sSup {r : ℝ | ∃ j ≤ m,
        r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
          supNormOn (translatedCube d (m : ℤ) 0)
            (shellBlock m j (translatePotentialSample z omega))} =
      sSup {r : ℝ | ∃ j ≤ m,
        r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
          supNormOn (translatedCube d (m : ℤ) z) (shellBlock m j omega)} := by
    congr 1
    ext r
    simp only [Set.mem_setOf_eq]
    refine exists_congr fun j ↦ and_congr_right fun _ ↦ ?_
    have hfun : shellBlock m j (translatePotentialSample z omega) =
        fun x ↦ shellBlock m j omega (x + z) := by
      funext x
      exact shellBlock_translatePotentialSample m j omega z x
    rw [hfun,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.supNormOn_translatedCube_comp_add]
    simp only [add_zero]
  rw [hshell]
  have hzero : supNormOn (translatedCube d (m : ℤ) 0)
      (translatePotentialSample z omega 0) =
      supNormOn (translatedCube d (m : ℤ) z) (omega 0) := by
    have hfun : (translatePotentialSample z omega 0 : Vec d → ℝ) =
        fun x ↦ omega 0 (x + z) := rfl
    rw [hfun,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.supNormOn_translatedCube_comp_add,
      add_zero]
  rw [hzero]
  congr 1
  apply tsum_congr
  intro j
  split_ifs
  · congr 1
    have hfun : shellGradient (translatePotentialSample z omega j) =
        fun x ↦ shellGradient (omega j) (x + z) := by
      rfl
    rw [hfun, vectorSupNormOn_translatedCube_comp_add]
    simp only [add_zero]
  · rfl

/-- Local translated form of the refined good-scale error cap. -/
theorem exists_section6HomogenizationError_le_min_accumulatedError_local (d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      ∀ L m : ℕ, m ≤ L → ∀ omega z,
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
          omega ∈ goodEvent M none m z epsilon s →
            section6HomogenizationError M s L m omega z ≤
              K * min epsilon (s⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
                accumulatedError M none m z s omega) := by
  obtain ⟨K, hK, horigin⟩ := exists_section6HomogenizationError_le_min_accumulatedError d
  refine ⟨K, hK, ?_⟩
  intro M s hs L m hmL omega z epsilon hepsilon hgood
  have hgood0 : translatePotentialSample z omega ∈
      goodEvent M none m 0 epsilon s :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.mem_goodEvent_translatePotentialSample
      M none m 0 epsilon s z omega).2 (by simpa only [add_zero] using hgood)
  have h := horigin M s hs L m hmL (translatePotentialSample z omega)
    epsilon hepsilon hgood0
  rw [← SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.section6HomogenizationError_eq_translate_zero,
    accumulatedError_translatePotentialSample] at h
  exact h

/-- Fixed-`s0` form used verbatim by the Hölder recurrence.  The factor
`s0⁻¹ = 32` is absorbed into the dimension-only constant, leaving the
manuscript bracket `delta² + epsilon⁸ + accumulatedError`. -/
theorem exists_holderSection6Error_le_recurrenceMin (d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      64 * M.delta ^ 2 ≤ Section6Stopping.holderStoppingS →
      ∀ L m : ℕ, m ≤ L → ∀ omega z,
        ∀ epsilon ∈ Set.Icc
            (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2) 1,
          omega ∈ goodEvent M none m z epsilon
              Section6Stopping.holderStoppingS →
            section6HomogenizationError M Section6Stopping.holderStoppingS
                L m omega z ≤
              K * min epsilon (M.delta ^ 2 + epsilon ^ 8 +
                accumulatedError M none m z Section6Stopping.holderStoppingS omega) := by
  obtain ⟨K, hK, hlocal⟩ :=
    exists_section6HomogenizationError_le_min_accumulatedError_local d
  refine ⟨32 * K, by positivity, ?_⟩
  intro M hsmall L m hmL omega z epsilon hepsilon hgood
  have hs : Section6Stopping.holderStoppingS ∈
      Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ) := by
    constructor
    · exact hsmall
    · rw [Section6Stopping.holderStoppingS]
      norm_num
  have h := hlocal M Section6Stopping.holderStoppingS hs L m hmL omega z
    epsilon hepsilon hgood
  let E := accumulatedError M none m z Section6Stopping.holderStoppingS omega
  let B := M.delta ^ 2 + epsilon ^ 8 + E
  have hE0 : 0 ≤ E := accumulatedError_nonneg M none
    Section6Stopping.holderStoppingS m z omega
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hepsilon0 : 0 ≤ epsilon := by
    have hs0 : 0 ≤ Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 := by
      exact mul_nonneg (inv_nonneg.mpr Section6Stopping.holderStoppingS_pos.le)
        (sq_nonneg _)
    exact hs0.trans hepsilon.1
  have hbracket : Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 +
      epsilon ^ 8 + E ≤ 32 * B := by
    rw [Section6Stopping.holderStoppingS]
    norm_num
    dsimp only [B]
    nlinarith [sq_nonneg M.delta, pow_nonneg hepsilon0 8, hE0]
  have hmin : min epsilon
      (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E) ≤
      32 * min epsilon B := by
    rcases le_total epsilon B with heB | hBe
    · rw [min_eq_left heB]
      have hleft : epsilon ≤
          Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 + epsilon ^ 8 + E := by
        apply heB.trans
        rw [Section6Stopping.holderStoppingS]
        norm_num
        dsimp only [B]
        nlinarith [sq_nonneg M.delta]
      rw [min_eq_left hleft]
      nlinarith
    · rw [min_eq_right hBe]
      exact (min_le_right _ _).trans (hbracket.trans_eq (by ring))
  have hpush := mul_le_mul_of_nonneg_left hmin hK.le
  dsimp only [E, B] at h hpush ⊢
  calc
    section6HomogenizationError M Section6Stopping.holderStoppingS L m omega z ≤
        K * min epsilon
          (Section6Stopping.holderStoppingS⁻¹ * M.delta ^ 2 + epsilon ^ 8 +
            accumulatedError M none m z Section6Stopping.holderStoppingS omega) := h
    _ ≤ K * (32 * min epsilon (M.delta ^ 2 + epsilon ^ 8 +
          accumulatedError M none m z Section6Stopping.holderStoppingS omega)) := hpush
    _ = 32 * K * min epsilon (M.delta ^ 2 + epsilon ^ 8 +
          accumulatedError M none m z Section6Stopping.holderStoppingS omega) := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
