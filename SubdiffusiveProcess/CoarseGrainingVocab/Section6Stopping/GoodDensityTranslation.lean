import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance

/-!
# Translation of the good-scale density estimate

This file is the centre-translation adapter used by
`l.min.scale.good.scale`.  The density anchor is sealed but quarantined until
its audit, so `DensityOfGoodScalesInput` records its conclusion byte-for-byte
without importing either the frozen anchor or its provider.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The elementary threshold conversion in the proof of
`l.min.scale.good.scale`: more than `lambda * K` bad indices in an interval
of `K+1` indices forces bad density at least `lambda / 2`. -/
theorem goodDensityFailure_of_badCount_large
    (P : ℕ → Prop) (lambda : ℝ) (hlambda0 : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (m0 K : ℕ)
    (hbad : lambda * K <
      ∑ m ∈ Finset.Icc m0 (m0 + K),
        (1 - if P m then (1 : ℝ) else 0)) :
    (∑ m ∈ Finset.Icc m0 (m0 + K),
        if P m then (1 : ℝ) else 0) / (K + 1) ≤ 1 - lambda / 2 := by
  let I := Finset.Icc m0 (m0 + K)
  let G : ℝ := ∑ m ∈ I, if P m then 1 else 0
  let B : ℝ := ∑ m ∈ I, (1 - if P m then 1 else 0)
  have hcard : (I.card : ℝ) = K + 1 := by
    dsimp only [I]
    rw [Nat.card_Icc, Nat.cast_sub (by omega : m0 ≤ m0 + K + 1), Nat.cast_add]
    push_cast
    ring
  have hpartition : G + B = K + 1 := by
    rw [← hcard]
    dsimp only [G, B]
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x ∈ I, ((if P x then 1 else 0) +
          (1 - if P x then 1 else 0))) = ∑ _x ∈ I, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x _hx
        split_ifs <;> norm_num
      _ = I.card := by simp
  have hBcard : B = ((I.filter fun x ↦ ¬P x).card : ℝ) := by
    dsimp only [B]
    calc
      (∑ x ∈ I, (1 - if P x then 1 else 0)) =
          ∑ x ∈ I, if ¬P x then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        split_ifs <;> norm_num
      _ = ((I.filter fun x ↦ ¬P x).card : ℝ) :=
        Finset.sum_boole (R := ℝ) (fun x ↦ ¬P x) I
  have hB0 : 0 ≤ B := by rw [hBcard]; positivity
  have hBlarge : lambda / 2 * (K + 1) ≤ B := by
    by_cases hsmall : lambda * (K + 1) ≤ 2
    · have hBpos : 0 < B := by
        have : 0 ≤ lambda * K := mul_nonneg hlambda0.le (Nat.cast_nonneg K)
        exact this.trans_lt (by simpa only [B, I] using hbad)
      have hBone : 1 ≤ B := by
        rw [hBcard]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
          intro hzero
          have h := hBpos
          rw [hBcard, hzero] at h
          norm_num at h)
      nlinarith
    · have hK : (1 : ℝ) ≤ K := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
          intro hKzero
          apply hsmall
          simp only [hKzero, Nat.cast_zero, zero_add, mul_one]
          linarith)
      have hthreshold : lambda / 2 * (K + 1) ≤ lambda * K := by
        nlinarith
      exact hthreshold.trans (le_of_lt (by simpa only [B, I] using hbad))
  have hden : (0 : ℝ) < K + 1 := by positivity
  rw [div_le_iff₀ hden]
  change G ≤ (1 - lambda / 2) * (K + 1)
  nlinarith

/-- The exact conclusion of the quarantined `p.density.of.good.scales`.
At promotion this is discharged by one application of the audited export. -/
def DensityOfGoodScalesInput (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s theta epsilon : ℝ,
      s ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 * |Real.log M.delta| ≤ theta →
      ∀ m0 K : ℕ,
        M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
            if omega ∈ goodEvent M none m 0 epsilon s then (1 : ℝ) else 0) /
              (K + 1) ≤ 1 - theta} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
            (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1)))

/-- Translating the centre of every good event in a scale interval is exactly
precomposition by the measure-preserving sample translation. -/
theorem goodDensityFailure_eq_preimage_translate {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s theta epsilon : ℝ)
    (z : Vec d) (m0 K : ℕ) :
    {omega : Sample d | (∑ m ∈ Finset.Icc m0 (m0 + K),
        if omega ∈ goodEvent M none m z epsilon s then (1 : ℝ) else 0) /
          (K + 1) ≤ 1 - theta} =
      translatePotentialSample z ⁻¹'
        {omega : Sample d | (∑ m ∈ Finset.Icc m0 (m0 + K),
          if omega ∈ goodEvent M none m 0 epsilon s then (1 : ℝ) else 0) /
            (K + 1) ≤ 1 - theta} := by
  ext omega
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  have hsum : (∑ m ∈ Finset.Icc m0 (m0 + K),
        if omega ∈ goodEvent M none m z epsilon s then (1 : ℝ) else 0) =
      ∑ m ∈ Finset.Icc m0 (m0 + K),
        if translatePotentialSample z omega ∈ goodEvent M none m 0 epsilon s then
          (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro m _hm
    rw [if_congr (mem_goodEvent_iff_translate_zero M none m epsilon s z omega)
      rfl rfl]
  rw [hsum]

/-- The origin-centred density theorem holds with the same constant and rate
at every deterministic spatial centre. -/
theorem densityOfGoodScalesInput_translated {d : ℕ}
    (hDensity : DensityOfGoodScalesInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s theta epsilon : ℝ,
      s ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 * |Real.log M.delta| ≤ theta →
      ∀ z : Vec d, ∀ m0 K : ℕ,
        M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
            if omega ∈ goodEvent M none m z epsilon s then (1 : ℝ) else 0) /
              (K + 1) ≤ 1 - theta} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
            (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1))) := by
  obtain ⟨C, hC, hbase⟩ := hDensity
  refine ⟨C, hC, ?_⟩
  intro M s theta epsilon hs htheta hepsilon hsmall z m0 K
  rw [goodDensityFailure_eq_preimage_translate M s theta epsilon z m0 K,
    measure_preimage_translatePotentialSample]
  exact hbase M s theta epsilon hs htheta hepsilon hsmall m0 K

/-- One-centre form used immediately before the spatial union bound in
`l.min.scale.good.scale`.  The interval has `K+1` scales, while the stopping
threshold is `lambda * K`, hence the density theorem is applied at
`theta = lambda / 2`. -/
theorem measure_translated_badScaleCount_large_le {d : ℕ}
    (hDensity : DensityOfGoodScalesInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s lambda epsilon : ℝ,
      s ∈ Set.Ioc 0 1 → lambda ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| ≤ lambda / 2 →
      ∀ z : Vec d, ∀ m0 K : ℕ,
        M.P.toMeasure {omega |
            lambda * K < ∑ m ∈ Finset.Icc m0 (m0 + K),
              (1 - if omega ∈ goodEvent M none m z epsilon s then
                (1 : ℝ) else 0)} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
            (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1))) := by
  obtain ⟨C, hC, htranslated⟩ := densityOfGoodScalesInput_translated hDensity
  refine ⟨C, hC, ?_⟩
  intro M s lambda epsilon hs hlambda hepsilon hsmall z m0 K
  have hhalf : lambda / 2 ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨by linarith [hlambda.1], by linarith [hlambda.2]⟩
  calc
    M.P.toMeasure {omega |
        lambda * K < ∑ m ∈ Finset.Icc m0 (m0 + K),
          (1 - if omega ∈ goodEvent M none m z epsilon s then
            (1 : ℝ) else 0)} ≤
      M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
          if omega ∈ goodEvent M none m z epsilon s then (1 : ℝ) else 0) /
            (K + 1) ≤ 1 - lambda / 2} := by
      apply measure_mono
      intro omega homega
      exact goodDensityFailure_of_badCount_large
        (fun m ↦ omega ∈ goodEvent M none m z epsilon s)
        lambda hlambda.1 hlambda.2 m0 K homega
    _ ≤ ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * (lambda / 2) /
          (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1))) :=
      htranslated M s (lambda / 2) epsilon hs hhalf hepsilon hsmall z m0 K

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping
