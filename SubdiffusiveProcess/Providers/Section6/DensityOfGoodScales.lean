module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodEventDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldOneDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldTwoDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.ResponseDensity

@[expose] public section




namespace SubdiffusiveProcess.Providers.Section6

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open Homogenization hiding Vec
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Sample (d : ℕ) := SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

def goodFieldOneEvent {d : ℕ} (m : ℕ) (epsilon s : ℝ) : Set (Sample d) :=
  {ω | GoodFieldOne m 0 epsilon s ω}

def goodFieldTwoEvent {d : ℕ} (m : ℕ) (s : ℝ) : Set (Sample d) :=
  {ω | GoodFieldTwo m 0 s ω}

def goodResponseEvent {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (m : ℕ) (epsilon s : ℝ) : Set (Sample d) :=
  {ω | GoodResponse M none m 0 epsilon s ω}



theorem measure_densityFailure_le_componentDensityFailures {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s theta epsilon : ℝ)
    (m0 K : ℕ) :
    M.P.toMeasure {ω | (∑ m ∈ Finset.Icc m0 (m0 + K),
          if ω ∈ goodEvent M none m 0 epsilon s then (1 : ℝ) else 0) /
            (K + 1) ≤ 1 - theta} ≤
      M.P.toMeasure {ω | theta / 3 ≤ intervalEventDensity
        (fun m => (goodFieldOneEvent (d := d) m epsilon s)ᶜ) m0 K ω} +
      M.P.toMeasure {ω | theta / 3 ≤ intervalEventDensity
        (fun m => (goodFieldTwoEvent (d := d) m s)ᶜ) m0 K ω} +
      M.P.toMeasure {ω | theta / 3 ≤ intervalEventDensity
        (fun m => (goodResponseEvent M m epsilon s)ᶜ) m0 K ω} := by
  let A : ℕ → Set (Sample d) := fun m => goodFieldOneEvent m epsilon s
  let B : ℕ → Set (Sample d) := fun m => goodFieldTwoEvent m s
  let C : ℕ → Set (Sample d) := fun m => goodResponseEvent M m epsilon s
  have h := measure_inter_three_density_failure_le M.P.toMeasure A B C m0 K theta
  have hleft : {ω | (∑ m ∈ Finset.Icc m0 (m0 + K),
        if ω ∈ goodEvent M none m 0 epsilon s then (1 : ℝ) else 0) /
          (K + 1) ≤ 1 - theta} =
      {ω | intervalEventDensity (fun m => A m ∩ B m ∩ C m) m0 K ω ≤
        1 - theta} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have hsum : (∑ m ∈ Finset.Icc m0 (m0 + K),
          if ω ∈ goodEvent M none m 0 epsilon s then (1 : ℝ) else 0) =
        ∑ m ∈ Finset.Icc m0 (m0 + K),
          eventIndicator (A m ∩ B m ∩ C m) ω := by
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hA : GoodFieldOne m 0 epsilon s ω <;>
        by_cases hB : GoodFieldTwo m 0 s ω <;>
        by_cases hC : GoodResponse M none m 0 epsilon s ω <;>
        simp [eventIndicator, A, B, C, goodFieldOneEvent, goodFieldTwoEvent,
          goodResponseEvent, goodEvent, hA, hB, hC]
    rw [hsum]
    rfl
  rw [hleft]
  simpa only [A, B, C] using h



theorem measure_densityFailure_le_of_component_bounds {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s theta epsilon : ℝ)
    (m0 K : ℕ) (tail : ℝ≥0∞)
    (hfieldOne : M.P.toMeasure {ω | theta / 3 ≤ intervalEventDensity
        (fun m => (goodFieldOneEvent (d := d) m epsilon s)ᶜ) m0 K ω} ≤ tail / 4)
    (hfieldTwo : M.P.toMeasure {ω | theta / 3 ≤ intervalEventDensity
        (fun m => (goodFieldTwoEvent (d := d) m s)ᶜ) m0 K ω} ≤ tail / 4)
    (hresponse : M.P.toMeasure {ω | theta / 3 ≤ intervalEventDensity
        (fun m => (goodResponseEvent M m epsilon s)ᶜ) m0 K ω} ≤ tail / 4) :
    M.P.toMeasure {ω | (∑ m ∈ Finset.Icc m0 (m0 + K),
          if ω ∈ goodEvent M none m 0 epsilon s then (1 : ℝ) else 0) /
            (K + 1) ≤ 1 - theta} ≤ tail := by
  calc
    M.P.toMeasure {ω | (∑ m ∈ Finset.Icc m0 (m0 + K),
          if ω ∈ goodEvent M none m 0 epsilon s then (1 : ℝ) else 0) /
            (K + 1) ≤ 1 - theta} ≤
        M.P.toMeasure {ω | theta / 3 ≤ intervalEventDensity
          (fun m => (goodFieldOneEvent (d := d) m epsilon s)ᶜ) m0 K ω} +
        M.P.toMeasure {ω | theta / 3 ≤ intervalEventDensity
          (fun m => (goodFieldTwoEvent (d := d) m s)ᶜ) m0 K ω} +
        M.P.toMeasure {ω | theta / 3 ≤ intervalEventDensity
          (fun m => (goodResponseEvent M m epsilon s)ᶜ) m0 K ω} :=
      measure_densityFailure_le_componentDensityFailures M s theta epsilon m0 K
    _ ≤ tail / 4 + tail / 4 + tail / 4 :=
      add_le_add (add_le_add hfieldOne hfieldTwo) hresponse
    _ ≤ tail := by
      rw [ENNReal.div_eq_inv_mul]
      rw [← add_mul, ← add_mul]
      calc
        ((4 : ℝ≥0∞)⁻¹ + 4⁻¹ + 4⁻¹) * tail ≤ 1 * tail := by
          gcongr
          calc
            (4 : ℝ≥0∞)⁻¹ + 4⁻¹ + 4⁻¹ = 3 * 4⁻¹ := by ring
            _ ≤ 4 * 4⁻¹ := by gcongr; norm_num
            _ = 1 := ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top
        _ = tail := one_mul tail

private theorem ofReal_exp_neg_mul_le_quarter
    {a b w : ℝ} (hb : 1 ≤ b) (hab : 3 * b ≤ a) (hw : 1 ≤ w) :
    ENNReal.ofReal (Real.exp (-a * w)) ≤
      ENNReal.ofReal (Real.exp (-b * w)) / 4 := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.aux_dedup_d216_ofReal_exp_neg_mul_le_quarter (a := a) (b := b) (w := w) (hb := hb) (hab := hab) (hw := hw)

/-- The only square-root conversion in the final density assembly.  Keeping
it separate also keeps the exact-export declaration below a small
elaboration budget. -/
private theorem density_fieldTwo_small
    {C C2 delta s theta epsilon L : ℝ}
    (hC : 0 < C) (hC2 : 0 < C2) (hdelta : 0 < delta)
    (hs : 0 < s) (hs1 : s ≤ 1) (htheta : 0 < theta)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hLhalf : (1 : ℝ) / 2 ≤ L)
    (hCfieldTwo : 384 * C2 ^ 2 ≤ C)
    (hglobalBudget : C * delta ^ 2 * L ≤
      theta * s ^ 6 * epsilon ^ 2) :
    delta ≤ C2⁻¹ * s * Real.sqrt (theta / 3) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.aux_dedup_d082_cutoffDensity_fieldTwo_small (C := C) (C2 := C2) (delta := delta) (s := s) (theta := theta) (epsilon := epsilon) (logDelta := L) (hC := hC) (hC2 := hC2) (hdelta := hdelta) (hs := hs) (hs1 := hs1) (htheta := htheta) (hepsilon := hepsilon) (hepsilon1 := hepsilon1) (hlogHalf := hLhalf) (hCfieldTwo := hCfieldTwo) (hglobalBudget := hglobalBudget)

private theorem density_global_budget
    {C s epsilon delta L theta : ℝ}
    (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hsmall : C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * delta ^ 2 * L ≤ theta) :
    C * delta ^ 2 * L ≤ theta * s ^ 6 * epsilon ^ 2 := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.aux_dedup_d127_cutoffDensity_global_budget (C := C) (s := s) (epsilon := epsilon) (delta := delta) (logDelta := L) (theta := theta) (hs := hs) (hepsilon := hepsilon) (hsmall := hsmall)

theorem density_of_good_scales (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d,
      ∀ s theta epsilon : ℝ,
      s ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 → epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| ≤ theta →
      ∀ m0 K : ℕ,
        M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
            if omega ∈ goodEvent M none m 0 epsilon s then (1 : ℝ) else 0) /
              (K + 1) ≤ 1 - theta} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
            (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1))) := by
  obtain ⟨Cr, hCr, hresponse⟩ :=
    exists_measure_goodResponse_badDensity_le_all d
  let C1 := fieldOneDensityConst d
  let C2 := fieldTwoDensityConst d
  let R2 := fieldTwoRateDenom d
  let C : ℝ := 1 + 32 * (8 : ℝ) ^ 6 * C1 + 10000 * C2 ^ 2 +
    5000 * R2 + 10000 * Cr
  have hC1Def : C1 = fieldOneDensityConst d := rfl
  have hC2Def : C2 = fieldTwoDensityConst d := rfl
  have hR2Def : R2 = fieldTwoRateDenom d := rfl
  have hCDef : C = 1 + 32 * (8 : ℝ) ^ 6 * C1 + 10000 * C2 ^ 2 +
      5000 * R2 + 10000 * Cr := rfl
  have hC1 : 0 < C1 := fieldOneDensityConst_pos d
  have hcardOne : (1 : ℝ) ≤ ((shellCoverShifts d 1).card : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero.mpr (shellCoverShifts_nonempty d 1)))
  have hlogCard : 0 ≤ Real.log ((shellCoverShifts d 1).card : ℝ) :=
    Real.log_nonneg hcardOne
  have hD : 0 < fieldTwoSuffixScaleConst d := by
    unfold fieldTwoSuffixScaleConst
    have hlogTwo : 0 < 1 + Real.log 2 := by
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hbase : 0 < (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
      Real.rpow_pos_of_pos hlogTwo _
    have hcover : 0 ≤ (3 * Real.log ((shellCoverShifts d 1).card : ℝ)) ^
        (2 : ℝ)⁻¹ := Real.rpow_nonneg (by positivity) _
    exact mul_pos (mul_pos (by norm_num)
      (IndependentSums.gammaTriangleConst_pos (σ := 2)))
      (add_pos_of_pos_of_nonneg hbase (mul_nonneg hcover hbase.le))
  have hC2 : 0 < C2 := by
    rw [hC2Def]
    unfold fieldTwoDensityConst
    have hlogTwo : 0 < 1 + Real.log 2 := by
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hR : 0 < fieldTwoRateDenom d := by
      unfold fieldTwoRateDenom
      exact add_pos_of_pos_of_nonneg
        (mul_pos (by norm_num) expFieldMomentDenom_pos)
        (mul_nonneg
          (mul_nonneg (by norm_num) expSequenceConcentrationConst_pos.le)
          (sq_nonneg (fieldTwoSuffixScaleConst d)))
    have hF : 0 ≤ expFieldConcentrationConst d :=
      (expFieldConcentrationConst_pos d).le
    have hE : 0 ≤ expSequenceConcentrationConst :=
      expSequenceConcentrationConst_pos.le
    have hlogTwo : 0 < 1 + Real.log 2 := by
      linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have hnonneg : 0 ≤ 16 * expFieldConcentrationConst d +
        16 * expSequenceConcentrationConst * fieldTwoSuffixScaleConst d +
        2 * fieldTwoSuffixScaleConst d +
        4 * fieldTwoRateDenom d * (1 + Real.log 2) := by positivity
    linarith
  have hR2 : 0 < R2 := by
    rw [hR2Def]
    unfold fieldTwoRateDenom
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by norm_num) expFieldMomentDenom_pos)
      (mul_nonneg
        (mul_nonneg (by norm_num) expSequenceConcentrationConst_pos.le)
        (sq_nonneg (fieldTwoSuffixScaleConst d)))
  have hC : 0 < C := by rw [hCDef]; positivity
  clear_value C1 C2 R2 C
  refine ⟨C, hC, ?_⟩
  intro M s theta epsilon hs htheta hepsilon hsmall m0 K
  have hs0 := hs.1
  have hs1 := hs.2
  have ht0 := htheta.1
  have ht1 := htheta.2
  have he0 := hepsilon.1
  have he1 := hepsilon.2
  have hd := M.shellPrefix.delta_pos
  have hdhalf := M.shellPrefix.delta_le_half
  have hlogneg : Real.log M.delta < 0 :=
    Real.log_neg hd (hdhalf.trans_lt (by norm_num))
  have hL : 0 < |Real.log M.delta| := abs_pos.mpr hlogneg.ne
  have hLhalf : (1 : ℝ) / 2 ≤ |Real.log M.delta| := by
    have hm : Real.log M.delta ≤ Real.log (1 / 2 : ℝ) :=
      Real.log_le_log hd hdhalf
    have heq : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
      simp
    rw [heq] at hm
    rw [abs_of_neg hlogneg]
    linarith [Real.log_two_gt_d9]
  let t := s / 8
  let eta := theta / 3
  have ht : t ∈ Set.Ioc 0 1 := ⟨by dsimp only [t]; positivity,
    by dsimp only [t]; linarith⟩
  have heta : eta ∈ Set.Ioc 0 1 := ⟨by dsimp only [eta]; positivity,
    by dsimp only [eta]; linarith⟩
  have hCfield : 6 * (8 : ℝ) ^ 6 * C1 ≤ C := by
    rw [hCDef]
    have hrest : 0 ≤ 10000 * C2 ^ 2 + 5000 * R2 + 10000 * Cr := by positivity
    nlinarith only [hC1, hrest]
  have hCfieldMoment : 18 * (8 : ℝ) ^ 6 * C1 ≤ C := by
    rw [hCDef]
    have hrest : 0 ≤ 10000 * C2 ^ 2 + 5000 * R2 + 10000 * Cr := by positivity
    nlinarith only [hC1, hrest]
  have hCfieldTwo : 384 * C2 ^ 2 ≤ C := by
    rw [hCDef]
    have hnonneg : 0 ≤ 32 * (8 : ℝ) ^ 6 * C1 := by positivity
    have hnonneg' : 0 ≤ 5000 * R2 + 10000 * Cr := by positivity
    nlinarith only [sq_nonneg C2, hnonneg, hnonneg']
  have hCfieldRate : 2304 * R2 ≤ C := by
    rw [hCDef]
    have hnonneg : 0 ≤ 32 * (8 : ℝ) ^ 6 * C1 + 10000 * C2 ^ 2 := by
      positivity
    have hnonneg' : 0 ≤ 10000 * Cr := by positivity
    nlinarith only [hR2, hnonneg, hnonneg']
  have hCresponse : 4608 * Cr ≤ C := by
    rw [hCDef]
    have hnonneg : 0 ≤ 32 * (8 : ℝ) ^ 6 * C1 + 10000 * C2 ^ 2 +
        5000 * R2 := by positivity
    nlinarith only [hCr, hnonneg]
  have hfieldSmall : C1 * t ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 *
      M.delta ^ 2 ≤ eta := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    have hcoef : 3 * (8 : ℝ) ^ 6 * C1 ≤ C * |Real.log M.delta| := by
      calc
        3 * (8 : ℝ) ^ 6 * C1 ≤ C / 2 := by linarith only [hCfield]
        _ ≤ C * |Real.log M.delta| := by
          simpa only [mul_one, one_mul, div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left hLhalf hC.le
    have hcommon : 0 ≤ s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 := by positivity
    calc
      (C1 * t ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2) * 3 =
          (3 * (8 : ℝ) ^ 6 * C1) *
            (s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2) := by
        dsimp only [t]
        rw [div_zpow]
        norm_num
        ring
      _ ≤ (C * |Real.log M.delta|) *
          (s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2) :=
        mul_le_mul_of_nonneg_right hcoef hcommon
      _ = C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| := by ring
      _ ≤ theta := hsmall
  have hresponseSmall : Cr * t ^ (-3 : ℤ) * epsilon⁻¹ ^ 2 *
      M.delta ^ 2 * |Real.log M.delta| ≤ eta := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    have hs3 : s ^ 3 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hs0.le hs1 3
    have hcoef : 3 * (8 : ℝ) ^ 3 * Cr * s ^ 3 ≤ C := by
      have hmul := mul_le_mul_of_nonneg_left hs3
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 * 8 ^ 3) hCr.le)
      nlinarith only [hmul, hCresponse, hCr]
    have hcommon : 0 ≤ s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 *
        M.delta ^ 2 * |Real.log M.delta| := by positivity
    calc
      (Cr * t ^ (-3 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta|) * 3 =
        (3 * (8 : ℝ) ^ 3 * Cr * s ^ 3) *
          (s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta|) := by
          dsimp only [t]
          rw [div_zpow]
          norm_num
          field_simp [hs0.ne']; ring
      _ ≤ C * (s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta|) := mul_le_mul_of_nonneg_right hcoef hcommon
      _ = C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| := by ring
      _ ≤ theta := hsmall
  have hglobalBudget : C * M.delta ^ 2 * |Real.log M.delta| ≤
      theta * s ^ 6 * epsilon ^ 2 :=
    density_global_budget hs0 he0 hsmall
  have hfieldTwoSmall : M.delta ≤ C2⁻¹ * s * Real.sqrt eta := by
    dsimp only [eta]
    exact density_fieldTwo_small hC hC2 hd hs0 hs1 ht0 he0 he1 hLhalf
      hCfieldTwo hglobalBudget
  have hfield := measure_goodFieldOne_badDensity_le M ht.1 ht.2 heta.1 heta.2
    he0 he1 (by simpa only [hC1Def] using hfieldSmall) m0 K
  have hfieldTwo := measure_goodFieldTwo_badDensity_le M hs0 hs1 heta.1 heta.2
    (by simpa only [hC2Def] using hfieldTwoSmall) m0 K
  have hresp := hresponse M t eta epsilon ht heta hepsilon hresponseSmall m0 K
  let b : ℝ := s ^ 6 * epsilon ^ 2 * theta /
    (C * M.delta ^ 2 * |Real.log M.delta|)
  let a1 : ℝ := t ^ 6 * epsilon ^ 2 * eta / (C1 * M.delta ^ 2)
  let a2 : ℝ := s ^ 2 * eta / (2 * R2 * M.delta ^ 2)
  let ar : ℝ := t ^ 3 * epsilon ^ 2 * eta /
    (Cr * M.delta ^ 2 * |Real.log M.delta|)
  have hb : 1 ≤ b := by
    dsimp only [b]
    rw [le_div_iff₀ (by positivity : 0 < C * M.delta ^ 2 * |Real.log M.delta|)]
    simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using hglobalBudget
  have ha1 : 3 * b ≤ a1 := by
    dsimp only [b, a1, t, eta]
    field_simp [hC.ne', hC1.ne', hd.ne', hL.ne']
    have hhalf : 9 * (8 : ℝ) ^ 6 * C1 ≤ C / 2 := by
      linarith only [hCfieldMoment]
    rw [show (3 : ℝ) ^ 2 = 9 by norm_num]
    exact hhalf.trans (by simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hLhalf hC.le)
  have ha2 : 3 * b ≤ a2 := by
    dsimp only [b, a2, eta]
    field_simp [hC.ne', hR2.ne', hd.ne', hL.ne']
    have hs4e : s ^ 4 * epsilon ^ 2 ≤ 1 := by
      have hs4 : s ^ 4 ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ hs0.le hs1 4
      have he2 : epsilon ^ 2 ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ he0.le he1 2
      simpa only [one_mul] using mul_le_mul hs4 he2 (sq_nonneg epsilon) zero_le_one
    have hhalf : 18 * R2 ≤ C / 2 := by
      linarith only [hCfieldRate, hR2]
    have hbound : 18 * R2 ≤ C * |Real.log M.delta| :=
      hhalf.trans (by simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hLhalf hC.le)
    have hmul := mul_le_mul_of_nonneg_left hs4e
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) hR2.le)
    nlinarith only [hbound, hmul]
  have har : 3 * b ≤ ar := by
    dsimp only [b, ar, t, eta]
    field_simp [hC.ne', hCr.ne', hd.ne', hL.ne']
    have hs3 : s ^ 3 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hs0.le hs1 3
    nlinarith only [hCresponse, hCr, hLhalf, hC, hs0, he0, ht0,
      mul_le_mul_of_nonneg_left hs3 hCr.le]
  let w : ℝ := (K : ℝ) + 1
  have hw : 1 ≤ w := by
    dsimp only [w]
    have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  have height : 8 * t = s := by
    dsimp only [t]
    ring
  rw [height] at hfield hresp
  let tail : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-b * w))
  have hfieldQuarter : M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
      (fun m => (goodFieldOneEvent (d := d) m epsilon s)ᶜ) m0 K omega} ≤
      tail / 4 := by
    have hfield' : M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
        (fun m => (goodFieldOneEvent (d := d) m epsilon s)ᶜ) m0 K omega} ≤
        ENNReal.ofReal (Real.exp (-a1 * w)) := by
      simpa only [goodFieldOneEvent, hC1Def, t, eta, a1, w, Nat.cast_add,
        Nat.cast_one, mul_one] using hfield
    refine hfield'.trans ?_
    have hq := ofReal_exp_neg_mul_le_quarter hb ha1 hw
    simpa only [t, eta, a1, b, w, tail, mul_one, Nat.cast_add, Nat.cast_one]
      using hq
  have hfieldTwoQuarter : M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
      (fun m => (goodFieldTwoEvent (d := d) m s)ᶜ) m0 K omega} ≤
      tail / 4 := by
    refine hfieldTwo.trans ?_
    have hq := ofReal_exp_neg_mul_le_quarter hb ha2 hw
    simpa only [eta, a2, b, w, tail, hR2Def, mul_one, Nat.cast_add, Nat.cast_one] using hq
  have hresponseQuarter : M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
      (fun m => (goodResponseEvent M m epsilon s)ᶜ) m0 K omega} ≤
      tail / 4 := by
    have hresp' : M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
        (fun m => (goodResponseEvent M m epsilon s)ᶜ) m0 K omega} ≤
        ENNReal.ofReal (Real.exp (-ar * w)) := by
      simpa only [goodResponseEvent, t, eta, ar, w, Nat.cast_add, Nat.cast_one,
        mul_one] using hresp
    refine hresp'.trans ?_
    have hq := ofReal_exp_neg_mul_le_quarter hb har hw
    simpa only [t, eta, ar, b, w, tail, mul_one, Nat.cast_add, Nat.cast_one]
      using hq
  have hfinal := measure_densityFailure_le_of_component_bounds M s theta epsilon m0 K tail
    hfieldQuarter hfieldTwoQuarter hresponseQuarter
  simpa only [tail, b, w, Nat.cast_add, Nat.cast_one] using hfinal

end

end SubdiffusiveProcess.Providers.Section6
