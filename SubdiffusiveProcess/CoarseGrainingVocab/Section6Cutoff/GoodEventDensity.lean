module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldOneDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Density.FieldTwoDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.GoodDensityTranslation

@[expose] public section

/-!
# Finite-cutoff good-event density assembly
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

def cutoffGoodFieldOneEvent {d : ℕ}
    (m : ℕ) (epsilon s : ℝ) : Set (Sample d) :=
  {omega | GoodFieldOne m 0 epsilon s omega}

def cutoffGoodFieldTwoEvent {d : ℕ}
    (m : ℕ) (s : ℝ) : Set (Sample d) :=
  {omega | GoodFieldTwo m 0 s omega}

def cutoffGoodResponseEvent {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (epsilon s : ℝ) : Set (Sample d) :=
  {omega | GoodResponse M (some L) m 0 epsilon s omega}

theorem measure_cutoffDensityFailure_le_componentDensityFailures {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (s theta epsilon : ℝ) (m0 K : ℕ) :
    M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
          if omega ∈ goodEvent M (some L) m 0 epsilon s then
            (1 : ℝ) else 0) / (K + 1) ≤ 1 - theta} ≤
      M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
        (fun m => (cutoffGoodFieldOneEvent (d := d) m epsilon s)ᶜ) m0 K omega} +
      M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
        (fun m => (cutoffGoodFieldTwoEvent (d := d) m s)ᶜ) m0 K omega} +
      M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
        (fun m => (cutoffGoodResponseEvent M L m epsilon s)ᶜ) m0 K omega} := by
  let A : ℕ → Set (Sample d) := fun m =>
    cutoffGoodFieldOneEvent m epsilon s
  let B : ℕ → Set (Sample d) := fun m => cutoffGoodFieldTwoEvent m s
  let C : ℕ → Set (Sample d) := fun m =>
    cutoffGoodResponseEvent M L m epsilon s
  have h := measure_inter_three_density_failure_le M.P.toMeasure A B C m0 K theta
  have hleft : {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
        if omega ∈ goodEvent M (some L) m 0 epsilon s then
          (1 : ℝ) else 0) / (K + 1) ≤ 1 - theta} =
      {omega | intervalEventDensity (fun m => A m ∩ B m ∩ C m)
        m0 K omega ≤ 1 - theta} := by
    ext omega
    simp only [Set.mem_ofPred_eq]
    have hsum : (∑ m ∈ Finset.Icc m0 (m0 + K),
          if omega ∈ goodEvent M (some L) m 0 epsilon s then
            (1 : ℝ) else 0) =
        ∑ m ∈ Finset.Icc m0 (m0 + K),
          eventIndicator (A m ∩ B m ∩ C m) omega := by
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hA : GoodFieldOne m 0 epsilon s omega <;>
        by_cases hB : GoodFieldTwo m 0 s omega <;>
        by_cases hC : GoodResponse M (some L) m 0 epsilon s omega <;>
        simp [eventIndicator, A, B, C, cutoffGoodFieldOneEvent,
          cutoffGoodFieldTwoEvent, cutoffGoodResponseEvent, goodEvent,
          hA, hB, hC]
    rw [hsum]
    rfl
  rw [hleft]
  simpa only [A, B, C] using h

theorem measure_cutoffDensityFailure_le_of_component_bounds {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (s theta epsilon : ℝ) (m0 K : ℕ) (tail : ℝ≥0∞)
    (hfieldOne : M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
        (fun m => (cutoffGoodFieldOneEvent (d := d) m epsilon s)ᶜ) m0 K omega}
          ≤ tail / 4)
    (hfieldTwo : M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
        (fun m => (cutoffGoodFieldTwoEvent (d := d) m s)ᶜ) m0 K omega}
          ≤ tail / 4)
    (hresponse : M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
        (fun m => (cutoffGoodResponseEvent M L m epsilon s)ᶜ) m0 K omega}
          ≤ tail / 4) :
    M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
          if omega ∈ goodEvent M (some L) m 0 epsilon s then
            (1 : ℝ) else 0) / (K + 1) ≤ 1 - theta} ≤ tail := by
  calc
    _ ≤
        M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
          (fun m => (cutoffGoodFieldOneEvent (d := d) m epsilon s)ᶜ) m0 K omega} +
        M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
          (fun m => (cutoffGoodFieldTwoEvent (d := d) m s)ᶜ) m0 K omega} +
        M.P.toMeasure {omega | theta / 3 ≤ intervalEventDensity
          (fun m => (cutoffGoodResponseEvent M L m epsilon s)ᶜ) m0 K omega} :=
      measure_cutoffDensityFailure_le_componentDensityFailures
        M L s theta epsilon m0 K
    _ ≤ tail / 4 + tail / 4 + tail / 4 :=
      add_le_add (add_le_add hfieldOne hfieldTwo) hresponse
    _ ≤ tail := by
      rw [ENNReal.div_eq_inv_mul, ← add_mul, ← add_mul]
      calc
        ((4 : ℝ≥0∞)⁻¹ + 4⁻¹ + 4⁻¹) * tail ≤ 1 * tail := by
          gcongr
          calc
            (4 : ℝ≥0∞)⁻¹ + 4⁻¹ + 4⁻¹ = 3 * 4⁻¹ := by ring
            _ ≤ 4 * 4⁻¹ := by gcongr; norm_num
            _ = 1 := ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top
        _ = tail := one_mul tail

theorem aux_dedup_d216_ofReal_exp_neg_mul_le_quarter
    {a b w : ℝ} (hb : 1 ≤ b) (hab : 3 * b ≤ a) (hw : 1 ≤ w) :
    ENNReal.ofReal (Real.exp (-a * w)) ≤
      ENNReal.ofReal (Real.exp (-b * w)) / 4 := by
  have hexpTwo : 4 ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  have hnegTwo : Real.exp (-2) ≤ (1 : ℝ) / 4 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_le_inv₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 4)).2 hexpTwo
  have hbw : 1 ≤ b * w := by
    simpa only [one_mul] using
      mul_le_mul hb hw zero_le_one (by linarith : 0 ≤ b)
  have hexponent : -a * w ≤ -b * w - 2 := by
    have hmul := mul_le_mul_of_nonneg_right hab (by linarith : 0 ≤ w)
    nlinarith
  have hreal : Real.exp (-a * w) ≤ Real.exp (-b * w) / 4 := by
    calc
      Real.exp (-a * w) ≤ Real.exp (-b * w - 2) :=
        Real.exp_le_exp.2 hexponent
      _ = Real.exp (-b * w) * Real.exp (-2) := by
        rw [← Real.exp_add]
        ring_nf
      _ ≤ Real.exp (-b * w) * (1 / 4) :=
        mul_le_mul_of_nonneg_left hnegTwo (Real.exp_pos _).le
      _ = Real.exp (-b * w) / 4 := by ring
  calc
    ENNReal.ofReal (Real.exp (-a * w)) ≤
        ENNReal.ofReal (Real.exp (-b * w) / 4) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Real.exp (-b * w)) / 4 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num

private theorem ofReal_exp_neg_mul_le_quarter
    {a b w : ℝ} (hb : 1 ≤ b) (hab : 3 * b ≤ a) (hw : 1 ≤ w) :
    ENNReal.ofReal (Real.exp (-a * w)) ≤
      ENNReal.ofReal (Real.exp (-b * w)) / 4 := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.aux_dedup_d216_ofReal_exp_neg_mul_le_quarter (a := a) (b := b) (w := w) (hb := hb) (hab := hab) (hw := hw)

theorem aux_dedup_d082_cutoffDensity_fieldTwo_small
    {C C2 delta s theta epsilon logDelta : ℝ}
    (hC : 0 < C) (hC2 : 0 < C2) (hdelta : 0 < delta)
    (hs : 0 < s) (hs1 : s ≤ 1) (htheta : 0 < theta)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hlogHalf : (1 : ℝ) / 2 ≤ logDelta)
    (hCfieldTwo : 384 * C2 ^ 2 ≤ C)
    (hglobalBudget : C * delta ^ 2 * logDelta ≤
      theta * s ^ 6 * epsilon ^ 2) :
    delta ≤ C2⁻¹ * s * Real.sqrt (theta / 3) := by
  apply (sq_le_sq₀ hdelta.le (by positivity)).mp
  have hs62 : s ^ 6 ≤ s ^ 2 := by
    have hs4 : s ^ 4 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hs.le hs1 4
    nlinarith [mul_le_mul_of_nonneg_right hs4 (sq_nonneg s)]
  have heps2 : epsilon ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      pow_le_pow_left₀ hepsilon.le hepsilon1 2
  have hleft : 3 * C2 ^ 2 * delta ^ 2 ≤ C * delta ^ 2 * logDelta := by
    have hcoef : 3 * C2 ^ 2 ≤ C * logDelta := by
      calc
        3 * C2 ^ 2 ≤ C / 2 := by nlinarith [hCfieldTwo]
        _ ≤ C * logDelta := by
          have := mul_le_mul_of_nonneg_left hlogHalf hC.le
          nlinarith
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_right hcoef (sq_nonneg delta)
  have hright : theta * s ^ 6 * epsilon ^ 2 ≤ theta * s ^ 2 := by
    have hpow : s ^ 6 * epsilon ^ 2 ≤ s ^ 2 := by
      calc
        s ^ 6 * epsilon ^ 2 ≤ s ^ 6 * 1 :=
          mul_le_mul_of_nonneg_left heps2 (pow_nonneg hs.le 6)
        _ ≤ s ^ 2 := by simpa only [mul_one] using hs62
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow htheta.le
  have hsq : 3 * C2 ^ 2 * delta ^ 2 ≤ theta * s ^ 2 :=
    hleft.trans (hglobalBudget.trans hright)
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ theta / 3)]
  field_simp [hC2.ne']
  nlinarith

private theorem cutoffDensity_fieldTwo_small
    {C C2 delta s theta epsilon logDelta : ℝ}
    (hC : 0 < C) (hC2 : 0 < C2) (hdelta : 0 < delta)
    (hs : 0 < s) (hs1 : s ≤ 1) (htheta : 0 < theta)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hlogHalf : (1 : ℝ) / 2 ≤ logDelta)
    (hCfieldTwo : 384 * C2 ^ 2 ≤ C)
    (hglobalBudget : C * delta ^ 2 * logDelta ≤
      theta * s ^ 6 * epsilon ^ 2) :
    delta ≤ C2⁻¹ * s * Real.sqrt (theta / 3) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.aux_dedup_d082_cutoffDensity_fieldTwo_small (C := C) (C2 := C2) (delta := delta) (s := s) (theta := theta) (epsilon := epsilon) (logDelta := logDelta) (hC := hC) (hC2 := hC2) (hdelta := hdelta) (hs := hs) (hs1 := hs1) (htheta := htheta) (hepsilon := hepsilon) (hepsilon1 := hepsilon1) (hlogHalf := hlogHalf) (hCfieldTwo := hCfieldTwo) (hglobalBudget := hglobalBudget)

theorem aux_dedup_d127_cutoffDensity_global_budget
    {C s epsilon delta logDelta theta : ℝ}
    (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hsmall : C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * delta ^ 2 *
      logDelta ≤ theta) :
    C * delta ^ 2 * logDelta ≤ theta * s ^ 6 * epsilon ^ 2 := by
  have hm := mul_le_mul_of_nonneg_right hsmall
    (mul_nonneg (pow_nonneg hs.le 6) (sq_nonneg epsilon))
  calc
    C * delta ^ 2 * logDelta =
        (C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * delta ^ 2 * logDelta) *
          (s ^ 6 * epsilon ^ 2) := by
      rw [zpow_neg]
      field_simp [hs.ne', hepsilon.ne']
    _ ≤ theta * (s ^ 6 * epsilon ^ 2) := hm
    _ = theta * s ^ 6 * epsilon ^ 2 := by ring

private theorem cutoffDensity_global_budget
    {C s epsilon delta logDelta theta : ℝ}
    (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hsmall : C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * delta ^ 2 *
      logDelta ≤ theta) :
    C * delta ^ 2 * logDelta ≤ theta * s ^ 6 * epsilon ^ 2 := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.aux_dedup_d127_cutoffDensity_global_budget (C := C) (s := s) (epsilon := epsilon) (delta := delta) (logDelta := logDelta) (theta := theta) (hs := hs) (hepsilon := hepsilon) (hsmall := hsmall)

private theorem aux_heartbeat_cutoff_rate_compare
    {x y C D E L : ℝ} (hC : 0 < C) (hD : 0 < D)
    (hE : 0 < E) (hL : 0 < L)
    (hbound : 3 * E * x ≤ C * L * y) :
    3 * (x / (C * D * L)) ≤ y / (E * D) := by
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos (mul_pos hC hD) hL) (mul_pos hE hD)).2
  calc
    (3 * x) * (E * D) = (3 * E * x) * D := by ring
    _ ≤ (C * L * y) * D := mul_le_mul_of_nonneg_right hbound hD.le
    _ = y * (C * D * L) := by ring

private theorem aux_heartbeat_cutoff_density_rates
    {C C1 R2 Cr s epsilon theta delta logDelta : ℝ}
    (hC : 0 < C) (hC1 : 0 < C1) (hR2 : 0 < R2) (hCr : 0 < Cr)
    (hs : 0 < s) (hs1 : s ≤ 1) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (ht : 0 < theta) (hd : 0 < delta) (hL : 0 < logDelta)
    (hLhalf : (1 : ℝ) / 2 ≤ logDelta)
    (hfield : 18 * (8 : ℝ) ^ 6 * C1 ≤ C)
    (hfieldRate : 2304 * R2 ≤ C) (hresponse : 4608 * Cr ≤ C) :
    3 * (s ^ 6 * epsilon ^ 2 * theta / (C * delta ^ 2 * logDelta)) ≤
        (s / 8) ^ 6 * epsilon ^ 2 * (theta / 3) / (C1 * delta ^ 2) ∧
    3 * (s ^ 6 * epsilon ^ 2 * theta / (C * delta ^ 2 * logDelta)) ≤
        s ^ 2 * (theta / 3) / (2 * R2 * delta ^ 2) ∧
    3 * (s ^ 6 * epsilon ^ 2 * theta / (C * delta ^ 2 * logDelta)) ≤
        (s / 8) ^ 3 * epsilon ^ 2 * (theta / 3) / (Cr * delta ^ 2 * logDelta) := by
  have hD : 0 < delta ^ 2 := sq_pos_of_pos hd
  have hCL : C / 2 ≤ C * logDelta := by
    have hm := mul_le_mul_of_nonneg_left hLhalf hC.le
    linarith only [hm]
  refine ⟨?_, ?_, ?_⟩
  · apply aux_heartbeat_cutoff_rate_compare hC hD hC1 hL
    have hcoef : 9 * (8 : ℝ) ^ 6 * C1 ≤ C * logDelta := by
      exact (by linarith only [hfield] : 9 * (8 : ℝ) ^ 6 * C1 ≤ C / 2).trans hCL
    have hm := mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ (s / 8) ^ 6 * epsilon ^ 2 * (theta / 3))
    convert hm using 1
    ring
  · apply aux_heartbeat_cutoff_rate_compare hC hD (mul_pos (by norm_num) hR2) hL
    have hs4 : s ^ 4 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hs.le hs1 4
    have he2 : epsilon ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ he.le he1 2
    have hse : s ^ 4 * epsilon ^ 2 ≤ 1 := by
      simpa only [one_mul] using mul_le_mul hs4 he2 (sq_nonneg epsilon) zero_le_one
    have hx : s ^ 6 * epsilon ^ 2 * theta ≤ s ^ 2 * theta := by
      have hm := mul_le_mul_of_nonneg_right hse (mul_nonneg (sq_nonneg s) ht.le)
      convert hm using 1 <;> ring
    have hcoef : 18 * R2 ≤ C * logDelta := by
      exact (by linarith only [hfieldRate, hR2] : 18 * R2 ≤ C / 2).trans hCL
    calc
      _ ≤ 3 * (2 * R2) * (s ^ 2 * theta) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      _ ≤ C * logDelta * (s ^ 2 * (theta / 3)) := by
        have hm := mul_le_mul_of_nonneg_right hcoef
          (by positivity : 0 ≤ s ^ 2 * (theta / 3))
        convert hm using 1
        ring
  · rw [show Cr * delta ^ 2 * logDelta = (Cr * logDelta) * delta ^ 2 by ring]
    apply aux_heartbeat_cutoff_rate_compare hC hD (mul_pos hCr hL) hL
    have hs3 : s ^ 3 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hs.le hs1 3
    have hcoef : 9 * (8 : ℝ) ^ 3 * Cr * s ^ 3 ≤ C := by
      have hm := mul_le_mul_of_nonneg_left hs3
        (by positivity : 0 ≤ 9 * (8 : ℝ) ^ 3 * Cr)
      nlinarith only [hm, hresponse]
    have hm := mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ logDelta * ((s / 8) ^ 3 * epsilon ^ 2 * (theta / 3)))
    convert hm using 1 <;> ring

/-- Source-form finite-cutoff density estimate.  The two shell-field events
are unchanged by the response cutoff; only the response argument is replaced by
the genuinely local `min n L` score array. -/
theorem exists_measure_cutoffGoodEvent_badDensity_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ L : ℕ, ∀ s theta epsilon : ℝ,
      s ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 →
      epsilon ∈ Set.Ioc 0 1 →
      C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| ≤ theta →
      ∀ m0 K : ℕ,
        M.P.toMeasure {omega | (∑ m ∈ Finset.Icc m0 (m0 + K),
            if omega ∈ goodEvent M (some L) m 0 epsilon s then
              (1 : ℝ) else 0) / (K + 1) ≤ 1 - theta} ≤
          ENNReal.ofReal (Real.exp (-(s ^ 6 * epsilon ^ 2 * theta /
            (C * M.delta ^ 2 * |Real.log M.delta|)) * (K + 1))) := by
  obtain ⟨Cr, hCr, hresponse⟩ :=
    exists_measure_goodResponse_some_badDensity_le_all d
  let C1 := fieldOneDensityConst d
  let C2 := fieldTwoDensityConst d
  let R2 := fieldTwoRateDenom d
  let C : ℝ := 1 + 32 * (8 : ℝ) ^ 6 * C1 + 10000 * C2 ^ 2 +
    5000 * R2 + 10000 * Cr
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
    dsimp only [C2]
    unfold fieldTwoDensityConst
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
        4 * fieldTwoRateDenom d * (1 + Real.log 2) := by
      positivity
    linarith
  have hR2 : 0 < R2 := by
    dsimp only [R2]
    unfold fieldTwoRateDenom
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by norm_num) expFieldMomentDenom_pos)
      (mul_nonneg
        (mul_nonneg (by norm_num) expSequenceConcentrationConst_pos.le)
        (sq_nonneg (fieldTwoSuffixScaleConst d)))
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro M L s theta epsilon hs htheta hepsilon hsmall m0 K
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
  have ht : t ∈ Set.Ioc 0 1 :=
    ⟨by dsimp only [t]; positivity, by dsimp only [t]; linarith⟩
  have heta : eta ∈ Set.Ioc 0 1 :=
    ⟨by dsimp only [eta]; positivity, by dsimp only [eta]; linarith⟩
  have hCfield : 18 * (8 : ℝ) ^ 6 * C1 ≤ C := by
    dsimp only [C]
    have hrest : 0 ≤ 10000 * C2 ^ 2 + 5000 * R2 + 10000 * Cr := by
      positivity
    nlinarith only [hC1, hrest]
  have hCfieldTwo : 384 * C2 ^ 2 ≤ C := by
    dsimp only [C]
    have hnonneg : 0 ≤ 32 * (8 : ℝ) ^ 6 * C1 := by positivity
    have hnonneg' : 0 ≤ 5000 * R2 + 10000 * Cr := by positivity
    nlinarith only [hC1, hnonneg, hnonneg', sq_nonneg C2]
  have hCfieldRate : 2304 * R2 ≤ C := by
    dsimp only [C]
    have hnonneg : 0 ≤ 32 * (8 : ℝ) ^ 6 * C1 + 10000 * C2 ^ 2 := by
      positivity
    have hnonneg' : 0 ≤ 10000 * Cr := by positivity
    nlinarith only [hnonneg, hnonneg', hR2]
  have hCresponse : 4608 * Cr ≤ C := by
    dsimp only [C]
    have hnonneg : 0 ≤ 32 * (8 : ℝ) ^ 6 * C1 + 10000 * C2 ^ 2 +
        5000 * R2 := by positivity
    nlinarith only [hnonneg, hCr]
  have hfieldSmall : C1 * t ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 *
      M.delta ^ 2 ≤ eta := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    have hcoef : 3 * (8 : ℝ) ^ 6 * C1 ≤ C * |Real.log M.delta| := by
      calc
        3 * (8 : ℝ) ^ 6 * C1 ≤ C / 2 := by nlinarith [hCfield]
        _ ≤ C * |Real.log M.delta| := by
          have := mul_le_mul_of_nonneg_left hLhalf hC.le
          nlinarith
    have hcommon : 0 ≤ s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 := by
      positivity
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
      nlinarith [hCresponse, mul_le_mul_of_nonneg_left hs3
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 * 8 ^ 3) hCr.le)]
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
          field_simp [hs0.ne']
          ring
      _ ≤ C * (s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta|) :=
        mul_le_mul_of_nonneg_right hcoef hcommon
      _ = C * s ^ (-6 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
          |Real.log M.delta| := by ring
      _ ≤ theta := hsmall
  have hglobalBudget : C * M.delta ^ 2 * |Real.log M.delta| ≤
      theta * s ^ 6 * epsilon ^ 2 :=
    cutoffDensity_global_budget hs0 he0 hsmall
  have hfieldTwoSmall : M.delta ≤ C2⁻¹ * s * Real.sqrt eta := by
    dsimp only [eta]
    exact cutoffDensity_fieldTwo_small hC hC2 hd hs0 hs1 ht0 he0 he1
      hLhalf hCfieldTwo hglobalBudget
  have hfield := measure_goodFieldOne_badDensity_le M ht.1 ht.2 heta.1
    heta.2 he0 he1 hfieldSmall m0 K
  have hfieldTwo := measure_goodFieldTwo_badDensity_le M hs0 hs1 heta.1
    heta.2 hfieldTwoSmall m0 K
  have hresp := hresponse M L t eta epsilon ht heta hepsilon hresponseSmall m0 K
  let b : ℝ := s ^ 6 * epsilon ^ 2 * theta /
    (C * M.delta ^ 2 * |Real.log M.delta|)
  let a1 : ℝ := t ^ 6 * epsilon ^ 2 * eta / (C1 * M.delta ^ 2)
  let a2 : ℝ := s ^ 2 * eta / (2 * R2 * M.delta ^ 2)
  let ar : ℝ := t ^ 3 * epsilon ^ 2 * eta /
    (Cr * M.delta ^ 2 * |Real.log M.delta|)
  have hb : 1 ≤ b := by
    dsimp only [b]
    rw [le_div_iff₀ (by positivity :
      0 < C * M.delta ^ 2 * |Real.log M.delta|)]
    simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using hglobalBudget
  have hrates := aux_heartbeat_cutoff_density_rates hC hC1 hR2 hCr
    hs0 hs1 he0 he1 ht0 hd hL hLhalf hCfield hCfieldRate hCresponse
  have ha1 : 3 * b ≤ a1 := hrates.1
  have ha2 : 3 * b ≤ a2 := hrates.2.1
  have har : 3 * b ≤ ar := hrates.2.2
  let w : ℝ := (K : ℝ) + 1
  have hw : 1 ≤ w := by
    dsimp only [w]
    have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    linarith
  have height : 8 * t = s := by dsimp only [t]; ring
  rw [height] at hfield hresp
  let tail : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-b * w))
  have hfieldQuarter : M.P.toMeasure {omega |
      theta / 3 ≤ intervalEventDensity
        (fun m => (cutoffGoodFieldOneEvent (d := d) m epsilon s)ᶜ)
          m0 K omega} ≤ tail / 4 := by
    have hfield' : M.P.toMeasure {omega |
        theta / 3 ≤ intervalEventDensity
          (fun m => (cutoffGoodFieldOneEvent (d := d) m epsilon s)ᶜ)
            m0 K omega} ≤ ENNReal.ofReal (Real.exp (-a1 * w)) := by
      simpa only [cutoffGoodFieldOneEvent, C1, t, eta, a1, w,
        Nat.cast_add, Nat.cast_one, mul_one] using hfield
    exact hfield'.trans (by
      have hq := ofReal_exp_neg_mul_le_quarter hb ha1 hw
      simpa only [t, eta, a1, b, w, tail, mul_one, Nat.cast_add,
        Nat.cast_one] using hq)
  have hfieldTwoQuarter : M.P.toMeasure {omega |
      theta / 3 ≤ intervalEventDensity
        (fun m => (cutoffGoodFieldTwoEvent (d := d) m s)ᶜ) m0 K omega} ≤
      tail / 4 := by
    refine hfieldTwo.trans ?_
    have hq := ofReal_exp_neg_mul_le_quarter hb ha2 hw
    simpa only [eta, a2, b, w, tail, mul_one, Nat.cast_add, Nat.cast_one]
      using hq
  have hresponseQuarter : M.P.toMeasure {omega |
      theta / 3 ≤ intervalEventDensity
        (fun m => (cutoffGoodResponseEvent M L m epsilon s)ᶜ) m0 K omega} ≤
      tail / 4 := by
    have hresp' : M.P.toMeasure {omega |
        theta / 3 ≤ intervalEventDensity
          (fun m => (cutoffGoodResponseEvent M L m epsilon s)ᶜ) m0 K omega} ≤
        ENNReal.ofReal (Real.exp (-ar * w)) := by
      simpa only [cutoffGoodResponseEvent, t, eta, ar, w, Nat.cast_add,
        Nat.cast_one, mul_one] using hresp
    exact hresp'.trans (by
      have hq := ofReal_exp_neg_mul_le_quarter hb har hw
      simpa only [t, eta, ar, b, w, tail, mul_one, Nat.cast_add,
        Nat.cast_one] using hq)
  have hfinal := measure_cutoffDensityFailure_le_of_component_bounds
    M L s theta epsilon m0 K tail hfieldQuarter hfieldTwoQuarter
      hresponseQuarter
  simpa only [tail, b, w, Nat.cast_add, Nat.cast_one] using hfinal

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
