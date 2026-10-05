module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff.ResponseCarrier

@[expose] public section

/-!
# Finite-cutoff response density

This module connects the genuinely local finite-cutoff response score to the
literal `GoodResponse` event used by the cutoff regularity ladder.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open Filter MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Density
open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

theorem cutoffResponseScoreArray_nonneg {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (s epsilon K : ℝ) (m j : ℤ) (omega : Sample d) :
    0 ≤ cutoffResponseScoreArray M L s epsilon K m j omega := by
  unfold cutoffResponseScoreArray
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem summable_cutoffResponseScoreArray_row {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (s epsilon K : ℝ) (m : ℕ) (omega : Sample d) :
    Summable fun j : ℤ => SubdiffusiveProcess.Concentration.wt s (m : ℤ) j *
      cutoffResponseScoreArray M L s epsilon K (m : ℤ) j omega := by
  refine summable_of_ne_finset_zero
    (s := Finset.Icc (0 : ℤ) (m : ℤ)) fun j hj => ?_
  simp only [Finset.mem_Icc, not_and_or] at hj
  unfold cutoffResponseScoreArray
  have hinactive : ¬(0 ≤ (m : ℤ) ∧ 0 ≤ j ∧ j ≤ (m : ℤ)) := by omega
  rw [ite_eq_right hinactive]
  simp

private theorem cutoff_idist_natCast_eq_sub {m j : ℕ} (hjm : j ≤ m) :
    SubdiffusiveProcess.Concentration.idist (m : ℤ) (j : ℤ) = ((m - j : ℕ) : ℝ) := by
  unfold SubdiffusiveProcess.Concentration.idist
  change |(m : ℝ) - (j : ℝ)| = ((m - j : ℕ) : ℝ)
  have hcast : (m : ℝ) - (j : ℝ) = ((m - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hjm]
  rw [hcast, abs_of_nonneg (Nat.cast_nonneg _)]

theorem lintegral_cutoffResponseScoreArray_rpow_le_one_of_norm
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {s epsilon K p : ℝ} (hp : 1 ≤ p)
    (hnorm : ∀ j : ℕ,
      paperENNRealLpNorm M.P.toMeasure p
        (cutoffLocalResponseScore M L s epsilon K j) ≤ 1) :
    ∀ m j : ℤ,
      ∫⁻ omega,
        ENNReal.ofReal ((cutoffResponseScoreArray M L s epsilon K m j omega) ^ p)
        ∂M.P.toMeasure ≤ 1 := by
  intro m j
  unfold cutoffResponseScoreArray
  split_ifs with hactive
  · have hp0 : 0 < p := zero_lt_one.trans_le hp
    have hraw := hnorm j.toNat
    unfold paperENNRealLpNorm at hraw
    have hinv : 0 < p⁻¹ := inv_pos.mpr hp0
    have hmoment :
        ∫⁻ omega, (cutoffLocalResponseScore M L s epsilon K j.toNat omega) ^ p
          ∂M.P.toMeasure ≤ 1 := by
      rw [← ENNReal.one_rpow p⁻¹] at hraw
      exact (ENNReal.rpow_le_rpow_iff hinv).mp hraw
    have heq : (fun omega => ENNReal.ofReal
        (((cutoffLocalResponseScore M L s epsilon K j.toNat omega).toReal) ^ p)) =
        fun omega =>
          (cutoffLocalResponseScore M L s epsilon K j.toNat omega) ^ p := by
      funext omega
      calc
        ENNReal.ofReal
            (((cutoffLocalResponseScore M L s epsilon K j.toNat omega).toReal) ^ p) =
            ENNReal.ofReal
              ((cutoffLocalResponseScore M L s epsilon K j.toNat omega ^ p).toReal) :=
          congrArg ENNReal.ofReal (ENNReal.toReal_rpow _ _)
        _ = _ := ENNReal.ofReal_toReal
          (ENNReal.rpow_ne_top_of_nonneg hp0.le
            (cutoffLocalResponseScore_ne_top M L s epsilon K j.toNat omega))
    rw [heq]
    exact hmoment
  · rw [Real.zero_rpow (zero_lt_one.trans_le hp).ne']
    simp

/-- The manuscript's scalar cutoff response budget implies the unit score
moment required by `concentration_for_scales`. -/
theorem cutoffLocalResponseScore_norm_le_one_of_numeric
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {s epsilon K C p : ℝ} (j : ℕ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hepsilon : 0 < epsilon)
    (hK : 0 < K) (hC : 0 < C) (hp : 1 ≤ p)
    (hdim : 2 * (d : ℝ) * s⁻¹ ≤ p)
    (hmoment :
      paperENNRealLpNorm M.P.toMeasure p
          (cutoffLocalResponseScore M L s epsilon K j) ≤
        ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
          ∑ n ∈ Finset.range (j - 1),
            ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
              ((descendantsAtScale
                (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹ *
              ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2))
    (hnumeric :
      8 * K * C * p * Real.log (2 + p) * M.delta ^ 2 ≤
        s ^ 2 * epsilon ^ 2) :
    paperENNRealLpNorm M.P.toMeasure p
        (cutoffLocalResponseScore M L s epsilon K j) ≤ 1 := by
  have hsum := responseScore_geometric_sum_le (j := j) hs hs1
    (zero_lt_one.trans_le hp) hdim
  have hA0 : 0 ≤ C * p * Real.log (2 + p) * M.delta ^ 2 := by
    have hlog : 0 ≤ Real.log (2 + p) :=
      Real.log_nonneg (by linarith)
    positivity
  have hcoef0 : 0 ≤ 2 * K * s⁻¹ * (epsilon ^ 2)⁻¹ := by positivity
  have hsdiv0 : 0 ≤ 4 / s := by positivity
  have hfactor :
      (∑ n ∈ Finset.range (j - 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
          ((descendantsAtScale
            (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹ *
          ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2)) =
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹) *
          ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2) := by
    exact (Finset.sum_mul (s := Finset.range (j - 1))
        (f := fun n =>
          ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹)
        (ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2))).symm
  calc
    paperENNRealLpNorm M.P.toMeasure p
        (cutoffLocalResponseScore M L s epsilon K j) ≤
        ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
          ∑ n ∈ Finset.range (j - 1),
            ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
              ((descendantsAtScale
                (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹ *
              ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2) := hmoment
    _ = ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
        (∑ n ∈ Finset.range (j - 1),
          ENNReal.ofReal ((3 : ℝ) ^ (-s * ((j : ℝ) - (n : ℝ)))) *
            ((descendantsAtScale
              (originCube d (j : ℤ)) (n : ℤ)).card : ℝ≥0∞) ^ p⁻¹) *
          ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2) := by
      rw [hfactor]
      ring
    _ ≤ ENNReal.ofReal (2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
        ENNReal.ofReal (4 / s) *
          ENNReal.ofReal (C * p * Real.log (2 + p) * M.delta ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum zero_le) zero_le
    _ = ENNReal.ofReal ((2 * K * s⁻¹ * (epsilon ^ 2)⁻¹) *
        (4 / s) * (C * p * Real.log (2 + p) * M.delta ^ 2)) := by
      rw [← ENNReal.ofReal_mul hcoef0,
        ← ENNReal.ofReal_mul (mul_nonneg hcoef0 hsdiv0)]
    _ ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
      have heps2 : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
      field_simp [hs.ne', hepsilon.ne']
      nlinarith

theorem not_goodResponse_some_imp_lt_Yk_cutoffResponseScoreArray
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (omega : Sample d)
    {t epsilon K : ℝ} (ht : 0 < t) (hepsilon : 0 < epsilon)
    (hK : 0 < K)
    (hall : ∀ n : ℕ, ∀ R : TriadicCube d,
      R.scale = (n : ℤ) → ∀ e : Vec d, vecNormSq e = 1 →
        ENNReal.ofReal
            (section6Response M n (min n L) omega (triadicCubeShift R) e) ≤
          2 * localNormalizedResponseQuarterNetMax M (min n L) R omega)
    (m : ℕ) (hbad : ¬ GoodResponse M (some L) m 0 epsilon (8 * t) omega) :
    K * t⁻¹ < SubdiffusiveProcess.Concentration.Yk
      (cutoffResponseScoreArray M L t epsilon K) t (m : ℤ) omega := by
  unfold GoodResponse at hbad
  push Not at hbad
  obtain ⟨j, n, hjm, hnj, z, hzgrid, hzann, e, he, hresponse⟩ := hbad
  have hzparent : z ∈ cubeSet (originCube d (j : ℤ)) :=
    openCubeSet_subset_cubeSet _ (by simpa only [sub_zero] using! hzann.1)
  have hcover := cubeSet_subset_iUnion_descendantsAtScale
    (originCube d (j : ℤ))
    (show (n : ℤ) ≤ (originCube d (j : ℤ)).scale by
      change (n : ℤ) ≤ (j : ℤ)
      exact_mod_cast (show n ≤ j by omega)) hzparent
  obtain ⟨R, hR, hzR⟩ := Set.mem_iUnion₂.1 hcover
  have hscale : R.scale = (n : ℤ) :=
    scale_eq_of_mem_descendantsAtScale hR
  have hshift : triadicCubeShift R = z :=
    triadicCubeShift_eq_of_onTriadicGrid_of_mem_cubeSet hscale
      (by simpa only [sub_zero] using hzgrid) hzR
  have hannR : triadicCubeShift R ∉ cube d ((j : ℤ) - 1) := by
    rw [hshift]
    simpa only [sub_zero] using hzann.2
  have hnetAtom : localNormalizedResponseQuarterNetMax M (min n L) R omega ≤
      cutoffLocalResponseScaleAtom M L j n omega := by
    unfold cutoffLocalResponseScaleAtom
    rw [dite_eq_left hnj]
    dsimp only [cutoffLocalResponseAnnulusMax]
    calc
      localNormalizedResponseQuarterNetMax M (min n L) R omega =
          (if triadicCubeShift R ∉ cube d ((j : ℤ) - 1) then
            localNormalizedResponseQuarterNetMax M (min n L) R omega else 0) := by
        rw [ite_eq_left hannR]
      _ ≤ _ := Finset.le_sup' (fun Q =>
        if triadicCubeShift Q ∉ cube d ((j : ℤ) - 1) then
          localNormalizedResponseQuarterNetMax M (min n L) Q omega else 0) hR
  have hresponseLocal : ENNReal.ofReal
      (section6Response M n (min n L) omega z e) ≤
        2 * cutoffLocalResponseScaleAtom M L j n omega := by
    rw [← hshift]
    exact (hall n R hscale e he).trans
      (mul_le_mul_of_nonneg_left hnetAtom (by norm_num))
  have hresponse0 : 0 < section6Response M n (min n L) omega z e := by
    have hleft : 0 ≤ epsilon ^ 2 *
        (3 : ℝ) ^ (((8 * t) * ((m : ℝ) - (n : ℝ))) / 8) := by
      positivity
    exact hleft.trans_lt (by simpa using hresponse)
  have hlocalReal : section6Response M n (min n L) omega z e ≤
      2 * (cutoffLocalResponseScaleAtom M L j n omega).toReal := by
    have htop : 2 * cutoffLocalResponseScaleAtom M L j n omega ≠ ∞ :=
      ENNReal.mul_ne_top (by norm_num)
        (cutoffLocalResponseScaleAtom_ne_top M L j n omega)
    have hreal := ENNReal.toReal_mono htop hresponseLocal
    simpa only [ENNReal.toReal_ofReal hresponse0.le, ENNReal.toReal_ofNat,
      ENNReal.toReal_mul, cutoffLocalResponseScaleAtom_ne_top] using hreal
  have hjRange : j ∈ Finset.range (m + 1) := Finset.mem_range.2 (by omega)
  have hnRange : n ∈ Finset.range (j - 1) := Finset.mem_range.2 (by omega)
  have hscoreTerm :
      ENNReal.ofReal (2 * K * t⁻¹ * (epsilon ^ 2)⁻¹) *
          (ENNReal.ofReal ((3 : ℝ) ^ (-t * ((j : ℝ) - (n : ℝ)))) *
            cutoffLocalResponseScaleAtom M L j n omega) ≤
        cutoffLocalResponseScore M L t epsilon K j omega := by
    unfold cutoffLocalResponseScore
    apply mul_le_mul_right
    exact Finset.single_le_sum
      (f := fun q : ℕ => ENNReal.ofReal
        ((3 : ℝ) ^ (-t * ((j : ℝ) - (q : ℝ)))) *
          cutoffLocalResponseScaleAtom M L j q omega)
      (fun _ _ => bot_le) hnRange
  have hscoreReal := ENNReal.toReal_mono
    (cutoffLocalResponseScore_ne_top M L t epsilon K j omega) hscoreTerm
  have hcoef0 : 0 ≤ 2 * K * t⁻¹ * (epsilon ^ 2)⁻¹ := by positivity
  have hweight0 : 0 ≤ (3 : ℝ) ^ (-t * ((j : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hcoef0, ENNReal.toReal_ofReal hweight0] at hscoreReal
  have hexponent : (8 * t) * ((m : ℝ) - (n : ℝ)) / 8 =
      t * ((m : ℝ) - (n : ℝ)) := by ring
  have hresponse' : epsilon ^ 2 *
      (3 : ℝ) ^ (t * ((m : ℝ) - (n : ℝ))) <
        section6Response M n (min n L) omega z e := by
    simpa only [Option.getD_some, hexponent] using hresponse
  have hatom : epsilon ^ 2 *
      (3 : ℝ) ^ (t * ((m : ℝ) - (n : ℝ))) <
        2 * (cutoffLocalResponseScaleAtom M L j n omega).toReal :=
    hresponse'.trans_le hlocalReal
  have hlocalScore : K * t⁻¹ *
      (3 : ℝ) ^ (t * ((m : ℝ) - (j : ℝ))) <
        (cutoffLocalResponseScore M L t epsilon K j omega).toReal := by
    calc
      K * t⁻¹ * (3 : ℝ) ^ (t * ((m : ℝ) - (j : ℝ))) =
          (2 * K * t⁻¹ * (epsilon ^ 2)⁻¹) *
            (3 : ℝ) ^ (-t * ((j : ℝ) - (n : ℝ))) *
              (epsilon ^ 2 *
                (3 : ℝ) ^ (t * ((m : ℝ) - (n : ℝ))) / 2) := by
        field_simp [ht.ne', hepsilon.ne']
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring
      _ < (2 * K * t⁻¹ * (epsilon ^ 2)⁻¹) *
            (3 : ℝ) ^ (-t * ((j : ℝ) - (n : ℝ))) *
              (cutoffLocalResponseScaleAtom M L j n omega).toReal := by
        apply mul_lt_mul_of_pos_left
        · nlinarith
        · positivity
      _ ≤ _ := by simpa only [mul_assoc] using hscoreReal
  have hrow := (summable_cutoffResponseScoreArray_row
    M L t epsilon K m omega).le_tsum (j : ℤ)
      (fun q _ => mul_nonneg (SubdiffusiveProcess.Concentration.wt_nonneg _ _ _)
        (cutoffResponseScoreArray_nonneg M L t epsilon K _ _ omega))
  have hjInt : (j : ℤ) ≤ (m : ℤ) := by exact_mod_cast hjm
  have hterm : SubdiffusiveProcess.Concentration.wt t (m : ℤ) (j : ℤ) *
      (cutoffLocalResponseScore M L t epsilon K j omega).toReal ≤
        SubdiffusiveProcess.Concentration.Yk (cutoffResponseScoreArray M L t epsilon K)
          t (m : ℤ) omega := by
    unfold SubdiffusiveProcess.Concentration.Yk
    simpa only [cutoffResponseScoreArray, Int.natCast_nonneg, hjInt, and_self,
      ite_true, Int.toNat_natCast] using hrow
  apply lt_of_lt_of_le _ hterm
  unfold SubdiffusiveProcess.Concentration.wt
  rw [cutoff_idist_natCast_eq_sub hjm]
  have hweightPos : 0 < (3 : ℝ) ^ (-(t * ((m - j : ℕ) : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc
    K * t⁻¹ = (3 : ℝ) ^ (-(t * ((m - j : ℕ) : ℝ))) *
        (K * t⁻¹ * (3 : ℝ) ^ (t * ((m : ℝ) - (j : ℝ)))) := by
      have hcast : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := by
        exact Nat.cast_sub hjm
      rw [hcast]
      rw [show (3 : ℝ) ^ (-(t * ((m : ℝ) - (j : ℝ)))) *
          (K * t⁻¹ * (3 : ℝ) ^ (t * ((m : ℝ) - (j : ℝ)))) =
        K * t⁻¹ * ((3 : ℝ) ^ (-(t * ((m : ℝ) - (j : ℝ)))) *
          (3 : ℝ) ^ (t * ((m : ℝ) - (j : ℝ)))) by ring]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
    _ < _ := mul_lt_mul_of_pos_left hlocalScore hweightPos

/-- The literal finite-cutoff response failure is dominated by the local
score on one common full-measure quarter-net event. -/
theorem ae_not_goodResponse_some_imp_lt_Yk_cutoffResponseScoreArray
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {t epsilon K : ℝ} (ht : 0 < t) (hepsilon : 0 < epsilon)
    (hK : 0 < K) :
    ∀ᵐ omega ∂M.P.toMeasure, ∀ m : ℕ,
      ¬ GoodResponse M (some L) m 0 epsilon (8 * t) omega →
        K * t⁻¹ < SubdiffusiveProcess.Concentration.Yk
          (cutoffResponseScoreArray M L t epsilon K) t (m : ℤ) omega := by
  filter_upwards [ae_forall_section6Response_cutoff_le_two_mul_localNet M L]
    with omega hall
  intro m hbad
  exact not_goodResponse_some_imp_lt_Yk_cutoffResponseScoreArray
    M L omega ht hepsilon hK hall m hbad

/-- Response-event density concentration at a fixed deterministic cutoff,
after exposing the score-moment and scalar threshold normalizations. -/
theorem measure_goodResponse_some_badDensity_le_of_parameters
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    {t epsilon theta K p : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hepsilon : 0 < epsilon)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hK : 0 < K) (hp : 1 ≤ p) (htp : 1 ≤ t * p)
    (hthreshold : 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
        (theta / 2) ^ (-1 / p) < K * t⁻¹)
    (hnorm : ∀ j : ℕ,
      paperENNRealLpNorm M.P.toMeasure p
        (cutoffLocalResponseScore M L t epsilon K j) ≤ 1)
    (m0 window : ℕ) :
    M.P.toMeasure {omega | theta ≤ intervalEventDensity
        (fun m => {omega : Sample d |
          GoodResponse M (some L) m 0 epsilon (8 * t) omega}ᶜ)
        m0 window omega} ≤
      ENNReal.ofReal (Real.exp
        (-(t * p * (theta / 2)) /
          (16 * (responseScoreRange d : ℝ)) * ((window : ℝ) + 1))) := by
  have hconc := SubdiffusiveProcess.Concentration.concentration_for_scales_Cstar
    M.P.toMeasure (cutoffResponseScoreArray M L t epsilon K) hp ht ht1 htp
    (responseScoreRange_pos d)
    (measurable_cutoffResponseScoreArray M L t epsilon K)
    (cutoffResponseScoreArray_nonneg M L t epsilon K)
    (lintegral_cutoffResponseScoreArray_rpow_le_one_of_norm M L hp hnorm)
    (columnsIndep_cutoffResponseScoreArray M L t epsilon K)
    (m0 : ℤ) window (theta / 2) (by positivity) (by linarith)
  let CE : Set (Sample d) := {omega | theta / 2 <
      (1 / ((window : ℝ) + 1)) *
        ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
          (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
              (theta / 2) ^ (-1 / p) <
                SubdiffusiveProcess.Concentration.Yk
                  (cutoffResponseScoreArray M L t epsilon K) t k omega
            then (1 : ℝ) else 0)}
  have hreduce := ae_not_goodResponse_some_imp_lt_Yk_cutoffResponseScoreArray
    M L ht hepsilon hK
  have hmono : {omega | theta ≤ intervalEventDensity
        (fun m => {omega : Sample d |
          GoodResponse M (some L) m 0 epsilon (8 * t) omega}ᶜ)
        m0 window omega} ≤ᶠ[ae M.P.toMeasure] CE := by
    filter_upwards [hreduce] with omega hreduce homega
    unfold intervalEventDensity at homega
    change theta / 2 < (1 / ((window : ℝ) + 1)) *
      ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
        (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) <
              SubdiffusiveProcess.Concentration.Yk
                (cutoffResponseScoreArray M L t epsilon K) t k omega
          then (1 : ℝ) else 0)
    have hcount :
        ∑ k ∈ Finset.Icc m0 (m0 + window),
            (if omega ∈ {omega : Sample d |
                GoodResponse M (some L) k 0 epsilon (8 * t) omega}ᶜ
              then (1 : ℝ) else 0) ≤
          ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
            (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
                (theta / 2) ^ (-1 / p) <
                  SubdiffusiveProcess.Concentration.Yk
                    (cutoffResponseScoreArray M L t epsilon K) t k omega
              then (1 : ℝ) else 0) := by
      let natToInt : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
      rw [show Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)) =
          (Finset.Icc m0 (m0 + window)).map natToInt by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_map]
        constructor
        · intro hz
          have hz0 : 0 ≤ z := (show (0 : ℤ) ≤ m0 by omega).trans hz.1
          have hzEq : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
          refine ⟨z.toNat, ?_, ?_⟩
          · constructor
            · have hzLower : (m0 : ℤ) ≤ (z.toNat : ℤ) := by
                simpa only [hzEq] using hz.1
              omega
            · have hzUpper : (z.toNat : ℤ) ≤ ((m0 + window : ℕ) : ℤ) := by
                simpa only [hzEq, Nat.cast_add] using hz.2
              omega
          · simp only [natToInt, Function.Embedding.coeFn_mk]
            exact hzEq
        · rintro ⟨k, hk, rfl⟩
          simp only [natToInt, Function.Embedding.coeFn_mk]
          constructor
          · simpa only [Int.ofNat_eq_natCast] using
              (show (m0 : ℤ) ≤ (k : ℤ) by exact_mod_cast hk.1)
          · simpa only [Int.ofNat_eq_natCast, Nat.cast_add] using
              (show (k : ℤ) ≤ ((m0 + window : ℕ) : ℤ) by
                exact_mod_cast hk.2),
        Finset.sum_map]
      apply Finset.sum_le_sum
      intro k hk
      by_cases hbad : omega ∈ {omega : Sample d |
          GoodResponse M (some L) k 0 epsilon (8 * t) omega}ᶜ
      · rw [ite_eq_left hbad]
        have hy := hreduce k (by simpa only [Set.mem_compl_iff,
          Set.mem_ofPred_eq, not_not] using hbad)
        have hscore : 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
            (theta / 2) ^ (-1 / p) <
              SubdiffusiveProcess.Concentration.Yk
                (cutoffResponseScoreArray M L t epsilon K) t (k : ℤ) omega :=
          hthreshold.trans hy
        rw [ite_eq_left (by simpa only [natToInt,
          Function.Embedding.coeFn_mk] using! hscore)]
      · rw [ite_eq_right hbad]
        split_ifs <;> norm_num
    have hcount' :
        (∑ m ∈ Finset.Icc m0 (m0 + window),
          eventIndicator
            ((fun m => {omega : Sample d |
              GoodResponse M (some L) m 0 epsilon (8 * t) omega}ᶜ) m) omega) ≤
          ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
            (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
                (theta / 2) ^ (-1 / p) <
                  SubdiffusiveProcess.Concentration.Yk
                    (cutoffResponseScoreArray M L t epsilon K) t k omega
              then (1 : ℝ) else 0) := by
      convert hcount using 1
      simp only [eventIndicator, Set.mem_compl_iff, Set.mem_ofPred_eq]
    have havg := homega.trans
      (div_le_div_of_nonneg_right hcount' (by positivity))
    have havg' : theta ≤ (1 / ((window : ℝ) + 1)) *
        ∑ k ∈ Finset.Icc (m0 : ℤ) ((m0 : ℤ) + (window : ℤ)),
          (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
              (theta / 2) ^ (-1 / p) <
                SubdiffusiveProcess.Concentration.Yk
                  (cutoffResponseScoreArray M L t epsilon K) t k omega
            then (1 : ℝ) else 0) := by
      calc
        theta ≤ (∑ k ∈ Finset.Icc (m0 : ℤ)
            ((m0 : ℤ) + (window : ℤ)),
              (if 6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
                  (theta / 2) ^ (-1 / p) <
                    SubdiffusiveProcess.Concentration.Yk
                      (cutoffResponseScoreArray M L t epsilon K) t k omega
                then (1 : ℝ) else 0)) / ((window : ℝ) + 1) := havg
        _ = _ := by ring
    exact (by linarith : theta / 2 < theta).trans_le havg'
  exact (MeasureTheory.measure_mono_ae hmono).trans (by
    simpa only [CE] using hconc)

/-- Source-form cutoff response density estimate.  Its constant is uniform
in the deterministic cutoff `L`. -/
theorem exists_measure_goodResponse_some_badDensity_le
    (d : ℕ) [NeZero d] :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (t theta epsilon : ℝ),
        t ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 →
        epsilon ∈ Set.Ioc 0 1 →
        C0 * t ^ (-3 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta| ≤ theta →
        ∀ m0 window : ℕ,
          M.P.toMeasure {omega | theta ≤ intervalEventDensity
              (fun m => {omega : Sample d |
                GoodResponse M (some L) m 0 epsilon (8 * t) omega}ᶜ)
              m0 window omega} ≤
            ENNReal.ofReal (Real.exp
              (-(t ^ 3 * epsilon ^ 2 * theta /
                (C0 * M.delta ^ 2 * |Real.log M.delta|)) *
                  ((window : ℝ) + 1))) := by
  obtain ⟨_c, C, _hc, hC, hscore⟩ :=
    exists_cutoffLocalResponseScore_moment_bound (d := d)
  let A : ℝ := expSequenceAmplitude
  let D : ℝ := 2 + C + 32 * A * C
  let Q : ℝ := 1 + 2 * D + 2 * (d : ℝ) * D
  let C0 : ℝ := 1 + Q + 32 * D * (responseScoreRange d : ℝ)
  have hA : 0 < A := zero_lt_one.trans expSequenceAmplitude_gt_one
  have hD : 0 < D := by dsimp only [D]; positivity
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hC0 : 0 < C0 := by dsimp only [C0]; positivity
  refine ⟨C0, hC0, ?_⟩
  intro M L t theta epsilon ht htheta hepsilon hsource m0 window
  have ht0 := ht.1
  have ht1 := ht.2
  have htheta0 := htheta.1
  have htheta1 := htheta.2
  have hepsilon0 := hepsilon.1
  have hepsilon1 := hepsilon.2
  have hdelta := M.shellPrefix.delta_pos
  have hdeltaHalf := M.shellPrefix.delta_le_half
  have hlogNeg : Real.log M.delta < 0 :=
    Real.log_neg hdelta (hdeltaHalf.trans_lt (by norm_num))
  have hL : 0 < |Real.log M.delta| := abs_pos.mpr hlogNeg.ne
  have hdeltaLog : 0 < M.delta ^ 2 * |Real.log M.delta| :=
    mul_pos (sq_pos_of_pos hdelta) hL
  have hbudget : C0 * (M.delta ^ 2 * |Real.log M.delta|) ≤
      theta * t ^ 3 * epsilon ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsource
      (mul_nonneg (pow_nonneg ht0.le 3) (sq_nonneg epsilon))
    calc
      C0 * (M.delta ^ 2 * |Real.log M.delta|) =
          (C0 * t ^ (-3 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta|) * (t ^ 3 * epsilon ^ 2) := by
        rw [zpow_neg]
        field_simp [ht0.ne', hepsilon0.ne']
      _ ≤ theta * (t ^ 3 * epsilon ^ 2) := hmul
      _ = theta * t ^ 3 * epsilon ^ 2 := by ring
  have hC0D : 2 * D ≤ C0 := by
    dsimp only [C0, Q]
    have hr : 0 ≤ (responseScoreRange d : ℝ) := by positivity
    nlinarith
  have hC0dD : 2 * (d : ℝ) * D ≤ C0 := by
    dsimp only [C0, Q]
    have hr : 0 ≤ (responseScoreRange d : ℝ) := by positivity
    nlinarith
  have hDgeC : C ≤ D := by
    change C ≤ 2 + C + 32 * A * C
    have hAC : 0 ≤ 32 * A * C := by positivity
    linarith
  have hlogHalf : (1 : ℝ) / 2 ≤ |Real.log M.delta| := by
    have hmono : Real.log M.delta ≤ Real.log (1 / 2 : ℝ) :=
      Real.log_le_log hdelta hdeltaHalf
    have heq : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
      simp
    rw [heq] at hmono
    rw [abs_of_neg hlogNeg]
    linarith [Real.log_two_gt_d9]
  have hDtwo : 2 ≤ D := by
    change 2 ≤ 2 + C + 32 * A * C
    have hAC : 0 ≤ 32 * A * C := by positivity
    linarith
  have hDlog : 1 ≤ D * |Real.log M.delta| := by
    calc
      1 = 2 * ((1 : ℝ) / 2) := by norm_num
      _ ≤ D * |Real.log M.delta| :=
        mul_le_mul hDtwo hlogHalf (by norm_num) (by positivity)
  have hDlarge : 32 * A * C ≤ D := by
    change 32 * A * C ≤ 2 + C + 32 * A * C
    linarith [hC]
  obtain ⟨p, hpDef, hp, hpTheta, hdim, hsmall, hnumeric⟩ :=
    exists_responseMoment_parameters_of_budget (d := d)
      hA hC hD hC0 ht0 ht1 htheta0 htheta1 hepsilon0 hepsilon1
      hdelta hdeltaHalf hbudget hC0D hC0dD hDgeC hDlog hDlarge
  have hnorm : ∀ j : ℕ,
      paperENNRealLpNorm M.P.toMeasure p
        (cutoffLocalResponseScore M L t epsilon A j) ≤ 1 := by
    intro j
    exact cutoffLocalResponseScore_norm_le_one_of_numeric
      M L j ht0 ht1 hepsilon0 hA hC hp hdim
      (hscore M p hp hsmall L t epsilon A j) hnumeric
  have hthresholdBase :
      6 * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
          (theta / 2) ^ (-1 / p) < A :=
    expSequence_threshold_lt_amplitude htheta0 htheta1 hpTheta
  have hthreshold :
      6 * t⁻¹ * SubdiffusiveProcess.Concentration.Cstar ^ (1 / p) *
          (theta / 2) ^ (-1 / p) < A * t⁻¹ := by
    have hmul := mul_lt_mul_of_pos_right hthresholdBase (inv_pos.mpr ht0)
    convert hmul using 1
    all_goals ring
  have htp : 1 ≤ t * p := by
    have hmul := mul_le_mul_of_nonneg_right hdim ht0.le
    have hcancel : 2 * (d : ℝ) * t⁻¹ * t = 2 * (d : ℝ) := by
      field_simp [ht0.ne']
    rw [hcancel] at hmul
    have hd : (1 : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast (NeZero.one_le : 1 ≤ d)
    exact (by linarith only [hd] : 1 ≤ 2 * (d : ℝ)).trans
      (by simpa only [mul_comm] using hmul)
  have hraw := measure_goodResponse_some_badDensity_le_of_parameters
    M L ht0 ht1 hepsilon0 htheta0 htheta1 hA hp htp hthreshold hnorm
      m0 window
  refine hraw.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have hC0rate : 32 * D * (responseScoreRange d : ℝ) ≤ C0 := by
    change 32 * D * (responseScoreRange d : ℝ) ≤
      1 + Q + 32 * D * (responseScoreRange d : ℝ)
    exact le_add_of_nonneg_left (by linarith only [hQ] : 0 ≤ 1 + Q)
  have hrpos : 0 < (responseScoreRange d : ℝ) := by
    exact_mod_cast responseScoreRange_pos d
  have hrate : t * p * (theta / 2) /
        (16 * (responseScoreRange d : ℝ)) ≥
      t ^ 3 * epsilon ^ 2 * theta /
        (C0 * M.delta ^ 2 * |Real.log M.delta|) := by
    rw [hpDef]
    field_simp [hD.ne', hC0.ne', hdelta.ne', hL.ne', hrpos.ne']
    nlinarith [hC0rate]
  have hw : 0 ≤ (window : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hrate hw
  convert neg_le_neg hmul using 1 <;> ring

/-- Dimension-zero completion of the cutoff response density argument. -/
theorem exists_measure_goodResponse_some_badDensity_le_all (d : ℕ) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (t theta epsilon : ℝ),
        t ∈ Set.Ioc 0 1 → theta ∈ Set.Ioc 0 1 →
        epsilon ∈ Set.Ioc 0 1 →
        C0 * t ^ (-3 : ℤ) * epsilon⁻¹ ^ 2 * M.delta ^ 2 *
            |Real.log M.delta| ≤ theta →
        ∀ m0 window : ℕ,
          M.P.toMeasure {omega | theta ≤ intervalEventDensity
              (fun m => {omega : Sample d |
                GoodResponse M (some L) m 0 epsilon (8 * t) omega}ᶜ)
              m0 window omega} ≤
            ENNReal.ofReal (Real.exp
              (-(t ^ 3 * epsilon ^ 2 * theta /
                (C0 * M.delta ^ 2 * |Real.log M.delta|)) *
                  ((window : ℝ) + 1))) := by
  by_cases hd : d = 0
  · subst d
    refine ⟨1, by norm_num, ?_⟩
    intro M L t theta epsilon _ht htheta _hepsilon _hsmall m0 window
    have hgood : ∀ (omega : Sample 0) (m : ℕ),
        GoodResponse M (some L) m 0 epsilon (8 * t) omega := by
      intro omega m
      unfold GoodResponse
      intro j n hjm hnj z hzgrid hzann e he
      have he0 : e = 0 := Subsingleton.elim _ _
      subst e
      simp [vecNormSq, vecDot] at he
    have hevent : {omega | theta ≤ intervalEventDensity
          (fun m => {omega : Sample 0 |
            GoodResponse M (some L) m 0 epsilon (8 * t) omega}ᶜ)
          m0 window omega} = ∅ := by
      ext omega
      constructor
      · intro homega
        simp only [Set.mem_ofPred_eq] at homega
        unfold intervalEventDensity eventIndicator at homega
        simp only [hgood, Set.mem_compl_iff, Set.mem_ofPred_eq,
          not_true_eq_false, ite_false, Finset.sum_const_zero, zero_div] at homega
        linarith [htheta.1]
      · intro hempty
        exact (Set.notMem_empty omega hempty).elim
    rw [hevent, measure_empty]
    exact bot_le
  · let : NeZero d := ⟨hd⟩
    exact exists_measure_goodResponse_some_badDensity_le d

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
