import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentAggregation
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.ResponseObservableMeasurability
import Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality




namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The scale-`n-l` response maximum occurring after moving the two outer
suprema in `ellipticityMomentObservable` through the nonnegative depth sum. -/
noncomputable def ellipticityScaleResponseObservable {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ) (l : ℕ)
    (omega : Sample d) : ℝ≥0∞ :=
  ⨆ L : {L : ℕ // m ≤ L},
    ⨆ R : {R : TriadicCube d //
        R ∈ descendantsAtScale (originCube d (m : ℤ)) n},
      paperScaleResponseAtScale R.1 (n - (l : ℤ)) .infinity
        (aCutoffFamily M L.1 omega)
        (tailCoefficientCubeAverage M L.1 m omega)

theorem measurable_ellipticityScaleResponseObservable {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ) (l : ℕ) :
    Measurable (ellipticityScaleResponseObservable M m n l) := by
  unfold ellipticityScaleResponseObservable paperScaleResponseAtScale
    paperMaxDescendantProbeAtScale
  exact Measurable.iSup fun L => Measurable.iSup fun R =>
    ENNReal.continuous_rpow_const.measurable.comp
      (Measurable.iSup fun T =>
        measurable_paperScalarProbeMaxOn_cutoff_randomNormalization M L.1
          (Ch02.cubeDomain T.1)
          (measurable_tailCoefficientCubeAverage M L.1 m))

/-- Pointwise Step 2 decomposition of the literal `q = 1` paper error. -/
theorem ellipticityMomentObservable_le_scaleSeries {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ) (s : ℝ)
    (omega : Sample d) :
    ellipticityMomentObservable M m n s omega ≤
      ∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s 1 l) *
        ellipticityScaleResponseObservable M m n l omega := by
  unfold ellipticityMomentObservable
  apply iSup_le
  intro L
  apply iSup_le
  intro R
  unfold paperHomogenizationErrorDefault
  simp only [paperHomogenizationError]
  unfold paperHomogenizationErrorFinite
  norm_num
  apply ENNReal.tsum_le_tsum
  intro l
  apply mul_le_mul' le_rfl
  unfold ellipticityScaleResponseObservable
  exact le_iSup_of_le L (le_iSup_of_le R le_rfl)

/-- At a nonnegative observation scale, the one-scale carrier is bounded by
the finite maximum of the positive-scale P-40 response observable. -/
theorem ellipticityScaleResponseObservable_le_positiveScaleMaximum
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (m : ℕ) {n : ℤ} (l k : ℕ) (hkm : k ≤ m)
    (hk : (k : ℤ) = n - (l : ℤ))
    (omega : Sample d) :
    ellipticityScaleResponseObservable M m n l omega ≤
      (descendantsAtScale (originCube d (m : ℤ)) (k : ℤ)).sup'
        (descendantsAtScale_nonempty (originCube d (m : ℤ))
          (by
            have : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm
            simpa [originCube] using this))
        (fun Q => (positiveScaleResponseObservable M m Q omega) ^ (1 / 2 : ℝ)) := by
  unfold ellipticityScaleResponseObservable
  apply iSup_le
  intro L
  apply iSup_le
  intro R
  simp only [paperScaleResponseAtScale]
  unfold paperMaxDescendantProbeAtScale
  let hnonempty :
      (descendantsAtScale (originCube d (m : ℤ)) (k : ℤ)).Nonempty :=
    descendantsAtScale_nonempty (originCube d (m : ℤ))
    (by
      have : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm
      simpa [originCube] using this)
  have hbase :
      (⨆ T : {T : TriadicCube d //
          T ∈ descendantsAtScale R.1 (n - (l : ℤ))},
        paperScalarProbeMaxOn (Ch02.cubeDomain T.1)
          (aCutoffCoeffOnData M L.1 omega (Ch02.cubeDomain T.1)).toCoeffOn
          (tailCoefficientCubeAverage M L.1 m omega)) ≤
        (descendantsAtScale (originCube d (m : ℤ)) (k : ℤ)).sup' hnonempty
          (fun Q => positiveScaleResponseObservable M m Q omega) := by
    apply iSup_le
    intro T
    have hTglobal : T.1 ∈
        descendantsAtScale (originCube d (m : ℤ)) (k : ℤ) :=
      mem_descendantsAtScale_trans R.2 (by rw [hk]; exact T.2)
    calc
      _ ≤ positiveScaleResponseObservable M m T.1 omega := by
        unfold positiveScaleResponseObservable
        exact le_iSup_of_le L le_rfl
      _ ≤ _ := Finset.le_sup'
        (f := fun Q => positiveScaleResponseObservable M m Q omega) hTglobal
  calc
    _ ≤ ((descendantsAtScale (originCube d (m : ℤ)) (k : ℤ)).sup' hnonempty
          (fun Q => positiveScaleResponseObservable M m Q omega)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hbase (by norm_num)
    _ = _ := by
      simpa only [Function.comp_apply] using
        map_finset_sup'
          (ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num : 0 < (1 / 2 : ℝ)))
          hnonempty (fun Q => positiveScaleResponseObservable M m Q omega)

/-- At a negative observation scale, the one-scale carrier is one term of the
subunit P-40 response observable. -/
theorem ellipticityScaleResponseObservable_le_subunit {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ)
    {n : ℤ} (l : ℕ) (k : ℤ) (hk : k = n - (l : ℤ))
    (omega : Sample d) :
    ellipticityScaleResponseObservable M m n l omega ≤
      (subunitResponseObservable M m k omega) ^ (1 / 2 : ℝ) := by
  unfold ellipticityScaleResponseObservable
  apply iSup_le
  intro L
  apply iSup_le
  intro R
  simp only [paperScaleResponseAtScale]
  unfold paperMaxDescendantProbeAtScale
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply iSup_le
  intro T
  unfold subunitResponseObservable
  apply le_iSup_of_le L
  apply le_iSup_of_le
    (⟨T.1, mem_descendantsAtScale_trans R.2 (by simpa only [hk] using T.2)⟩ :
      {Q : TriadicCube d //
        Q ∈ descendantsAtScale (originCube d (m : ℤ)) k})
  exact le_rfl

/-! ## The geometric depth sum -/

/-- A normalized `q = 1` geometric weight absorbs any depth amplification
whose exponent is at most `3s/4`.  The deliberately loose `20 s⁻¹` constant
is the form consumed by the printed Section 4 display. -/
theorem tsum_geometricWeight_mul_shifted_rpow_le
    {s a A : ℝ} (N : ℕ) (hs : 0 < s) (hs1 : s ≤ 1)
    (hA : 0 ≤ A) (ha : 0 ≤ a) (haUpper : a ≤ 3 * s / 4) :
    (∑' l : ℕ, Ch02.geometricWeight s 1 l *
        (A * Real.rpow 3 (a * ((N + l : ℕ) : ℝ)))) ≤
      20 * A * s⁻¹ * Real.rpow 3 (a * (N : ℝ)) := by
  let gap := s - a
  have hgap : 0 < gap := by
    dsimp only [gap]
    linarith
  have hgap_le : gap ≤ 1 := by
    dsimp only [gap]
    linarith
  have hdisc_nonneg : 0 ≤ Ch02.geometricDiscount s 1 :=
    (Homogenization.geometricDiscount_pos (by simpa using hs)).le
  have hdisc_le : Ch02.geometricDiscount s 1 ≤ 1 :=
    Homogenization.Book.Ch05.Section52.geometricDiscount_one_le_one s
  have hterm : ∀ l : ℕ,
      Ch02.geometricWeight s 1 l *
          (A * Real.rpow 3 (a * ((N + l : ℕ) : ℝ))) =
        (Ch02.geometricDiscount s 1 * A *
            Real.rpow 3 (a * (N : ℝ))) *
          Real.rpow 3 (-gap * (l : ℝ)) := by
    intro l
    rw [Ch02.geometricWeight]
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hsplit :
        Real.rpow 3 (a * ((N + l : ℕ) : ℝ)) =
          Real.rpow 3 (a * (N : ℝ)) * Real.rpow 3 (a * (l : ℝ)) := by
      calc
        _ = Real.rpow 3 (a * (N : ℝ) + a * (l : ℝ)) := by
          congr 1
          norm_num
          ring
        _ = _ := Real.rpow_add h3 _ _
    rw [hsplit]
    have hcombine :
        Real.rpow 3 (-s * 1 * (l : ℝ)) * Real.rpow 3 (a * (l : ℝ)) =
          Real.rpow 3 (-gap * (l : ℝ)) := by
      calc
        _ = Real.rpow 3
            ((-s * 1 * (l : ℝ)) + a * (l : ℝ)) :=
          (Real.rpow_add h3 _ _).symm
        _ = _ := by
          congr 1
          dsimp only [gap]
          ring
    calc
      Ch02.geometricDiscount s 1 * Real.rpow 3 (-s * 1 * (l : ℝ)) *
          (A * (Real.rpow 3 (a * (N : ℝ)) * Real.rpow 3 (a * (l : ℝ)))) =
        Ch02.geometricDiscount s 1 * A * Real.rpow 3 (a * (N : ℝ)) *
          (Real.rpow 3 (-s * 1 * (l : ℝ)) *
            Real.rpow 3 (a * (l : ℝ))) := by ring
      _ = _ := by rw [hcombine]
  rw [show (∑' l : ℕ, Ch02.geometricWeight s 1 l *
      (A * Real.rpow 3 (a * ((N + l : ℕ) : ℝ)))) =
      ∑' l : ℕ, (Ch02.geometricDiscount s 1 * A *
        Real.rpow 3 (a * (N : ℝ))) * Real.rpow 3 (-gap * (l : ℝ)) by
        exact tsum_congr hterm,
    tsum_mul_left,
    Homogenization.Book.Ch05.Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount
      hgap]
  have hgapInv : gap⁻¹ ≤ 4 * s⁻¹ := by
    have hraw := (inv_le_inv₀ hgap (by positivity : 0 < s / 4)).2
      (show s / 4 ≤ gap by dsimp only [gap]; linarith)
    calc
      gap⁻¹ ≤ (s / 4)⁻¹ := hraw
      _ = 4 * s⁻¹ := by field_simp [hs.ne']
  have hdiscountGap : (Ch02.geometricDiscount gap 1)⁻¹ ≤ 5 * gap⁻¹ :=
    Ch02.inv_geometricDiscount_le_five_inv hgap hgap_le (by norm_num)
  have hfactor_nonneg :
      0 ≤ A * Real.rpow 3 (a * (N : ℝ)) :=
    mul_nonneg hA (Real.rpow_nonneg (by norm_num) _)
  have hdiscountGapNonneg :
      0 ≤ (Ch02.geometricDiscount gap 1)⁻¹ :=
    inv_nonneg.mpr
      (Homogenization.geometricDiscount_pos (by simpa using hgap)).le
  calc
    Ch02.geometricDiscount s 1 * A * Real.rpow 3 (a * (N : ℝ)) *
          (Ch02.geometricDiscount gap 1)⁻¹ ≤
        (A * Real.rpow 3 (a * (N : ℝ))) *
          (Ch02.geometricDiscount gap 1)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ hdiscountGapNonneg
      calc
        Ch02.geometricDiscount s 1 * A * Real.rpow 3 (a * (N : ℝ)) =
            Ch02.geometricDiscount s 1 *
              (A * Real.rpow 3 (a * (N : ℝ))) := by ring
        _ ≤ 1 * (A * Real.rpow 3 (a * (N : ℝ))) :=
          mul_le_mul_of_nonneg_right hdisc_le hfactor_nonneg
        _ = _ := one_mul _
    _ ≤ (A * Real.rpow 3 (a * (N : ℝ))) * (5 * gap⁻¹) := by
      exact mul_le_mul_of_nonneg_left hdiscountGap hfactor_nonneg
    _ ≤ (A * Real.rpow 3 (a * (N : ℝ))) * (20 * s⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ hfactor_nonneg
      nlinarith
    _ = 20 * A * s⁻¹ * Real.rpow 3 (a * (N : ℝ)) := by ring

theorem summable_geometricWeight_mul_shifted_rpow
    {s a A : ℝ} (N : ℕ) (haUpper : a < s) :
    Summable (fun l : ℕ => Ch02.geometricWeight s 1 l *
      (A * Real.rpow 3 (a * ((N + l : ℕ) : ℝ)))) := by
  let gap := s - a
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  have hterm : ∀ l : ℕ,
      Ch02.geometricWeight s 1 l *
          (A * Real.rpow 3 (a * ((N + l : ℕ) : ℝ))) =
        (Ch02.geometricDiscount s 1 * A * Real.rpow 3 (a * (N : ℝ))) *
          Real.rpow 3 (-gap * (l : ℝ)) := by
    intro l
    rw [Ch02.geometricWeight]
    have h3 : (0 : ℝ) < 3 := by norm_num
    have hsplit :
        Real.rpow 3 (a * ((N + l : ℕ) : ℝ)) =
          Real.rpow 3 (a * (N : ℝ)) * Real.rpow 3 (a * (l : ℝ)) := by
      calc
        _ = Real.rpow 3 (a * (N : ℝ) + a * (l : ℝ)) := by
          congr 1
          norm_num
          ring
        _ = _ := Real.rpow_add h3 _ _
    rw [hsplit]
    have hcombine :
        Real.rpow 3 (-s * 1 * (l : ℝ)) * Real.rpow 3 (a * (l : ℝ)) =
          Real.rpow 3 (-gap * (l : ℝ)) := by
      calc
        _ = Real.rpow 3 ((-s * 1 * (l : ℝ)) + a * (l : ℝ)) :=
          (Real.rpow_add h3 _ _).symm
        _ = _ := by congr 1; dsimp only [gap]; ring
    calc
      Ch02.geometricDiscount s 1 * Real.rpow 3 (-s * 1 * (l : ℝ)) *
          (A * (Real.rpow 3 (a * (N : ℝ)) * Real.rpow 3 (a * (l : ℝ)))) =
        Ch02.geometricDiscount s 1 * A * Real.rpow 3 (a * (N : ℝ)) *
          (Real.rpow 3 (-s * 1 * (l : ℝ)) *
            Real.rpow 3 (a * (l : ℝ))) := by ring
      _ = _ := by rw [hcombine]
  refine Summable.congr
    ((Homogenization.Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hgap).mul_left
      (Ch02.geometricDiscount s 1 * A * Real.rpow 3 (a * (N : ℝ)))) ?_
  intro l
  exact (hterm l).symm

/-! ## Moment bounds for one depth -/

/-- Nonnegative-scale aggregation: take the square-root moment on each cube,
then pay the sharp `card^(1/xi)` cost for the finite descendant maximum. -/
theorem ellipticityScaleResponseMoment_le_positive
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (m : ℕ) {n : ℤ} (l k : ℕ) (s xi delta1 C : ℝ)
    (hnm : n ≤ (m : ℤ)) (hk : (k : ℤ) = n - (l : ℤ))
    (hxi : 0 < xi) (hdelta : 0 ≤ delta1) (hC : 1 ≤ C)
    (hmoment : ∀ Q : TriadicCube d,
      Q ∈ descendantsAtScale (originCube d (m : ℤ)) (k : ℤ) →
      paperENNRealLpNorm M.P.toMeasure xi
          (positiveScaleResponseObservable M m Q) ≤
        ENNReal.ofReal (C * delta1 *
          Real.rpow 3 (s * ((m - k : ℕ) : ℝ)))) :
    paperENNRealLpNorm M.P.toMeasure xi
        (ellipticityScaleResponseObservable M m n l) ≤
      ENNReal.ofReal (C * Real.sqrt delta1 *
        Real.rpow 3 (((d : ℝ) / xi + s / 2) *
          ((((m : ℤ) - n : ℤ) : ℝ) + (l : ℝ)))) := by
  have hkm : k ≤ m := by
    exact_mod_cast (calc
      (k : ℤ) = n - (l : ℤ) := hk
      _ ≤ n := sub_le_self _ (by exact_mod_cast Nat.zero_le l)
      _ ≤ (m : ℤ) := hnm)
  let D := descendantsAtScale (originCube d (m : ℤ)) (k : ℤ)
  let hD : D.Nonempty := descendantsAtScale_nonempty (originCube d (m : ℤ))
    (by
      have : (k : ℤ) ≤ (m : ℤ) := by exact_mod_cast hkm
      simpa [originCube] using this)
  let X : TriadicCube d → Sample d → ℝ≥0∞ := fun Q omega =>
    (positiveScaleResponseObservable M m Q omega) ^ (1 / 2 : ℝ)
  have hXmeas : ∀ Q ∈ D, Measurable (X Q) := by
    intro Q _hQ
    exact ENNReal.continuous_rpow_const.measurable.comp
      (measurable_positiveScaleResponseObservable M m Q)
  have hXmoment : ∀ Q ∈ D,
      paperENNRealLpNorm M.P.toMeasure xi (X Q) ≤
        ENNReal.ofReal (C * Real.sqrt delta1 *
          Real.rpow 3 ((s / 2) * ((m - k : ℕ) : ℝ))) := by
    intro Q hQ
    have hsqrt := paperENNRealLpNorm_rpow_half_le M.P.toMeasure hxi
      (measurable_positiveScaleResponseObservable M m Q)
    have hraw := ENNReal.rpow_le_rpow (hmoment Q hQ) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    refine hsqrt.trans (hraw.trans ?_)
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    have hpow0 : 0 ≤ Real.rpow 3 (s * ((m - k : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hbase : 0 ≤ C * delta1 *
        Real.rpow 3 (s * ((m - k : ℕ) : ℝ)) :=
      mul_nonneg (mul_nonneg hC0 hdelta) hpow0
    rw [ENNReal.ofReal_rpow_of_nonneg hbase (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.mul_rpow (mul_nonneg hC0 hdelta) hpow0,
      Real.mul_rpow hC0 hdelta]
    have hsqrtC : Real.rpow C (1 / 2 : ℝ) ≤ C := by
      exact Real.rpow_le_self_of_one_le hC (by norm_num)
    have hpow :
        Real.rpow 3 (s * ((m - k : ℕ) : ℝ)) ^ (1 / 2 : ℝ) =
          Real.rpow 3 ((s / 2) * ((m - k : ℕ) : ℝ)) := by
      calc
        _ = Real.rpow 3
            (s * ((m - k : ℕ) : ℝ) * (1 / 2 : ℝ)) :=
          (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
        _ = _ := by congr 1; ring
    rw [← Real.sqrt_eq_rpow delta1, hpow]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsqrtC (Real.sqrt_nonneg delta1))
      (Real.rpow_nonneg (by norm_num) _)
  have hmax := paperENNRealLpNorm_finset_sup'_le_card_rpow_mul
    M.P.toMeasure hxi D hD X hXmeas
    (ENNReal.ofReal (C * Real.sqrt delta1 *
      Real.rpow 3 ((s / 2) * ((m - k : ℕ) : ℝ)))) hXmoment
  calc
    paperENNRealLpNorm M.P.toMeasure xi
        (ellipticityScaleResponseObservable M m n l) ≤
        paperENNRealLpNorm M.P.toMeasure xi (D.sup' hD X) := by
      apply paperENNRealLpNorm_mono_ae M.P.toMeasure hxi.le
      apply Filter.Eventually.of_forall
      intro omega
      simpa only [D, X, Finset.sup'_apply] using
        ellipticityScaleResponseObservable_le_positiveScaleMaximum
          M m l k hkm hk omega
    _ ≤ _ := hmax.trans (by
  have hdepth :
      ((m - k : ℕ) : ℝ) = (((m : ℤ) - n : ℤ) : ℝ) + (l : ℝ) := by
    have hint : (m - k : ℕ) = m - k := rfl
    exact_mod_cast (show (m : ℤ) - (k : ℤ) = (m : ℤ) - n + (l : ℤ) by
      rw [hk]
      ring)
  rw [show D.card = (3 ^ d) ^ (m - k) by
    dsimp only [D]
    simpa using
      Homogenization.Book.Ch05.Section52.section52_descendantsAtScale_originCube_large_card
        d m (show (k : ℤ) ≤ (m : ℤ) by exact_mod_cast hkm)]
  rw [hdepth]
  rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg
      (Nat.cast_nonneg _) (inv_nonneg.mpr hxi.le)]
  rw [← ENNReal.ofReal_mul
    (Real.rpow_nonneg (Nat.cast_nonneg _) xi⁻¹)]
  apply ENNReal.ofReal_le_ofReal
  have hcard :
      Real.rpow (((3 ^ d) ^ (m - k) : ℕ) : ℝ) xi⁻¹ =
        Real.rpow 3 (((d : ℝ) / xi) *
          ((((m : ℤ) - n : ℤ) : ℝ) + (l : ℝ))) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    norm_num only [Nat.cast_ofNat]
    rw [← Real.rpow_natCast (3 : ℝ) d]
    change Real.rpow ((Real.rpow 3 (d : ℝ)) ^ (m - k)) xi⁻¹ = _
    rw [← Real.rpow_natCast (Real.rpow 3 (d : ℝ)) (m - k)]
    calc
      Real.rpow (Real.rpow (Real.rpow 3 (d : ℝ)) ((m - k : ℕ) : ℝ)) xi⁻¹ =
          Real.rpow (Real.rpow 3 ((d : ℝ) * ((m - k : ℕ) : ℝ))) xi⁻¹ := by
        congr 1
        exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
      _ = Real.rpow 3
          (((d : ℝ) * ((m - k : ℕ) : ℝ)) * xi⁻¹) :=
        (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
      _ = _ := by
        congr 1
        rw [hdepth]
        field_simp [hxi.ne']
  change Real.rpow (((3 ^ d) ^ (m - k) : ℕ) : ℝ) xi⁻¹ *
      (C * Real.sqrt delta1 *
        Real.rpow 3 (s / 2 *
          ((((m : ℤ) - n : ℤ) : ℝ) + (l : ℝ)))) ≤ _
  rw [hcard]
  let z : ℝ := (((m : ℤ) - n : ℤ) : ℝ) + (l : ℝ)
  change Real.rpow 3 ((d : ℝ) / xi * z) *
      (C * Real.sqrt delta1 * Real.rpow 3 (s / 2 * z)) ≤
    C * Real.sqrt delta1 *
      Real.rpow 3 (((d : ℝ) / xi + s / 2) * z)
  calc
    Real.rpow 3 ((d : ℝ) / xi * z) *
        (C * Real.sqrt delta1 * Real.rpow 3 (s / 2 * z)) =
      C * Real.sqrt delta1 *
        (Real.rpow 3 ((d : ℝ) / xi * z) *
          Real.rpow 3 (s / 2 * z)) := by ring
    _ = C * Real.sqrt delta1 *
        Real.rpow 3 (((d : ℝ) / xi * z) + s / 2 * z) := by
      congr 1
      exact (Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _).symm
    _ = C * Real.sqrt delta1 *
        Real.rpow 3 (((d : ℝ) / xi + s / 2) * z) := by
      congr 2
      ring
    _ ≤ _ := le_rfl)

/-- Negative-scale aggregation: the subunit moment is independent of the
negative scale, and the inequality `n-l < 0` supplies exactly the missing
depth needed to place it under the common shifted geometric profile. -/
theorem ellipticityScaleResponseMoment_le_subunit
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (m : ℕ) {n : ℤ} (l : ℕ) (s xi delta1 C : ℝ)
    (hnm : n ≤ (m : ℤ)) (hkneg : n - (l : ℤ) < 0)
    (hxi : 0 < xi) (hs : 0 < s) (hdelta : 0 ≤ delta1) (hC : 1 ≤ C)
    (hmoment : paperENNRealLpNorm M.P.toMeasure xi
        (subunitResponseObservable M m (n - (l : ℤ))) ≤
      ENNReal.ofReal (C * delta1 *
        Real.rpow 3 (s * (m : ℝ)))) :
    paperENNRealLpNorm M.P.toMeasure xi
        (ellipticityScaleResponseObservable M m n l) ≤
      ENNReal.ofReal (C * Real.sqrt delta1 *
        Real.rpow 3 (((d : ℝ) / xi + s / 2) *
          ((((m : ℤ) - n : ℤ) : ℝ) + (l : ℝ)))) := by
  have hmeas := measurable_subunitResponseObservable M m (n - (l : ℤ))
  have hsqrt := paperENNRealLpNorm_rpow_half_le M.P.toMeasure hxi hmeas
  have hraw := ENNReal.rpow_le_rpow hmoment (by norm_num : 0 ≤ (1 / 2 : ℝ))
  have hsqrtBound :
      ENNReal.ofReal (C * delta1 * Real.rpow 3 (s * (m : ℝ))) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * Real.sqrt delta1 *
          Real.rpow 3 ((s / 2) * (m : ℝ))) := by
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    have hpow0 : 0 ≤ Real.rpow 3 (s * (m : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hbase : 0 ≤ C * delta1 * Real.rpow 3 (s * (m : ℝ)) :=
      mul_nonneg (mul_nonneg hC0 hdelta) hpow0
    rw [ENNReal.ofReal_rpow_of_nonneg hbase (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.mul_rpow (mul_nonneg hC0 hdelta) hpow0,
      Real.mul_rpow hC0 hdelta]
    have hsqrtC : Real.rpow C (1 / 2 : ℝ) ≤ C :=
      Real.rpow_le_self_of_one_le hC (by norm_num)
    have hpow : Real.rpow 3 (s * (m : ℝ)) ^ (1 / 2 : ℝ) =
        Real.rpow 3 ((s / 2) * (m : ℝ)) := by
      calc
        _ = Real.rpow 3 (s * (m : ℝ) * (1 / 2 : ℝ)) :=
          (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
        _ = _ := by congr 1; ring
    rw [← Real.sqrt_eq_rpow delta1, hpow]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsqrtC (Real.sqrt_nonneg delta1))
      (Real.rpow_nonneg (by norm_num) _)
  have hmono := paperENNRealLpNorm_mono_ae M.P.toMeasure hxi.le
    (Filter.Eventually.of_forall
      (ellipticityScaleResponseObservable_le_subunit M m l
        (n - (l : ℤ)) rfl))
  refine hmono.trans (hsqrt.trans (hraw.trans (hsqrtBound.trans ?_)))
  apply ENNReal.ofReal_le_ofReal
  have ha0 : 0 ≤ (d : ℝ) / xi + s / 2 := by positivity
  have hdepth : (m : ℝ) ≤
      (((m : ℤ) - n : ℤ) : ℝ) + (l : ℝ) := by
    exact_mod_cast (show (m : ℤ) ≤ (m : ℤ) - n + (l : ℤ) by omega)
  have hexp : (s / 2) * (m : ℝ) ≤
      ((d : ℝ) / xi + s / 2) *
        ((((m : ℤ) - n : ℤ) : ℝ) + (l : ℝ)) := by
    have hleft := mul_le_mul_of_nonneg_left hdepth (by positivity : 0 ≤ s / 2)
    have hright := mul_le_mul_of_nonneg_right
      (show s / 2 ≤ (d : ℝ) / xi + s / 2 by
        have : 0 ≤ (d : ℝ) / xi := div_nonneg (by positivity) hxi.le
        linarith)
      (show 0 ≤ (((m : ℤ) - n : ℤ) : ℝ) + (l : ℝ) by
        exact add_nonneg (by exact_mod_cast sub_nonneg.mpr hnm) (by positivity))
    exact hleft.trans hright
  have hpowle := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 3) hexp
  exact mul_le_mul_of_nonneg_left hpowle
    (mul_nonneg (zero_le_one.trans hC) (Real.sqrt_nonneg delta1))

end

end SubdiffusiveProcess.CoarseGrainingVocab
