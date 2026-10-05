module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.EllipticitySpecialization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.EllipticityAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.LargeCubePartitionResponse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.PositiveScaleMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitResponseMoment
public import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds
public import Homogenization.Book.Ch05.Theorems.Section52.GeometrySeries.DescendantCardinality

@[expose] public section

/-!
# Section 4 support: large-cube response aggregation

The observable below is the finite spatial maximum in source display
`e.multiscale.response.large.cubes.sum`.  This file keeps the three scale
ranges separate so their geometric losses remain visible.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal BigOperators

noncomputable section


/-- The maximum over all scale-`k` descendants of the scale-`K` cube of the
square root of the normalized scalar response. -/
noncomputable def largeCubeScaleMaximum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L K : ℕ) (k : ℤ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  if _hk : k ≤ (K : ℤ) then
    ⨆ Q : {Q : TriadicCube d //
        Q ∈ descendantsAtScale (originCube d (K : ℤ)) k},
      (normalizedDefect M L (Ch02.cubeDomain Q.1) omega) ^ (1 / 2 : ℝ)
  else 0

theorem measurable_largeCubeScaleMaximum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L K : ℕ) (k : ℤ) :
    Measurable (largeCubeScaleMaximum M L K k) := by
  classical
  unfold largeCubeScaleMaximum
  split_ifs with hk
  · apply Measurable.iSup
    intro Q
    apply ENNReal.continuous_rpow_const.measurable.comp
    let : NeZero d :=
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
    exact (measurable_normalizedDefect_potentialShellIndexSigma_Iic
      M L (Ch02.cubeDomain Q)).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl
  · exact measurable_const

/-- One response is a term of the large-cube finite maximum. -/
theorem normalizedDefect_rpow_half_le_largeCubeScaleMaximum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L K : ℕ) {k : ℤ}
    (hk : k ≤ (K : ℤ)) (Q : TriadicCube d)
    (hQ : Q ∈ descendantsAtScale (originCube d (K : ℤ)) k)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (normalizedDefect M L (Ch02.cubeDomain Q) omega) ^ (1 / 2 : ℝ) ≤
      largeCubeScaleMaximum M L K k omega := by
  classical
  rw [largeCubeScaleMaximum, dite_eq_left hk]
  exact le_iSup_of_le (⟨Q, hQ⟩ : {R : TriadicCube d //
    R ∈ descendantsAtScale (originCube d (K : ℤ)) k}) le_rfl

private theorem iSup_subtype_eq_finset_sup' {a : Type*} [DecidableEq a]
    (D : Finset a) (hD : D.Nonempty) (f : a → ℝ≥0∞) :
    (⨆ x : {x : a // x ∈ D}, f x.1) = D.sup' hD f := by
  apply le_antisymm
  · apply iSup_le
    intro x
    exact Finset.le_sup' f x.2
  · apply Finset.sup'_le
    intro x hx
    exact le_iSup_of_le (⟨x, hx⟩ : {y : a // y ∈ D}) le_rfl

/-- Finite-grid maximum after a uniform moment bound for the unrooted
response on every cell. -/
theorem largeCubeScaleMaximum_moment_le_of_each {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L K : ℕ) {k : ℤ}
    {xi : ℝ} (hxi : 0 < xi) (hk : k ≤ (K : ℤ)) (A : ℝ≥0∞)
    (hEach : ∀ Q ∈ descendantsAtScale (originCube d (K : ℤ)) k,
      paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M L (Ch02.cubeDomain Q)) ≤ A) :
    paperENNRealLpNorm M.P.toMeasure xi
        (largeCubeScaleMaximum M L K k) ≤
      (((descendantsAtScale (originCube d (K : ℤ)) k).card : ℝ≥0∞) ^ xi⁻¹) *
        A ^ (1 / 2 : ℝ) := by
  classical
  let D := descendantsAtScale (originCube d (K : ℤ)) k
  have hD : D.Nonempty := by
    simpa only [D] using! descendantsAtScale_nonempty (originCube d (K : ℤ)) hk
  let X : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun Q omega =>
    (normalizedDefect M L (Ch02.cubeDomain Q) omega) ^ (1 / 2 : ℝ)
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  have hXmeas : ∀ Q ∈ D, Measurable (X Q) := by
    intro Q _hQ
    exact ENNReal.continuous_rpow_const.measurable.comp
      ((measurable_normalizedDefect_potentialShellIndexSigma_Iic
        M L (Ch02.cubeDomain Q)).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl)
  have hXmoment : ∀ Q ∈ D,
      paperENNRealLpNorm M.P.toMeasure xi (X Q) ≤ A ^ (1 / 2 : ℝ) := by
    intro Q hQ
    exact (paperENNRealLpNorm_rpow_half_le M.P.toMeasure hxi
      ((measurable_normalizedDefect_potentialShellIndexSigma_Iic
        M L (Ch02.cubeDomain Q)).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl)).trans
        (ENNReal.rpow_le_rpow (hEach Q hQ) (by norm_num))
  have hmax := paperENNRealLpNorm_finset_sup'_le_card_rpow_mul
    M.P.toMeasure hxi D hD X hXmeas (A ^ (1 / 2 : ℝ)) hXmoment
  rw [show largeCubeScaleMaximum M L K k = D.sup' hD X by
    funext omega
    rw [largeCubeScaleMaximum, dite_eq_left hk]
    simpa only [X, Finset.sup'_apply] using!
      iSup_subtype_eq_finset_sup' D hD (fun Q => X Q omega)]
  exact hmax

/-- At scales above the cutoff, subadditivity onto the scale-`L` partition
and the induction hypothesis control every translated cube before taking the
finite spatial maximum. -/
theorem largeCubeScaleMaximum_moment_above_cutoff {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L K k m0 : ℕ}
    {xi delta1 : ℝ} (hxi : 1 ≤ xi)
    (hS : inductionHypothesis M m0 xi delta1)
    (hLk : L ≤ k) (hkK : k ≤ K) (hLm0 : L ≤ m0) :
    paperENNRealLpNorm M.P.toMeasure xi
        (largeCubeScaleMaximum M L K (k : ℤ)) ≤
      (((descendantsAtScale (originCube d (K : ℤ)) (k : ℤ)).card : ℝ≥0∞) ^ xi⁻¹) *
        (ENNReal.ofReal delta1) ^ (1 / 2 : ℝ) := by
  classical
  let D := descendantsAtScale (originCube d (K : ℤ)) (k : ℤ)
  have hki : (k : ℤ) ≤ (K : ℤ) := by exact_mod_cast hkK
  have hD : D.Nonempty := by
    simpa only [D] using! descendantsAtScale_nonempty (originCube d (K : ℤ)) hki
  let X : TriadicCube d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun Q omega =>
    (normalizedDefect M L (Ch02.cubeDomain Q) omega) ^ (1 / 2 : ℝ)
  have hXmeas : ∀ Q ∈ D, Measurable (X Q) := by
    intro Q _hQ
    let : NeZero d :=
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
    exact ENNReal.continuous_rpow_const.measurable.comp
      ((measurable_normalizedDefect_potentialShellIndexSigma_Iic
        M L (Ch02.cubeDomain Q)).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl)
  have hXmoment : ∀ Q ∈ D,
      paperENNRealLpNorm M.P.toMeasure xi (X Q) ≤
        (ENNReal.ofReal delta1) ^ (1 / 2 : ℝ) := by
    intro Q hQ
    have hQscale : Q.scale = (k : ℤ) :=
      Homogenization.Book.Ch04.scale_eq_of_mem_descendantsAtScale_originCube hki hQ
    have hraw := normalizedDefect_largeCube_lpnorm_le_induction
      M hxi hS hLk hLm0 Q hQscale
    exact (paperENNRealLpNorm_rpow_half_le M.P.toMeasure
      (zero_lt_one.trans_le hxi)
      ((measurable_normalizedDefect_potentialShellIndexSigma_Iic
        M L (Ch02.cubeDomain Q)).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Iic L)) le_rfl)).trans
        (ENNReal.rpow_le_rpow hraw (by norm_num))
  have hmax := paperENNRealLpNorm_finset_sup'_le_card_rpow_mul
    M.P.toMeasure (zero_lt_one.trans_le hxi) D hD X hXmeas
      ((ENNReal.ofReal delta1) ^ (1 / 2 : ℝ)) hXmoment
  rw [show largeCubeScaleMaximum M L K (k : ℤ) = D.sup' hD X by
    funext omega
    rw [largeCubeScaleMaximum, dite_eq_left hki]
    simpa only [X, Finset.sup'_apply] using!
      iSup_subtype_eq_finset_sup' D hD (fun Q => X Q omega)]
  change paperENNRealLpNorm M.P.toMeasure xi (D.sup' hD X) ≤ _
  exact hmax

/-- Every translated scale-`k` cube has the same normalized-defect moment as
the centered scale-`k` cube. -/
theorem normalizedDefect_cube_lpnorm_eq_origin {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (xi : ℝ)
    (Q : TriadicCube d) :
    paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M L (Ch02.cubeDomain Q)) =
      paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M L (Ch02.cubeDomain (originCube d Q.scale))) :=
  paperENNRealLpNorm_normalizedDefect_cube_eq_origin M L xi Q

private theorem originCube_pred_mem_childCubes_originCube {d : ℕ} (t : ℤ) :
    originCube d (t - 1) ∈ childCubes (originCube d t) := by
  rw [mem_childCubes_iff]
  refine ⟨fun _ => (1 : Fin 3), ?_⟩
  simp only [originCube]
  apply congrArg₂ TriadicCube.mk
  · rfl
  · funext i
    norm_num

private theorem originCube_sub_nat_mem_descendantsAtDepth {d : ℕ}
    (t : ℤ) : ∀ n : ℕ,
    originCube d (t - (n : ℤ)) ∈ descendantsAtDepth (originCube d t) n
  | 0 => by simp
  | n + 1 => by
      rw [descendantsAtDepth_succ]
      refine Finset.mem_biUnion.mpr ⟨originCube d (t - (n : ℤ)),
        originCube_sub_nat_mem_descendantsAtDepth t n, ?_⟩
      convert originCube_pred_mem_childCubes_originCube (d := d) (t - (n : ℤ)) using 1
      congr 1
      push_cast
      ring

/-- For `0 ≤ k < L`, positive-scale response estimate controls the
literal cutoff-`L`, `ahom_L` response on every translated scale-`k` cube. -/
theorem normalizedDefect_positive_scale_moment {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m0 k : ℕ}
    {xi delta1 s c C : ℝ}
    (hpos : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (m0 : ℕ) (xi delta1 s : ℝ) (m k : ℕ)
        (Q : TriadicCube d),
        inductionHypothesis M m0 xi delta1 →
        M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        0 < s → s ≤ 1 →
        xi ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
        k ≤ m0 → k ≤ m →
        Q ∈ descendantsAtScale (originCube d (m : ℤ)) (k : ℤ) →
        paperENNRealLpNorm M.P.toMeasure xi
            (positiveScaleResponseObservable M m Q) ≤
          ENNReal.ofReal (C * delta1 *
            (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))))
    (hS : inductionHypothesis M m0 xi delta1)
    (hdelta : M.delta ^ 2 ≤ delta1) (hdelta1 : delta1 < 1)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hupper : xi ≤ c * s * (M.delta ^ 2)⁻¹ * delta1)
    (hxi0 : 0 ≤ xi)
    (hk0 : k ≤ m0) (hkL : k ≤ L) (Q : TriadicCube d)
    (hQscale : Q.scale = (k : ℤ)) :
    paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M L (Ch02.cubeDomain Q)) ≤
      ENNReal.ofReal (C * delta1 *
        (3 : ℝ) ^ (s * ((L - k : ℕ) : ℝ))) := by
  have hcenter : originCube d (k : ℤ) ∈
      descendantsAtScale (originCube d (L : ℤ)) (k : ℤ) := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d (L : ℤ))
      (by simpa only [originCube] using! (show (k : ℤ) ≤ (L : ℤ) by
        exact_mod_cast hkL))]
    simp only [originCube]
    have hcast : Int.toNat ((L : ℤ) - (k : ℤ)) = L - k := by omega
    rw [hcast]
    have hkcast : (k : ℤ) = (L : ℤ) - ((L - k : ℕ) : ℤ) := by omega
    simpa only [originCube, hkcast] using!
      originCube_sub_nat_mem_descendantsAtDepth (d := d) (L : ℤ) (L - k)
  have hmoment := hpos M m0 xi delta1 s L k (originCube d (k : ℤ))
    hS hdelta hdelta1 hs hs1 hupper hk0 hkL hcenter
  have hpoint : ∀ omega,
      normalizedDefect M L (Ch02.cubeDomain (originCube d (k : ℤ))) omega ≤
        positiveScaleResponseObservable M L (originCube d (k : ℤ)) omega := by
    intro omega
    unfold positiveScaleResponseObservable normalizedDefect
    apply le_iSup_of_le (⟨L, le_rfl⟩ : {N : ℕ // L ≤ N})
    rw [tailCoefficientCubeAverage_self]
  rw [normalizedDefect_cube_lpnorm_eq_origin M L xi Q, hQscale]
  exact (paperENNRealLpNorm_mono_ae M.P.toMeasure hxi0
    (Filter.Eventually.of_forall hpoint)).trans hmoment

/-- For a negative scale, every translated cell is a term of the centered
subunit response observable after stationarity. -/
theorem normalizedDefect_negative_scale_moment {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L : ℕ} {k : ℤ}
    {xi delta1 s C : ℝ} (hxi : 0 ≤ xi) (hk : k < 0)
    (hsub : paperENNRealLpNorm M.P.toMeasure xi
        (subunitResponseObservable M L k) ≤
      ENNReal.ofReal (C * delta1 * (3 : ℝ) ^ (s * (L : ℝ))))
    (Q : TriadicCube d) (hQscale : Q.scale = k) :
    paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefect M L (Ch02.cubeDomain Q)) ≤
      ENNReal.ofReal (C * delta1 * (3 : ℝ) ^ (s * (L : ℝ))) := by
  have hkiL : k ≤ (L : ℤ) := hk.le.trans (by exact_mod_cast Nat.zero_le L)
  have hcenter : originCube d k ∈
      descendantsAtScale (originCube d (L : ℤ)) k := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d (L : ℤ)) hkiL]
    convert originCube_sub_nat_mem_descendantsAtDepth (d := d) (L : ℤ)
      (Int.toNat ((L : ℤ) - k)) using 1
    congr 1
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hkiL)]
    ring
  have hpoint : ∀ omega,
      normalizedDefect M L (Ch02.cubeDomain (originCube d k)) omega ≤
        subunitResponseObservable M L k omega := by
    intro omega
    unfold subunitResponseObservable normalizedDefect
    apply le_iSup_of_le (⟨L, le_rfl⟩ : {N : ℕ // L ≤ N})
    apply le_iSup_of_le
      (⟨originCube d k, hcenter⟩ : {R : TriadicCube d //
        R ∈ descendantsAtScale (originCube d (L : ℤ)) k})
    rw [tailCoefficientCubeAverage_self]
  rw [normalizedDefect_cube_lpnorm_eq_origin M L xi Q, hQscale]
  exact (paperENNRealLpNorm_mono_ae M.P.toMeasure hxi
    (Filter.Eventually.of_forall hpoint)).trans hsub

/-! ## Deterministic reduction of the finite-`r` paper error -/

/-- At every scale below the root, the finite-`r` response aggregation is
bounded by the spatial maximum used in the manuscript proof. -/
theorem paperScaleResponseAtScale_infinity_eq_largeCubeScaleMaximum {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L K : ℕ) {k : ℤ}
    (hk : k ≤ (K : ℤ)) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    paperScaleResponseAtScale (originCube d (K : ℤ)) k .infinity
        (aCutoffFamily M L omega) (ahom M L) =
      largeCubeScaleMaximum M L K k omega := by
  classical
  let D := descendantsAtScale (originCube d (K : ℤ)) k
  have hD : D.Nonempty := by
    simpa only [D] using! descendantsAtScale_nonempty (originCube d (K : ℤ)) hk
  rw [largeCubeScaleMaximum, dite_eq_left hk]
  simp only [paperScaleResponseAtScale]
  unfold paperMaxDescendantProbeAtScale
  have hmap := (ENNReal.orderIsoRpow (1 / 2 : ℝ)
    (by norm_num : 0 < (1 / 2 : ℝ))).map_iSup
      (fun Q : {Q : TriadicCube d //
        Q ∈ descendantsAtScale (originCube d (K : ℤ)) k} =>
          paperScalarProbeMax Q.1 (aCutoffFamily M L omega) (ahom M L))
  simpa only [normalizedDefect, paperScalarProbeMax,
    aCutoffFamily, aCutoffTriadicData] using! hmap

/-- Pointwise reduction of the finite-`r` paper error to the weighted series
of finite spatial response maxima. -/
theorem translatedHomogenizationErrorRandom_le_scaleMaximumSeries {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L K : ℕ)
    (z : PaperCubeTranslate d) (s : ℝ) {r : ℕ} (hr : 0 < r)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    translatedHomogenizationErrorRandom M L K z s r omega ≤
      (∑' l : ℕ, ENNReal.ofReal (Ch02.geometricWeight s (r : ℝ) l) *
        (largeCubeScaleMaximum M L K ((K : ℤ) - (l : ℤ))
          (translatePotentialSample z omega)) ^ (r : ℝ)) ^ ((r : ℝ)⁻¹) := by
  unfold translatedHomogenizationErrorRandom
  simp only [paperHomogenizationError]
  unfold paperHomogenizationErrorFinite
  rw [one_div]
  apply ENNReal.rpow_le_rpow _ (inv_nonneg.mpr (by positivity : 0 ≤ (r : ℝ)))
  apply ENNReal.tsum_le_tsum
  intro l
  apply mul_le_mul' le_rfl
  apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ (r : ℝ))
  rw [paperScaleResponseAtScale_infinity_eq_largeCubeScaleMaximum M L K
    (by omega) (translatePotentialSample z omega)]

private theorem ENNReal_rpow_tsum_le_tsum_rpow (F : ℕ → ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑' n, F n) ^ p ≤ ∑' n, (F n) ^ p := by
  rw [ENNReal.tsum_eq_iSup_nat]
  have hmap := (ENNReal.orderIsoRpow p hp).map_iSup
      (fun n => ∑ k ∈ Finset.range n, F k)
  change (ENNReal.orderIsoRpow p hp)
      (⨆ n, ∑ k ∈ Finset.range n, F k) ≤ _
  rw [hmap]
  apply iSup_le
  intro n
  have hfinite : (∑ k ∈ Finset.range n, F k) ^ p ≤
      ∑ k ∈ Finset.range n, (F k) ^ p := by
    induction n with
    | zero => simp [hp]
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        exact (ENNReal.rpow_add_le_add_rpow _ _ hp.le hp1).trans
          (add_le_add ih le_rfl)
  exact hfinite.trans (ENNReal.sum_le_tsum (Finset.range n))

/-- The manuscript's Minkowski step: the `L^xi` norm of the finite-`r`
homogenization error is bounded by the sum of one-scale maximum moments with
the `r`th root of the normalized geometric weight. -/
theorem translatedHomogenizationErrorRandom_lpnorm_le_scaleMaximumMoments
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L K : ℕ)
    (z : PaperCubeTranslate d) (s xi : ℝ) {r : ℕ}
    (hr : 0 < r) (hxi : 1 ≤ xi) :
    paperENNRealLpNorm M.P.toMeasure xi
        (translatedHomogenizationErrorRandom M L K z s r) ≤
      ∑' l : ℕ,
        (ENNReal.ofReal (Ch02.geometricWeight s (r : ℝ) l)) ^ ((r : ℝ)⁻¹) *
          paperENNRealLpNorm M.P.toMeasure xi
            (largeCubeScaleMaximum M L K ((K : ℤ) - (l : ℤ))) := by
  let W : ℕ → ℝ≥0∞ := fun l =>
    ENNReal.ofReal (Ch02.geometricWeight s (r : ℝ) l)
  let A : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun l omega =>
    largeCubeScaleMaximum M L K ((K : ℤ) - (l : ℤ)) omega
  let Z : ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun l omega =>
    W l ^ ((r : ℝ)⁻¹) * A l omega
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hp0 : 0 ≤ (r : ℝ)⁻¹ := inv_nonneg.mpr hrR.le
  have hp : 0 < (r : ℝ)⁻¹ := inv_pos.mpr hrR
  have hp1 : (r : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hrR).2 (by exact_mod_cast hr)
  have hZmeas : ∀ l, Measurable (Z l) := by
    intro l
    exact (measurable_largeCubeScaleMaximum M L K
      ((K : ℤ) - (l : ℤ))).const_mul _
  have hroot : ∀ omega,
      (∑' l : ℕ, W l *
        (A l (translatePotentialSample z omega)) ^ (r : ℝ)) ^ ((r : ℝ)⁻¹) ≤
      ∑' l : ℕ, Z l (translatePotentialSample z omega) := by
    intro omega
    refine (ENNReal_rpow_tsum_le_tsum_rpow
      (fun l => W l * (A l (translatePotentialSample z omega)) ^ (r : ℝ))
      hp hp1).trans_eq ?_
    apply tsum_congr
    intro l
    dsimp only [Z]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.rpow_mul]
    have : (r : ℝ) * (r : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hrR.ne'
    rw [this, ENNReal.rpow_one]
  have hpoint : ∀ omega,
      translatedHomogenizationErrorRandom M L K z s r omega ≤
        ∑' l, Z l (translatePotentialSample z omega) := by
    intro omega
    exact (translatedHomogenizationErrorRandom_le_scaleMaximumSeries
      M L K z s hr omega).trans (by simpa only [W, A] using! hroot omega)
  calc
    paperENNRealLpNorm M.P.toMeasure xi
        (translatedHomogenizationErrorRandom M L K z s r) ≤
        paperENNRealLpNorm M.P.toMeasure xi
          (fun omega => ∑' l, Z l (translatePotentialSample z omega)) :=
      paperENNRealLpNorm_mono_ae M.P.toMeasure (zero_le_one.trans hxi)
        (Filter.Eventually.of_forall hpoint)
    _ ≤ ∑' l, paperENNRealLpNorm M.P.toMeasure xi
          (fun omega => Z l (translatePotentialSample z omega)) :=
      paperENNRealLpNorm_tsum_le_tsum M.P.toMeasure hxi
        (fun l omega => Z l (translatePotentialSample z omega))
        (fun l => (hZmeas l).comp (measurable_translatePotentialSequence z))
    _ = ∑' l, (W l ^ ((r : ℝ)⁻¹) *
          paperENNRealLpNorm M.P.toMeasure xi (A l)) := by
      apply tsum_congr
      intro l
      rw [paperENNRealLpNorm_comp_translatePotentialSample_eq M z (Z l) (hZmeas l)]
      rw [paperENNRealLpNorm_const_mul_eq M.P.toMeasure
        (zero_lt_one.trans_le hxi) _ _
        (measurable_largeCubeScaleMaximum M L K ((K : ℤ) - (l : ℤ)))]
    _ = _ := by rfl

/-! ## Uniform scale profile and its geometric sum -/

/-- Conversion from a uniform per-cell unrooted moment to the scale profile
used in all three manuscript ranges. -/
theorem largeCubeScaleMaximum_moment_profile_of_each {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L K l : ℕ)
    {xi delta1 s C : ℝ} (hxi : 0 < xi) (hdelta : 0 ≤ delta1)
    (hC : 1 ≤ C)
    (hEach : ∀ Q ∈ descendantsAtScale (originCube d (K : ℤ))
        ((K : ℤ) - (l : ℤ)),
      paperENNRealLpNorm M.P.toMeasure xi
          (normalizedDefect M L (Ch02.cubeDomain Q)) ≤
        ENNReal.ofReal (C * delta1 * (3 : ℝ) ^ (s * (l : ℝ)))) :
    paperENNRealLpNorm M.P.toMeasure xi
        (largeCubeScaleMaximum M L K ((K : ℤ) - (l : ℤ))) ≤
      ENNReal.ofReal (C * Real.sqrt delta1 *
        (3 : ℝ) ^ (((d : ℝ) / xi + s / 2) * (l : ℝ))) := by
  have hk : (K : ℤ) - (l : ℤ) ≤ (K : ℤ) := by omega
  have hmax := largeCubeScaleMaximum_moment_le_of_each M L K hxi hk
    (ENNReal.ofReal (C * delta1 * (3 : ℝ) ^ (s * (l : ℝ)))) hEach
  have hcard :
      (descendantsAtScale (originCube d (K : ℤ))
        ((K : ℤ) - (l : ℤ))).card = (3 ^ d) ^ l := by
    rw [descendantsAtScale_eq_descendantsAtDepth (originCube d (K : ℤ)) hk]
    have hdepth : Int.toNat ((originCube d (K : ℤ)).scale -
        ((K : ℤ) - (l : ℤ))) = l := by simp [originCube]
    rw [hdepth, descendantsAtDepth_card]
  rw [hcard] at hmax
  refine hmax.trans ?_
  have hbase0 : 0 ≤ C * delta1 * (3 : ℝ) ^ (s * (l : ℝ)) := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hbase0 (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  rw [← ENNReal.ofReal_natCast,
    ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr hxi.le),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) xi⁻¹)]
  apply ENNReal.ofReal_le_ofReal
  have hcardPow :
      Real.rpow (((3 ^ d) ^ l : ℕ) : ℝ) xi⁻¹ =
        Real.rpow 3 (((d : ℝ) / xi) * (l : ℝ)) := by
    rw [Nat.cast_pow, Nat.cast_pow]
    norm_num only [Nat.cast_ofNat]
    rw [← Real.rpow_natCast (3 : ℝ) d]
    change Real.rpow ((Real.rpow 3 (d : ℝ)) ^ l) xi⁻¹ = _
    rw [← Real.rpow_natCast (Real.rpow 3 (d : ℝ)) l]
    calc
      Real.rpow (Real.rpow (Real.rpow 3 (d : ℝ)) (l : ℝ)) xi⁻¹ =
          Real.rpow (Real.rpow 3 ((d : ℝ) * (l : ℝ))) xi⁻¹ := by
        congr 1
        exact (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
      _ = Real.rpow 3 (((d : ℝ) * (l : ℝ)) * xi⁻¹) :=
        (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _).symm
      _ = _ := by
        congr 1
        field_simp [hxi.ne']
  change Real.rpow (((3 ^ d) ^ l : ℕ) : ℝ) xi⁻¹ *
      Real.rpow (C * delta1 * Real.rpow 3 (s * (l : ℝ))) (1 / 2 : ℝ) ≤ _
  rw [hcardPow]
  have hsplit : Real.rpow (C * delta1 * Real.rpow 3 (s * (l : ℝ)))
      (1 / 2 : ℝ) =
      Real.rpow C (1 / 2 : ℝ) * Real.rpow delta1 (1 / 2 : ℝ) *
        Real.rpow (Real.rpow 3 (s * (l : ℝ))) (1 / 2 : ℝ) := by
    calc
      _ = Real.rpow (C * delta1) (1 / 2 : ℝ) *
          Real.rpow (Real.rpow 3 (s * (l : ℝ))) (1 / 2 : ℝ) := by
        simpa only [Real.instPow] using!
          (Real.mul_rpow (mul_nonneg (zero_le_one.trans hC) hdelta)
            (Real.rpow_nonneg (by norm_num) _) (z := (1 / 2 : ℝ)))
      _ = _ := by
        rw [show Real.rpow (C * delta1) (1 / 2 : ℝ) =
            Real.rpow C (1 / 2 : ℝ) * Real.rpow delta1 (1 / 2 : ℝ) by
          simpa only [Real.instPow] using!
            (Real.mul_rpow (zero_le_one.trans hC) hdelta (z := (1 / 2 : ℝ)))]
  rw [hsplit]
  change Real.rpow 3 ((d : ℝ) / xi * (l : ℝ)) *
      (Real.rpow C (1 / 2 : ℝ) * Real.rpow delta1 (1 / 2 : ℝ) *
        Real.rpow (Real.rpow 3 (s * (l : ℝ))) (1 / 2 : ℝ)) ≤
    C * Real.sqrt delta1 *
      Real.rpow 3 (((d : ℝ) / xi + s / 2) * (l : ℝ))
  rw [show Real.rpow delta1 (1 / 2 : ℝ) = Real.sqrt delta1 by
    simpa only [Real.instPow] using! (Real.sqrt_eq_rpow delta1).symm]
  have hCr : Real.rpow C (1 / 2 : ℝ) ≤ C :=
    Real.rpow_le_self_of_one_le hC (by norm_num)
  have hscale : Real.rpow (Real.rpow 3 (s * (l : ℝ))) (1 / 2 : ℝ) =
      Real.rpow 3 ((s / 2) * (l : ℝ)) := by
    have h := (Real.rpow_mul (by positivity : 0 ≤ (3 : ℝ))
      (s * (l : ℝ)) (1 / 2 : ℝ)).symm
    simpa only [Real.instPow] using! h.trans (by congr 1; ring)
  rw [hscale]
  have hmiddle :
      Real.rpow 3 ((d : ℝ) / xi * (l : ℝ)) *
          (Real.rpow C (1 / 2 : ℝ) * Real.sqrt delta1 *
            Real.rpow 3 (s / 2 * (l : ℝ))) ≤
        Real.rpow 3 ((d : ℝ) / xi * (l : ℝ)) *
          (C * Real.sqrt delta1 * Real.rpow 3 (s / 2 * (l : ℝ))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCr (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)
  calc
      Real.rpow 3 ((d : ℝ) / xi * (l : ℝ)) *
        (Real.rpow C (1 / 2 : ℝ) * Real.sqrt delta1 *
          Real.rpow 3 (s / 2 * (l : ℝ))) ≤
      Real.rpow 3 ((d : ℝ) / xi * (l : ℝ)) *
        (C * Real.sqrt delta1 * Real.rpow 3 (s / 2 * (l : ℝ))) := hmiddle
    _ = C * Real.sqrt delta1 *
        Real.rpow 3 (((d : ℝ) / xi + s / 2) * (l : ℝ)) := by
      calc
        _ = C * Real.sqrt delta1 *
            (Real.rpow 3 ((d : ℝ) / xi * (l : ℝ)) *
              Real.rpow 3 (s / 2 * (l : ℝ))) := by ring
        _ = C * Real.sqrt delta1 *
            Real.rpow 3 (((d : ℝ) / xi * (l : ℝ)) +
              s / 2 * (l : ℝ)) := by
          congr 1
          simpa only [Real.instPow] using!
            (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
              ((d : ℝ) / xi * (l : ℝ)) (s / 2 * (l : ℝ))).symm
        _ = _ := by (congr 2; ring)

/-- Summation of the normalized geometric weights against a profile whose
growth exponent is at most `3s/4`.  The two admitted anchor exponents are
handled separately to retain the sharp `s^(-1/r)` normalization. -/
theorem tsum_geometricWeight_root_mul_profile_le {s a A : ℝ} {r : ℕ}
    (hr : r = 1 ∨ r = 2) (hs : 0 < s) (hs1 : s ≤ 1)
    (hA : 0 ≤ A) (ha0 : 0 ≤ a) (ha : a ≤ 3 * s / 4) :
    (∑' l : ℕ,
      Real.rpow (Ch02.geometricWeight s (r : ℝ) l) ((r : ℝ)⁻¹) *
        (A * Real.rpow 3 (a * (l : ℝ)))) ≤
      40 * A * Real.rpow s (-(1 / (r : ℝ))) := by
  let gap := s - a
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  have hgap_le : gap ≤ 1 := by dsimp only [gap]; linarith
  have hinv : (Ch02.geometricDiscount gap 1)⁻¹ ≤ 20 * s⁻¹ := by
    have h := Ch02.inv_geometricDiscount_le_five_inv (p := 1)
      hgap hgap_le (by norm_num)
    have hgapInv : gap⁻¹ ≤ 4 * s⁻¹ := by
      have hraw := (inv_le_inv₀ hgap (by positivity : 0 < s / 4)).2
        (show s / 4 ≤ gap by dsimp only [gap]; linarith)
      calc gap⁻¹ ≤ (s / 4)⁻¹ := hraw
        _ = 4 * s⁻¹ := by field_simp [hs.ne']
    linarith
  have hseries : ∑' l : ℕ, Real.rpow 3 (-gap * (l : ℝ)) =
      (Ch02.geometricDiscount gap 1)⁻¹ :=
    Homogenization.Book.Ch05.Section52.tsum_rpow_three_neg_mul_nat_eq_inv_geometricDiscount hgap
  rcases hr with rfl | rfl
  · have hterm : ∀ l : ℕ,
        Real.rpow (Ch02.geometricWeight s (1 : ℝ) l) (1 : ℝ)⁻¹ *
            (A * Real.rpow 3 (a * (l : ℝ))) ≤
          A * Real.rpow 3 (-gap * (l : ℝ)) := by
      intro l
      norm_num
      rw [Ch02.geometricWeight]
      have hdisc : Ch02.geometricDiscount s 1 ≤ 1 :=
        Homogenization.Book.Ch05.Section52.geometricDiscount_one_le_one s
      have hpow0 : 0 ≤ A * Real.rpow 3 (-gap * (l : ℝ)) :=
        mul_nonneg hA (Real.rpow_nonneg (by norm_num) _)
      have hpows : Real.rpow 3 (-s * 1 * (l : ℝ)) *
          Real.rpow 3 (a * (l : ℝ)) = Real.rpow 3 (-gap * (l : ℝ)) := by
        calc
          _ = Real.rpow 3 ((-s * 1 * (l : ℝ)) + a * (l : ℝ)) :=
            by simpa only [Real.instPow] using!
              (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
                (-s * 1 * (l : ℝ)) (a * (l : ℝ))).symm
          _ = _ := by
            congr 1
            dsimp only [gap]
            ring
      have hcalc : Ch02.geometricDiscount s 1 *
          Real.rpow 3 (-s * 1 * (l : ℝ)) *
            (A * Real.rpow 3 (a * (l : ℝ))) ≤
          A * Real.rpow 3 (-gap * (l : ℝ)) := by
        calc
          _ = Ch02.geometricDiscount s 1 * A *
            (Real.rpow 3 (-s * 1 * (l : ℝ)) *
              Real.rpow 3 (a * (l : ℝ))) := by ring
          _ = Ch02.geometricDiscount s 1 *
            (A * Real.rpow 3 (-gap * (l : ℝ))) := by rw [hpows]; ring
          _ ≤ 1 * (A * Real.rpow 3 (-gap * (l : ℝ))) :=
            mul_le_mul_of_nonneg_right hdisc hpow0
          _ = _ := by ring
      rw [show (3 : ℝ) ^ (a * (l : ℝ)) =
          Real.rpow 3 (a * (l : ℝ)) by rfl,
        show (3 : ℝ) ^ (-(gap * (l : ℝ))) =
          Real.rpow 3 (-gap * (l : ℝ)) by
            rw [show -(gap * (l : ℝ)) = -gap * (l : ℝ) by ring]
            rfl]
      exact hcalc
    have hrhsSum :=
      (Homogenization.Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hgap).mul_left A
    have hlhsSum : Summable (fun l : ℕ =>
        Real.rpow (Ch02.geometricWeight s (1 : ℝ) l) (1 : ℝ)⁻¹ *
          (A * Real.rpow 3 (a * (l : ℝ)))) :=
      Summable.of_nonneg_of_le (fun l => mul_nonneg
        (Real.rpow_nonneg (Homogenization.geometricWeight_nonneg l (by positivity)) _)
        (mul_nonneg hA (Real.rpow_nonneg (by norm_num) _))) hterm hrhsSum
    calc
      _ ≤ ∑' l : ℕ, A * Real.rpow 3 (-gap * (l : ℝ)) := by
        (convert Summable.tsum_le_tsum (fun l => by simpa using! hterm l)
          hlhsSum hrhsSum using 1; norm_num)
      _ = A * (Ch02.geometricDiscount gap 1)⁻¹ := by rw [tsum_mul_left, hseries]
      _ ≤ A * (20 * s⁻¹) := mul_le_mul_of_nonneg_left hinv hA
      _ ≤ 40 * A * Real.rpow s (-(1 / (1 : ℝ))) := by
        norm_num
        rw [Real.rpow_neg_one]
        nlinarith [mul_nonneg hA (inv_nonneg.mpr hs.le)]
      _ = 40 * A * Real.rpow s (-(1 / ((1 : ℕ) : ℝ))) := by norm_num
  · have hdisc : Ch02.geometricDiscount s 2 ≤ 4 * s := by
      exact (Ch02.geometricDiscount_le_two_mul (mul_nonneg hs.le (by norm_num))).trans_eq
        (by ring)
    have hdisc0 : 0 ≤ Ch02.geometricDiscount s 2 :=
      Homogenization.geometricDiscount_nonneg (by positivity)
    have hsqrtDisc : Real.rpow (Ch02.geometricDiscount s 2) (1 / 2 : ℝ) ≤
        2 * Real.sqrt s := by
      have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
          Real.sqrt_nonneg (4 : ℝ)]
      rw [show Real.rpow (Ch02.geometricDiscount s 2) (1 / 2 : ℝ) =
          Real.sqrt (Ch02.geometricDiscount s 2) by
        simpa only [Real.instPow] using!
          (Real.sqrt_eq_rpow (Ch02.geometricDiscount s 2)).symm]
      calc
        _ ≤ Real.sqrt (4 * s) := Real.sqrt_le_sqrt hdisc
        _ = Real.sqrt 4 * Real.sqrt s := Real.sqrt_mul (by norm_num) s
        _ = _ := by rw [hsqrt4]
    have hterm : ∀ l : ℕ,
        Real.rpow (Ch02.geometricWeight s (2 : ℝ) l) (2 : ℝ)⁻¹ *
            (A * Real.rpow 3 (a * (l : ℝ))) ≤
          (2 * Real.sqrt s * A) * Real.rpow 3 (-gap * (l : ℝ)) := by
      intro l
      norm_num
      rw [Ch02.geometricWeight]
      have hsplit :
          (Ch02.geometricDiscount s 2 * Real.rpow 3 (-s * 2 * (l : ℝ)))
            ^ (1 / 2 : ℝ) =
          (Ch02.geometricDiscount s 2) ^ (1 / 2 : ℝ) *
            (Real.rpow 3 (-s * 2 * (l : ℝ))) ^ (1 / 2 : ℝ) :=
        Real.mul_rpow hdisc0 (Real.rpow_nonneg (by norm_num) _)
      have hsplit' : Real.rpow
          (Ch02.geometricDiscount s 2 * Real.rpow 3 (-s * 2 * (l : ℝ)))
            (1 / 2 : ℝ) =
          Real.rpow (Ch02.geometricDiscount s 2) (1 / 2 : ℝ) *
            Real.rpow (Real.rpow 3 (-s * 2 * (l : ℝ))) (1 / 2 : ℝ) := by
        simpa only [Real.instPow] using! hsplit
      have hscale : Real.rpow (Real.rpow 3 (-s * 2 * (l : ℝ)))
          (1 / 2 : ℝ) = Real.rpow 3 (-s * 2 * (l : ℝ) * (1 / 2 : ℝ)) := by
        simpa only [Real.instPow] using!
          (Real.rpow_mul (by positivity : 0 ≤ (3 : ℝ))
            (-s * 2 * (l : ℝ)) (1 / 2 : ℝ)).symm
      have hp : Real.rpow 3 (-s * 2 * (l : ℝ) * (1 / 2 : ℝ)) *
          Real.rpow 3 (a * (l : ℝ)) = Real.rpow 3 (-gap * (l : ℝ)) := by
        calc
          _ = Real.rpow 3
              ((-s * 2 * (l : ℝ) * (1 / 2 : ℝ)) + a * (l : ℝ)) :=
            by simpa only [Real.instPow] using!
              (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
                (-s * 2 * (l : ℝ) * (1 / 2 : ℝ)) (a * (l : ℝ))).symm
          _ = _ := by
            congr 1
            dsimp only [gap]
            ring
      have hcalc : Real.rpow
          (Ch02.geometricDiscount s 2 * Real.rpow 3 (-s * 2 * (l : ℝ)))
            (1 / 2 : ℝ) * (A * Real.rpow 3 (a * (l : ℝ))) ≤
          (2 * Real.sqrt s * A) * Real.rpow 3 (-gap * (l : ℝ)) := by
        rw [hsplit', hscale]
        calc
          _ = Real.rpow (Ch02.geometricDiscount s 2) (1 / 2 : ℝ) * A *
            (Real.rpow 3 (-s * 2 * (l : ℝ) * (1 / 2 : ℝ)) *
              Real.rpow 3 (a * (l : ℝ))) := by ring
          _ = Real.rpow (Ch02.geometricDiscount s 2) (1 / 2 : ℝ) * A *
            Real.rpow 3 (-gap * (l : ℝ)) := by rw [hp]
          _ ≤ (2 * Real.sqrt s) * A * Real.rpow 3 (-gap * (l : ℝ)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hsqrtDisc hA)
              (Real.rpow_nonneg (by norm_num) _)
          _ = _ := by ring
      rw [show (3 : ℝ) ^ (a * (l : ℝ)) =
          Real.rpow 3 (a * (l : ℝ)) by rfl,
        show (3 : ℝ) ^ (-(gap * (l : ℝ))) =
          Real.rpow 3 (-gap * (l : ℝ)) by
            rw [show -(gap * (l : ℝ)) = -gap * (l : ℝ) by ring]
            rfl,
        show (Ch02.geometricDiscount s 2 *
            Real.rpow 3 (-s * 2 * (l : ℝ))) ^ (1 / 2 : ℝ) =
          Real.rpow (Ch02.geometricDiscount s 2 *
            Real.rpow 3 (-s * 2 * (l : ℝ))) (1 / 2 : ℝ) by rfl]
      exact hcalc
    have hrhsSum :=
      (Homogenization.Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hgap).mul_left
        (2 * Real.sqrt s * A)
    have hlhsSum : Summable (fun l : ℕ =>
        Real.rpow (Ch02.geometricWeight s (2 : ℝ) l) (2 : ℝ)⁻¹ *
          (A * Real.rpow 3 (a * (l : ℝ)))) :=
      Summable.of_nonneg_of_le (fun l => mul_nonneg
        (Real.rpow_nonneg (Homogenization.geometricWeight_nonneg l (by positivity)) _)
        (mul_nonneg hA (Real.rpow_nonneg (by norm_num) _))) hterm hrhsSum
    calc
      _ ≤ ∑' l : ℕ, (2 * Real.sqrt s * A) *
          Real.rpow 3 (-gap * (l : ℝ)) := by
        exact Summable.tsum_le_tsum (fun l => by simpa using! hterm l) hlhsSum hrhsSum
      _ = (2 * Real.sqrt s * A) * (Ch02.geometricDiscount gap 1)⁻¹ := by
        rw [tsum_mul_left, hseries]
      _ ≤ (2 * Real.sqrt s * A) * (20 * s⁻¹) := by
        gcongr
      _ = 40 * A * Real.rpow s (-(1 / (2 : ℝ))) := by
        have hrpow : Real.rpow s (-(1 / 2 : ℝ)) = (Real.sqrt s)⁻¹ := by
          calc
            _ = (Real.rpow s (1 / 2 : ℝ))⁻¹ := by
              simpa only [Real.instPow] using!
                (Real.rpow_neg hs.le (1 / 2 : ℝ))
            _ = _ := by
              congr 1
              simpa only [Real.instPow] using! (Real.sqrt_eq_rpow s).symm
        rw [hrpow]
        field_simp [hs.ne', (Real.sqrt_pos.2 hs).ne']
        rw [Real.sq_sqrt hs.le]
        ring
      _ = 40 * A * Real.rpow s (-(1 / ((2 : ℕ) : ℝ))) := by norm_num

/-- Summability companion to `tsum_geometricWeight_root_mul_profile_le`. -/
theorem summable_geometricWeight_root_mul_profile {s a A : ℝ} {r : ℕ}
    (hr : r = 1 ∨ r = 2) (hs : 0 < s)
    (ha : a ≤ 3 * s / 4) :
    Summable (fun l : ℕ =>
      Real.rpow (Ch02.geometricWeight s (r : ℝ) l) ((r : ℝ)⁻¹) *
        (A * Real.rpow 3 (a * (l : ℝ)))) := by
  have haLt : a < s := by linarith
  rcases hr with rfl | rfl
  · have h := summable_geometricWeight_mul_shifted_rpow
      (s := s) (a := a) (A := A) 0 haLt
    convert h using 1
    funext l
    norm_num only [Nat.cast_one, inv_one, Nat.zero_add]
    rw [show Real.rpow (Ch02.geometricWeight s 1 l) 1 =
        Ch02.geometricWeight s 1 l by
      simpa only [Real.instPow] using!
        (Real.rpow_one (Ch02.geometricWeight s 1 l))]
  · let gap := s - a
    have hgap : 0 < gap := by dsimp only [gap]; linarith
    have hdisc0 : 0 ≤ Ch02.geometricDiscount s 2 :=
      Homogenization.geometricDiscount_nonneg (by positivity)
    have hgeom :=
      (Homogenization.Book.Ch05.Section52.summable_rpow_three_neg_mul_nat hgap).mul_left
        (Real.rpow (Ch02.geometricDiscount s 2) (1 / 2 : ℝ) * A)
    convert hgeom using 1
    funext l
    norm_num
    rw [Ch02.geometricWeight]
    rw [show (Ch02.geometricDiscount s 2 * Real.rpow 3 (-s * 2 * (l : ℝ))) ^
          (1 / 2 : ℝ) =
        Real.rpow (Ch02.geometricDiscount s 2 *
          Real.rpow 3 (-s * 2 * (l : ℝ))) (1 / 2 : ℝ) by rfl,
      show (3 : ℝ) ^ (a * (l : ℝ)) = Real.rpow 3 (a * (l : ℝ)) by rfl,
      show (3 : ℝ) ^ (-(gap * (l : ℝ))) =
          Real.rpow 3 (-gap * (l : ℝ)) by
        rw [show -(gap * (l : ℝ)) = -gap * (l : ℝ) by ring]
        rfl]
    rw [show (Ch02.geometricDiscount s 2) ^ (1 / 2 : ℝ) =
        Real.rpow (Ch02.geometricDiscount s 2) (1 / 2 : ℝ) by rfl]
    have hsplit : Real.rpow
        (Ch02.geometricDiscount s 2 * Real.rpow 3 (-s * 2 * (l : ℝ)))
          (1 / 2 : ℝ) =
        Real.rpow (Ch02.geometricDiscount s 2) (1 / 2 : ℝ) *
          Real.rpow (Real.rpow 3 (-s * 2 * (l : ℝ))) (1 / 2 : ℝ) := by
      simpa only [Real.instPow] using!
        (Real.mul_rpow hdisc0 (Real.rpow_nonneg (by norm_num) _)
          (z := (1 / 2 : ℝ)))
    rw [hsplit]
    have hscale : Real.rpow (Real.rpow 3 (-s * 2 * (l : ℝ)))
        (1 / 2 : ℝ) = Real.rpow 3 (-s * (l : ℝ)) := by
      calc
        _ = Real.rpow 3 (-s * 2 * (l : ℝ) * (1 / 2 : ℝ)) := by
          simpa only [Real.instPow] using!
            (Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ))
              (-s * 2 * (l : ℝ)) (1 / 2 : ℝ)).symm
        _ = _ := by congr 1; ring
    rw [hscale]
    have hcombine : Real.rpow 3 (-s * (l : ℝ)) *
        Real.rpow 3 (a * (l : ℝ)) = Real.rpow 3 (-gap * (l : ℝ)) := by
      calc
        _ = Real.rpow 3 ((-s * (l : ℝ)) + a * (l : ℝ)) := by
          simpa only [Real.instPow] using!
            (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
              (-s * (l : ℝ)) (a * (l : ℝ))).symm
        _ = _ := by congr 1; dsimp only [gap]; ring
    calc
      _ = Real.rpow (Ch02.geometricDiscount s 2) (1 / 2 : ℝ) * A *
          (Real.rpow 3 (-s * (l : ℝ)) * Real.rpow 3 (a * (l : ℝ))) := by ring
      _ = _ := by rw [hcombine]

end

end SubdiffusiveProcess.CoarseGrainingVocab
