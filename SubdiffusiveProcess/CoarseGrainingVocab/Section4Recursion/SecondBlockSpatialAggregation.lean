module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellMomentAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.LargeCubePartitionResponse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpTwoBlockMoment
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.EllipticitySpecialization
public import SubdiffusiveProcess.Frozen.Section3.AnnealedMatrixBounds

@[expose] public section

/-!
# Spatial aggregation in the second Section 4 induction

This module composes the four ingredients in source lines 5010--5059:
parent response subadditivity, cellwise two-block localization, finite spatial
Cauchy--Schwarz, and prefix/suffix moment factorization.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal BigOperators

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Exact exponent conversion for the square root of a nonnegative
observable in the manuscript moment convention. -/
theorem paperENNRealLpNorm_rpow_half_eq {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) {p : ℝ} (hp : 0 < p)
    (X : Omega → ℝ≥0∞) :
    paperENNRealLpNorm mu p (fun omega => X omega ^ (1 / 2 : ℝ)) =
      (paperENNRealLpNorm mu (p / 2) X) ^ (1 / 2 : ℝ) := by
  unfold paperENNRealLpNorm
  have hp2 : 0 < p / 2 := by positivity
  rw [show (fun omega => (X omega ^ (1 / 2 : ℝ)) ^ p) =
      fun omega => X omega ^ (p / 2) by
    funext omega
    rw [← ENNReal.rpow_mul]
    congr 1
    ring]
  rw [← ENNReal.rpow_mul]
  congr 1
  field_simp

/-- Exact exponent conversion for a squared nonnegative observable. -/
theorem paperENNRealLpNorm_rpow_two_eq {Omega : Type*}
    [MeasurableSpace Omega] (mu : Measure Omega) {p : ℝ} (hp : 0 < p)
    (X : Omega → ℝ≥0∞) :
    paperENNRealLpNorm mu p (fun omega => X omega ^ (2 : ℝ)) =
      (paperENNRealLpNorm mu (2 * p) X) ^ (2 : ℝ) := by
  unfold paperENNRealLpNorm
  rw [show (fun omega => (X omega ^ (2 : ℝ)) ^ p) =
      fun omega => X omega ^ (2 * p) by
    funext omega
    rw [← ENNReal.rpow_mul]]
  rw [← ENNReal.rpow_mul]
  congr 1
  field_simp

/-- Dimension-only coefficient of the linear shell term in the second
induction.  The factor `3` is the exact value of the geometric loss after
choosing the interpolation exponent `s = 1 / h`. -/
noncomputable def secondBlockSpatialShellFactor (d : ℕ) : ℝ :=
  3 * sharpTwoBlockMomentConst d * (sharpTwoBlockSmallnessConst d)⁻¹

theorem secondBlockSpatialShellFactor_pos (d : ℕ) :
    0 < secondBlockSpatialShellFactor d := by
  unfold secondBlockSpatialShellFactor
  exact mul_pos (mul_pos (by norm_num)
    (zero_lt_one.trans_le (one_le_sharpTwoBlockMomentConst d)))
      (inv_pos.mpr (sharpTwoBlockSmallnessConst_pos d))

/-- The cellwise sharp two-block suffix moment with the source choice
`s = 1 / h`.  Its geometric factor is exactly three, leaving a term linear
in the block length. -/
theorem sharpTwoBlock_suffix_square_moment_le_linear_shell
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {r k h : ℕ}
    (hkr : k < r) (hgap : r - k = h) (hh : 0 < h) {xi : ℝ}
    (hxi : 1 ≤ xi)
    (hsmall : (sharpTwoBlockSmallnessConst d)⁻¹ *
      xi * M.delta ^ 2 * (h : ℝ) < 1)
    (R : Homogenization.TriadicCube d) :
    paperENNRealLpNorm M.P.toMeasure xi (fun omega => ENNReal.ofReal
        (sharpTwoBlockSuffixRepresentative M r k
          (triadicCubeShift R) omega ^ 2)) ≤
      ENNReal.ofReal
        (secondBlockSpatialShellFactor d * xi * M.delta ^ 2 * (h : ℝ)) := by
  let c := sharpTwoBlockSmallnessConst d
  let deltaShell : ℝ := c⁻¹ * xi * M.delta ^ 2 * (h : ℝ)
  let s : ℝ := ((h : ℝ))⁻¹
  have hc : 0 < c := sharpTwoBlockSmallnessConst_pos d
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hs : 0 < s := by dsimp only [s]; positivity
  have hs1 : s ≤ 1 := by
    dsimp only [s]
    exact (inv_le_one₀ hhR).2 (by exact_mod_cast hh)
  have hdelta : deltaShell < 1 := by simpa only [deltaShell, c] using! hsmall
  have hxiE : xi * M.delta ^ 2 ≤ c * s * deltaShell := by
    dsimp only [s, deltaShell]
    field_simp [hc.ne', hhR.ne']
    exact le_rfl
  have hraw := sharpTwoBlock_squared_moment_of_ordering M hkr
    (triadicCubeShift R) hxi hdelta hs hs1 hxiE
      (SubdiffusiveProcess.Frozen.Section3.annealed_matrix_bounds.2 M r k hkr)
  have hgeom : (3 : ℝ) ^ (s * ((r - k : ℕ) : ℝ)) = 3 := by
    rw [hgap]
    dsimp only [s]
    rw [inv_mul_cancel₀ hhR.ne', Real.rpow_one]
  refine hraw.trans_eq ?_
  congr 1
  dsimp only [deltaShell, c, secondBlockSpatialShellFactor]
  rw [hgeom]
  ring

private theorem normalizedDefect_ne_top_of_quarterNet {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (omega : Sample d) : normalizedDefect M L U omega ≠ ⊤ := by
  have hle := normalizedDefect_le_two_mul_quarterNetMax M L U omega
  have hmax : normalizedResponseQuarterNetMax M L U omega ≠ ⊤ := by
    unfold normalizedResponseQuarterNetMax
    rw [Finset.sup'_apply]
    obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_sup'
      (sphereQuarterNet_points_nonempty (d := d)) (fun e =>
        ENNReal.ofReal
          (J U (aCutoffCoeffOnData M L omega U).toCoeffOn
            ((Real.sqrt (ahom M L))⁻¹ • e)
            (Real.sqrt (ahom M L) • e)))
    rw [heq]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by norm_num) hmax) hle

/-- Cauchy--Schwarz for a normalized finite average, in the real carrier used
by the literal localization error and normalized-defect `toReal`. -/
private theorem normalized_finset_sum_mul_le_sqrt_mul_sqrt
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (f g : ι → ℝ) :
    ((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i * g i ≤
      Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, f i ^ 2) *
        Real.sqrt (((s.card : ℝ)⁻¹) * ∑ i ∈ s, g i ^ 2) := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.normalized_finset_sum_mul_le_sqrt_mul_sqrt (ι := ι) (s := s) (hs := hs) (f := f) (g := g)

/-- The exact source display at lines 5010--5059.  A uniform suffix-square
moment and the prefix square-average moment imply the parent-scale response
bound after spatial Cauchy--Schwarz and shell independence. -/
theorem normalizedDefect_parent_le_secondBlockSpatialBound
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {r k : ℕ}
    (hkr : k < r) {xi delta1 shell : ℝ}
    (hxi : 4 ≤ xi) (hdelta : 0 ≤ delta1) (hshell : 0 ≤ shell)
    (hprefix :
      paperENNRealLpNorm M.P.toMeasure (xi / 2) (fun omega =>
        ENNReal.ofReal
          ((((descendantsAtScale (originCube d (r : ℤ)) (k : ℤ)).card : ℝ)⁻¹) *
            ∑ R ∈ descendantsAtScale (originCube d (r : ℤ)) (k : ℤ),
              (normalizedDefect M k (Ch02.cubeDomain R) omega).toReal ^ 2)) ≤
        ENNReal.ofReal ((1 / 36 : ℝ) * delta1 ^ 2))
    (hsuffix : ∀ R ∈ descendantsAtScale (originCube d (r : ℤ)) (k : ℤ),
      paperENNRealLpNorm M.P.toMeasure xi (fun omega => ENNReal.ofReal
        (sharpTwoBlockSuffixRepresentative M r k (triadicCubeShift R) omega ^ 2)) ≤
        ENNReal.ofReal shell) :
    paperENNRealLpNorm M.P.toMeasure xi
        (normalizedDefectAt M r r) ≤
      ENNReal.ofReal
        (3 * shell + (1 / 2 : ℝ) * (1 + shell) * delta1) := by
  classical
  let D := descendantsAtScale (originCube d (r : ℤ)) (k : ℤ)
  let c : ℝ := ((D.card : ℝ)⁻¹)
  let X : TriadicCube d → Sample d → ℝ := fun R omega =>
    sharpTwoBlockSuffixRepresentative M r k (triadicCubeShift R) omega ^ 2
  let Jk : TriadicCube d → Sample d → ℝ := fun R omega =>
    (normalizedDefect M k (Ch02.cubeDomain R) omega).toReal
  let Xavg : Sample d → ℝ := fun omega => c * ∑ R ∈ D, X R omega
  let XA : Sample d → ℝ := fun omega =>
    Real.sqrt (c * ∑ R ∈ D, (1 + X R omega) ^ 2)
  let JB : Sample d → ℝ := fun omega =>
    Real.sqrt (c * ∑ R ∈ D, Jk R omega ^ 2)
  have hD : D.Nonempty := descendantsAtScale_nonempty _ (by
    change (k : ℤ) ≤ (r : ℤ)
    exact_mod_cast hkr.le)
  have hc_ofReal : ENNReal.ofReal c = (D.card : ℝ≥0∞)⁻¹ := by
    dsimp only [c]
    rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hX0 : ∀ R omega, 0 ≤ X R omega := fun _ _ => by dsimp only [X]; positivity
  have hJ0 : ∀ R omega, 0 ≤ Jk R omega := fun _ _ => by
    dsimp only [Jk]
    exact ENNReal.toReal_nonneg
  have hXavg0 : ∀ omega, 0 ≤ Xavg omega := fun _ => by
    dsimp only [Xavg]
    positivity
  have hXA0 : ∀ omega, 0 ≤ XA omega := fun _ => Real.sqrt_nonneg _
  have hJB0 : ∀ omega, 0 ≤ JB omega := fun _ => Real.sqrt_nonneg _
  have hXmeas : ∀ R ∈ D,
      @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Ioi k)) _ (X R) := by
    intro R hR
    dsimp only [X]
    exact (measurable_sharpTwoBlockSuffixRepresentative M hkr.le
      (triadicCubeShift R)).pow_const 2
  have hJmeas : ∀ R ∈ D,
      @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Iic k)) _ (Jk R) := by
    intro R hR
    dsimp only [Jk]
    exact (measurable_normalizedDefect_potentialShellIndexSigma_Iic M k
      (Ch02.cubeDomain R)).ennreal_toReal
  have hXavgMeas :
      @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Ioi k)) _ Xavg := by
    dsimp only [Xavg]
    exact measurable_const.mul (Finset.measurable_sum _ hXmeas)
  have hXAMeas :
      @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Ioi k)) _ XA := by
    dsimp only [XA]
    exact (measurable_const.mul (Finset.measurable_sum _ fun R hR =>
      (measurable_const.add (hXmeas R hR)).pow_const 2)).sqrt
  have hJBMeas :
      @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Iic k)) _ JB := by
    dsimp only [JB]
    exact (measurable_const.mul (Finset.measurable_sum _ fun R hR =>
      (hJmeas R hR).pow_const 2)).sqrt
  have hloc : ∀ R ∈ D, ∀ᵐ omega ∂M.P.toMeasure,
      normalizedDefect M r (Ch02.cubeDomain R) omega ≤
        ENNReal.ofReal (2 * Jk R omega + 3 * X R omega * (Jk R omega + 1)) := by
    intro R hR
    have hsuf := sharpTwoBlock_dominates_localization M hkr.le le_rfl R hR
    filter_upwards [hsuf] with omega hsufomega
    have hraw := paperScalarProbeMaxOn_cutoff_le_localized M r k
      (Ch02.cubeDomain R) (ahom M r) (ahom_pos M r) omega
    rw [tailCoefficientCubeAverage_self M r omega] at hsufomega
    have hDtop := normalizedDefect_ne_top_of_quarterNet M k
      (Ch02.cubeDomain R) omega
    have hDof : ENNReal.ofReal (Jk R omega) =
        normalizedDefect M k (Ch02.cubeDomain R) omega := by
      dsimp only [Jk]
      exact ENNReal.ofReal_toReal hDtop
    have hbound :
        paperScalarProbeMaxOn (Ch02.cubeDomain R)
            (aCutoffCoeffOnData M r omega (Ch02.cubeDomain R)).toCoeffOn
            (ahom M r) ≤
          2 * normalizedDefect M k (Ch02.cubeDomain R) omega +
            3 * ENNReal.ofReal (X R omega) *
              (normalizedDefect M k (Ch02.cubeDomain R) omega + 1) :=
      hraw.trans (by
        gcongr)
    calc
      normalizedDefect M r (Ch02.cubeDomain R) omega ≤
          2 * normalizedDefect M k (Ch02.cubeDomain R) omega +
            3 * ENNReal.ofReal (X R omega) *
              (normalizedDefect M k (Ch02.cubeDomain R) omega + 1) := by
        simpa only [normalizedDefect] using! hbound
      _ = ENNReal.ofReal
          (2 * Jk R omega + 3 * X R omega * (Jk R omega + 1)) := by
        rw [← hDof, ENNReal.ofReal_add (mul_nonneg (by norm_num) (hJ0 R omega))
            (mul_nonneg (mul_nonneg (by norm_num) (hX0 R omega))
              (add_nonneg (hJ0 R omega) zero_le_one)),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
          ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
            (hX0 R omega)),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_ofNat,
          ENNReal.ofReal_add (hJ0 R omega) zero_le_one, ENNReal.ofReal_one]
  have hpoint : ∀ᵐ omega ∂M.P.toMeasure,
      normalizedDefectAt M r r omega ≤
        ENNReal.ofReal (3 * Xavg omega + 3 * XA omega * JB omega) := by
    filter_upwards [ae_all_iff.2 fun R => ae_all_iff.2 fun hR => hloc R hR]
      with omega hall
    have hsub := normalizedDefect_le_descendantsENNAverage M r
      (originCube d (r : ℤ)) (r - k) omega
    have hscale : (k : ℤ) ≤ (originCube d (r : ℤ)).scale := by
      change (k : ℤ) ≤ (r : ℤ)
      exact_mod_cast hkr.le
    have hdepth : descendantsAtDepth (originCube d (r : ℤ)) (r - k) = D := by
      dsimp only [D]
      rw [descendantsAtScale_eq_descendantsAtDepth _ hscale]
      congr 1
      change r - k = ((r : ℤ) - (k : ℤ)).toNat
      omega
    rw [descendantsENNAverage, hdepth] at hsub
    have hsum := Finset.sum_le_sum fun R hR => hall R hR
    have hrealCell : c * ∑ R ∈ D,
        (2 * Jk R omega + 3 * X R omega * (Jk R omega + 1)) ≤
        3 * Xavg omega + 3 * XA omega * JB omega := by
      have hcs := normalized_finset_sum_mul_le_sqrt_mul_sqrt D hD
        (fun R => 1 + X R omega) (fun R => Jk R omega)
      dsimp only [Xavg, XA, JB, c] at hcs ⊢
      have hterm : ∀ R ∈ D,
          2 * Jk R omega + 3 * X R omega * (Jk R omega + 1) ≤
            3 * X R omega + 3 * (1 + X R omega) * Jk R omega := by
        intro R hR
        nlinarith [hJ0 R omega, hX0 R omega]
      have havg := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum hterm) hc0
      calc
        c * ∑ R ∈ D,
            (2 * Jk R omega + 3 * X R omega * (Jk R omega + 1)) ≤
            c * ∑ R ∈ D,
              (3 * X R omega + 3 * (1 + X R omega) * Jk R omega) := havg
        _ = 3 * (c * ∑ R ∈ D, X R omega) +
            3 * (c * ∑ R ∈ D, (1 + X R omega) * Jk R omega) := by
          rw [Finset.sum_add_distrib]
          simp_rw [mul_assoc, ← Finset.mul_sum]
          ring
        _ ≤ 3 * (c * ∑ R ∈ D, X R omega) +
            3 * Real.sqrt (c * ∑ R ∈ D, (1 + X R omega) ^ 2) *
              Real.sqrt (c * ∑ R ∈ D, Jk R omega ^ 2) := by
          nlinarith [hcs]
    calc
      normalizedDefectAt M r r omega ≤
          (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D,
            normalizedDefect M r (Ch02.cubeDomain R) omega := by
        simpa only [normalizedDefectAt, hdepth, descendantsENNAverage] using! hsub
      _ ≤ (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D,
          ENNReal.ofReal
            (2 * Jk R omega + 3 * X R omega * (Jk R omega + 1)) := by gcongr
      _ = ENNReal.ofReal (c * ∑ R ∈ D,
          (2 * Jk R omega + 3 * X R omega * (Jk R omega + 1))) := by
        rw [← hc_ofReal, ENNReal.ofReal_mul hc0,
          ENNReal.ofReal_sum_of_nonneg (fun R _ => by positivity)]
      _ ≤ ENNReal.ofReal (3 * Xavg omega + 3 * XA omega * JB omega) :=
        ENNReal.ofReal_le_ofReal hrealCell
  have hxi0 : 0 < xi := by linarith
  have hrho0 : 0 < xi / 2 := by linarith
  let XE : TriadicCube d → Sample d → ℝ≥0∞ := fun R omega =>
    ENNReal.ofReal (X R omega)
  have hXEnorm : ∀ R ∈ D,
      paperENNRealLpNorm M.P.toMeasure xi (XE R) ≤ ENNReal.ofReal shell := by
    intro R hR
    simpa only [XE, X, D] using! hsuffix R hR
  have hXEambient : ∀ R ∈ D, Measurable (XE R) := by
    intro R hR
    exact (hXmeas R hR).ennreal_ofReal.mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi k)) le_rfl
  have hXavgNorm : paperENNRealLpNorm M.P.toMeasure xi
      (fun omega => ENNReal.ofReal (Xavg omega)) ≤ ENNReal.ofReal shell := by
    have hsum := paperENNRealLpNorm_finset_sum_le M.P.toMeasure
      (show 1 ≤ xi by linarith) D XE hXEambient
    have hbound := hsum.trans (Finset.sum_le_sum fun R hR => hXEnorm R hR)
    have hconst := paperENNRealLpNorm_const_mul_eq M.P.toMeasure hxi0
      (D.card : ℝ≥0∞)⁻¹ (fun omega => ∑ R ∈ D, XE R omega)
      (Finset.measurable_sum _ hXEambient)
    have hfun : (fun omega => ENNReal.ofReal (Xavg omega)) =
        fun omega => (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, XE R omega := by
      funext omega
      dsimp only [Xavg, c, XE]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg]
      · rw [hc_ofReal]
      · exact fun R hR => hX0 R omega
    rw [hfun, hconst]
    calc
      (D.card : ℝ≥0∞)⁻¹ *
          paperENNRealLpNorm M.P.toMeasure xi (fun omega => ∑ R ∈ D, XE R omega) ≤
          (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, ENNReal.ofReal shell := by gcongr
      _ = ENNReal.ofReal shell := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← mul_assoc, ENNReal.inv_mul_cancel]
        · simp
        · exact_mod_cast hD.card_ne_zero
        · exact ENNReal.coe_ne_top
  let XplusSq : Sample d → ℝ≥0∞ := fun omega => ENNReal.ofReal
    (c * ∑ R ∈ D, (1 + X R omega) ^ 2)
  have hXplusSqMeas : Measurable XplusSq := by
    dsimp only [XplusSq]
    exact (measurable_const.mul (Finset.measurable_sum _ fun R hR =>
      (measurable_const.add ((hXmeas R hR).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi k)) le_rfl)).pow_const 2)).ennreal_ofReal
  have hXplusSqNorm : paperENNRealLpNorm M.P.toMeasure (xi / 2) XplusSq ≤
      ENNReal.ofReal ((1 + shell) ^ 2) := by
    let Z : TriadicCube d → Sample d → ℝ≥0∞ := fun R omega =>
      (1 + XE R omega) ^ (2 : ℝ)
    have hZmeas : ∀ R ∈ D, Measurable (Z R) := by
      intro R hR
      exact ENNReal.continuous_rpow_const.measurable.comp
        (measurable_const.add (hXEambient R hR))
    have hZnorm : ∀ R ∈ D,
        paperENNRealLpNorm M.P.toMeasure (xi / 2) (Z R) ≤
          ENNReal.ofReal ((1 + shell) ^ 2) := by
      intro R hR
      rw [paperENNRealLpNorm_rpow_two_eq M.P.toMeasure hrho0]
      have hadd := paperENNRealLpNorm_add_le M.P.toMeasure
        (show 1 ≤ xi by linarith)
        (X := fun _ : Sample d => 1) (Y := XE R)
        measurable_const.aemeasurable (hXEambient R hR).aemeasurable
      rw [paperENNRealLpNorm_one M.P.toMeasure xi] at hadd
      have hbase := hadd.trans (add_le_add_right (hXEnorm R hR) 1)
      have hsquare := ENNReal.rpow_le_rpow hbase (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [show 2 * (xi / 2) = xi by ring, ENNReal.rpow_two,
        ENNReal.ofReal_pow (by positivity : 0 ≤ 1 + shell),
        ENNReal.ofReal_add zero_le_one hshell, ENNReal.ofReal_one] using! hsquare
    have hsum := paperENNRealLpNorm_finset_sum_le M.P.toMeasure
      (show 1 ≤ xi / 2 by linarith) D Z hZmeas
    have hbound := hsum.trans (Finset.sum_le_sum fun R hR => hZnorm R hR)
    have hfun : XplusSq = fun omega =>
        (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D, Z R omega := by
      funext omega
      dsimp only [XplusSq, Z, XE, c]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg]
      · norm_num
        congr 1
        congr 1
        funext R
        rw [ENNReal.ofReal_pow (by positivity : 0 ≤ 1 + X R omega),
          ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (hX0 R omega)]
        norm_num
      · intro R hR
        positivity
    rw [hfun, paperENNRealLpNorm_const_mul_eq M.P.toMeasure hrho0]
    · calc
        (D.card : ℝ≥0∞)⁻¹ *
            paperENNRealLpNorm M.P.toMeasure (xi / 2)
              (fun omega => ∑ R ∈ D, Z R omega) ≤
            (D.card : ℝ≥0∞)⁻¹ * ∑ R ∈ D,
              ENNReal.ofReal ((1 + shell) ^ 2) := by gcongr
        _ = ENNReal.ofReal ((1 + shell) ^ 2) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [← mul_assoc, ENNReal.inv_mul_cancel]
          · simp
          · exact_mod_cast hD.card_ne_zero
          · exact ENNReal.coe_ne_top
    · exact Finset.measurable_sum _ hZmeas
  have hXANorm : paperENNRealLpNorm M.P.toMeasure xi
      (fun omega => ENNReal.ofReal (XA omega)) ≤ ENNReal.ofReal (1 + shell) := by
    have hfun : (fun omega => ENNReal.ofReal (XA omega)) =
        fun omega => XplusSq omega ^ (1 / 2 : ℝ) := by
      funext omega
      dsimp only [XA, XplusSq]
      rw [Real.sqrt_eq_rpow,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    rw [hfun, paperENNRealLpNorm_rpow_half_eq M.P.toMeasure hxi0]
    have hpow := ENNReal.rpow_le_rpow hXplusSqNorm
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hplus0 : 0 ≤ 1 + shell := by linarith
    rw [ENNReal.ofReal_pow hplus0, ← ENNReal.rpow_two,
      ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      ENNReal.rpow_one] at hpow
    exact hpow
  let Jsq : Sample d → ℝ≥0∞ := fun omega => ENNReal.ofReal
    (c * ∑ R ∈ D, Jk R omega ^ 2)
  have hJsqMeas : Measurable Jsq := by
    dsimp only [Jsq]
    exact (measurable_const.mul (Finset.measurable_sum _ fun R hR =>
      ((hJmeas R hR).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Iic k)) le_rfl).pow_const 2)).ennreal_ofReal
  have hJBNorm : paperENNRealLpNorm M.P.toMeasure xi
      (fun omega => ENNReal.ofReal (JB omega)) ≤
        ENNReal.ofReal ((1 / 6 : ℝ) * delta1) := by
    have hfun : (fun omega => ENNReal.ofReal (JB omega)) =
        fun omega => Jsq omega ^ (1 / 2 : ℝ) := by
      funext omega
      dsimp only [JB, Jsq]
      rw [Real.sqrt_eq_rpow,
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    rw [hfun, paperENNRealLpNorm_rpow_half_eq M.P.toMeasure hxi0]
    have hprefix' : paperENNRealLpNorm M.P.toMeasure (xi / 2) Jsq ≤
        ENNReal.ofReal ((1 / 36 : ℝ) * delta1 ^ 2) := by
      simpa only [Jsq, Jk, c, D] using! hprefix
    have hpow := ENNReal.rpow_le_rpow hprefix'
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have heq : (1 / 36 : ℝ) * delta1 ^ 2 =
        ((1 / 6 : ℝ) * delta1) ^ 2 := by ring
    rw [heq, ENNReal.ofReal_pow (by positivity : 0 ≤ (1 / 6 : ℝ) * delta1),
      ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at hpow
    exact hpow
  have hprod := paperENNRealLpNorm_mul_eq_prefix_suffix M k hxi0.le
    hJBMeas.ennreal_ofReal hXAMeas.ennreal_ofReal
  have hprod' : paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
      ENNReal.ofReal (XA omega * JB omega)) ≤
        ENNReal.ofReal ((1 + shell) * ((1 / 6 : ℝ) * delta1)) := by
    have hfun : (fun omega => ENNReal.ofReal (XA omega * JB omega)) =
        fun omega => ENNReal.ofReal (JB omega) * ENNReal.ofReal (XA omega) := by
      funext omega
      rw [ENNReal.ofReal_mul (hXA0 omega)]
      ring
    rw [hfun, hprod]
    calc
      paperENNRealLpNorm M.P.toMeasure xi (fun omega => ENNReal.ofReal (JB omega)) *
          paperENNRealLpNorm M.P.toMeasure xi (fun omega => ENNReal.ofReal (XA omega)) ≤
          ENNReal.ofReal ((1 / 6 : ℝ) * delta1) *
            ENNReal.ofReal (1 + shell) := by gcongr
      _ = ENNReal.ofReal ((1 + shell) * ((1 / 6 : ℝ) * delta1)) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 6 : ℝ) * delta1)]
        rw [mul_comm]
  have hXAambient : Measurable XA := hXAMeas.mono
    (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi k)) le_rfl
  have hJBambient : Measurable JB := hJBMeas.mono
    (potentialShellIndexSigma_le_borel (d := d) (Set.Iic k)) le_rfl
  have hXavgAmbient : Measurable Xavg := hXavgMeas.mono
    (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi k)) le_rfl
  have hpoint' : ∀ᵐ omega ∂M.P.toMeasure,
      normalizedDefectAt M r r omega ≤
        ENNReal.ofReal (3 * Xavg omega) +
          ENNReal.ofReal (3 * XA omega * JB omega) := by
    filter_upwards [hpoint] with omega homega
    calc
      normalizedDefectAt M r r omega ≤
          ENNReal.ofReal (3 * Xavg omega + 3 * XA omega * JB omega) := homega
      _ = ENNReal.ofReal (3 * Xavg omega) +
          ENNReal.ofReal (3 * XA omega * JB omega) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  have hmono := paperENNRealLpNorm_mono_ae M.P.toMeasure hxi0.le hpoint'
  have hadd := paperENNRealLpNorm_add_le M.P.toMeasure
    (show 1 ≤ xi by linarith)
    (X := fun omega => ENNReal.ofReal (3 * Xavg omega))
    (Y := fun omega => ENNReal.ofReal (3 * XA omega * JB omega))
    ((hXavgAmbient.const_mul 3).ennreal_ofReal.aemeasurable)
    (((hXAambient.const_mul 3).mul hJBambient).ennreal_ofReal.aemeasurable)
  have hxconst := paperENNRealLpNorm_const_mul_eq M.P.toMeasure hxi0
    (3 : ℝ≥0∞) (fun omega => ENNReal.ofReal (Xavg omega))
    (hXavgMeas.ennreal_ofReal.mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi k)) le_rfl)
  have hpconst := paperENNRealLpNorm_const_mul_eq M.P.toMeasure hxi0
    (3 : ℝ≥0∞) (fun omega => ENNReal.ofReal (XA omega * JB omega))
    (hXAambient.mul hJBambient).ennreal_ofReal
  refine hmono.trans (hadd.trans ?_)
  rw [show (fun omega => ENNReal.ofReal (3 * Xavg omega)) =
      fun omega => (3 : ℝ≥0∞) * ENNReal.ofReal (Xavg omega) by
    funext omega
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num, hxconst]
  rw [show (fun omega => ENNReal.ofReal (3 * XA omega * JB omega)) =
      fun omega => (3 : ℝ≥0∞) * ENNReal.ofReal (XA omega * JB omega) by
    funext omega
    rw [show 3 * XA omega * JB omega = 3 * (XA omega * JB omega) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num, hpconst]
  calc
    3 * paperENNRealLpNorm M.P.toMeasure xi (fun omega => ENNReal.ofReal (Xavg omega)) +
        3 * paperENNRealLpNorm M.P.toMeasure xi
          (fun omega => ENNReal.ofReal (XA omega * JB omega)) ≤
        3 * ENNReal.ofReal shell +
          3 * ENNReal.ofReal ((1 + shell) * ((1 / 6 : ℝ) * delta1)) := by gcongr
    _ = ENNReal.ofReal
        (3 * shell + (1 / 2 : ℝ) * (1 + shell) * delta1) := by
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ 3 * shell)
          (by positivity : 0 ≤ 3 * ((1 + shell) * ((1 / 6 : ℝ) * delta1)))]
      congr 1
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion
