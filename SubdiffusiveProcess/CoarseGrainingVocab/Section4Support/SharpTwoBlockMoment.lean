module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.MomentFactorization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpSuffixRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitResponse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.TranslatedDefect
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

/-!
# Absorbed moment of the sharp two-block suffix representative

This module performs the finite product/Hölder calculation in
`e.XmLk.bound`.  The two-sided annealed ordering is an explicit hypothesis
with the exact clauses (5)--(6) of the quarantined Section 3 anchor.

the product-moment layer mirrors

the GMC-specific absorption follows paper label `e.XmLk.bound`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

theorem aux_dedup_d091_paperENNRealLpNorm_le_of_real_moment
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} {W : Omega → ℝ}
    (hW0 : ∀ omega, 0 ≤ W omega)
    (hWint : Integrable (fun omega => W omega ^ p) mu)
    (hXW : ∀ᵐ omega ∂mu, X omega ≤ ENNReal.ofReal (W omega)) :
    paperENNRealLpNorm mu p X ≤
      ENNReal.ofReal ((∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by
  have hp0 : 0 ≤ p := hp.le
  have hinv0 : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0
  have hpow : ∀ᵐ omega ∂mu, X omega ^ p ≤ ENNReal.ofReal (W omega ^ p) := by
    filter_upwards [hXW] with omega homega
    calc
      X omega ^ p ≤ (ENNReal.ofReal (W omega)) ^ p :=
        ENNReal.rpow_le_rpow homega hp0
      _ = ENNReal.ofReal (W omega ^ p) :=
        ENNReal.ofReal_rpow_of_nonneg (hW0 omega) hp0
  unfold paperENNRealLpNorm
  calc
    (∫⁻ omega, X omega ^ p ∂mu) ^ p⁻¹ ≤
        (∫⁻ omega, ENNReal.ofReal (W omega ^ p) ∂mu) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow (lintegral_mono_ae hpow) hinv0
    _ = (ENNReal.ofReal (∫ omega, W omega ^ p ∂mu)) ^ p⁻¹ := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hWint
        (Filter.Eventually.of_forall fun omega =>
          Real.rpow_nonneg (hW0 omega) p)]
    _ = ENNReal.ofReal ((∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun omega =>
        Real.rpow_nonneg (hW0 omega) p) hinv0]

private theorem paperENNRealLpNorm_le_of_real_moment
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X : Omega → ℝ≥0∞} {W : Omega → ℝ}
    (hW0 : ∀ omega, 0 ≤ W omega)
    (hWint : Integrable (fun omega => W omega ^ p) mu)
    (hXW : ∀ᵐ omega ∂mu, X omega ≤ ENNReal.ofReal (W omega)) :
    paperENNRealLpNorm mu p X ≤
      ENNReal.ofReal ((∫ omega, W omega ^ p ∂mu) ^ p⁻¹) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d091_paperENNRealLpNorm_le_of_real_moment (Omega := Omega) (mu := mu) (p := p) (hp := hp) (X := X) (W := W) (hW0 := hW0) (hWint := hWint) (hXW := hXW)

theorem aux_dedup_d190_scalarRatioLInf_le_of_forall_bound
    {d : ℕ} {U : Ch02.Domain d} {a b : Vec d → ℝ} {W : ℝ}
    (hW0 : 0 ≤ W) (h : ∀ x ∈ (U : Set (Vec d)), |a x / b x - 1| ≤ W) :
    scalarRatioLInf U a b ≤ W := by
  unfold scalarRatioLInf
  rw [SubdiffusiveProcess.RawLp.eLpNorm_top_exponent]
  have hae : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      |a x / b x - 1| ≤ W := by
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    exact h x hx
  have hess : eLpNormEssSup (fun x => a x / b x - 1)
      (volumeMeasureOn (U : Set (Vec d))) ≤ ENNReal.ofReal W :=
    eLpNormEssSup_le_of_ae_bound (by simpa only [Real.norm_eq_abs] using hae)
  calc
    (eLpNormEssSup (fun x => a x / b x - 1)
        (volumeMeasureOn (U : Set (Vec d)))).toReal ≤
        (ENNReal.ofReal W).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    _ = W := ENNReal.toReal_ofReal hW0

private theorem scalarRatioLInf_le_of_forall_bound
    {d : ℕ} {U : Ch02.Domain d} {a b : Vec d → ℝ} {W : ℝ}
    (hW0 : 0 ≤ W) (h : ∀ x ∈ (U : Set (Vec d)), |a x / b x - 1| ≤ W) :
    scalarRatioLInf U a b ≤ W := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d190_scalarRatioLInf_le_of_forall_bound (d := d) (U := U) (a := a) (b := b) (W := W) (hW0 := hW0) (h := h)

private theorem paperENNRealLpNorm_mul_le_two_mul
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) {X Y : Omega → ℝ≥0∞}
    (hX : AEMeasurable X mu) (hY : AEMeasurable Y mu) :
    paperENNRealLpNorm mu p (fun omega => X omega * Y omega) ≤
      paperENNRealLpNorm mu (2 * p) X *
        paperENNRealLpNorm mu (2 * p) Y := by
  have hp0 : 0 ≤ p := hp.le
  have h2p0 : 0 ≤ 2 * p := by positivity
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq mu
    Real.HolderConjugate.two_two (hX.pow_const p) (hY.pow_const p)
  unfold paperENNRealLpNorm
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
  have hbase :
      (∫⁻ omega, X omega ^ p * Y omega ^ p ∂mu) ≤
        (∫⁻ omega, X omega ^ (2 * p) ∂mu) ^ (1 / 2 : ℝ) *
          (∫⁻ omega, Y omega ^ (2 * p) ∂mu) ^ (1 / 2 : ℝ) := by
    convert hholder using 1
    all_goals simp only [← ENNReal.rpow_mul, one_div, mul_comm p]
  calc
    (∫⁻ omega, X omega ^ p * Y omega ^ p ∂mu) ^ p⁻¹ ≤
        ((∫⁻ omega, X omega ^ (2 * p) ∂mu) ^ (1 / 2 : ℝ) *
          (∫⁻ omega, Y omega ^ (2 * p) ∂mu) ^ (1 / 2 : ℝ)) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow hbase (inv_nonneg.mpr hp0)
    _ = (∫⁻ omega, X omega ^ (2 * p) ∂mu) ^ (2 * p)⁻¹ *
          (∫⁻ omega, Y omega ^ (2 * p) ∂mu) ^ (2 * p)⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp0),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 2 <;> field_simp

theorem aux_dedup_d131_paperENNRealLpNorm_sq
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) (X : Omega → ℝ≥0∞) :
    paperENNRealLpNorm mu p (fun omega => X omega ^ (2 : ℕ)) =
      (paperENNRealLpNorm mu (2 * p) X) ^ (2 : ℕ) := by
  unfold paperENNRealLpNorm
  simp_rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  norm_num
  field_simp

private theorem paperENNRealLpNorm_sq
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {p : ℝ} (hp : 0 < p) (X : Omega → ℝ≥0∞) :
    paperENNRealLpNorm mu p (fun omega => X omega ^ (2 : ℕ)) =
      (paperENNRealLpNorm mu (2 * p) X) ^ (2 : ℕ) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d131_paperENNRealLpNorm_sq (Omega := Omega) (mu := mu) (p := p) (hp := hp) (X := X)

private theorem paperENNRealLpNorm_product_envelope_le
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] {p : ℝ} (hp : 1 ≤ p) (D : ℝ≥0∞)
    {Y Z : Omega → ℝ≥0∞} (hY : Measurable Y) (hZ : Measurable Z) :
    paperENNRealLpNorm mu p (fun omega =>
        2 * (D + (1 + D) * (Y omega + Z omega + Y omega * Z omega))) ≤
      2 * (D + (1 + D) *
        (paperENNRealLpNorm mu p Y + paperENNRealLpNorm mu p Z +
          paperENNRealLpNorm mu (2 * p) Y *
            paperENNRealLpNorm mu (2 * p) Z)) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  have hYae : AEMeasurable Y mu := hY.aemeasurable
  have hZae : AEMeasurable Z mu := hZ.aemeasurable
  have hYZ :
      paperENNRealLpNorm mu p (fun omega => Y omega * Z omega) ≤
        paperENNRealLpNorm mu (2 * p) Y *
          paperENNRealLpNorm mu (2 * p) Z :=
    paperENNRealLpNorm_mul_le_two_mul mu hpPos hYae hZae
  have hsum :
      paperENNRealLpNorm mu p
          (fun omega => Y omega + Z omega + Y omega * Z omega) ≤
        paperENNRealLpNorm mu p Y + paperENNRealLpNorm mu p Z +
          paperENNRealLpNorm mu (2 * p) Y *
            paperENNRealLpNorm mu (2 * p) Z := by
    calc
      paperENNRealLpNorm mu p
          (fun omega => Y omega + Z omega + Y omega * Z omega) ≤
          paperENNRealLpNorm mu p (fun omega => Y omega + Z omega) +
            paperENNRealLpNorm mu p (fun omega => Y omega * Z omega) :=
        paperENNRealLpNorm_add_le mu hp
          (hY.add hZ).aemeasurable (hY.mul hZ).aemeasurable
      _ ≤ (paperENNRealLpNorm mu p Y + paperENNRealLpNorm mu p Z) +
          paperENNRealLpNorm mu (2 * p) Y *
            paperENNRealLpNorm mu (2 * p) Z := by
        gcongr
        exact paperENNRealLpNorm_add_le mu hp hYae hZae
      _ = _ := by rfl
  have hD : paperENNRealLpNorm mu p (fun _ : Omega => D) = D := by
    calc
      paperENNRealLpNorm mu p (fun _ : Omega => D) =
          D * paperENNRealLpNorm mu p (fun _ : Omega => 1) := by
        simpa using paperENNRealLpNorm_const_mul_eq mu hpPos D
          (fun _ : Omega => 1) measurable_const
      _ = D := by rw [paperENNRealLpNorm_one mu p, mul_one]
  calc
    paperENNRealLpNorm mu p (fun omega =>
        2 * (D + (1 + D) * (Y omega + Z omega + Y omega * Z omega))) =
        2 * paperENNRealLpNorm mu p (fun omega =>
          D + (1 + D) * (Y omega + Z omega + Y omega * Z omega)) := by
      exact paperENNRealLpNorm_const_mul_eq mu hpPos 2 _
        (measurable_const.add (measurable_const.mul
          (hY.add hZ |>.add (hY.mul hZ))))
    _ ≤ 2 * (paperENNRealLpNorm mu p (fun _ : Omega => D) +
        paperENNRealLpNorm mu p (fun omega =>
          (1 + D) * (Y omega + Z omega + Y omega * Z omega))) := by
      gcongr
      exact paperENNRealLpNorm_add_le mu hp measurable_const.aemeasurable
        (measurable_const.mul (hY.add hZ |>.add (hY.mul hZ))).aemeasurable
    _ = 2 * (D + (1 + D) * paperENNRealLpNorm mu p
        (fun omega => Y omega + Z omega + Y omega * Z omega)) := by
      rw [hD]
      have hscale := paperENNRealLpNorm_const_mul_eq mu hpPos (1 + D)
        (fun omega => Y omega + Z omega + Y omega * Z omega)
        (by simpa only [Pi.add_apply, Pi.mul_apply] using! (hY.add hZ |>.add (hY.mul hZ)))
      simpa only using! congrArg (fun x => 2 * (D + x)) hscale
    _ ≤ _ := by gcongr

/-! ## Dimension-only constants and real absorption -/

/-- A common upper bound for the two shell-envelope scales. -/
def sharpTwoBlockScaleConst (d : ℕ) : ℝ :=
  max 1 (max (shellSensitivityConst d) smallCubeBlockConst)

/-- Smallness threshold allocating one sixteenth of the geometric exponent
to the raw lognormal exponential. -/
def sharpTwoBlockSmallnessConst (d : ℕ) : ℝ :=
  min 1 (Real.log 3 /
    (16 * (4 * sharpTwoBlockScaleConst d ^ 2 + 1)))

/-- Common raw-moment prefactor after writing `sqrt (2*p)` as
`sqrt 2 * sqrt p`. -/
def sharpTwoBlockGammaConst : ℝ :=
  2 * Ch04.gammaMomentConst 2 * Real.sqrt 2



def sharpTwoBlockFactorConst (d : ℕ) : ℝ :=
  max 1 (max
    (sharpTwoBlockGammaConst * 2 * sharpTwoBlockScaleConst d *
      (3 : ℝ) ^ ((16 : ℝ)⁻¹))
    (max
      (sharpTwoBlockGammaConst *
        (2 * sharpTwoBlockScaleConst d * (1 + 16 / Real.log 3) +
          32 / Real.log 3))
      (64 / Real.log 3)))

/-- Final constant after the three-factor envelope and the terminal square. -/
def sharpTwoBlockMomentConst (d : ℕ) : ℝ :=
  let A := sharpTwoBlockFactorConst d
  max 1 ((2 * (3 * A + 3 * A ^ 2 + A ^ 3)) ^ 2)

private theorem log_three_pos : 0 < Real.log 3 :=
  Real.log_pos (by norm_num)

theorem sharpTwoBlockScaleConst_pos (d : ℕ) :
    0 < sharpTwoBlockScaleConst d :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem shellSensitivityConst_le_sharpTwoBlockScaleConst (d : ℕ) :
    shellSensitivityConst d ≤ sharpTwoBlockScaleConst d :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem smallCubeBlockConst_le_sharpTwoBlockScaleConst (d : ℕ) :
    smallCubeBlockConst ≤ sharpTwoBlockScaleConst d :=
  le_trans (le_max_right _ _) (le_max_right _ _)

theorem sharpTwoBlockSmallnessConst_pos (d : ℕ) :
    0 < sharpTwoBlockSmallnessConst d := by
  unfold sharpTwoBlockSmallnessConst
  refine lt_min (by norm_num) (div_pos log_three_pos ?_)
  positivity

theorem sharpTwoBlockSmallnessConst_le_one (d : ℕ) :
    sharpTwoBlockSmallnessConst d ≤ 1 :=
  min_le_left _ _

theorem one_le_sharpTwoBlockFactorConst (d : ℕ) :
    1 ≤ sharpTwoBlockFactorConst d :=
  le_max_left _ _

theorem one_le_sharpTwoBlockMomentConst (d : ℕ) :
    1 ≤ sharpTwoBlockMomentConst d := by
  change (1 : ℝ) ≤ max (1 : ℝ)
    ((2 * (3 * sharpTwoBlockFactorConst d +
      3 * sharpTwoBlockFactorConst d ^ 2 +
      sharpTwoBlockFactorConst d ^ 3)) ^ 2)
  exact le_max_left (1 : ℝ)
    ((2 * (3 * sharpTwoBlockFactorConst d +
      3 * sharpTwoBlockFactorConst d ^ 2 +
      sharpTwoBlockFactorConst d ^ 3)) ^ 2)

private theorem sharpTwoBlock_geometric {u : ℝ} (hu : 0 ≤ u) :
    let R := (3 : ℝ) ^ (u / 16)
    1 ≤ R ∧ R ^ 16 = (3 : ℝ) ^ u ∧
      u ≤ 16 / Real.log 3 * R := by
  dsimp only
  have hR1 : (1 : ℝ) ≤ (3 : ℝ) ^ (u / 16) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hR16 : ((3 : ℝ) ^ (u / 16)) ^ 16 = (3 : ℝ) ^ u := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (u / 16)) 16,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hRe : (3 : ℝ) ^ (u / 16) =
      Real.exp (Real.log 3 * (u / 16)) :=
    Real.rpow_def_of_pos (by norm_num) _
  have huR : u ≤ 16 / Real.log 3 * (3 : ℝ) ^ (u / 16) := by
    have hle : Real.log 3 * (u / 16) ≤
        Real.exp (Real.log 3 * (u / 16)) := by
      linarith [Real.add_one_le_exp (Real.log 3 * (u / 16))]
    have hmul := mul_le_mul_of_nonneg_left hle
      (show 0 ≤ 16 / Real.log 3 by positivity)
    rw [hRe]
    calc
      u = 16 / Real.log 3 * (Real.log 3 * (u / 16)) := by field_simp
      _ ≤ 16 / Real.log 3 * Real.exp (Real.log 3 * (u / 16)) := hmul
  exact ⟨hR1, hR16, huR⟩

private theorem sharpTwoBlock_gap_raw_bound
    {K G c xi E delta1 s g A b : ℝ}
    (hK : 1 ≤ K) (hG : 0 ≤ G) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcthresh : c ≤ Real.log 3 / (16 * (4 * K ^ 2 + 1)))
    (hxi : 1 ≤ xi) (hE : 0 < E) (hdelta1 : delta1 < 1)
    (hs : 0 < s) (hg : 1 ≤ g)
    (hxiE : xi * E ≤ c * s * delta1)
    (hA0 : 0 ≤ A) (hb0 : 0 ≤ b)
    (hA2 : A ^ 2 ≤ K ^ 2 * E * g) (hb : b ≤ E * g) :
    G * Real.sqrt (4 * xi) * (A + b) *
        Real.exp (4 * xi * A ^ 2 + b) ≤
      G * (2 * K * (1 + 16 / Real.log 3) + 32 / Real.log 3) *
        Real.sqrt delta1 * ((3 : ℝ) ^ (s * g / 16)) ^ 2 := by
  have hxi0 : 0 < xi := zero_lt_one.trans_le hxi
  have hdelta1pos : 0 < delta1 := by
    have hxiEpos : 0 < xi * E := mul_pos hxi0 hE
    have hcspos : 0 < c * s := mul_pos hc0 hs
    nlinarith
  have hg0 : 0 ≤ g := zero_le_one.trans hg
  have hu0 : 0 ≤ s * g := mul_nonneg hs.le hg0
  obtain ⟨hR1, _hR16, huR⟩ := sharpTwoBlock_geometric hu0
  let R : ℝ := (3 : ℝ) ^ (s * g / 16)
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hxiEg : xi * E * g ≤ c * delta1 * (s * g) := by
    have h := mul_le_mul_of_nonneg_right hxiE hg0
    calc
      xi * E * g ≤ c * s * delta1 * g := h
      _ = c * delta1 * (s * g) := by ring
  have hEg_le_xiEg : E * g ≤ xi * E * g := by
    have h := mul_le_mul_of_nonneg_right hxi (mul_nonneg hE.le hg0)
    nlinarith
  have hEg : E * g ≤ c * delta1 * (s * g) :=
    hEg_le_xiEg.trans hxiEg
  have hthreshold : c * (4 * K ^ 2 + 1) ≤ Real.log 3 / 16 := by
    have hden : 0 < 16 * (4 * K ^ 2 + 1) := by positivity
    have h := (le_div_iff₀ hden).mp hcthresh
    nlinarith
  have hexponent : 4 * xi * A ^ 2 + b ≤
      Real.log 3 * (s * g / 16) := by
    have hAexp : 4 * xi * A ^ 2 ≤ 4 * K ^ 2 * (c * delta1 * (s * g)) := by
      have h1 := mul_le_mul_of_nonneg_left hA2 (show 0 ≤ 4 * xi by positivity)
      have h2 := mul_le_mul_of_nonneg_left hxiEg (show 0 ≤ 4 * K ^ 2 by positivity)
      nlinarith
    have hbexp : b ≤ c * delta1 * (s * g) := hb.trans hEg
    have hdelta1le : delta1 ≤ 1 := hdelta1.le
    have hcu : 0 ≤ c * (s * g) := mul_nonneg hc0.le hu0
    have hsum : 4 * xi * A ^ 2 + b ≤
        c * (4 * K ^ 2 + 1) * (s * g) := by
      have hd := mul_le_mul_of_nonneg_left hdelta1le hcu
      nlinarith
    have ht := mul_le_mul_of_nonneg_right hthreshold hu0
    nlinarith
  have hexp : Real.exp (4 * xi * A ^ 2 + b) ≤ R := by
    change Real.exp (4 * xi * A ^ 2 + b) ≤ (3 : ℝ) ^ (s * g / 16)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.mpr hexponent
  have hsqrtP : Real.sqrt (4 * xi) ^ 2 = 4 * xi :=
    Real.sq_sqrt (by positivity)
  have hsqrtDU : Real.sqrt (delta1 * (s * g)) ^ 2 =
      delta1 * (s * g) := Real.sq_sqrt (mul_nonneg hdelta1pos.le hu0)
  have hrootA : Real.sqrt (4 * xi) * A ≤
      2 * K * Real.sqrt (delta1 * (s * g)) := by
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    have hleft0 : 0 ≤ Real.sqrt (4 * xi) * A :=
      mul_nonneg (Real.sqrt_nonneg _) hA0
    have hright0 : 0 ≤ 2 * K * Real.sqrt (delta1 * (s * g)) := by positivity
    apply (sq_le_sq₀ hleft0 hright0).mp
    have hxiA : xi * A ^ 2 ≤ K ^ 2 * (c * delta1 * (s * g)) := by
      have h1 := mul_le_mul_of_nonneg_left hA2 hxi0.le
      have h2 := mul_le_mul_of_nonneg_left hxiEg (sq_nonneg K)
      calc
        xi * A ^ 2 ≤ xi * (K ^ 2 * E * g) := h1
        _ = K ^ 2 * (xi * E * g) := by ring
        _ ≤ K ^ 2 * (c * delta1 * (s * g)) := h2
    have hcdu : c * delta1 * (s * g) ≤ delta1 * (s * g) := by
      have hcd : c * delta1 ≤ delta1 := by
        simpa using mul_le_mul_of_nonneg_right hc1 hdelta1pos.le
      exact mul_le_mul_of_nonneg_right hcd hu0
    have hxiA' : xi * A ^ 2 ≤ K ^ 2 * (delta1 * (s * g)) :=
      hxiA.trans (mul_le_mul_of_nonneg_left hcdu (sq_nonneg K))
    rw [mul_pow, hsqrtP, mul_pow, mul_pow, hsqrtDU]
    nlinarith only [hxiA']
  have hrootB : Real.sqrt (4 * xi) * b ≤ 2 * delta1 * (s * g) := by
    have hleft0 : 0 ≤ Real.sqrt (4 * xi) * b :=
      mul_nonneg (Real.sqrt_nonneg _) hb0
    have hright0 : 0 ≤ 2 * delta1 * (s * g) := by positivity
    apply (sq_le_sq₀ hleft0 hright0).mp
    have hb2 : b ^ 2 ≤ (E * g) ^ 2 := pow_le_pow_left₀ hb0 hb 2
    have hprod : xi * b ^ 2 ≤
        (c * delta1 * (s * g)) ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hb2 hxi0.le
      have h2 := mul_le_mul hxiEg hEg
        (mul_nonneg hE.le hg0) (by positivity : 0 ≤ c * delta1 * (s * g))
      calc
        xi * b ^ 2 ≤ xi * (E * g) ^ 2 := h1
        _ = (xi * E * g) * (E * g) := by ring
        _ ≤ (c * delta1 * (s * g)) * (c * delta1 * (s * g)) := h2
        _ = (c * delta1 * (s * g)) ^ 2 := by ring
    have hprod' : xi * b ^ 2 ≤ (delta1 * (s * g)) ^ 2 :=
      hprod.trans (pow_le_pow_left₀ (by positivity)
        (by
          have hcd : c * delta1 ≤ delta1 := by
            simpa using mul_le_mul_of_nonneg_right hc1 hdelta1pos.le
          exact mul_le_mul_of_nonneg_right hcd hu0) 2)
    rw [mul_pow, hsqrtP]
    nlinarith only [hprod']
  have hsqrtu : Real.sqrt (s * g) ≤ 1 + s * g := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hu0]
    calc
      s * g ≤ s * g + (1 + s * g + (s * g) ^ 2) :=
        le_add_of_nonneg_right (by positivity)
      _ = (1 + s * g) ^ 2 := by ring
  have hsqrtuR : Real.sqrt (s * g) ≤
      (1 + 16 / Real.log 3) * R := by
    have h1 : (1 : ℝ) + s * g ≤ R + 16 / Real.log 3 * R :=
      add_le_add hR1 huR
    calc
      Real.sqrt (s * g) ≤ 1 + s * g := hsqrtu
      _ ≤ R + 16 / Real.log 3 * R := h1
      _ = (1 + 16 / Real.log 3) * R := by ring
  have hsqrtDelta : Real.sqrt delta1 ^ 2 = delta1 :=
    Real.sq_sqrt hdelta1pos.le
  have hsqrtDeltaLeOne : Real.sqrt delta1 ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hdelta1.le
  have hdeltaSqrt : delta1 ≤ Real.sqrt delta1 := by
    calc
      delta1 = Real.sqrt delta1 * Real.sqrt delta1 := by
        rw [← pow_two, hsqrtDelta]
      _ ≤ Real.sqrt delta1 * 1 :=
        mul_le_mul_of_nonneg_left hsqrtDeltaLeOne (Real.sqrt_nonneg _)
      _ = Real.sqrt delta1 := mul_one _
  have hpref : Real.sqrt (4 * xi) * (A + b) ≤
      (2 * K * (1 + 16 / Real.log 3) + 32 / Real.log 3) *
        Real.sqrt delta1 * R := by
    have hrootSum : Real.sqrt (4 * xi) * (A + b) ≤
        2 * K * Real.sqrt (delta1 * (s * g)) +
          2 * delta1 * (s * g) := by linarith only [hrootA, hrootB]
    rw [Real.sqrt_mul hdelta1pos.le] at hrootSum
    have hfirst := mul_le_mul_of_nonneg_left hsqrtuR
      (show 0 ≤ 2 * K * Real.sqrt delta1 by positivity)
    have hsecond := mul_le_mul_of_nonneg_left huR
      (show 0 ≤ 2 * delta1 by positivity)
    have hdeltaSecond := mul_le_mul_of_nonneg_right hdeltaSqrt
      (show 0 ≤ 32 / Real.log 3 * R by positivity)
    calc
      Real.sqrt (4 * xi) * (A + b) ≤
          2 * K * Real.sqrt delta1 * Real.sqrt (s * g) +
            2 * delta1 * (s * g) := by
        simpa only [mul_assoc] using hrootSum
      _ ≤ 2 * K * Real.sqrt delta1 * ((1 + 16 / Real.log 3) * R) +
          2 * delta1 * (16 / Real.log 3 * R) := add_le_add hfirst hsecond
      _ = 2 * K * Real.sqrt delta1 * ((1 + 16 / Real.log 3) * R) +
          delta1 * (32 / Real.log 3 * R) := by ring
      _ ≤ 2 * K * Real.sqrt delta1 * ((1 + 16 / Real.log 3) * R) +
          Real.sqrt delta1 * (32 / Real.log 3 * R) :=
        add_le_add_right hdeltaSecond _
      _ = (2 * K * (1 + 16 / Real.log 3) + 32 / Real.log 3) *
          Real.sqrt delta1 * R := by ring
  have hmul := mul_le_mul hpref hexp (Real.exp_pos _).le
    (by positivity : 0 ≤
      (2 * K * (1 + 16 / Real.log 3) + 32 / Real.log 3) *
        Real.sqrt delta1 * R)
  have hGmul := mul_le_mul_of_nonneg_left hmul hG
  simpa only [pow_two, mul_assoc] using hGmul

private theorem sharpTwoBlock_base_raw_bound
    {K G c xi E delta1 s A : ℝ}
    (hK : 1 ≤ K) (hG : 0 ≤ G) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcthresh : c ≤ Real.log 3 / (16 * (4 * K ^ 2 + 1)))
    (hxi : 1 ≤ xi) (hE : 0 < E) (hdelta1 : delta1 < 1)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hxiE : xi * E ≤ c * s * delta1)
    (hA0 : 0 ≤ A) (hA2 : A ^ 2 ≤ K ^ 2 * E) :
    G * Real.sqrt (4 * xi) * A * Real.exp (4 * xi * A ^ 2) ≤
      G * (2 * K * (3 : ℝ) ^ ((16 : ℝ)⁻¹) * Real.sqrt delta1) := by
  have hxi0 : 0 < xi := zero_lt_one.trans_le hxi
  have hdelta1pos : 0 < delta1 := by
    have hleft : 0 < xi * E := mul_pos hxi0 hE
    have hcs : 0 < c * s := mul_pos hc0 hs
    nlinarith
  have hcs : c * s ≤ 1 := by
    exact (mul_le_mul hc1 hs1 hs.le zero_le_one).trans_eq (mul_one 1)
  have hxiA : xi * A ^ 2 ≤ K ^ 2 * (c * s * delta1) := by
    calc
      xi * A ^ 2 ≤ xi * (K ^ 2 * E) :=
        mul_le_mul_of_nonneg_left hA2 hxi0.le
      _ = K ^ 2 * (xi * E) := by ring
      _ ≤ K ^ 2 * (c * s * delta1) :=
        mul_le_mul_of_nonneg_left hxiE (sq_nonneg K)
  have hcsd : c * s * delta1 ≤ delta1 := by
    simpa using mul_le_mul_of_nonneg_right hcs hdelta1pos.le
  have hroot : Real.sqrt (4 * xi) * A ≤ 2 * K * Real.sqrt delta1 := by
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hA0) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 4 * xi),
      mul_pow, mul_pow, Real.sq_sqrt hdelta1pos.le]
    have hxiA' : xi * A ^ 2 ≤ K ^ 2 * delta1 :=
      hxiA.trans (mul_le_mul_of_nonneg_left hcsd (sq_nonneg K))
    nlinarith only [hxiA']
  have hthreshold : 4 * K ^ 2 * c ≤ Real.log 3 / 16 := by
    have hden : 0 < 16 * (4 * K ^ 2 + 1) := by positivity
    have ht := (le_div_iff₀ hden).mp hcthresh
    have hlog : 0 < Real.log 3 := log_three_pos
    nlinarith [sq_nonneg K]
  have hexponent : 4 * xi * A ^ 2 ≤ Real.log 3 / 16 := by
    have h1 : 4 * xi * A ^ 2 ≤ 4 * K ^ 2 * (c * s * delta1) := by
      nlinarith only [hxiA]
    have hsd : s * delta1 ≤ 1 := by
      have := mul_le_mul hs1 hdelta1.le hdelta1pos.le zero_le_one
      nlinarith
    have h2 := mul_le_mul_of_nonneg_left hsd
      (show 0 ≤ 4 * K ^ 2 * c by positivity)
    calc
      4 * xi * A ^ 2 ≤ 4 * K ^ 2 * (c * s * delta1) := h1
      _ = (4 * K ^ 2 * c) * (s * delta1) := by ring
      _ ≤ (4 * K ^ 2 * c) * 1 := h2
      _ ≤ Real.log 3 / 16 := by simpa using hthreshold
  have hexp : Real.exp (4 * xi * A ^ 2) ≤
      (3 : ℝ) ^ ((16 : ℝ)⁻¹) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    apply Real.exp_le_exp.mpr
    simpa only [div_eq_mul_inv] using hexponent
  have hmul := mul_le_mul hroot hexp (Real.exp_pos _).le
    (by positivity : 0 ≤ 2 * K * Real.sqrt delta1)
  have hGmul := mul_le_mul_of_nonneg_left hmul hG
  convert hGmul using 1 <;> ring

private theorem raw_suffix_rhs_le_four_xi
    {q xi A b : ℝ} (hq : q ≤ 4 * xi)
    (hA0 : 0 ≤ A) (hb0 : 0 ≤ b) :
    2 * Ch04.gammaMomentConst 2 * Real.sqrt (2 * q) * (A + b) *
        Real.exp (q * A ^ 2 + b) ≤
      sharpTwoBlockGammaConst * Real.sqrt (4 * xi) * (A + b) *
        Real.exp (4 * xi * A ^ 2 + b) := by
  have hcoef : 2 * Ch04.gammaMomentConst 2 * Real.sqrt (2 * q) ≤
      sharpTwoBlockGammaConst * Real.sqrt (4 * xi) := by
    have hgamma : 0 < Ch04.gammaMomentConst 2 := by
      simpa using (IndependentSums.gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2))
    have hsqrt : Real.sqrt (2 * q) ≤ Real.sqrt (2 * (4 * xi)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hq (by norm_num))
    calc
      2 * Ch04.gammaMomentConst 2 * Real.sqrt (2 * q) ≤
          2 * Ch04.gammaMomentConst 2 * Real.sqrt (2 * (4 * xi)) :=
        mul_le_mul_of_nonneg_left hsqrt
          (mul_nonneg (by norm_num) hgamma.le)
      _ = sharpTwoBlockGammaConst * Real.sqrt (4 * xi) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        unfold sharpTwoBlockGammaConst
        ring
  have hexponent : q * A ^ 2 + b ≤ 4 * xi * A ^ 2 + b := by
    gcongr
  have hexp := Real.exp_le_exp.mpr hexponent
  have hcoefAB := mul_le_mul_of_nonneg_right hcoef (add_nonneg hA0 hb0)
  have hgamma : 0 < Ch04.gammaMomentConst 2 := by
    simpa using (IndependentSums.gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2))
  have hright0 : 0 ≤ sharpTwoBlockGammaConst * Real.sqrt (4 * xi) * (A + b) := by
    unfold sharpTwoBlockGammaConst
    positivity
  exact mul_le_mul hcoefAB hexp (Real.exp_pos _).le
    hright0

/-! ## Absorbed moments of the two random factors -/

theorem cutoffChangeSuffixRepresentative_lp_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    {q xi delta1 s : ℝ}
    (hq : 1 ≤ q) (hxi : 1 ≤ xi) (hqxi : q ≤ 4 * xi)
    (hdelta1 : delta1 < 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (hxiE : xi * M.delta ^ 2 ≤
      sharpTwoBlockSmallnessConst d * s * delta1) :
    paperENNRealLpNorm M.P.toMeasure q (fun omega =>
        ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega)) ≤
      ENNReal.ofReal (sharpTwoBlockFactorConst d * Real.sqrt delta1) := by
  let K := sharpTwoBlockScaleConst d
  let c := sharpTwoBlockSmallnessConst d
  let A := shellSensitivityConst d * M.delta
  have hK : 1 ≤ K := le_max_left _ _
  have hc0 : 0 < c := sharpTwoBlockSmallnessConst_pos d
  have hc1 : c ≤ 1 := sharpTwoBlockSmallnessConst_le_one d
  have hcthresh : c ≤ Real.log 3 / (16 * (4 * K ^ 2 + 1)) :=
    min_le_right _ _
  have hE : 0 < M.delta ^ 2 := sq_pos_of_pos M.shellPrefix.delta_pos
  have hA0 : 0 ≤ A := by
    exact mul_nonneg (shellSensitivityConst_pos d).le M.shellPrefix.delta_pos.le
  have hA2 : A ^ 2 ≤ K ^ 2 * M.delta ^ 2 := by
    have hscale := mul_le_mul_of_nonneg_right
      (shellSensitivityConst_le_sharpTwoBlockScaleConst d)
      M.shellPrefix.delta_pos.le
    have hsquare := pow_le_pow_left₀ hA0 hscale 2
    simpa only [A, K, mul_pow] using hsquare
  have hraw := cutoffChangeSuffixRepresentative_moment M m (m : ℤ) q hq
  dsimp only at hraw
  simp only [sub_self, zpow_zero, mul_one] at hraw
  have hnorm := paperENNRealLpNorm_le_of_real_moment M.P.toMeasure
    (zero_lt_one.trans_le hq)
    (fun omega => cutoffChangeSuffixRepresentative_nonneg m (m : ℤ) omega)
    hraw.1 (Filter.Eventually.of_forall fun _ => le_rfl)
  refine hnorm.trans (ENNReal.ofReal_le_ofReal ?_)
  have hraw4 := raw_suffix_rhs_le_four_xi hqxi hA0 (show 0 ≤ (0 : ℝ) by norm_num)
  have hraw4' :
      2 * Ch04.gammaMomentConst 2 * Real.sqrt (2 * q) * A *
          Real.exp (q * A ^ 2) ≤
        sharpTwoBlockGammaConst * Real.sqrt (4 * xi) * A *
          Real.exp (4 * xi * A ^ 2) := by
    simpa only [add_zero] using hraw4
  have habsorb := sharpTwoBlock_base_raw_bound hK
    (show 0 ≤ sharpTwoBlockGammaConst by
      unfold sharpTwoBlockGammaConst
      have hgamma : 0 < Ch04.gammaMomentConst 2 := by
        simpa using (IndependentSums.gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2))
      positivity)
    hc0 hc1 hcthresh hxi hE hdelta1 hs hs1 hxiE hA0 hA2
  have hbase :
      sharpTwoBlockGammaConst * 2 * K * (3 : ℝ) ^ ((16 : ℝ)⁻¹) ≤
        sharpTwoBlockFactorConst d := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hfac := mul_le_mul_of_nonneg_right hbase (Real.sqrt_nonneg delta1)
  have hraw' :
      (∫ omega, cutoffChangeSuffixRepresentative m (m : ℤ) omega ^ q
          ∂M.P.toMeasure) ^ q⁻¹ ≤
        2 * Ch04.gammaMomentConst 2 * Real.sqrt (2 * q) * A *
          Real.exp (q * A ^ 2) := by
    simpa only [A] using hraw.2
  exact hraw'.trans (hraw4'.trans (habsorb.trans (by
    convert hfac using 1
    ring)))

theorem finiteBlockRatioRepresentative_lp_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m k : ℕ} (hkm : k < m)
    (z : Vec d) {q xi delta1 s : ℝ}
    (hq : 1 ≤ q) (hxi : 1 ≤ xi) (hqxi : q ≤ 4 * xi)
    (hdelta1 : delta1 < 1) (hs : 0 < s)
    (hxiE : xi * M.delta ^ 2 ≤
      sharpTwoBlockSmallnessConst d * s * delta1) :
    paperENNRealLpNorm M.P.toMeasure q (fun omega =>
        ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega)) ≤
      ENNReal.ofReal (sharpTwoBlockFactorConst d * Real.sqrt delta1 *
        ((3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ) / 16)) ^ 2) := by
  let K := sharpTwoBlockScaleConst d
  let c := sharpTwoBlockSmallnessConst d
  let g : ℝ := ((m - k : ℕ) : ℝ)
  let A := smallCubeBlockScale M (k + 1) m (k : ℤ)
  let b := g * _root_.SubdiffusiveProcess.Model.tauSq M.P
  have hK : 1 ≤ K := le_max_left _ _
  have hc0 : 0 < c := sharpTwoBlockSmallnessConst_pos d
  have hc1 : c ≤ 1 := sharpTwoBlockSmallnessConst_le_one d
  have hcthresh : c ≤ Real.log 3 / (16 * (4 * K ^ 2 + 1)) :=
    min_le_right _ _
  have hE : 0 < M.delta ^ 2 := sq_pos_of_pos M.shellPrefix.delta_pos
  have hg : 1 ≤ g := by
    dsimp only [g]
    exact_mod_cast (show 1 ≤ m - k by omega)
  have hA0 : 0 ≤ A := by
    apply (show 0 < A from ?_).le
    unfold A smallCubeBlockScale
    apply mul_pos IndependentSums.gammaTriangleConst_pos
    apply add_pos
    · exact mul_pos (mul_pos cutoffGammaConst_pos
        (Real.sqrt_pos.mpr (by positivity))) M.shellPrefix.delta_pos
    · exact mul_pos IndependentSums.gammaTriangleConst_pos
        (Finset.sum_pos
          (fun j _ => translatedSmallShellScale_pos M j (k : ℤ))
          (Finset.nonempty_Icc.mpr (by omega)))
  have hscale : A ≤ K * Real.sqrt g * M.delta := by
    calc
      A ≤ smallCubeBlockConst * Real.sqrt g * M.delta := by
        simpa only [A, g] using finiteBlockRatioRepresentative_scale_le M hkm
      _ ≤ K * Real.sqrt g * M.delta := by
        have hc := smallCubeBlockConst_le_sharpTwoBlockScaleConst d
        have hright : 0 ≤ Real.sqrt g * M.delta :=
          mul_nonneg (Real.sqrt_nonneg _) M.shellPrefix.delta_pos.le
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hright
  have hA2 : A ^ 2 ≤ K ^ 2 * M.delta ^ 2 * g := by
    have hsquare := pow_le_pow_left₀ hA0 hscale 2
    calc
      A ^ 2 ≤ (K * Real.sqrt g * M.delta) ^ 2 := hsquare
      _ = K ^ 2 * M.delta ^ 2 * g := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (zero_le_one.trans hg)]
        ring
  have hb0 : 0 ≤ b := by
    exact mul_nonneg (zero_le_one.trans hg) M.G4.tauSq_pos.le
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 := by
    have hlog : Real.log 2 / 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    exact (tauSq_le_delta_sq M).trans <| by
      calc
        Real.log 2 / 2 * M.delta ^ 2 ≤ 1 * M.delta ^ 2 :=
          mul_le_mul_of_nonneg_right hlog hE.le
        _ = M.delta ^ 2 := one_mul _
  have hb : b ≤ M.delta ^ 2 * g := by
    unfold b
    have := mul_le_mul_of_nonneg_left htau (zero_le_one.trans hg)
    nlinarith
  have hraw := finiteBlockRatioRepresentative_moment_raw M hkm z q hq
  dsimp only at hraw
  have hnorm := paperENNRealLpNorm_le_of_real_moment M.P.toMeasure
    (zero_lt_one.trans_le hq)
    (finiteBlockRatioRepresentative_nonneg M m k z)
    hraw.1 (Filter.Eventually.of_forall fun _ => le_rfl)
  refine hnorm.trans (ENNReal.ofReal_le_ofReal ?_)
  have hraw4 := raw_suffix_rhs_le_four_xi hqxi hA0 hb0
  have habsorb := sharpTwoBlock_gap_raw_bound hK
    (show 0 ≤ sharpTwoBlockGammaConst by
      unfold sharpTwoBlockGammaConst
      have hgamma : 0 < Ch04.gammaMomentConst 2 := by
        simpa using (IndependentSums.gammaMomentConst_pos (by norm_num : (0 : ℝ) < 2))
      positivity)
    hc0 hc1 hcthresh hxi hE hdelta1 hs hg hxiE hA0 hb0 hA2 hb
  have hgapConst : sharpTwoBlockGammaConst *
        (2 * K * (1 + 16 / Real.log 3) + 32 / Real.log 3) ≤
      sharpTwoBlockFactorConst d := by
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hfac := mul_le_mul_of_nonneg_right hgapConst
    (mul_nonneg (Real.sqrt_nonneg delta1)
      (sq_nonneg ((3 : ℝ) ^ (s * g / 16))))
  have hraw' :
      (∫ omega, finiteBlockRatioRepresentative M m k z omega ^ q
          ∂M.P.toMeasure) ^ q⁻¹ ≤
        2 * Ch04.gammaMomentConst 2 * Real.sqrt (2 * q) * (A + b) *
          Real.exp (q * A ^ 2 + b) := by
    simpa only [A, b, g, mul_comm g] using hraw.2
  have hfac' :
      sharpTwoBlockGammaConst *
          (2 * K * (1 + 16 / Real.log 3) + 32 / Real.log 3) *
          Real.sqrt delta1 * ((3 : ℝ) ^ (s * g / 16)) ^ 2 ≤
        sharpTwoBlockFactorConst d * Real.sqrt delta1 *
          ((3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ) / 16)) ^ 2 := by
    simpa only [g, mul_assoc] using hfac
  exact hraw'.trans (hraw4.trans (habsorb.trans hfac'))

private theorem sharpTwoBlock_deterministic_bound
    {K c xi E delta1 s g : ℝ}
    (hK : 1 ≤ K) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hcthresh : c ≤ Real.log 3 / (16 * (4 * K ^ 2 + 1)))
    (hxi : 1 ≤ xi) (hE : 0 < E) (hdelta1 : delta1 < 1)
    (hs : 0 < s) (hg : 1 ≤ g)
    (hxiE : xi * E ≤ c * s * delta1) :
    4 * E * g * Real.exp (2 * E * g) ≤
      (64 / Real.log 3) * Real.sqrt delta1 *
        ((3 : ℝ) ^ (s * g / 16)) ^ 2 := by
  have hxi0 : 0 < xi := zero_lt_one.trans_le hxi
  have hdelta1pos : 0 < delta1 := by
    have : 0 < xi * E := mul_pos hxi0 hE
    have : 0 < c * s := mul_pos hc0 hs
    nlinarith
  have hg0 : 0 ≤ g := zero_le_one.trans hg
  have hu0 : 0 ≤ s * g := mul_nonneg hs.le hg0
  obtain ⟨hR1, _, huR⟩ := sharpTwoBlock_geometric hu0
  let R : ℝ := (3 : ℝ) ^ (s * g / 16)
  have hxiEg : xi * E * g ≤ c * delta1 * (s * g) := by
    have h := mul_le_mul_of_nonneg_right hxiE hg0
    nlinarith
  have hEgxi : E * g ≤ xi * E * g := by
    have h := mul_le_mul_of_nonneg_right hxi (mul_nonneg hE.le hg0)
    nlinarith
  have hEg : E * g ≤ delta1 * (s * g) := by
    have h1 := hEgxi.trans hxiEg
    have hcdu : c * delta1 * (s * g) ≤ delta1 * (s * g) := by
      have hcd : c * delta1 ≤ delta1 := by
        simpa using mul_le_mul_of_nonneg_right hc1 hdelta1pos.le
      exact mul_le_mul_of_nonneg_right hcd hu0
    exact h1.trans hcdu
  have hsqrt : delta1 ≤ Real.sqrt delta1 := by
    have hsqrtSq := Real.sq_sqrt hdelta1pos.le
    have hsqrtOne : Real.sqrt delta1 ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact hdelta1.le
    calc
      delta1 = Real.sqrt delta1 * Real.sqrt delta1 := by
        rw [← pow_two, hsqrtSq]
      _ ≤ Real.sqrt delta1 * 1 :=
        mul_le_mul_of_nonneg_left hsqrtOne (Real.sqrt_nonneg _)
      _ = Real.sqrt delta1 := mul_one _
  have hpref : 4 * E * g ≤ 64 / Real.log 3 * Real.sqrt delta1 * R := by
    have h1 := mul_le_mul_of_nonneg_left hEg (by norm_num : (0 : ℝ) ≤ 4)
    have h2 := mul_le_mul_of_nonneg_left huR
      (show 0 ≤ 4 * delta1 by positivity)
    have h3 := mul_le_mul_of_nonneg_right hsqrt
      (show 0 ≤ 64 / Real.log 3 * R by positivity)
    calc
      4 * E * g ≤ 4 * (delta1 * (s * g)) := by
        nlinarith only [h1]
      _ ≤ 4 * delta1 * (16 / Real.log 3 * R) := by
        simpa only [R, mul_assoc] using h2
      _ = delta1 * (64 / Real.log 3 * R) := by ring
      _ ≤ Real.sqrt delta1 * (64 / Real.log 3 * R) := h3
      _ = 64 / Real.log 3 * Real.sqrt delta1 * R := by ring
  have htwoc : 2 * c ≤ Real.log 3 / 16 := by
    have hden : 0 < 16 * (4 * K ^ 2 + 1) := by positivity
    have ht := (le_div_iff₀ hden).mp hcthresh
    have hKsq : 1 ≤ K ^ 2 :=
      (one_le_sq_iff₀ (zero_le_one.trans hK)).2 hK
    have hlog := log_three_pos
    nlinarith
  have hexponent : 2 * E * g ≤ Real.log 3 * (s * g / 16) := by
    have h1 : E * g ≤ c * delta1 * (s * g) :=
      hEgxi.trans hxiEg
    have hdelta : delta1 ≤ 1 := hdelta1.le
    have hcu : 0 ≤ c * (s * g) := mul_nonneg hc0.le hu0
    have h2 := mul_le_mul_of_nonneg_left hdelta hcu
    have h3 := mul_le_mul_of_nonneg_right htwoc hu0
    nlinarith
  have hexp : Real.exp (2 * E * g) ≤ R := by
    change Real.exp (2 * E * g) ≤ (3 : ℝ) ^ (s * g / 16)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_le_exp.mpr hexponent
  have hmul := mul_le_mul hpref hexp (Real.exp_pos _).le (by positivity)
  simpa only [pow_two, mul_assoc] using hmul

theorem annealedRatioDefect_le_absorbed {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m k : ℕ} (hkm : k < m)
    {xi delta1 s : ℝ} (hxi : 1 ≤ xi) (hdelta1 : delta1 < 1)
    (hs : 0 < s)
    (hxiE : xi * M.delta ^ 2 ≤
      sharpTwoBlockSmallnessConst d * s * delta1)
    (horder : ahom M m ≤ ahom M k ∧
      ahom M k ≤ Real.exp
        (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - k : ℕ) : ℝ)) *
          ahom M m) :
    annealedRatioDefect M m k ≤
      sharpTwoBlockFactorConst d * Real.sqrt delta1 *
        ((3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ) / 16)) ^ 2 := by
  have hratio := annealedOrderingRatio_of_ordering M hkm.le horder
  have habsorb := sharpTwoBlock_deterministic_bound
    (g := ((m - k : ℕ) : ℝ))
    (show 1 ≤ sharpTwoBlockScaleConst d from le_max_left _ _)
    (sharpTwoBlockSmallnessConst_pos d)
    (sharpTwoBlockSmallnessConst_le_one d)
    (show sharpTwoBlockSmallnessConst d ≤
        Real.log 3 / (16 * (4 * sharpTwoBlockScaleConst d ^ 2 + 1)) from
      min_le_right _ _)
    hxi (sq_pos_of_pos M.shellPrefix.delta_pos) hdelta1 hs
    (by exact_mod_cast (show 1 ≤ m - k by omega)) hxiE
  have hconst : 64 / Real.log 3 ≤ sharpTwoBlockFactorConst d := by
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hmul := mul_le_mul_of_nonneg_right hconst
    (mul_nonneg (Real.sqrt_nonneg delta1)
      (sq_nonneg ((3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ) / 16))))
  exact (show annealedRatioDefect M m k ≤
      4 * M.delta ^ 2 * ((m - k : ℕ) : ℝ) *
        Real.exp (2 * M.delta ^ 2 * ((m - k : ℕ) : ℝ)) from hratio).trans
    (habsorb.trans (by simpa only [mul_assoc] using hmul))

private theorem ofReal_sharpTwoBlockSuffixRepresentative
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m k : ℕ)
    (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m k z omega) =
      2 * (ENNReal.ofReal (annealedRatioDefect M m k) +
        (1 + ENNReal.ofReal (annealedRatioDefect M m k)) *
          (ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega) +
            ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega) +
            ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega) *
              ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega))) := by
  let D := annealedRatioDefect M m k
  let Y := cutoffChangeSuffixRepresentative m (m : ℤ) omega
  let Z := finiteBlockRatioRepresentative M m k z omega
  have hD : 0 ≤ D := annealedRatioDefect_nonneg M m k
  have hY : 0 ≤ Y := cutoffChangeSuffixRepresentative_nonneg m (m : ℤ) omega
  have hZ : 0 ≤ Z := finiteBlockRatioRepresentative_nonneg M m k z omega
  have hreal : sharpTwoBlockSuffixRepresentative M m k z omega =
      2 * (D + (1 + D) * (Y + Z + Y * Z)) := by
    unfold sharpTwoBlockSuffixRepresentative
    dsimp only [D, Y, Z]
    ring
  rw [hreal, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_add hD (mul_nonneg (add_nonneg zero_le_one hD)
      (add_nonneg (add_nonneg hY hZ) (mul_nonneg hY hZ))),
    ENNReal.ofReal_mul (add_nonneg zero_le_one hD),
    ENNReal.ofReal_add zero_le_one hD,
    ENNReal.ofReal_add (add_nonneg hY hZ) (mul_nonneg hY hZ),
    ENNReal.ofReal_add hY hZ, ENNReal.ofReal_mul hY]
  norm_num
  rfl

private theorem sharpTwoBlock_polynomial_bound
    {A delta R : ℝ} (hA : 1 ≤ A)
    (hdelta1 : delta < 1) (hR : 1 ≤ R) :
    let B := A * Real.sqrt delta * R ^ 2
    2 * (3 * B + 3 * B ^ 2 + B ^ 3) ≤
      2 * (3 * A + 3 * A ^ 2 + A ^ 3) * Real.sqrt delta * R ^ 6 := by
  dsimp only
  let t := Real.sqrt delta
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht1 : t ≤ 1 := by
    dsimp only [t]
    rw [Real.sqrt_le_one]
    exact hdelta1.le
  have ht2 : t ^ 2 ≤ t := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have ht3 : t ^ 3 ≤ t := by
    have hmul := mul_le_mul_of_nonneg_left ht2 ht0
    calc
      t ^ 3 = t * t ^ 2 := by ring
      _ ≤ t * t := hmul
      _ = t ^ 2 := by ring
      _ ≤ t := ht2
  have hR26 : R ^ 2 ≤ R ^ 6 := pow_le_pow_right₀ hR (by omega)
  have hR46 : R ^ 4 ≤ R ^ 6 := pow_le_pow_right₀ hR (by omega)
  have hB1 : A * t * R ^ 2 ≤ A * t * R ^ 6 :=
    mul_le_mul_of_nonneg_left hR26 (mul_nonneg (zero_le_one.trans hA) ht0)
  have hB2 : (A * t * R ^ 2) ^ 2 ≤ A ^ 2 * t * R ^ 6 := by
    calc
      (A * t * R ^ 2) ^ 2 = A ^ 2 * t ^ 2 * R ^ 4 := by ring
      _ ≤ A ^ 2 * t * R ^ 4 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ht2 (sq_nonneg A))
          (pow_nonneg (zero_le_one.trans hR) 4)
      _ ≤ A ^ 2 * t * R ^ 6 :=
        mul_le_mul_of_nonneg_left hR46
          (mul_nonneg (sq_nonneg A) ht0)
  have hB3 : (A * t * R ^ 2) ^ 3 ≤ A ^ 3 * t * R ^ 6 := by
    have hA0 : 0 ≤ A := zero_le_one.trans hA
    have hR0 : 0 ≤ R := zero_le_one.trans hR
    calc
      (A * t * R ^ 2) ^ 3 = A ^ 3 * t ^ 3 * R ^ 6 := by ring
      _ ≤ A ^ 3 * t * R ^ 6 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ht3 (pow_nonneg hA0 3)) (pow_nonneg hR0 6)
  dsimp only [t] at hB1 hB2 hB3 ⊢
  nlinarith only [hB1, hB2, hB3]

private theorem ennreal_product_polynomial_eq {B : ℝ} (hB : 0 ≤ B) :
    2 * (ENNReal.ofReal B + (1 + ENNReal.ofReal B) *
      (ENNReal.ofReal B + ENNReal.ofReal B +
        ENNReal.ofReal B * ENNReal.ofReal B)) =
      ENNReal.ofReal (2 * (3 * B + 3 * B ^ 2 + B ^ 3)) := by
  rw [show 2 * (3 * B + 3 * B ^ 2 + B ^ 3) =
      2 * (B + (1 + B) * (B + B + B * B)) by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_add hB
      (mul_nonneg (add_nonneg zero_le_one hB)
        (add_nonneg (add_nonneg hB hB) (mul_nonneg hB hB))),
    ENNReal.ofReal_mul (add_nonneg zero_le_one hB),
    ENNReal.ofReal_add zero_le_one hB,
    ENNReal.ofReal_add (add_nonneg hB hB) (mul_nonneg hB hB),
    ENNReal.ofReal_add hB hB, ENNReal.ofReal_mul hB]
  norm_num

theorem sharpTwoBlockSuffixRepresentative_lp_le_of_ordering {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m k : ℕ} (hkm : k < m)
    (z : Vec d) {xi delta1 s : ℝ}
    (hxi : 1 ≤ xi) (hdelta1 : delta1 < 1)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hxiE : xi * M.delta ^ 2 ≤
      sharpTwoBlockSmallnessConst d * s * delta1)
    (horder : ahom M m ≤ ahom M k ∧
      ahom M k ≤ Real.exp
        (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - k : ℕ) : ℝ)) *
          ahom M m) :
    paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
        ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m k z omega)) ≤
      ENNReal.ofReal
        (2 * (3 * sharpTwoBlockFactorConst d +
            3 * sharpTwoBlockFactorConst d ^ 2 +
            sharpTwoBlockFactorConst d ^ 3) *
          Real.sqrt delta1 *
          ((3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ) / 16)) ^ 6) := by
  let A := sharpTwoBlockFactorConst d
  let R : ℝ := (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ) / 16)
  let B := A * Real.sqrt delta1 * R ^ 2
  have hA : 1 ≤ A := one_le_sharpTwoBlockFactorConst d
  have hdelta1pos : 0 < delta1 := by
    have hleft : 0 < xi * M.delta ^ 2 :=
      mul_pos (zero_lt_one.trans_le hxi) (sq_pos_of_pos M.shellPrefix.delta_pos)
    have hcs : 0 < sharpTwoBlockSmallnessConst d * s :=
      mul_pos (sharpTwoBlockSmallnessConst_pos d) hs
    nlinarith
  have hR : 1 ≤ R := by
    apply Real.one_le_rpow (by norm_num)
    exact div_nonneg
      (mul_nonneg hs.le (by positivity)) (by norm_num)
  have hB0 : 0 ≤ B := by
    exact mul_nonneg
      (mul_nonneg (zero_le_one.trans hA) (Real.sqrt_nonneg _)) (pow_nonneg (zero_le_one.trans hR) 2)
  have hYR : A * Real.sqrt delta1 ≤ B := by
    unfold B
    have hR2 : 1 ≤ R ^ 2 := by
      simpa using pow_le_pow_right₀ (m := 0) (n := 2) hR (by omega)
    simpa only [mul_assoc, mul_one] using
      mul_le_mul_of_nonneg_left hR2
        (mul_nonneg (zero_le_one.trans hA) (Real.sqrt_nonneg _))
  have hY2 := cutoffChangeSuffixRepresentative_lp_le M m
    (q := 2 * xi) (xi := xi) (delta1 := delta1) (s := s)
    (by nlinarith) hxi (by nlinarith) hdelta1 hs hs1 hxiE
  have hY4 := cutoffChangeSuffixRepresentative_lp_le M m
    (q := 4 * xi) (xi := xi) (delta1 := delta1) (s := s)
    (by nlinarith) hxi le_rfl hdelta1 hs hs1 hxiE
  have hZ2 := finiteBlockRatioRepresentative_lp_le M hkm z
    (q := 2 * xi) (xi := xi) (delta1 := delta1) (s := s)
    (by nlinarith) hxi (by nlinarith) hdelta1 hs hxiE
  have hZ4 := finiteBlockRatioRepresentative_lp_le M hkm z
    (q := 4 * xi) (xi := xi) (delta1 := delta1) (s := s)
    (by nlinarith) hxi le_rfl hdelta1 hs hxiE
  have hD := annealedRatioDefect_le_absorbed M hkm hxi hdelta1 hs hxiE horder
  have hY2B : paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
      ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega)) ≤
      ENNReal.ofReal B := hY2.trans (ENNReal.ofReal_le_ofReal hYR)
  have hY4B : paperENNRealLpNorm M.P.toMeasure (4 * xi) (fun omega =>
      ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega)) ≤
      ENNReal.ofReal B := hY4.trans (ENNReal.ofReal_le_ofReal hYR)
  have hZ2B : paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
      ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega)) ≤
      ENNReal.ofReal B := by simpa only [B, A, R]
      using hZ2
  have hZ4B : paperENNRealLpNorm M.P.toMeasure (4 * xi) (fun omega =>
      ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega)) ≤
      ENNReal.ofReal B := by simpa only [B, A, R]
      using hZ4
  have hY22B : paperENNRealLpNorm M.P.toMeasure (2 * (2 * xi)) (fun omega =>
      ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega)) ≤
      ENNReal.ofReal B := by
    convert hY4B using 1
    ring_nf
  have hZ22B : paperENNRealLpNorm M.P.toMeasure (2 * (2 * xi)) (fun omega =>
      ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega)) ≤
      ENNReal.ofReal B := by
    convert hZ4B using 1
    ring_nf
  have hDB : ENNReal.ofReal (annealedRatioDefect M m k) ≤ ENNReal.ofReal B := by
    exact ENNReal.ofReal_le_ofReal (by simpa only [B, A, R] using hD)
  have hYmeas : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega)) :=
    ((measurable_cutoffChangeSuffixRepresentative (d := d) m (m : ℤ)).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi m)) le_rfl).ennreal_ofReal
  have hZmeas : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega)) :=
    ((measurable_finiteBlockRatioRepresentative M m k z).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi k)) le_rfl).ennreal_ofReal
  have hpoint : ∀ᵐ omega ∂M.P.toMeasure,
      ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m k z omega) ≤
        2 * (ENNReal.ofReal (annealedRatioDefect M m k) +
          (1 + ENNReal.ofReal (annealedRatioDefect M m k)) *
            (ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega) +
              ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega) +
              ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega) *
                ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega))) :=
    Filter.Eventually.of_forall fun omega =>
      (ofReal_sharpTwoBlockSuffixRepresentative M m k z omega).le
  have hmono := paperENNRealLpNorm_mono_ae M.P.toMeasure
    (show 0 ≤ 2 * xi by positivity) hpoint
  have henv := paperENNRealLpNorm_product_envelope_le M.P.toMeasure
    (show 1 ≤ 2 * xi by nlinarith)
    (ENNReal.ofReal (annealedRatioDefect M m k)) hYmeas hZmeas
  have hcompose :
      paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
        2 * (ENNReal.ofReal (annealedRatioDefect M m k) +
          (1 + ENNReal.ofReal (annealedRatioDefect M m k)) *
            (ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega) +
              ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega) +
              ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega) *
                ENNReal.ofReal (finiteBlockRatioRepresentative M m k z omega)))) ≤
        2 * (ENNReal.ofReal B + (1 + ENNReal.ofReal B) *
          (ENNReal.ofReal B + ENNReal.ofReal B +
            ENNReal.ofReal B * ENNReal.ofReal B)) := by
    refine henv.trans ?_
    gcongr
  refine hmono.trans (hcompose.trans ?_)
  rw [ennreal_product_polynomial_eq hB0]
  apply ENNReal.ofReal_le_ofReal
  simpa only [A, R, B] using sharpTwoBlock_polynomial_bound hA hdelta1 hR

theorem sharpTwoBlock_squared_moment_of_ordering {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m k : ℕ} (hkm : k < m)
    (z : Vec d) {xi delta1 s : ℝ}
    (hxi : 1 ≤ xi) (hdelta1 : delta1 < 1)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (hxiE : xi * M.delta ^ 2 ≤
      sharpTwoBlockSmallnessConst d * s * delta1)
    (horder : ahom M m ≤ ahom M k ∧
      ahom M k ≤ Real.exp
        (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - k : ℕ) : ℝ)) *
          ahom M m) :
    paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
        ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m k z omega ^ 2)) ≤
      ENNReal.ofReal (sharpTwoBlockMomentConst d * delta1 *
        (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))) := by
  let A := sharpTwoBlockFactorConst d
  let P := 2 * (3 * A + 3 * A ^ 2 + A ^ 3)
  let R : ℝ := (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ) / 16)
  have hroot := sharpTwoBlockSuffixRepresentative_lp_le_of_ordering
    M hkm z hxi hdelta1 hs hs1 hxiE horder
  have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m k z omega ^ 2)) =
      fun omega =>
        (ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m k z omega)) ^ 2 := by
    funext omega
    rw [← ENNReal.ofReal_pow
      (sharpTwoBlockSuffixRepresentative_nonneg M m k z omega)]
  rw [hfun, paperENNRealLpNorm_sq M.P.toMeasure
    (show 0 < xi by exact zero_lt_one.trans_le hxi)]
  have hroot' : paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
      ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m k z omega)) ≤
      ENNReal.ofReal (P * Real.sqrt delta1 * R ^ 6) := by
    simpa only [P, A, R] using hroot
  have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ≥0∞) ≤
      paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
        ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m k z omega))) hroot' 2
  refine hsquare.trans ?_
  have hP0 : 0 ≤ P := by
    dsimp only [P, A]
    have hAf : 0 ≤ sharpTwoBlockFactorConst d :=
      zero_le_one.trans (one_le_sharpTwoBlockFactorConst d)
    positivity
  have hbound0 : 0 ≤ P * Real.sqrt delta1 * R ^ 6 := by positivity
  rw [← ENNReal.ofReal_pow hbound0]
  apply ENNReal.ofReal_le_ofReal
  have hdelta1pos : 0 < delta1 := by
    have hleft : 0 < xi * M.delta ^ 2 :=
      mul_pos (zero_lt_one.trans_le hxi) (sq_pos_of_pos M.shellPrefix.delta_pos)
    have hcs : 0 < sharpTwoBlockSmallnessConst d * s :=
      mul_pos (sharpTwoBlockSmallnessConst_pos d) hs
    nlinarith
  have hR : 1 ≤ R := by
    apply Real.one_le_rpow (by norm_num)
    exact div_nonneg (mul_nonneg hs.le (by positivity)) (by norm_num)
  have hR1216 : R ^ 12 ≤ R ^ 16 := pow_le_pow_right₀ hR (by omega)
  have hR16 : R ^ 16 = (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ)) := by
    simpa only [R] using (sharpTwoBlock_geometric
      (mul_nonneg hs.le (by positivity : 0 ≤ ((m - k : ℕ) : ℝ)))).2.1
  have hC : P ^ 2 ≤ sharpTwoBlockMomentConst d := by
    exact le_max_right _ _
  have hCdelta0 : 0 ≤ sharpTwoBlockMomentConst d * delta1 :=
    mul_nonneg (zero_le_one.trans (one_le_sharpTwoBlockMomentConst d)) hdelta1pos.le
  calc
    (P * Real.sqrt delta1 * R ^ 6) ^ 2 =
        P ^ 2 * delta1 * R ^ 12 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hdelta1pos.le]
      ring
    _ ≤ sharpTwoBlockMomentConst d * delta1 * R ^ 12 := by
      gcongr
    _ ≤ sharpTwoBlockMomentConst d * delta1 * R ^ 16 := by
      exact mul_le_mul_of_nonneg_left hR1216 hCdelta0
    _ = sharpTwoBlockMomentConst d * delta1 *
        (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ)) := by rw [hR16]

private theorem finiteBlockRatioRepresentative_self
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    finiteBlockRatioRepresentative M m m z omega = 0 := by
  simp [finiteBlockRatioRepresentative, smallCubeBlockEnvelope,
    cutoffShellSum, cutoffShellIndices]

private theorem annealedRatioDefect_self
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) :
    annealedRatioDefect M m m = 0 := by
  have hmpos : 0 < ahom M m :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m)
  simp [annealedRatioDefect, hmpos.ne']

private theorem sharpTwoBlockSuffixRepresentative_self
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    sharpTwoBlockSuffixRepresentative M m m z omega =
      2 * cutoffChangeSuffixRepresentative m (m : ℤ) omega := by
  rw [sharpTwoBlockSuffixRepresentative, annealedRatioDefect_self,
    finiteBlockRatioRepresentative_self]
  ring

private theorem sharpTwoBlock_self_squared_moment {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ) (z : Vec d)
    {xi delta1 s : ℝ} (hxi : 1 ≤ xi)
    (hdelta1 : delta1 < 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (hxiE : xi * M.delta ^ 2 ≤
      sharpTwoBlockSmallnessConst d * s * delta1) :
    paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
        ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m m z omega ^ 2)) ≤
      ENNReal.ofReal (sharpTwoBlockMomentConst d * delta1) := by
  let A := sharpTwoBlockFactorConst d
  let P := 2 * (3 * A + 3 * A ^ 2 + A ^ 3)
  have hA : 1 ≤ A := one_le_sharpTwoBlockFactorConst d
  have hdelta1pos : 0 < delta1 := by
    have hleft : 0 < xi * M.delta ^ 2 :=
      mul_pos (zero_lt_one.trans_le hxi) (sq_pos_of_pos M.shellPrefix.delta_pos)
    have hcs : 0 < sharpTwoBlockSmallnessConst d * s :=
      mul_pos (sharpTwoBlockSmallnessConst_pos d) hs
    nlinarith
  have hY := cutoffChangeSuffixRepresentative_lp_le M m
    (q := 2 * xi) (xi := xi) (delta1 := delta1) (s := s)
    (by nlinarith) hxi (by nlinarith) hdelta1 hs hs1 hxiE
  have hYmeas : Measurable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega)) :=
    ((measurable_cutoffChangeSuffixRepresentative (d := d) m (m : ℤ)).mono
      (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi m)) le_rfl).ennreal_ofReal
  have hrep : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m m z omega)) =
      fun omega => 2 *
        ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega) := by
    funext omega
    rw [sharpTwoBlockSuffixRepresentative_self,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hroot : paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
      ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m m z omega)) ≤
      ENNReal.ofReal (2 * A * Real.sqrt delta1) := by
    rw [hrep, paperENNRealLpNorm_const_mul_eq M.P.toMeasure
      (show 0 < 2 * xi by positivity) 2 _ hYmeas]
    calc
      2 * paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
          ENNReal.ofReal (cutoffChangeSuffixRepresentative m (m : ℤ) omega)) ≤
          2 * ENNReal.ofReal (A * Real.sqrt delta1) :=
        mul_le_mul_of_nonneg_left (by simpa only [A] using hY) (by norm_num)
      _ = ENNReal.ofReal (2 * A * Real.sqrt delta1) := by
        calc
          2 * ENNReal.ofReal (A * Real.sqrt delta1) =
              ENNReal.ofReal 2 * ENNReal.ofReal (A * Real.sqrt delta1) := by norm_num
          _ = ENNReal.ofReal (2 * (A * Real.sqrt delta1)) :=
            (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
          _ = ENNReal.ofReal (2 * A * Real.sqrt delta1) := by
            congr 1
            ring
  have hfun : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m m z omega ^ 2)) =
      fun omega =>
        (ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m m z omega)) ^ 2 := by
    funext omega
    rw [← ENNReal.ofReal_pow
      (sharpTwoBlockSuffixRepresentative_nonneg M m m z omega)]
  rw [hfun, paperENNRealLpNorm_sq M.P.toMeasure
    (show 0 < xi by exact zero_lt_one.trans_le hxi)]
  have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℝ≥0∞) ≤
      paperENNRealLpNorm M.P.toMeasure (2 * xi) (fun omega =>
        ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m m z omega))) hroot 2
  refine hsquare.trans ?_
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * A * Real.sqrt delta1)]
  apply ENNReal.ofReal_le_ofReal
  have h2AP : 2 * A ≤ P := by
    dsimp only [P]
    have hA0 : 0 ≤ A := zero_le_one.trans hA
    nlinarith [sq_nonneg A, pow_nonneg hA0 3]
  have h2Asq : (2 * A) ^ 2 ≤ P ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2AP 2
  have hPC : P ^ 2 ≤ sharpTwoBlockMomentConst d := le_max_right _ _
  calc
    (2 * A * Real.sqrt delta1) ^ 2 = (2 * A) ^ 2 * delta1 := by
      rw [mul_pow, Real.sq_sqrt hdelta1pos.le]
    _ ≤ P ^ 2 * delta1 := mul_le_mul_of_nonneg_right h2Asq hdelta1pos.le
    _ ≤ sharpTwoBlockMomentConst d * delta1 :=
      mul_le_mul_of_nonneg_right hPC hdelta1pos.le

/-- The absorbed `e.XmLk.bound` payload, conditional only on the byte-exact
strict two-sided ordering clause of `l.annealed.matrix.bounds`. -/
theorem sharpTwoBlock_squared_moment_of_annealed_ordering {d : ℕ}
    (horder : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m k : ℕ), k < m →
      ahom M m ≤ ahom M k ∧
      ahom M k ≤ Real.exp
        (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - k : ℕ) : ℝ)) *
          ahom M m) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (xi delta1 s : ℝ) (m k : ℕ) (Q : Homogenization.TriadicCube d),
        1 ≤ xi → M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        0 < s → s ≤ 1 →
        xi ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
        k ≤ m →
        Q ∈ Homogenization.descendantsAtScale
          (Homogenization.originCube d (m : ℤ)) (k : ℤ) →
        paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
          ENNReal.ofReal
            (sharpTwoBlockSuffixRepresentative M m k
              (Homogenization.triadicCubeShift Q) omega ^ 2)) ≤
          ENNReal.ofReal (C * delta1 *
            (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))) := by
  refine ⟨sharpTwoBlockSmallnessConst d, sharpTwoBlockMomentConst d,
    sharpTwoBlockSmallnessConst_pos d, sharpTwoBlockSmallnessConst_le_one d,
    one_le_sharpTwoBlockMomentConst d, ?_⟩
  intro M xi delta1 s m k Q hxi _hdelta hdelta1 hs hs1 hxic hkm _hQ
  have hE : 0 < M.delta ^ 2 := sq_pos_of_pos M.shellPrefix.delta_pos
  have hxiE : xi * M.delta ^ 2 ≤
      sharpTwoBlockSmallnessConst d * s * delta1 := by
    have h := mul_le_mul_of_nonneg_right hxic hE.le
    calc
      xi * M.delta ^ 2 ≤
          sharpTwoBlockSmallnessConst d * s * (M.delta ^ 2)⁻¹ * delta1 *
            M.delta ^ 2 := h
      _ = sharpTwoBlockSmallnessConst d * s * delta1 := by
        field_simp [M.shellPrefix.delta_pos.ne']
  rcases hkm.eq_or_lt with rfl | hkm'
  · simpa using sharpTwoBlock_self_squared_moment M k
      (Homogenization.triadicCubeShift Q) hxi hdelta1 hs hs1 hxiE
  · exact sharpTwoBlock_squared_moment_of_ordering M hkm'
      (Homogenization.triadicCubeShift Q) hxi hdelta1 hs hs1 hxiE
      (horder M m k hkm')

/-! ## Pathwise localization domination -/

theorem sharpTwoBlock_dominates_localization {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {m k L : ℕ}
    (hkm : k ≤ m) (hmL : m ≤ L) (Q : Homogenization.TriadicCube d)
    (hQ : Q ∈ Homogenization.descendantsAtScale
      (Homogenization.originCube d (m : ℤ)) (k : ℤ)) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ENNReal.ofReal
          (responseLocalizationError M L k (Ch02.cubeDomain Q)
            (tailCoefficientCubeAverage M L m omega) omega ^ 2) ≤
        ENNReal.ofReal
            (sharpTwoBlockSuffixRepresentative M m k
              (Homogenization.triadicCubeShift Q) omega ^ 2) := by
  have hparent : openCubeSet Q ⊆ openCubeSet (originCube d (m : ℤ)) := by
    have hscale : (k : ℤ) ≤ (originCube d (m : ℤ)).scale := by
      change (k : ℤ) ≤ (m : ℤ)
      exact_mod_cast hkm
    exact openCubeSet_subset_of_mem_descendantsAtDepth
      ((mem_descendantsAtScale_iff hscale).mp hQ)
  have hQscale : Q.scale = (k : ℤ) := scale_eq_of_mem_descendantsAtScale hQ
  filter_upwards [ae_tailCutoff_pair_ratio_le_cutoffChangeSuffixRepresentative M m]
    with omega htail
  let b := tailCoefficientCubeAverage M L m omega
  let D := annealedRatioDefect M m k
  let Y := cutoffChangeSuffixRepresentative m (m : ℤ) omega
  let Z := finiteBlockRatioRepresentative M m k (triadicCubeShift Q) omega
  let E := (1 + D) * (1 + Y) * (1 + Z) - 1
  have hb : 0 < b := tailCoefficientCubeAverage_pos M L m omega
  have hhomM : 0 < ahom M m :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M m)
  have hhomK : 0 < ahom M k :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M k)
  have hD0 : 0 ≤ D := annealedRatioDefect_nonneg M m k
  have hY0 : 0 ≤ Y := cutoffChangeSuffixRepresentative_nonneg m (m : ℤ) omega
  have hZ0 : 0 ≤ Z := finiteBlockRatioRepresentative_nonneg M m k _ omega
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    nlinarith [mul_nonneg hD0 hY0,
      mul_nonneg (sub_nonneg.mpr (by nlinarith [mul_nonneg hD0 hY0])) hZ0]
  have htcont := continuous_tailCoefficient M L m omega
  have htpos : ∀ x, 0 < tailCoefficient M L m omega x := by
    intro x
    apply tailCoefficient_pos_of_ahom_pos M L m omega
    simpa [Nat.min_eq_left hmL] using hhomM
  have hpair : ∀ x ∈ openCubeSet (originCube d (m : ℤ)),
      ∀ y ∈ openCubeSet (originCube d (m : ℤ)),
      |tailCoefficient M L m omega x / tailCoefficient M L m omega y - 1| ≤ Y := by
    intro x hx y hy
    have hraw := htail L hmL x y hx hy
    dsimp only [Y]
    convert hraw using 1
    unfold tailCoefficient
    rw [Nat.min_eq_left hmL]
    field_simp [hhomM.ne',
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x).ne',
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega y).ne',
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).ne',
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega y).ne']
  have havg : ∀ y ∈ openCubeSet (originCube d (m : ℤ)),
      |b / tailCoefficient M L m omega y - 1| ≤ Y ∧
      |tailCoefficient M L m omega y / b - 1| ≤ Y := by
    intro y hy
    simpa only [b, tailCoefficientCubeAverage, Ch02.cubeDomain_coe] using
      tailAverage_ratio_bounds
        (Ch02.cubeDomain (originCube d (m : ℤ)))
        (tailCoefficient M L m omega) htcont htpos hpair hb hy
  have hxshift : ∀ x ∈ openCubeSet Q,
      x - triadicCubeShift Q ∈ openCubeSet (originCube d (k : ℤ)) := by
    intro x hx
    have hx' : x ∈ translateSet (triadicCubeShift Q)
        (openCubeSet (originCube d Q.scale)) := by
      rwa [← openCubeSet_eq_translateSet_originCube_of_triadicCube Q]
    rw [mem_translateSet_iff_sub_mem] at hx'
    simpa only [hQscale] using hx'
  have hfirst : scalarRatioLInf (Ch02.cubeDomain Q)
      (fun x => b / ahom M k * _root_.SubdiffusiveProcess.Model.aCutoff M k omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) ≤ E := by
    apply scalarRatioLInf_le_of_forall_bound hE0
    intro x hx
    have hxParent := hparent hx
    have hav := (havg x hxParent).1
    have hf : |_root_.SubdiffusiveProcess.Model.aCutoff M k omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x - 1| ≤ Z := by
      rcases hkm.eq_or_lt with rfl | hkm'
      · simp [Z, finiteBlockRatioRepresentative_self,
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M k omega x).ne']
      · exact abs_inverseCutoffRatioMinusOne_le_finiteBlockRatioRepresentative
          M hkm' (triadicCubeShift Q) omega (hxshift x hx)
    have hp := abs_mul_three_sub_one_le_product_envelope hD0 hY0
      (show |ahom M m / ahom M k - 1| ≤ D by
        dsimp only [D, annealedRatioDefect]
        rw [div_eq_mul_inv]
        exact le_add_of_nonneg_right (abs_nonneg _)) hav hf
    have hid : b / ahom M k * _root_.SubdiffusiveProcess.Model.aCutoff M k omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x =
        (ahom M m / ahom M k) *
          (b / tailCoefficient M L m omega x) *
          (_root_.SubdiffusiveProcess.Model.aCutoff M k omega x /
            _root_.SubdiffusiveProcess.Model.aCutoff M m omega x) := by
      unfold tailCoefficient
      rw [Nat.min_eq_left hmL]
      field_simp [hhomM.ne', hhomK.ne',
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x).ne',
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).ne']
    rw [hid]
    simpa only [D, Y, Z, E] using hp
  have hsecond : scalarRatioLInf (Ch02.cubeDomain Q)
      (fun x => (b / ahom M k)⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M L omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff M k omega) ≤ E := by
    apply scalarRatioLInf_le_of_forall_bound hE0
    intro x hx
    have hxParent := hparent hx
    have hav := (havg x hxParent).2
    have hf : |_root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
        _root_.SubdiffusiveProcess.Model.aCutoff M k omega x - 1| ≤ Z := by
      rcases hkm.eq_or_lt with rfl | hkm'
      · simp [Z, finiteBlockRatioRepresentative_self,
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M k omega x).ne']
      · exact abs_cutoffRatioMinusOne_le_finiteBlockRatioRepresentative
          M hkm' (triadicCubeShift Q) omega (hxshift x hx)
    have hp := abs_mul_three_sub_one_le_product_envelope hD0 hY0
      (show |ahom M k / ahom M m - 1| ≤ D by
        dsimp only [D, annealedRatioDefect]
        rw [div_eq_mul_inv, mul_comm]
        exact le_add_of_nonneg_left (abs_nonneg _)) hav hf
    have hid : (b / ahom M k)⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M k omega x =
        (ahom M k / ahom M m) *
          (tailCoefficient M L m omega x / b) *
          (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
            _root_.SubdiffusiveProcess.Model.aCutoff M k omega x) := by
      unfold tailCoefficient
      rw [Nat.min_eq_left hmL]
      field_simp [hb.ne', hhomM.ne', hhomK.ne',
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x).ne',
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M k omega x).ne',
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).ne']
    rw [hid]
    simpa only [D, Y, Z, E] using hp
  have herror : responseLocalizationError M L k (Ch02.cubeDomain Q) b omega ≤
      sharpTwoBlockSuffixRepresentative M m k (triadicCubeShift Q) omega := by
    unfold responseLocalizationError
    dsimp only
    have hsum := add_le_add hfirst hsecond
    dsimp only [E] at hsum
    unfold sharpTwoBlockSuffixRepresentative
    dsimp only [D, Y, Z, b]
    convert hsum using 1
    ring
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
    (responseLocalizationError_nonneg M L k (Ch02.cubeDomain Q) b omega)
    herror 2)

/-- The exact left side of `e.moment.bound.for.J` on one scale-`k`
descendant of the scale-`m` parent. -/
noncomputable def positiveScaleResponseObservable {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℕ)
    (Q : Homogenization.TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ≥0∞ :=
  ⨆ L : {L : ℕ // m ≤ L},
    paperScalarProbeMaxOn (Ch02.cubeDomain Q)
      (aCutoffCoeffOnData M L.1 omega (Ch02.cubeDomain Q)).toCoeffOn
      (tailCoefficientCubeAverage M L.1 m omega)

/-- Exact positive-scale response consumer after the prefix/suffix
factorization, conditional on the strict annealed ordering clause. -/
theorem positiveScaleResponseMoment_of_annealed_ordering {d : ℕ}
    (horder : ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m k : ℕ), k < m →
      ahom M m ≤ ahom M k ∧
      ahom M k ≤ Real.exp
        (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - k : ℕ) : ℝ)) *
          ahom M m) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (m0 : ℕ) (xi delta1 s : ℝ) (m k : ℕ)
        (Q : Homogenization.TriadicCube d),
        inductionHypothesis M m0 xi delta1 →
        M.delta ^ 2 ≤ delta1 → delta1 < 1 →
        0 < s → s ≤ 1 →
        xi ≤ c * s * (M.delta ^ 2)⁻¹ * delta1 →
        k ≤ m0 → k ≤ m →
        Q ∈ Homogenization.descendantsAtScale
          (Homogenization.originCube d (m : ℤ)) (k : ℤ) →
        paperENNRealLpNorm M.P.toMeasure xi
            (positiveScaleResponseObservable M m Q) ≤
          ENNReal.ofReal (C * delta1 *
            (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))) := by
  let C : ℝ := 2 + 6 * sharpTwoBlockMomentConst d
  refine ⟨sharpTwoBlockSmallnessConst d, C,
    sharpTwoBlockSmallnessConst_pos d, sharpTwoBlockSmallnessConst_le_one d,
    ?_, ?_⟩
  · dsimp only [C]
    have := one_le_sharpTwoBlockMomentConst d
    linarith
  intro M m0 xi delta1 s m k Q hS hdelta hdelta1 hs hs1 hxic hk0 hkm hQ
  have hE : 0 < M.delta ^ 2 := sq_pos_of_pos M.shellPrefix.delta_pos
  have hxiE : xi * M.delta ^ 2 ≤
      sharpTwoBlockSmallnessConst d * s * delta1 := by
    have h := mul_le_mul_of_nonneg_right hxic hE.le
    calc
      xi * M.delta ^ 2 ≤
          sharpTwoBlockSmallnessConst d * s * (M.delta ^ 2)⁻¹ * delta1 *
            M.delta ^ 2 := h
      _ = sharpTwoBlockSmallnessConst d * s * delta1 := by
        field_simp [M.shellPrefix.delta_pos.ne']
  have hXnorm : paperENNRealLpNorm M.P.toMeasure xi (fun omega =>
      ENNReal.ofReal (sharpTwoBlockSuffixRepresentative M m k
        (triadicCubeShift Q) omega ^ 2)) ≤
      ENNReal.ofReal (sharpTwoBlockMomentConst d * delta1 *
        (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))) := by
    rcases hkm.eq_or_lt with rfl | hkm'
    · simpa using sharpTwoBlock_self_squared_moment M k
        (triadicCubeShift Q) hS.1 hdelta1 hs hs1 hxiE
    · exact sharpTwoBlock_squared_moment_of_ordering M hkm'
        (triadicCubeShift Q) hS.1 hdelta1 hs hs1 hxiE
        (horder M m k hkm')
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega => ENNReal.ofReal
    (sharpTwoBlockSuffixRepresentative M m k (triadicCubeShift Q) omega ^ 2)
  let D := normalizedDefect M k (Ch02.cubeDomain Q)
  have hXmeas : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Ioi k))
      inferInstance X := by
    dsimp only [X]
    exact ((measurable_sharpTwoBlockSuffixRepresentative M hkm (triadicCubeShift Q)).pow_const 2).ennreal_ofReal
  have hDmeas : @Measurable _ _ (potentialShellIndexSigma (d := d) (Set.Iic k))
      inferInstance D :=
    measurable_normalizedDefect_potentialShellIndexSigma_Iic M k
      (Ch02.cubeDomain Q)
  have hEach : ∀ L : {L : ℕ // m ≤ L}, ∀ᵐ omega ∂M.P.toMeasure,
      ENNReal.ofReal
          (responseLocalizationError M L.1 k (Ch02.cubeDomain Q)
            (tailCoefficientCubeAverage M L.1 m omega) omega ^ 2) ≤ X omega := by
    intro L
    simpa only [X] using sharpTwoBlock_dominates_localization M hkm L.2 Q hQ
  have hpoint : ∀ᵐ omega ∂M.P.toMeasure,
      positiveScaleResponseObservable M m Q omega ≤
        2 * D omega + 3 * X omega * (D omega + 1) := by
    filter_upwards [ae_all_iff.2 hEach] with omega hall
    unfold positiveScaleResponseObservable
    apply iSup_le
    intro L
    have hloc := paperScalarProbeMaxOn_cutoff_le_localized M L.1 k
      (Ch02.cubeDomain Q) (tailCoefficientCubeAverage M L.1 m omega)
      (tailCoefficientCubeAverage_pos M L.1 m omega) omega
    calc
      paperScalarProbeMaxOn (Ch02.cubeDomain Q)
          (aCutoffCoeffOnData M L.1 omega (Ch02.cubeDomain Q)).toCoeffOn
          (tailCoefficientCubeAverage M L.1 m omega) ≤
        2 * D omega + 3 * ENNReal.ofReal
          (responseLocalizationError M L.1 k (Ch02.cubeDomain Q)
            (tailCoefficientCubeAverage M L.1 m omega) omega ^ 2) *
              (D omega + 1) := hloc
      _ ≤ 2 * D omega + 3 * X omega * (D omega + 1) := by
        gcongr
        exact hall L
  have hraw := paperENNRealLpNorm_localized_prefix_suffix M k hS.1 hDmeas hXmeas hpoint
  have hQscale : Q.scale = (k : ℤ) := scale_eq_of_mem_descendantsAtScale hQ
  have hDbound : paperENNRealLpNorm M.P.toMeasure xi D ≤ ENNReal.ofReal delta1 :=
    inductionHypothesis_normalizedDefect_cube M hS hk0 Q hQscale
  have hXbound : paperENNRealLpNorm M.P.toMeasure xi X ≤
      ENNReal.ofReal (sharpTwoBlockMomentConst d * delta1 *
        (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))) := by
    simpa only [X] using hXnorm
  have hbound : paperENNRealLpNorm M.P.toMeasure xi
      (positiveScaleResponseObservable M m Q) ≤
      2 * ENNReal.ofReal delta1 +
        3 * ENNReal.ofReal (sharpTwoBlockMomentConst d * delta1 *
          (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))) *
          (ENNReal.ofReal delta1 + 1) := by
    refine hraw.trans ?_
    gcongr
  refine hbound.trans ?_
  have hdelta0 : 0 ≤ delta1 := hdelta.trans' (sq_nonneg M.delta)
  have hR : 1 ≤ (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hs.le (by positivity))
  have hreal : 2 * delta1 +
      3 * (sharpTwoBlockMomentConst d * delta1 *
        (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))) * (delta1 + 1) ≤
      C * delta1 * (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ)) := by
    have hC0 : 0 ≤ sharpTwoBlockMomentConst d :=
      zero_le_one.trans (one_le_sharpTwoBlockMomentConst d)
    have hd1 : delta1 + 1 ≤ 2 := by linarith
    have hfirst := mul_le_mul_of_nonneg_left hR
      (show 0 ≤ 2 * delta1 by positivity)
    have hsecond := mul_le_mul_of_nonneg_left hd1
      (show 0 ≤ 3 * (sharpTwoBlockMomentConst d * delta1 *
        (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))) by positivity)
    dsimp only [C]
    nlinarith
  have hrewrite :
      2 * ENNReal.ofReal delta1 +
          3 * ENNReal.ofReal (sharpTwoBlockMomentConst d * delta1 *
            (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))) *
            (ENNReal.ofReal delta1 + 1) =
        ENNReal.ofReal (2 * delta1 +
          3 * (sharpTwoBlockMomentConst d * delta1 *
            (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ))) * (delta1 + 1)) := by
    have hterm0 : 0 ≤ sharpTwoBlockMomentConst d * delta1 *
        (3 : ℝ) ^ (s * ((m - k : ℕ) : ℝ)) :=
      mul_nonneg (mul_nonneg
        (zero_le_one.trans (one_le_sharpTwoBlockMomentConst d)) hdelta0)
        (Real.rpow_nonneg (by norm_num) _)
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hdelta0)
        (mul_nonneg (mul_nonneg (by norm_num) hterm0)
          (add_nonneg hdelta0 zero_le_one)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (mul_nonneg (by norm_num) hterm0),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ENNReal.ofReal_add hdelta0 zero_le_one]
    norm_num
  rw [hrewrite]
  exact ENNReal.ofReal_le_ofReal hreal

end


end SubdiffusiveProcess.CoarseGrainingVocab
