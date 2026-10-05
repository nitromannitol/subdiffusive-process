module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.DiscountedGrowth

@[expose] public section

/-!
# Section 6 localization: collapsing the combined coefficient ratios

This module formalizes the algebraic collapse immediately after
`e.combined.coefficient.ratio.reg` in Step 2 of
`p.good.scale.mathcal.E` (`e.combined.coefficient.ratio.reg` and `p.good.scale.mathcal.E`).  The long tail ratio,
the finite shell block, and the deterministic normalizer error remain separate
inputs until the last estimate.

First isolate the scalar exponential-product estimate, then read it at the
model carriers.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open MeasureTheory Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

private theorem shellBlock_continuous (m n : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Continuous (shellBlock m n omega) := by
  unfold shellBlock
  fun_prop

private theorem bddAbove_abs_values_cube {m : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ cube d m, a = |f x|} := by
  let Q := originCube d (m : ℤ)
  obtain ⟨K, hK⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 K, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hK x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using!
    h.trans (le_max_right _ _)

/-- Point evaluation is bounded by the real supremum norm on a centered cube
for continuous functions. -/
theorem abs_apply_le_supNormOn_cube_of_continuous
    {m : ℕ} {f : Vec d → ℝ} (hf : Continuous f)
    {x : Vec d} (hx : x ∈ cube d m) :
    |f x| ≤ supNormOn (cube d m) f := by
  unfold supNormOn
  exact le_csSup (bddAbove_abs_values_cube hf) ⟨x, hx, rfl⟩

/-- A uniform pointwise deviation bounds the real `L^∞` ratio error against
the constant coefficient one. -/
theorem scalarRatioLInf_one_le_of_forall_bound
    {U : Ch02.Domain d} {a : Vec d → ℝ} {W : ℝ}
    (hW0 : 0 ≤ W) (h : ∀ x ∈ (U : Set (Vec d)), |a x - 1| ≤ W) :
    scalarRatioLInf U a (fun _ => 1) ≤ W := by
  unfold scalarRatioLInf
  rw [SubdiffusiveProcess.RawLp.eLpNorm_top_exponent]
  have hae : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      |a x / 1 - 1| ≤ W := by
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    simpa only [div_one] using! h x hx
  have hess : eLpNormEssSup (fun x => a x / 1 - 1)
      (volumeMeasureOn (U : Set (Vec d))) ≤ ENNReal.ofReal W :=
    eLpNormEssSup_le_of_ae_bound
      (by simpa only [Real.norm_eq_abs] using! hae)
  calc
    (eLpNormEssSup (fun x => a x / 1 - 1)
        (volumeMeasureOn (U : Set (Vec d)))).toReal ≤
        (ENNReal.ofReal W).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    _ = W := ENNReal.toReal_ofReal hW0

/-- The global mean-value estimate for the real exponential, with no smallness
assumption on its argument. -/
private theorem abs_exp_sub_one_le_abs_mul_exp_abs (r : ℝ) :
    |Real.exp r - 1| ≤ |r| * Real.exp |r| := by
  rcases le_or_gt 0 r with hr | hr
  · rw [abs_of_nonneg hr, abs_of_nonneg
      (sub_nonneg.mpr (Real.one_le_exp hr))]
    have hneg := Real.add_one_le_exp (-r)
    have hmul := mul_le_mul_of_nonneg_left hneg (Real.exp_pos r).le
    rw [Real.exp_neg, mul_add, mul_one,
      mul_inv_cancel₀ (Real.exp_ne_zero r)] at hmul
    nlinarith
  · have hr' : r ≤ 0 := hr.le
    rw [abs_of_neg hr, abs_of_nonpos
      (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hr'))]
    have hlin := Real.add_one_le_exp r
    have hexp : 1 ≤ Real.exp (-r) := Real.one_le_exp (by linarith)
    nlinarith

/-- Linear regime of the three-factor collapse. -/
private theorem abs_mul_exp_add_sub_one_le_linear
    {A g r D G R Eg Er : ℝ}
    (hD0 : 0 ≤ D) (hG0 : 0 ≤ G) (hR0 : 0 ≤ R)
    (hA : |A - 1| ≤ D) (hg : |g| ≤ G) (hr : |r| ≤ R)
    (hEg : Real.exp G ≤ Eg) (hEr : Real.exp R ≤ Er) :
    |A * Real.exp (g + r) - 1| ≤ (D + G + R) * (Eg * Er) := by
  have hEg0 : 0 ≤ Eg := (Real.exp_pos G).le.trans hEg
  have hEr0 : 0 ≤ Er := (Real.exp_pos R).le.trans hEr
  have hu : |g + r| ≤ G + R :=
    (abs_add_le g r).trans (add_le_add hg hr)
  have hexpAbs : Real.exp |g + r| ≤ Eg * Er := by
    calc
      Real.exp |g + r| ≤ Real.exp (G + R) := Real.exp_le_exp.mpr hu
      _ = Real.exp G * Real.exp R := Real.exp_add G R
      _ ≤ Eg * Er := mul_le_mul hEg hEr (Real.exp_pos R).le hEg0
  have hexp : Real.exp (g + r) ≤ Eg * Er :=
    (Real.exp_le_exp.mpr (le_abs_self (g + r))).trans hexpAbs
  have hfirst : |A - 1| * Real.exp (g + r) ≤ D * (Eg * Er) :=
    mul_le_mul hA hexp (Real.exp_pos _).le hD0
  have hsecond : |Real.exp (g + r) - 1| ≤ (G + R) * (Eg * Er) := by
    calc
      |Real.exp (g + r) - 1| ≤
          |g + r| * Real.exp |g + r| :=
        abs_exp_sub_one_le_abs_mul_exp_abs (g + r)
      _ ≤ (G + R) * (Eg * Er) :=
        mul_le_mul hu hexpAbs (Real.exp_pos _).le (add_nonneg hG0 hR0)
  calc
    |A * Real.exp (g + r) - 1| =
        |(A - 1) * Real.exp (g + r) + (Real.exp (g + r) - 1)| := by
      congr 1
      ring
    _ ≤ |A - 1| * Real.exp (g + r) +
        |Real.exp (g + r) - 1| := by
      simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using!
        abs_add_le ((A - 1) * Real.exp (g + r)) (Real.exp (g + r) - 1)
    _ ≤ D * (Eg * Er) + (G + R) * (Eg * Er) :=
      add_le_add hfirst hsecond
    _ = (D + G + R) * (Eg * Er) := by ring

/-- Saturated regime of the same collapse. -/
private theorem abs_mul_exp_add_sub_one_le_saturated
    {A g r D G R Eg Er : ℝ}
    (hD0 : 0 ≤ D) (hG0 : 0 ≤ G) (hR0 : 0 ≤ R)
    (hA : |A - 1| ≤ D) (hg : |g| ≤ G) (hr : |r| ≤ R)
    (hEg : Real.exp G ≤ Eg) (hEr : Real.exp R ≤ Er) :
    |A * Real.exp (g + r) - 1| ≤ (D + 2) * (Eg * Er) := by
  have hEg1 : 1 ≤ Eg := (Real.one_le_exp hG0).trans hEg
  have hEr1 : 1 ≤ Er := (Real.one_le_exp hR0).trans hEr
  have hW1 : 1 ≤ Eg * Er := one_le_mul_of_one_le_of_one_le hEg1 hEr1
  have hu : |g + r| ≤ G + R :=
    (abs_add_le g r).trans (add_le_add hg hr)
  have hexp : Real.exp (g + r) ≤ Eg * Er := by
    calc
      Real.exp (g + r) ≤ Real.exp |g + r| :=
        Real.exp_le_exp.mpr (le_abs_self _)
      _ ≤ Real.exp (G + R) := Real.exp_le_exp.mpr hu
      _ = Real.exp G * Real.exp R := Real.exp_add G R
      _ ≤ Eg * Er := mul_le_mul hEg hEr (Real.exp_pos R).le
        (zero_le_one.trans hEg1)
  have hAabs : |A| ≤ D + 1 := by
    calc
      |A| = |(A - 1) + 1| := by congr 1; ring
      _ ≤ |A - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ D + 1 := by simpa only [abs_one] using! add_le_add hA le_rfl
  calc
    |A * Real.exp (g + r) - 1| ≤
        |A * Real.exp (g + r)| + |(1 : ℝ)| := abs_sub _ _
    _ = |A| * Real.exp (g + r) + 1 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_one]
    _ ≤ (D + 1) * (Eg * Er) + 1 := by
      exact add_le_add (mul_le_mul hAabs hexp (Real.exp_pos _).le
        (by linarith only [hD0])) le_rfl
    _ ≤ (D + 1) * (Eg * Er) + (Eg * Er) :=
      add_le_add le_rfl hW1
    _ = (D + 2) * (Eg * Er) := by ring

/-- Linear and saturated regimes combined in the manuscript's `min {1,·}`
form. -/
theorem abs_mul_exp_add_sub_one_le_weighted_min
    {A g r S G R C Eg Er : ℝ}
    (hC0 : 0 ≤ C) (hS0 : 0 ≤ S) (hG0 : 0 ≤ G) (hR0 : 0 ≤ R)
    (hA : |A - 1| ≤ C * min 1 S)
    (hg : |g| ≤ G) (hr : |r| ≤ R)
    (hEg : Real.exp G ≤ Eg) (hEr : Real.exp R ≤ Er) :
    |A * Real.exp (g + r) - 1| ≤
      (C + 2) * (Eg * Er) * min 1 (S + G + R) := by
  let D := C * min 1 S
  have hminS0 : 0 ≤ min 1 S := le_min zero_le_one hS0
  have hD0 : 0 ≤ D := mul_nonneg hC0 hminS0
  have hW0 : 0 ≤ Eg * Er := mul_nonneg
    ((Real.exp_pos G).le.trans hEg) ((Real.exp_pos R).le.trans hEr)
  have hlin := abs_mul_exp_add_sub_one_le_linear hD0 hG0 hR0 hA hg hr hEg hEr
  have hsat := abs_mul_exp_add_sub_one_le_saturated hD0 hG0 hR0 hA hg hr hEg hEr
  by_cases hsmall : S + G + R ≤ 1
  · rw [min_eq_right hsmall]
    have hDle : D ≤ C * S :=
      mul_le_mul_of_nonneg_left (min_le_right 1 S) hC0
    have hcoef : D + G + R ≤ (C + 2) * (S + G + R) := by
      calc
        D + G + R ≤ C * S + G + R := by linarith only [hDle]
        _ ≤ (C + 2) * (S + G + R) := by
          have hCG : 0 ≤ C * G := mul_nonneg hC0 hG0
          have hCR : 0 ≤ C * R := mul_nonneg hC0 hR0
          nlinarith only [hS0, hG0, hR0, hCG, hCR]
    exact hlin.trans <| by
      calc
        (D + G + R) * (Eg * Er) ≤
            ((C + 2) * (S + G + R)) * (Eg * Er) :=
          mul_le_mul_of_nonneg_right hcoef hW0
        _ = (C + 2) * (Eg * Er) * (S + G + R) := by ring
  · have hlarge : 1 ≤ S + G + R := le_of_not_ge hsmall
    rw [min_eq_left hlarge]
    have hDle : D ≤ C := by
      dsimp only [D]
      simpa only [mul_one] using!
        mul_le_mul_of_nonneg_left (min_le_left 1 S) hC0
    exact hsat.trans <| by
      simpa only [mul_one] using!
        mul_le_mul_of_nonneg_right (by linarith only [hDle]) hW0

/-- Two-sided form used for the forward and reciprocal coefficient ratios. -/
theorem combined_ratio_deviation_sum_le_weighted_min
    {A Ainv g r S G R C Eg Er : ℝ}
    (hC0 : 0 ≤ C) (hS0 : 0 ≤ S) (hG0 : 0 ≤ G) (hR0 : 0 ≤ R)
    (hA : |A - 1| ≤ C * min 1 S)
    (hAinv : |Ainv - 1| ≤ C * min 1 S)
    (hg : |g| ≤ G) (hr : |r| ≤ R)
    (hEg : Real.exp G ≤ Eg) (hEr : Real.exp R ≤ Er) :
    |A * Real.exp (g + r) - 1| +
        |Real.exp (-(g + r)) * Ainv - 1| ≤
      2 * (C + 2) * (Eg * Er) * min 1 (S + G + R) := by
  have hforward := abs_mul_exp_add_sub_one_le_weighted_min
    hC0 hS0 hG0 hR0 hA hg hr hEg hEr
  have hreverseRaw := abs_mul_exp_add_sub_one_le_weighted_min
    (A := Ainv) (g := -g) (r := -r) hC0 hS0 hG0 hR0 hAinv
      (by simpa only [abs_neg] using! hg) (by simpa only [abs_neg] using! hr) hEg hEr
  have hreverse : |Real.exp (-(g + r)) * Ainv - 1| ≤
      (C + 2) * (Eg * Er) * min 1 (S + G + R) := by
    rw [show -g + -r = -(g + r) by ring] at hreverseRaw
    rw [mul_comm Ainv (Real.exp (-(g + r)))] at hreverseRaw
    exact hreverseRaw
  calc
    |A * Real.exp (g + r) - 1| +
        |Real.exp (-(g + r)) * Ainv - 1| ≤
      (C + 2) * (Eg * Er) * min 1 (S + G + R) +
        (C + 2) * (Eg * Er) * min 1 (S + G + R) :=
      add_le_add hforward hreverse
    _ = 2 * (C + 2) * (Eg * Er) * min 1 (S + G + R) := by ring

/-- Pointwise reading of the two long-ratio orientations.  This avoids a
second `sSup` read: the continuous tail coefficient is compared directly with
its cube average at the selected point. -/
theorem tailCoefficient_average_ratio_bounds_le_constant_mul_min_of_goodFieldOne
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hs : s ≤ 1 / 2) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) {y : Vec d}
    (hy : y ∈ cube d m) :
    |tailCoefficient M L m omega y /
          tailCoefficientCubeAverage M L m omega - 1| ≤
        longRatioGoodEventConstant d * min 1 (longRatioGradientTail m omega) ∧
      |tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m omega y - 1| ≤
        longRatioGoodEventConstant d * min 1 (longRatioGradientTail m omega) := by
  let S := longRatioGradientTail m omega
  let E := Real.exp (3 * (d : ℝ))
  have hsum :=
    summable_longRatioGradientTail_of_goodFieldOne m hepsilon hs omega hgood
  obtain ⟨hreverse, hforward⟩ :=
    tailCoefficient_average_ratio_bounds M hmL omega hsum hy
  have hS0 : 0 ≤ S := longRatioGradientTail_nonneg m omega
  have hS3 : S ≤ 3 :=
    (longRatioGradientTail_le_three_mul_of_goodFieldOne
      m hepsilon hs omega hgood).trans (by nlinarith only [hepsilon1])
  have hexp : Real.exp ((d : ℝ) * S) ≤ E := by
    apply Real.exp_le_exp.mpr
    simpa only [mul_comm] using!
      mul_le_mul_of_nonneg_left hS3 (Nat.cast_nonneg d)
  have hdE0 : 0 ≤ (d : ℝ) * E :=
    mul_nonneg (Nat.cast_nonneg d) (Real.exp_pos _).le
  have hrough :
      ((d : ℝ) * S) * Real.exp ((d : ℝ) * S) ≤
        ((d : ℝ) * E) * S := by
    calc
      ((d : ℝ) * S) * Real.exp ((d : ℝ) * S) ≤
          ((d : ℝ) * S) * E :=
        mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (Nat.cast_nonneg d) hS0)
      _ = ((d : ℝ) * E) * S := by ring
  have hcore : ((d : ℝ) * E) * S ≤
      (6 * (d : ℝ) * E) * min 1 S := by
    by_cases hS1 : S ≤ 1
    · rw [min_eq_right hS1]
      nlinarith only [hS0, hdE0]
    · have h1S : 1 ≤ S := le_of_not_ge hS1
      rw [min_eq_left h1S]
      simpa only [mul_one] using! (show ((d : ℝ) * E) * S ≤ 6 * (d : ℝ) * E by
        calc
          ((d : ℝ) * E) * S ≤ ((d : ℝ) * E) * 3 :=
            mul_le_mul_of_nonneg_left hS3 hdE0
          _ ≤ 6 * (d : ℝ) * E := by nlinarith only [hdE0])
  have henlarge : (6 * (d : ℝ) * E) * min 1 S ≤
      longRatioGoodEventConstant d * min 1 S := by
    exact mul_le_mul_of_nonneg_right
      (le_max_right 3 (6 * (d : ℝ) * E)) (le_min zero_le_one hS0)
  constructor
  · exact hforward.trans (hrough.trans (hcore.trans henlarge))
  · exact hreverse.trans (hrough.trans (hcore.trans henlarge))

/-- Explicit dimension-only constant for the two-sided combined-ratio
collapse. -/
def ratioCollapseConstant (d : ℕ) : ℝ :=
  12 * (longRatioGoodEventConstant d + 2)

theorem ratioCollapseConstant_pos (d : ℕ) :
    0 < ratioCollapseConstant d := by
  unfold ratioCollapseConstant
  have h := longRatioGoodEventConstant_pos d
  nlinarith

/-- The manuscript's two-sided combined-ratio collapse at a selected point of
a translated local cube.  The `BddAbove` hypothesis is exactly the honest
guard required to read `GoodFieldTwo`'s real `sSup`. -/
theorem combinedCoefficientRatio_deviation_sum_le_of_goodEvent
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {z x : Vec d}
    (hz : z ∈ cube d m) (hx : x ∈ cube d n) (hy : x + z ∈ cube d m)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    (hBdd : BddAbove {a : ℝ | ∃ y ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i y|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i y - omega i 0|) else 1|}) :
    |combinedCoefficientRatio M L m n omega z x - 1| +
        |combinedCoefficientRatioInv M L m n omega z x - 1| ≤
      ratioCollapseConstant d *
        (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
        min 1 (longRatioGradientTail m omega +
          |shellBlock m n (translatePotentialSample z omega) x| +
          _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) := by
  let S := longRatioGradientTail m omega
  let g := shellBlock m n (translatePotentialSample z omega) x
  let r := normalizerLogError M m n
  let T : ℝ := ((m - n : ℕ) : ℝ)
  let C := longRatioGoodEventConstant d
  let Eg := 6 * (3 : ℝ) ^ ((s * T) / 8)
  let Er := (3 : ℝ) ^ ((s * T) / 16)
  have htail :=
    tailCoefficient_average_ratio_bounds_le_constant_mul_min_of_goodFieldOne
      M hmL zero_le_one le_rfl hsUpper omega hgood.1 hy
  have hforward :
      |tailCoefficient M L m (translatePotentialSample z omega) x /
          tailCoefficientCubeAverage M L m omega - 1| ≤ C * min 1 S := by
    rw [tailCoefficient_translatePotentialSample M L m omega z x]
    exact htail.1
  have hreverse :
      |tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m (translatePotentialSample z omega) x - 1| ≤
        C * min 1 S := by
    rw [tailCoefficient_translatePotentialSample M L m omega z x]
    exact htail.2
  have hxtranslated : x + z ∈ translatedCube d (n : ℤ) z := by
    refine ⟨x, hx, ?_⟩
    exact add_comm z x
  have hfieldRaw := exp_abs_shellBlock_le_of_goodFieldTwo
    hnm omega hz hgood.2.1 hBdd (x + z) hxtranslated
  have hEg : Real.exp |g| ≤ Eg := by
    dsimp only [g, Eg, T]
    rw [shellBlock_translatePotentialSample m n omega z x]
    exact hfieldRaw
  have hEr : Real.exp |r| ≤ Er :=
    exp_abs_normalizerLogError_le_three_rpow M hnm hsLower
  have hrho : |r| ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P * T :=
    abs_normalizerLogError_le_of_le M hnm
  have hraw := combined_ratio_deviation_sum_le_weighted_min
    (A := tailCoefficient M L m (translatePotentialSample z omega) x /
      tailCoefficientCubeAverage M L m omega)
    (Ainv := tailCoefficientCubeAverage M L m omega /
      tailCoefficient M L m (translatePotentialSample z omega) x)
    (g := g) (r := r) (S := S) (G := |g|) (R := |r|)
    (C := C) (Eg := Eg) (Er := Er)
    (longRatioGoodEventConstant_pos d).le
    (longRatioGradientTail_nonneg m omega) (abs_nonneg g) (abs_nonneg r)
    hforward hreverse le_rfl le_rfl hEg hEr
  have hmin : min 1 (S + |g| + |r|) ≤
      min 1 (S + |g| + _root_.SubdiffusiveProcess.Model.tauSq M.P * T) := by
    apply min_le_min le_rfl
    linarith only [hrho]
  have hfactor0 : 0 ≤ 2 * (C + 2) * (Eg * Er) := by
    dsimp only [C, Eg, Er]
    have hC := longRatioGoodEventConstant_pos d
    positivity
  have henlarged := hraw.trans
    (mul_le_mul_of_nonneg_left hmin hfactor0)
  have hpower : Eg * Er =
      6 * (3 : ℝ) ^ ((3 * s * T) / 16) := by
    dsimp only [Eg, Er]
    rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 2
    ring
  dsimp only [combinedCoefficientRatio, combinedCoefficientRatioInv] at henlarged ⊢
  rw [hpower] at henlarged
  dsimp only [ratioCollapseConstant, C, S, g, r, T] at henlarged ⊢
  convert henlarged using 1
  all_goals ring_nf

/-- Uniform local-cube version of the pointwise collapse.  The shell atom is
enlarged to the literal `supNormOn` carrier used by the annular assembly. -/
theorem combinedCoefficientRatio_deviation_sum_le_supNorm_of_goodEvent
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) {z x : Vec d}
    (hz : z ∈ cube d m) (hx : x ∈ cube d n) (hy : x + z ∈ cube d m)
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    (hBdd : BddAbove {a : ℝ | ∃ y ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i y|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i y - omega i 0|) else 1|}) :
    |combinedCoefficientRatio M L m n omega z x - 1| +
        |combinedCoefficientRatioInv M L m n omega z x - 1| ≤
      ratioCollapseConstant d *
        (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
        min 1 (longRatioGradientTail m omega +
          supNormOn (cube d n)
            (shellBlock m n (translatePotentialSample z omega)) +
          _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) := by
  have hpoint := combinedCoefficientRatio_deviation_sum_le_of_goodEvent
    M hnm hmL hsLower hsUpper omega hz hx hy hgood hBdd
  have hshell :
      |shellBlock m n (translatePotentialSample z omega) x| ≤
        supNormOn (cube d n)
          (shellBlock m n (translatePotentialSample z omega)) :=
    abs_apply_le_supNormOn_cube_of_continuous
      (shellBlock_continuous m n (translatePotentialSample z omega)) hx
  have hmin :
      min 1 (longRatioGradientTail m omega +
          |shellBlock m n (translatePotentialSample z omega) x| +
          _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) ≤
        min 1 (longRatioGradientTail m omega +
          supNormOn (cube d n)
            (shellBlock m n (translatePotentialSample z omega)) +
          _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) := by
    apply min_le_min le_rfl
    linarith only [hshell]
  exact hpoint.trans (mul_le_mul_of_nonneg_left hmin (by
    exact mul_nonneg (ratioCollapseConstant_pos d).le
      (Real.rpow_nonneg (by norm_num) _)))

/-- The actual two-squared-`L^∞` sensitivity error on a descendant cube.
This is the ratio-error carrier entering `responseJ_sensitivity`. -/
theorem cutoffRatioError_tailAverage_le_of_goodEvent_descendant
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m n : ℕ}
    (hnm : n ≤ m) (hmL : m ≤ L) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d (m : ℤ)) (n : ℤ))
    (hgood : omega ∈ goodEvent M none m 0 1 s)
    (hBdd : BddAbove {a : ℝ | ∃ y ∈
      translatedCube d ((m + 1 + (m - n) : ℕ) : ℤ) 0,
        a = |(∏ i ∈ Finset.Icc (m - (m - n)) (m + (m - n)),
            Real.exp |omega i y|) +
          ∏' i : ℕ, if m + (m - n) ≤ i then
            Real.exp (4 * |omega i y - omega i 0|) else 1|}) :
    cutoffRatioError M n L
        (translatePotentialSample (triadicCubeShift R) omega)
        (Ch02.cubeDomain (originCube d (n : ℤ)))
        (tailCoefficientCubeAverage M L m omega) ≤
      2 * (ratioCollapseConstant d *
        (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
        min 1 (longRatioGradientTail m omega +
          supNormOn (cube d n)
            (shellBlock m n
              (translatePotentialSample (triadicCubeShift R) omega)) +
          _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ))) ^ 2 := by
  let z := triadicCubeShift R
  let U := Ch02.cubeDomain (originCube d (n : ℤ))
  let W := ratioCollapseConstant d *
    (3 : ℝ) ^ ((3 * s * ((m - n : ℕ) : ℝ)) / 16) *
    min 1 (longRatioGradientTail m omega +
      supNormOn (cube d n) (shellBlock m n (translatePotentialSample z omega)) +
      _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ))
  have hz : z ∈ cube d m :=
    triadicCubeShift_mem_cube_of_mem_descendantsAtScale
      (by simpa using! (show (n : ℤ) ≤ (m : ℤ) by exact_mod_cast hnm)) hR
  have hpoint : ∀ x ∈ cube d n,
      |combinedCoefficientRatio M L m n omega z x - 1| +
          |combinedCoefficientRatioInv M L m n omega z x - 1| ≤ W := by
    intro x hx
    have hRscale : R.scale = (n : ℤ) :=
      scale_eq_of_mem_descendantsAtScale hR
    have hxR : z + x ∈ openCubeSet R := by
      rw [openCubeSet_eq_translateSet_originCube_of_triadicCube,
        mem_translateSet_iff_sub_mem]
      simpa only [z, hRscale, add_sub_cancel_left] using! hx
    have hy : x + z ∈ cube d m := by
      rw [add_comm]
      exact openCubeSet_subset_of_mem_descendantsAtScale
        (scale_le_of_mem_descendantsAtScale hR) hR hxR
    exact combinedCoefficientRatio_deviation_sum_le_supNorm_of_goodEvent
      M hnm hmL hsLower hsUpper omega hz hx hy hgood hBdd
  have hzero : (0 : Vec d) ∈ cube d n := by
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
    constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  have hW0 : 0 ≤ W :=
    (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hpoint 0 hzero)
  have hforwardPoint : ∀ x ∈ (U : Set (Vec d)),
      |combinedCoefficientRatio M L m n omega z x - 1| ≤ W := by
    intro x hx
    have h := hpoint x (by simpa only [U, Ch02.cubeDomain_coe] using! hx)
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans h
  have hreversePoint : ∀ x ∈ (U : Set (Vec d)),
      |combinedCoefficientRatioInv M L m n omega z x - 1| ≤ W := by
    intro x hx
    have h := hpoint x (by simpa only [U, Ch02.cubeDomain_coe] using! hx)
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans h
  have hforward := scalarRatioLInf_one_le_of_forall_bound hW0 hforwardPoint
  have hreverse := scalarRatioLInf_one_le_of_forall_bound hW0 hreversePoint
  rw [cutoffRatioError_tailAverage_eq_combined M hnm hmL omega z U]
  have hforward0 : 0 ≤ scalarRatioLInf U
      (combinedCoefficientRatio M L m n omega z) (fun _ => 1) :=
    scalarRatioLInf_nonneg _ _ _
  have hreverse0 : 0 ≤ scalarRatioLInf U
      (combinedCoefficientRatioInv M L m n omega z) (fun _ => 1) :=
    scalarRatioLInf_nonneg _ _ _
  have hforwardSq := mul_self_le_mul_self hforward0 hforward
  have hreverseSq := mul_self_le_mul_self hreverse0 hreverse
  dsimp only [W, z, U] at hforwardSq hreverseSq ⊢
  nlinarith only [hforwardSq, hreverseSq]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
