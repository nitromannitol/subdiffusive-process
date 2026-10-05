module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.SubunitTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6GoodScale

@[expose] public section

/-!
# Coarse-graining on good scales

This module assembles the frozen `p.good.scale.mathcal.E`
 from the two proved
lanes.

* **Step 1**  is
  `SubdiffusiveProcess.CoarseGrainingVocab.section6HomogenizationError_le_annularSupTwo`: the
  frozen `q = 2` error is bounded by the square root of `192` times the
  refined annular supremum of the local probes.
* **Step 2**  is the localization stack
  `SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.annularSupTwo_le_goodScaleBudget`:
  on the frozen good event the annular supremum is bounded by the sum of the
  positive-scale budget (sensitivity, long ratio, discounted shell growth,
  deterministic drift) and the subunit budget (`e.direct.J.bound.subunit`).

Only the final square-root arithmetic and the `e.what.e.good.gj.gives` event
readings for the shell and full-block slots are performed here.  The five
display slots are the literal terms of the frozen right side, and the single
constant serves both frozen clauses.

The proof-role split mirrors
`Algsuperdiff/Section4/Provider/Annular/FinalStitch.lean`: the analytic lanes
end in named slots, and the provider only stitches them.
-/

namespace SubdiffusiveProcess.Providers.Section6

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Nonnegativity of the display slots -/

private theorem supNormOn_nonneg (W : Set (Vec d))
    (f : Vec d → ℝ) : 0 ≤ supNormOn W f := by
  refine Real.sSup_nonneg ?_
  rintro a ⟨x, _, rfl⟩
  exact abs_nonneg _

private theorem goodScaleResponseSlot_nonneg
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (s : ℝ) (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ goodScaleResponseSlot M s m omega := by
  refine Real.sSup_nonneg ?_
  rintro a ⟨j, n, -, -, z, -, -, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)

private theorem goodScaleShellSlot_nonneg (s : ℝ) (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ goodScaleShellSlot s m omega := by
  refine Real.sSup_nonneg ?_
  rintro a ⟨j, -, rfl⟩
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (supNormOn_nonneg _ _)

private theorem goodScaleFullSlot_nonneg (s : ℝ) (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ goodScaleFullSlot s m omega :=
  mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (supNormOn_nonneg _ _)

private theorem goodScaleGradientSlot_nonneg (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ goodScaleGradientSlot m omega := by
  rw [goodScaleGradientSlot_eq_longRatioGradientTail]
  exact longRatioGradientTail_nonneg m omega

/-! ### The base constant -/

/-- The square of the base constant produced by the two budgets. -/
def goodScaleSquareConstant (d : ℕ) : ℝ :=
  384 + 13824 * ratioCollapseConstant d ^ 2 +
    373248 * subunitCollapseConstant d ^ 2

private theorem goodScaleSquareConstant_ge (d : ℕ) :
    384 ≤ goodScaleSquareConstant d := by
  unfold goodScaleSquareConstant
  nlinarith [sq_nonneg (ratioCollapseConstant d),
    sq_nonneg (subunitCollapseConstant d)]

/-- The base constant of the display. -/
def goodScaleBaseConstant (d : ℕ) : ℝ :=
  Real.sqrt (goodScaleSquareConstant d)

private theorem goodScaleBaseConstant_pos (d : ℕ) :
    0 < goodScaleBaseConstant d := by
  have := goodScaleSquareConstant_ge d
  exact Real.sqrt_pos.2 (by linarith)

/-! ### The core estimate on the good event -/

private theorem error_le_base
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {s : ℝ}
    (hsLower : 64 * M.delta ^ 2 ≤ s) (hsUpper : s ≤ 1 / 2)
    {L m : ℕ} (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : omega ∈ goodEvent M none m 0 1 s) :
    section6HomogenizationError M s L m omega 0 ≤
      goodScaleBaseConstant d *
        (goodScaleResponseSlot M s m omega + s⁻¹ * M.delta ^ 2 +
          goodScaleShellSlot s m omega + goodScaleFullSlot s m omega +
          goodScaleGradientSlot m omega) := by
  have hdim : 2 ≤ d := M.shellPrefix.dimension
  have : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  set A : ℝ := goodScaleResponseSlot M s m omega with hAdef
  set D : ℝ := s⁻¹ * M.delta ^ 2 with hDdef
  set Bs : ℝ := goodScaleShellSlot s m omega with hBsdef
  set Bf : ℝ := goodScaleFullSlot s m omega with hBfdef
  set Bg : ℝ := goodScaleGradientSlot m omega with hBgdef
  have hA0 : 0 ≤ A := goodScaleResponseSlot_nonneg M s m omega
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact mul_nonneg (inv_nonneg.2 hs0.le) (sq_nonneg _)
  have hBs0 : 0 ≤ Bs := goodScaleShellSlot_nonneg s m omega
  have hBf0 : 0 ≤ Bf := goodScaleFullSlot_nonneg s m omega
  have hBg0 : 0 ≤ Bg := goodScaleGradientSlot_nonneg m omega
  set Sigma : ℝ := A + D + Bs + Bf + Bg with hSigmadef
  have hSigma0 : 0 ≤ Sigma := by rw [hSigmadef]; linarith
  set B : ℝ := goodScalePositiveBudget M s m omega +
    goodScaleSubunitBudget M s m omega with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h1 := goodScalePositiveBudget_nonneg M s m omega
    have h2 := goodScaleSubunitBudget_nonneg M s m omega
    linarith
  -- Step 1 and Step 2
  have hstep1 := section6HomogenizationError_le_annularSupTwo hs0 hsUpper hd1
    M L m omega 0
  rw [Section6Covariance.translatePotentialSample_zero] at hstep1
  have hstep2 := annularSupTwo_le_goodScaleBudget M hmL hsLower hsUpper omega hgood
  have hmul : (192 : ℝ≥0∞) * annularSupTwo s (m : ℤ)
      (section6LocalProbeMax M L omega 0
        (tailCoefficientCubeAverage M L m omega)) ≤
      ENNReal.ofReal (192 * B) := by
    calc
      (192 : ℝ≥0∞) * annularSupTwo s (m : ℤ)
          (section6LocalProbeMax M L omega 0
            (tailCoefficientCubeAverage M L m omega)) ≤
          (192 : ℝ≥0∞) * ENNReal.ofReal B := by
        rw [hBdef]; gcongr
      _ = ENNReal.ofReal (192 * B) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 192)]
        congr 1
        simp
  have hchain : ENNReal.ofReal (section6HomogenizationError M s L m omega 0) ≤
      ENNReal.ofReal ((192 * B) ^ (1 / 2 : ℝ)) := by
    refine hstep1.trans ?_
    calc
      ((192 : ℝ≥0∞) * annularSupTwo s (m : ℤ)
          (section6LocalProbeMax M L omega 0
            (tailCoefficientCubeAverage M L m omega))) ^ (1 / 2 : ℝ) ≤
          (ENNReal.ofReal (192 * B)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hmul (by norm_num)
      _ = ENNReal.ofReal ((192 * B) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
  have hreal : section6HomogenizationError M s L m omega 0 ≤
      (192 * B) ^ (1 / 2 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
  have hsqrt : (192 * B) ^ (1 / 2 : ℝ) = Real.sqrt (192 * B) :=
    (Real.sqrt_eq_rpow (192 * B)).symm
  rw [hsqrt] at hreal
  refine hreal.trans ?_
  -- the square arithmetic
  have hsq : A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2 ≤ Sigma ^ 2 := by
    rw [hSigmadef]
    nlinarith [mul_nonneg hA0 hD0, mul_nonneg hA0 hBs0, mul_nonneg hA0 hBf0,
      mul_nonneg hA0 hBg0, mul_nonneg hD0 hBs0, mul_nonneg hD0 hBf0,
      mul_nonneg hD0 hBg0, mul_nonneg hBs0 hBf0, mul_nonneg hBs0 hBg0,
      mul_nonneg hBf0 hBg0]
  have hcoef : 192 * B ≤ goodScaleSquareConstant d *
      (A ^ 2 + D ^ 2 + Bs ^ 2 + Bf ^ 2 + Bg ^ 2) := by
    rw [hBdef, goodScalePositiveBudget, goodScaleSubunitBudget,
      goodScaleSquareConstant, ← hAdef, ← hDdef, ← hBsdef, ← hBfdef, ← hBgdef]
    nlinarith [mul_nonneg (sq_nonneg (ratioCollapseConstant d)) (sq_nonneg A),
      mul_nonneg (sq_nonneg (ratioCollapseConstant d)) (sq_nonneg D),
      mul_nonneg (sq_nonneg (ratioCollapseConstant d)) (sq_nonneg Bs),
      mul_nonneg (sq_nonneg (ratioCollapseConstant d)) (sq_nonneg Bf),
      mul_nonneg (sq_nonneg (ratioCollapseConstant d)) (sq_nonneg Bg),
      mul_nonneg (sq_nonneg (subunitCollapseConstant d)) (sq_nonneg A),
      mul_nonneg (sq_nonneg (subunitCollapseConstant d)) (sq_nonneg D),
      mul_nonneg (sq_nonneg (subunitCollapseConstant d)) (sq_nonneg Bs),
      mul_nonneg (sq_nonneg (subunitCollapseConstant d)) (sq_nonneg Bf),
      mul_nonneg (sq_nonneg (subunitCollapseConstant d)) (sq_nonneg Bg),
      sq_nonneg A, sq_nonneg D, sq_nonneg Bs, sq_nonneg Bf, sq_nonneg Bg]
  have hT0 : 0 ≤ goodScaleSquareConstant d := by
    have := goodScaleSquareConstant_ge d
    linarith
  calc
    Real.sqrt (192 * B) ≤
        Real.sqrt (goodScaleSquareConstant d * Sigma ^ 2) :=
      Real.sqrt_le_sqrt (hcoef.trans (mul_le_mul_of_nonneg_left hsq hT0))
    _ = goodScaleBaseConstant d * Sigma := by
      rw [Real.sqrt_mul hT0, Real.sqrt_sq hSigma0, goodScaleBaseConstant]

/-! ### Reading the field slots on the good event -/

private theorem bddAbove_abs_values_cube_int {k : ℤ} {f : Vec d → ℝ}
    (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ cube d k, a = |f x|} := by
  let Q := originCube d k
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using
    h.trans (le_max_right _ _)

private theorem abs_apply_le_supNormOn_cube_int {k : ℤ} {f : Vec d → ℝ}
    (hf : Continuous f) {x : Vec d} (hx : x ∈ cube d k) :
    |f x| ≤ supNormOn (cube d k) f :=
  le_csSup (bddAbove_abs_values_cube_int hf) ⟨x, hx, rfl⟩

private theorem cube_nonempty (k : ℤ) : (cube d k).Nonempty := by
  refine ⟨0, ?_⟩
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hp : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

private theorem translatedCube_zero (k : ℤ) :
    translatedCube d k 0 = cube d k := by
  unfold translatedCube
  simp

private theorem shellGradient_continuous
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    Continuous (shellGradient g) := by
  unfold shellGradient
  apply continuous_pi
  intro i
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous.clm_apply
    continuous_const

private theorem shellControl_continuous
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (i : ℕ) :
    Continuous (fun x => |g x| + (3 : ℝ) ^ i *
      euclideanNorm (shellGradient g x)) := by
  have hnorm : Continuous (fun x => euclideanNorm (shellGradient g x)) := by
    rw [show (fun x => euclideanNorm (shellGradient g x)) =
        fun x => ‖HilbertVec.ofVec (shellGradient g x)‖ by
      funext x
      rw [euclideanNorm_eq_norm_ofVec]]
    exact continuous_norm.comp
      ((HilbertVec.ofVecL d).continuous.comp (shellGradient_continuous g))
  exact (continuous_abs.comp g.1.1.continuous).add (continuous_const.mul hnorm)

private theorem sum_abs_le_of_goodFieldOne (m q : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega)
    {T : Finset ℕ} (hT : T ⊆ Finset.Icc (m - q) (m + q))
    {x : Vec d} (hx : x ∈ cube d (m : ℤ)) :
    ∑ i ∈ T, |omega i x| ≤ epsilon * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) := by
  have hevent := hgood q
  rw [translatedCube_zero] at hevent
  have hxlarge : x ∈ cube d ((m : ℤ) + 1 + (q : ℤ)) := by
    refine openCubeSet_originCube_subset_of_scale_le ?_ hx
    omega
  have hterm : ∀ i ∈ Finset.Icc (m - q) (m + q), |omega i x| ≤
      supNormOn (cube d ((m : ℤ) + 1 + (q : ℤ))) (fun y =>
        |omega i y| + (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) y)) := by
    intro i _
    have hcontrol := abs_apply_le_supNormOn_cube_int
      (shellControl_continuous (omega i) i) hxlarge
    have hnonneg : 0 ≤ |omega i x| + (3 : ℝ) ^ i *
        euclideanNorm (shellGradient (omega i) x) :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (euclideanNorm_nonneg _))
    rw [abs_of_nonneg hnonneg] at hcontrol
    refine le_trans ?_ hcontrol
    have : 0 ≤ (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x) :=
      mul_nonneg (by positivity) (euclideanNorm_nonneg _)
    linarith
  calc
    ∑ i ∈ T, |omega i x| ≤ ∑ i ∈ Finset.Icc (m - q) (m + q), |omega i x| :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun i _ _ => abs_nonneg _)
    _ ≤ ∑ i ∈ Finset.Icc (m - q) (m + q),
        supNormOn (cube d ((m : ℤ) + 1 + (q : ℤ))) (fun y =>
          |omega i y| + (3 : ℝ) ^ i *
            euclideanNorm (shellGradient (omega i) y)) :=
      Finset.sum_le_sum hterm
    _ ≤ epsilon * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) := hevent

private theorem supNormOn_shellBlock_le_of_goodFieldOne
    (m j : ℕ) (hj : j ≤ m) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    supNormOn (cube d (m : ℤ)) (shellBlock m j omega) ≤
      epsilon * (3 : ℝ) ^ ((s * ((m - j : ℕ) : ℝ)) / 8) := by
  refine csSup_le ?_ ?_
  · obtain ⟨x, hx⟩ := cube_nonempty (d := d) (m : ℤ)
    exact ⟨|shellBlock m j omega x|, x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hsubset : Finset.Icc (j + 1) m ⊆
        Finset.Icc (m - (m - j)) (m + (m - j)) := by
      intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega
    have hsum := sum_abs_le_of_goodFieldOne m (m - j) omega hgood hsubset hx
    refine le_trans ?_ hsum
    exact Finset.abs_sum_le_sum_abs _ _

private theorem supNormOn_fullShellBlock_le_of_goodFieldOne
    (m : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
      epsilon * (3 : ℝ) ^ ((s * (m : ℝ)) / 8) := by
  refine csSup_le ?_ ?_
  · obtain ⟨x, hx⟩ := cube_nonempty (d := d) (m : ℤ)
    exact ⟨|fullShellBlock m omega x|, x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hsubset : Finset.range (m + 1) ⊆ Finset.Icc (m - m) (m + m) := by
      intro i hi
      simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢
      omega
    have hsum := sum_abs_le_of_goodFieldOne m m omega hgood hsubset hx
    refine le_trans ?_ hsum
    exact Finset.abs_sum_le_sum_abs _ _

private theorem goodScaleShellSlot_le (m : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) (_heps : 0 ≤ epsilon) :
    goodScaleShellSlot s m omega ≤ epsilon := by
  refine csSup_le ⟨_, m, le_rfl, rfl⟩ ?_
  rintro _ ⟨j, hj, rfl⟩
  have hgap : (m : ℝ) - (j : ℝ) = ((m - j : ℕ) : ℝ) := by
    rw [Nat.cast_sub hj]
  have hsup := supNormOn_shellBlock_le_of_goodFieldOne m j hj omega hgood
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
        supNormOn (cube d (m : ℤ)) (shellBlock m j omega) ≤
        (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
          (epsilon * (3 : ℝ) ^ ((s * ((m - j : ℕ) : ℝ)) / 8)) :=
      mul_le_mul_of_nonneg_left hsup hw
    _ = epsilon := by
      rw [← hgap, ← mul_assoc, mul_comm _ epsilon, mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [show -(s / 8) * ((m : ℝ) - (j : ℝ)) + s * ((m : ℝ) - (j : ℝ)) / 8 = 0 by
        ring]
      rw [Real.rpow_zero, mul_one]

private theorem goodScaleFullSlot_le (m : ℕ) {epsilon s : ℝ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    goodScaleFullSlot s m omega ≤ epsilon := by
  have hsup := supNormOn_fullShellBlock_le_of_goodFieldOne m omega hgood
  have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  unfold goodScaleFullSlot
  calc
    (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) *
        supNormOn (cube d (m : ℤ)) (fullShellBlock m omega) ≤
        (3 : ℝ) ^ (-(s / 8) * (m : ℝ)) *
          (epsilon * (3 : ℝ) ^ ((s * (m : ℝ)) / 8)) :=
      mul_le_mul_of_nonneg_left hsup hw
    _ = epsilon := by
      rw [← mul_assoc, mul_comm _ epsilon, mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [show -(s / 8) * (m : ℝ) + s * (m : ℝ) / 8 = 0 by ring]
      rw [Real.rpow_zero, mul_one]

/-! ### The frozen export -/

-- FROZEN-APPLICATION-BEGIN
theorem good_scale_mathcal_e
    (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      ∀ L m : ℕ, m ≤ L → ∀ ω,
        indicatorValue (goodEvent M none m 0 1 s)
            (fun ω' => section6HomogenizationError M s L m ω' 0) ω ≤
          C * sSup {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
              ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
              r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
                Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
                  t = section6Response M n n ω z e})} +
            C * s⁻¹ * M.delta ^ 2 +
            C * sSup {r : ℝ | ∃ j ≤ m,
              r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
                supNormOn (cube d m) (shellBlock m j ω)} +
            C * (3 : ℝ) ^ (-(s / 8) * m) *
              supNormOn (cube d m)
                (fun x => ∑ i ∈ Finset.range (m + 1), ω i x) +
            (C * ∑' j : ℕ, if m ≤ j then
              (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (ω j)) else 0) ∧
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
          ω ∈ goodEvent M none m 0 epsilon s →
            section6HomogenizationError M s L m ω 0 ≤ C * epsilon := by
  have hbase := goodScaleBaseConstant_pos d
  refine ⟨7 * goodScaleBaseConstant d, by linarith, ?_⟩
  intro M s hs L m hmL omega
  obtain ⟨hsLower, hsUpper⟩ := hs
  have hs0 : 0 < s :=
    (mul_pos (by norm_num) (pow_pos M.shellPrefix.delta_pos 2)).trans_le hsLower
  have hA0 : 0 ≤ goodScaleResponseSlot M s m omega :=
    goodScaleResponseSlot_nonneg M s m omega
  have hD0 : (0 : ℝ) ≤ s⁻¹ * M.delta ^ 2 :=
    mul_nonneg (inv_nonneg.2 hs0.le) (sq_nonneg _)
  have hBs0 : 0 ≤ goodScaleShellSlot s m omega :=
    goodScaleShellSlot_nonneg s m omega
  have hBf0 : 0 ≤ goodScaleFullSlot s m omega :=
    goodScaleFullSlot_nonneg s m omega
  have hBg0 : 0 ≤ goodScaleGradientSlot m omega :=
    goodScaleGradientSlot_nonneg m omega
  have hsum0 : 0 ≤ goodScaleResponseSlot M s m omega + s⁻¹ * M.delta ^ 2 +
      goodScaleShellSlot s m omega + goodScaleFullSlot s m omega +
      goodScaleGradientSlot m omega := by linarith
  refine ⟨?_, ?_⟩
  · have hrhs :
        (7 * goodScaleBaseConstant d) *
              sSup {r : ℝ | ∃ j n : ℕ, j ≤ m ∧ n + 2 ≤ j ∧
                ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d j \ cube d (j - 1) ∧
                r = (3 : ℝ) ^ (-(s / 2) * ((m : ℝ) - (n : ℝ))) *
                  Real.sqrt (sSup {t : ℝ | ∃ e : Vec d, vecNormSq e = 1 ∧
                    t = section6Response M n n omega z e})} +
              (7 * goodScaleBaseConstant d) * s⁻¹ * M.delta ^ 2 +
              (7 * goodScaleBaseConstant d) * sSup {r : ℝ | ∃ j ≤ m,
                r = (3 : ℝ) ^ (-(s / 8) * ((m : ℝ) - (j : ℝ))) *
                  supNormOn (cube d m) (shellBlock m j omega)} +
              (7 * goodScaleBaseConstant d) * (3 : ℝ) ^ (-(s / 8) * m) *
                supNormOn (cube d m)
                  (fun x => ∑ i ∈ Finset.range (m + 1), omega i x) +
              ((7 * goodScaleBaseConstant d) * ∑' j : ℕ, if m ≤ j then
                (3 : ℝ) ^ m *
                  vectorSupNormOn (cube d m) (shellGradient (omega j)) else 0) =
          7 * goodScaleBaseConstant d *
            (goodScaleResponseSlot M s m omega + s⁻¹ * M.delta ^ 2 +
              goodScaleShellSlot s m omega + goodScaleFullSlot s m omega +
              goodScaleGradientSlot m omega) := by
      unfold goodScaleResponseSlot goodScaleShellSlot goodScaleFullSlot
        goodScaleGradientSlot fullShellBlock
      ring
    rw [hrhs]
    unfold indicatorValue
    split_ifs with hmem
    · refine (error_le_base M hsLower hsUpper hmL omega hmem).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) hsum0
    · exact mul_nonneg (by linarith) hsum0
  · intro epsilon hepsilon hmem
    obtain ⟨heps1, heps2⟩ := hepsilon
    have heps0 : 0 ≤ epsilon := le_trans hD0 heps1
    have hgood1 : omega ∈ goodEvent M none m 0 1 s :=
      goodEvent_subset_one M none m 0 heps0 heps2 hmem
    have hcore := error_le_base M hsLower hsUpper hmL omega hgood1
    have hAle : goodScaleResponseSlot M s m omega ≤ epsilon :=
      goodResponse_discounted_sSup_le M heps0 hs0.le hmem
    have hBsle : goodScaleShellSlot s m omega ≤ epsilon :=
      goodScaleShellSlot_le m omega hmem.1 heps0
    have hBfle : goodScaleFullSlot s m omega ≤ epsilon :=
      goodScaleFullSlot_le m omega hmem.1
    have hBgle : goodScaleGradientSlot m omega ≤ 3 * epsilon := by
      rw [goodScaleGradientSlot_eq_longRatioGradientTail]
      exact longRatioGradientTail_le_three_mul_of_goodFieldOne m heps0 hsUpper
        omega hmem.1
    refine hcore.trans ?_
    have hsum : goodScaleResponseSlot M s m omega + s⁻¹ * M.delta ^ 2 +
        goodScaleShellSlot s m omega + goodScaleFullSlot s m omega +
        goodScaleGradientSlot m omega ≤ 7 * epsilon := by linarith
    calc
      goodScaleBaseConstant d *
          (goodScaleResponseSlot M s m omega + s⁻¹ * M.delta ^ 2 +
            goodScaleShellSlot s m omega + goodScaleFullSlot s m omega +
            goodScaleGradientSlot m omega) ≤
          goodScaleBaseConstant d * (7 * epsilon) :=
        mul_le_mul_of_nonneg_left hsum hbase.le
      _ = 7 * goodScaleBaseConstant d * epsilon := by ring
-- FROZEN-APPLICATION-END

end

end SubdiffusiveProcess.Providers.Section6
