module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatioEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge

@[expose] public section

/-!
# Pointwise boundedness on the Section 6 good event

The localization estimates use the real `sSup` occurring in `GoodFieldTwo`.
Its pointwise reading requires a boundedness certificate.  The probability
layer supplies such a certificate almost surely, but the frozen good-scale
proposition is an all-sample statement.  This file obtains the certificate
directly from `GoodFieldOne`: its expanding-cube gradient bounds make the
logarithms of the tail-product factors uniformly summable on every fixed
good-field cube.

First extract a summable positive majorant from the event, then turn it into
the boundedness guard needed by the response layer.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open Homogenization Homogenization.Book
open scoped BigOperators

noncomputable section

variable {d : ℕ}

private theorem shellGradient_continuous
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    Continuous (shellGradient g) := by
  unfold shellGradient
  apply continuous_pi
  intro i
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous.clm_apply
    continuous_const

private theorem euclideanNorm_shellGradient_continuous
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    Continuous (fun x => euclideanNorm (shellGradient g x)) := by
  rw [show (fun x => euclideanNorm (shellGradient g x)) =
      fun x => ‖HilbertVec.ofVec (shellGradient g x)‖ by
    funext x
    rw [euclideanNorm_eq_norm_ofVec]]
  exact continuous_norm.comp
    ((HilbertVec.ofVecL d).continuous.comp (shellGradient_continuous g))

private theorem shellControl_continuous
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (i : ℕ) :
    Continuous (fun x => |g x| + (3 : ℝ) ^ i *
      euclideanNorm (shellGradient g x)) := by
  exact (continuous_abs.comp g.1.1.continuous).add
    (continuous_const.mul (euclideanNorm_shellGradient_continuous g))

private theorem cube_nonempty (r : ℕ) : (cube d r).Nonempty := by
  refine ⟨0, ?_⟩
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hp : (0 : ℝ) < (3 : ℝ) ^ (r : ℤ) := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

private theorem bddAbove_abs_values_cube {r : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ cube d r, a = |f x|} := by
  let Q := originCube d (r : ℤ)
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

private theorem abs_apply_le_supNormOn_cube {r : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) {x : Vec d} (hx : x ∈ cube d r) :
    |f x| ≤ supNormOn (cube d r) f := by
  unfold supNormOn
  exact le_csSup (bddAbove_abs_values_cube hf) ⟨x, hx, rfl⟩

private theorem supNormOn_cube_nonneg {r : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) : 0 ≤ supNormOn (cube d r) f := by
  obtain ⟨x, hx⟩ := cube_nonempty (d := d) r
  exact (abs_nonneg (f x)).trans (abs_apply_le_supNormOn_cube hf hx)

private theorem bddAbove_euclideanNorm_shellGradient_cube
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (r : ℕ) :
    BddAbove {a : ℝ | ∃ x ∈ cube d r,
      a = euclideanNorm (shellGradient g x)} := by
  let Q := originCube d (r : ℤ)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      (euclideanNorm_shellGradient_continuous g).continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (euclideanNorm_nonneg _)] using h.trans (le_max_right _ _)

private theorem vectorSupNormOn_shellGradient_nonneg
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (r : ℕ) :
    0 ≤ vectorSupNormOn (cube d r) (shellGradient g) := by
  obtain ⟨x, hx⟩ := cube_nonempty (d := d) r
  unfold vectorSupNormOn
  exact (euclideanNorm_nonneg (shellGradient g x)).trans
    (le_csSup (bddAbove_euclideanNorm_shellGradient_cube g r) ⟨x, hx, rfl⟩)

private theorem scaled_gradientSup_le_goodFieldOne_atom
    (m j q : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (3 : ℝ) ^ (m + j + q) *
        vectorSupNormOn (cube d (m + 1 + j))
          (shellGradient (omega (m + j + q))) ≤
      supNormOn (cube d (m + 1 + (j + q))) (fun x =>
        |omega (m + j + q) x| + (3 : ℝ) ^ (m + j + q) *
          euclideanNorm (shellGradient (omega (m + j + q)) x)) := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (m + j + q) := by positivity
  rw [mul_comm]
  apply (le_div_iff₀ hpow).1
  unfold vectorSupNormOn
  apply csSup_le
  · obtain ⟨x, hx⟩ := cube_nonempty (d := d) (m + 1 + j)
    exact ⟨euclideanNorm (shellGradient (omega (m + j + q)) x), x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hscale : ((m + 1 + j : ℕ) : ℤ) ≤
        ((m + 1 + (j + q) : ℕ) : ℤ) := by exact_mod_cast (by omega : m + 1 + j ≤ m + 1 + (j + q))
    have hxlarge : x ∈ cube d (m + 1 + (j + q)) :=
      openCubeSet_originCube_subset_of_scale_le hscale hx
    have hcontrol := abs_apply_le_supNormOn_cube
      (shellControl_continuous (omega (m + j + q)) (m + j + q)) hxlarge
    have hcontrol0 : 0 ≤ |omega (m + j + q) x| +
        (3 : ℝ) ^ (m + j + q) *
          euclideanNorm (shellGradient (omega (m + j + q)) x) :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (euclideanNorm_nonneg _))
    rw [abs_of_nonneg hcontrol0] at hcontrol
    rw [le_div_iff₀ hpow]
    calc
      euclideanNorm (shellGradient (omega (m + j + q)) x) *
          (3 : ℝ) ^ (m + j + q) =
        (3 : ℝ) ^ (m + j + q) *
          euclideanNorm (shellGradient (omega (m + j + q)) x) := mul_comm _ _
      _ ≤ |omega (m + j + q) x| +
          (3 : ℝ) ^ (m + j + q) *
            euclideanNorm (shellGradient (omega (m + j + q)) x) :=
        le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ _ := hcontrol

private theorem three_rpow_eighth_le_two {s : ℝ} (hs : s ≤ 1 / 2) :
    (3 : ℝ) ^ (s / 8) ≤ 2 := by
  have hmono : (3 : ℝ) ^ (s / 8) ≤ (3 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [← Real.sqrt_eq_rpow] at hmono
  exact hmono.trans (by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)])

private theorem scaled_gradientSup_le_geometric_of_goodFieldOne
    (m j q : ℕ) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs : s ≤ 1 / 2) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    (3 : ℝ) ^ (m + j + q) *
        vectorSupNormOn (cube d (m + 1 + j))
          (shellGradient (omega (m + j + q))) ≤
      epsilon * (2 : ℝ) ^ (j + q) := by
  have hfield :
      (∑ i ∈ Finset.Icc (m - (j + q)) (m + (j + q)),
        supNormOn (cube d (m + 1 + (j + q))) (fun x =>
          |omega i x| + (3 : ℝ) ^ i *
            euclideanNorm (shellGradient (omega i) x))) ≤
        epsilon * (3 : ℝ) ^ ((s * ((j + q : ℕ) : ℝ)) / 8) := by
    simpa [translatedCube, Nat.cast_add, add_assoc] using hgood (j + q)
  have hmem : m + j + q ∈ Finset.Icc (m - (j + q)) (m + (j + q)) := by
    simp only [Finset.mem_Icc]
    omega
  have hatom :
      supNormOn (cube d (m + 1 + (j + q))) (fun x =>
          |omega (m + j + q) x| + (3 : ℝ) ^ (m + j + q) *
            euclideanNorm (shellGradient (omega (m + j + q)) x)) ≤
        ∑ i ∈ Finset.Icc (m - (j + q)) (m + (j + q)),
          supNormOn (cube d (m + 1 + (j + q))) (fun x =>
            |omega i x| + (3 : ℝ) ^ i *
              euclideanNorm (shellGradient (omega i) x)) := by
    exact Finset.single_le_sum
      (fun i _ => supNormOn_cube_nonneg (shellControl_continuous (omega i) i)) hmem
  have hraw := (scaled_gradientSup_le_goodFieldOne_atom m j q omega).trans
    (hatom.trans hfield)
  have hrpow : (3 : ℝ) ^ ((s * ((j + q : ℕ) : ℝ)) / 8) =
      ((3 : ℝ) ^ (s / 8)) ^ (j + q) := by
    rw [show s * ((j + q : ℕ) : ℝ) / 8 = (s / 8) * ((j + q : ℕ) : ℝ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  have hrpow_le : (3 : ℝ) ^ ((s * ((j + q : ℕ) : ℝ)) / 8) ≤
      (2 : ℝ) ^ (j + q) := by
    rw [hrpow]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
      (three_rpow_eighth_le_two hs) _
  exact hraw.trans (mul_le_mul_of_nonneg_left hrpow_le hepsilon)

private theorem shell_increment_sup_le_geometric_of_goodFieldOne
    (m j q : ℕ) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs : s ≤ 1 / 2) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    4 * supNormOn (cube d (m + 1 + j))
        (fun x => omega (m + j + q) x - omega (m + j + q) 0) ≤
      (12 * (d : ℝ) * epsilon * (2 : ℝ) ^ j) * ((2 : ℝ) / 3) ^ q := by
  let g := omega (m + j + q)
  let r := m + 1 + j
  have hzero : (0 : Vec d) ∈ cube d r := by
    dsimp [r]
    rw [cube, mem_openCubeSet_originCube_iff]
    intro i
    have hp : (0 : ℝ) < (1 / 2 : ℝ) *
        (3 : ℝ) ^ ((m + 1 + j : ℕ) : ℤ) := by positivity
    push_cast at hp
    constructor <;> simp only [Pi.zero_apply] <;> nlinarith
  have hpoint : ∀ x ∈ cube d r,
      |g x - g 0| ≤ (d : ℝ) * ((3 : ℝ) ^ r *
        vectorSupNormOn (cube d r) (shellGradient g)) := by
    intro x hx
    exact abs_shell_sub_le_dimension_mul_scaled_gradientSup g r hx hzero
  have hsup : supNormOn (cube d r) (fun x => g x - g 0) ≤
      (d : ℝ) * ((3 : ℝ) ^ r *
        vectorSupNormOn (cube d r) (shellGradient g)) := by
    unfold supNormOn
    apply csSup_le
    · exact ⟨0, 0, hzero, by simp⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hpoint x hx
  have hscaled := scaled_gradientSup_le_geometric_of_goodFieldOne
    m j q hepsilon hs omega hgood
  have hden : (0 : ℝ) < (3 : ℝ) ^ (m + j + q) := by positivity
  have hre : (3 : ℝ) ^ r *
        vectorSupNormOn (cube d r) (shellGradient g) ≤
      3 * epsilon * (2 : ℝ) ^ j * ((2 : ℝ) / 3) ^ q := by
    dsimp [r, g]
    calc
      (3 : ℝ) ^ (m + 1 + j) *
          vectorSupNormOn (cube d (m + 1 + j))
            (shellGradient (omega (m + j + q))) =
        ((3 : ℝ) ^ (m + j + q) *
          vectorSupNormOn (cube d (m + 1 + j))
            (shellGradient (omega (m + j + q)))) *
              ((3 : ℝ) ^ (m + 1 + j) / (3 : ℝ) ^ (m + j + q)) := by
          field_simp
      _ ≤ (epsilon * (2 : ℝ) ^ (j + q)) *
              ((3 : ℝ) ^ (m + 1 + j) / (3 : ℝ) ^ (m + j + q)) := by
          gcongr
      _ = 3 * epsilon * (2 : ℝ) ^ j * ((2 : ℝ) / 3) ^ q := by
          rw [pow_add (2 : ℝ) j q, div_pow]
          field_simp
          ring
  calc
    4 * supNormOn (cube d r) (fun x => g x - g 0) ≤
        4 * ((d : ℝ) * ((3 : ℝ) ^ r *
          vectorSupNormOn (cube d r) (shellGradient g))) := by gcongr
    _ ≤ 4 * ((d : ℝ) * (3 * epsilon * (2 : ℝ) ^ j *
          ((2 : ℝ) / 3) ^ q)) := by
      gcongr
    _ = (12 * (d : ℝ) * epsilon * (2 : ℝ) ^ j) *
          ((2 : ℝ) / 3) ^ q := by ring

/-- `GoodFieldOne` makes the logarithms in the `GoodFieldTwo` tail product
uniformly summable on the fixed cube, for every sample in the event. -/
theorem summable_goodFieldTwo_tail_supNorm_of_goodFieldOne
    (m j : ℕ) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs : s ≤ 1 / 2) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    Summable (fun i : ℕ => if m + j ≤ i then
      4 * supNormOn (cube d (m + 1 + j))
        (fun x => omega i x - omega i 0) else 0) := by
  let F : ℕ → ℝ := fun i => if m + j ≤ i then
    4 * supNormOn (cube d (m + 1 + j))
      (fun x => omega i x - omega i 0) else 0
  have hshift : Summable (fun q : ℕ => F (q + (m + j))) := by
    refine Summable.of_nonneg_of_le (f := fun q =>
      (12 * (d : ℝ) * epsilon * (2 : ℝ) ^ j) * ((2 : ℝ) / 3) ^ q) ?_ ?_ ?_
    · intro q
      dsimp [F]
      rw [ite_eq_left (by omega : m + j ≤ q + (m + j))]
      exact mul_nonneg (by norm_num) (supNormOn_cube_nonneg
        ((omega (q + (m + j))).1.1.continuous.sub
          (continuous_const : Continuous (fun _ : Vec d => omega (q + (m + j)) 0))))
    · intro q
      dsimp [F]
      rw [ite_eq_left (by omega : m + j ≤ q + (m + j))]
      simpa only [Nat.add_comm q, Nat.add_assoc] using
        shell_increment_sup_le_geometric_of_goodFieldOne
          m j q hepsilon hs omega hgood
    · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 : ℝ) / 3 < 1)).mul_left
          (12 * (d : ℝ) * epsilon * (2 : ℝ) ^ j)
  exact (summable_nat_add_iff (m + j)).mp hshift

private theorem bddAbove_goodFieldTwo_values_of_summable
    (m j : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hsum : Summable (fun i : ℕ => if m + j ≤ i then
      4 * supNormOn (cube d (m + 1 + j))
        (fun x => omega i x - omega i 0) else 0)) :
    BddAbove {a : ℝ | ∃ x ∈ translatedCube d ((m + 1 + j : ℕ) : ℤ) 0,
      a = |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
        ∏' i : ℕ, if m + j ≤ i then
          Real.exp (4 * |omega i x - omega i 0|) else 1|} := by
  -- The already audited discharge proof is deterministic once its uniform
  -- logarithmic summability input is supplied.  We repeat its final compact
  -- finite-part plus exponential-tail estimate here for the pointwise argument.
  let W := cube d (m + 1 + j)
  let finitePart : Vec d → ℝ := fun x =>
    ∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|
  have hfinite : Continuous finitePart := by dsimp [finitePart]; fun_prop
  obtain ⟨C, hC⟩ := bddAbove_abs_values_cube (r := m + 1 + j) hfinite
  let S : ℝ := ∑' i : ℕ, if m + j ≤ i then
    4 * supNormOn W (fun x => omega i x - omega i 0) else 0
  refine ⟨C + Real.exp S, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hxW : x ∈ W := by simpa [W, translatedCube] using hx
  let pointTerm : ℕ → ℝ := fun i => if m + j ≤ i then
    4 * |omega i x - omega i 0| else 0
  have hpoint : Summable pointTerm := by
    refine Summable.of_nonneg_of_le
      (f := fun i => if m + j ≤ i then
        4 * supNormOn W (fun y => omega i y - omega i 0) else 0) ?_ ?_ hsum
    · intro i
      by_cases hi : m + j ≤ i
      · simp only [pointTerm, hi, ite_true]
        positivity
      · simp only [pointTerm, hi, ite_false]
        exact le_rfl
    · intro i
      by_cases hi : m + j ≤ i
      · simp only [pointTerm, hi, ite_true]
        exact mul_le_mul_of_nonneg_left
          (abs_apply_le_supNormOn_cube
            ((omega i).1.1.continuous.sub
              (continuous_const : Continuous (fun _ : Vec d => omega i 0))) hxW)
          (by norm_num)
      · simp only [hi, ite_false, pointTerm]
        exact le_rfl
  have hterm : ∀ i, pointTerm i ≤ if m + j ≤ i then
      4 * supNormOn W (fun y => omega i y - omega i 0) else 0 := by
    intro i
    by_cases hi : m + j ≤ i
    · simp only [pointTerm, hi, ite_true]
      exact mul_le_mul_of_nonneg_left
        (abs_apply_le_supNormOn_cube
          ((omega i).1.1.continuous.sub
            (continuous_const : Continuous (fun _ : Vec d => omega i 0))) hxW)
        (by norm_num)
    · simp only [pointTerm, hi, ite_false]
      exact le_rfl
  have hsumPoint : ∑' i, pointTerm i ≤ S := by
    exact Summable.tsum_le_tsum hterm hpoint hsum
  have hprod : (∏' i : ℕ, if m + j ≤ i then
      Real.exp (4 * |omega i x - omega i 0|) else 1) =
      Real.exp (∑' i, pointTerm i) := by
    have heq : (fun i : ℕ => if m + j ≤ i then
        Real.exp (4 * |omega i x - omega i 0|) else 1) =
        fun i => Real.exp (pointTerm i) := by
      funext i
      by_cases hi : m + j ≤ i <;> simp [pointTerm, hi]
    rw [heq]
    exact hpoint.hasSum.rexp.tprod_eq
  have htail : (∏' i : ℕ, if m + j ≤ i then
      Real.exp (4 * |omega i x - omega i 0|) else 1) ≤ Real.exp S := by
    rw [hprod]
    exact Real.exp_le_exp.mpr hsumPoint
  have hfin : |finitePart x| ≤ C := hC ⟨x, hxW, rfl⟩
  have hfin0 : 0 ≤ finitePart x := by dsimp [finitePart]; positivity
  have htail0 : 0 ≤ (∏' i : ℕ, if m + j ≤ i then
      Real.exp (4 * |omega i x - omega i 0|) else 1) := by
    rw [hprod]
    positivity
  rw [abs_of_nonneg (add_nonneg hfin0 htail0)]
  exact add_le_add (by simpa [abs_of_nonneg hfin0] using hfin) htail

/-- Pointwise boundedness guard required by the localization estimates. -/
theorem bddAbove_goodFieldTwo_values_of_goodFieldOne
    (m j : ℕ) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs : s ≤ 1 / 2) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    BddAbove {a : ℝ | ∃ x ∈ translatedCube d ((m + 1 + j : ℕ) : ℤ) 0,
      a = |(∏ i ∈ Finset.Icc (m - j) (m + j), Real.exp |omega i x|) +
        ∏' i : ℕ, if m + j ≤ i then
          Real.exp (4 * |omega i x - omega i 0|) else 1|} := by
  apply bddAbove_goodFieldTwo_values_of_summable m j omega
  simpa only [translatedCube, zero_add] using
    summable_goodFieldTwo_tail_supNorm_of_goodFieldOne
      m j hepsilon hs omega hgood

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
