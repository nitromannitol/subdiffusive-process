module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.CombinedCoefficientRatio
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SharpSuffixRepresentative
public import Homogenization.Sobolev.FiniteLpCoordinate
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

/-!
# Section 6 localization: the long coefficient ratio

This module isolates the deterministic mean-value part of display
`e.long.ratio.reg` in Step 2 of `p.good.scale.mathcal.E`.
The tail coefficient is compared with its
average on the scale-`m` cube using the literal gradient-tail carrier from the
theorem.

The deterministic response of the long ratio to a shell-gradient budget is proved first. Reading that budget from the good event is a separate theorem below.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The literal gradient tail `S_m` in `e.long.ratio.reg`. -/
def longRatioGradientTail (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) : ℝ :=
  ∑' j : ℕ, if m ≤ j then
    (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j))
  else 0

private theorem euclideanNorm_shellGradient_le_dimension_mul_deriv
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (x : Vec d) :
    euclideanNorm (shellGradient g x) ≤
      (d : ℝ) * ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ := by
  have hpi : ‖shellGradient g x‖ ≤
      ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    calc
      |shellGradient g x i| =
          ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x
            (Pi.single i (1 : ℝ) : Vec d)‖ := by
        rw [Real.norm_eq_abs]
        rfl
      _ ≤ ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ *
          ‖(Pi.single i (1 : ℝ) : Vec d)‖ :=
        (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x).le_opNorm _
      _ = ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ := by
        rw [Pi.norm_single]
        norm_num
  exact (euclideanNorm_le_dimension_mul_norm _).trans
    (mul_le_mul_of_nonneg_left hpi (Nat.cast_nonneg d))

private theorem cube_nonempty (m : ℕ) : (cube d m).Nonempty := by
  refine ⟨0, ?_⟩
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

private theorem bddAbove_euclideanNorm_shellGradient_cube
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (m : ℕ) :
    BddAbove {a : ℝ | ∃ x ∈ cube d m, a = euclideanNorm (shellGradient g x)} := by
  let Q := originCube d (m : ℤ)
  obtain ⟨K, hK⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_norm.comp
        (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous).continuousOn)
  refine ⟨(d : ℝ) * max 0 K, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hK x hx'
  have hderiv : ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤ max 0 K := by
    simpa only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using h.trans (le_max_right _ _)
  exact (euclideanNorm_shellGradient_le_dimension_mul_deriv g x).trans
    (mul_le_mul_of_nonneg_left hderiv (Nat.cast_nonneg d))

private theorem euclideanNorm_shellGradient_le_vectorSupNormOn_cube
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (m : ℕ)
    {x : Vec d} (hx : x ∈ cube d m) :
    euclideanNorm (shellGradient g x) ≤
      vectorSupNormOn (cube d m) (shellGradient g) := by
  unfold vectorSupNormOn
  exact le_csSup (bddAbove_euclideanNorm_shellGradient_cube g m) ⟨x, hx, rfl⟩

private theorem vectorSupNormOn_shellGradient_nonneg
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (m : ℕ) :
    0 ≤ vectorSupNormOn (cube d m) (shellGradient g) := by
  obtain ⟨x, hx⟩ := cube_nonempty (d := d) m
  exact (euclideanNorm_nonneg (shellGradient g x)).trans
    (euclideanNorm_shellGradient_le_vectorSupNormOn_cube g m hx)

theorem longRatioGradientTail_nonneg (m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ longRatioGradientTail m omega := by
  unfold longRatioGradientTail
  exact tsum_nonneg fun j => by
    split
    · exact mul_nonneg (by positivity)
        (vectorSupNormOn_shellGradient_nonneg (omega j) m)
    · exact le_rfl

/-- The operator norm of the stored derivative is controlled by the Euclidean
coordinate gradient.  The harmless factor `d` comes from retaining the
project's ambient sup norm on `Vec d`. -/
theorem potentialDeriv_norm_le_dimension_mul_shellGradient
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (x : Vec d) :
    ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv g x‖ ≤
      (d : ℝ) * euclideanNorm (shellGradient g x) := by
  let D := _root_.SubdiffusiveProcess.Model.PotentialField.deriv g x
  have hnonneg : 0 ≤ (d : ℝ) * euclideanNorm (shellGradient g x) :=
    mul_nonneg (Nat.cast_nonneg d) (euclideanNorm_nonneg _)
  apply D.opNorm_le_bound hnonneg
  intro v
  conv_lhs => rw [pi_eq_sum_univ' v, map_sum]
  calc
    ‖∑ i ∈ Finset.univ,
        D ((v i) • (Pi.single i (1 : ℝ) : Vec d))‖ ≤
        ∑ i ∈ Finset.univ,
          ‖D ((v i) • (Pi.single i (1 : ℝ) : Vec d))‖ :=
      norm_sum_le Finset.univ
        (fun i => D ((v i) • (Pi.single i (1 : ℝ) : Vec d)))
    _ = ∑ i, |v i| * |shellGradient g x i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [map_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      rfl
    _ ≤ ∑ _i : Fin d, ‖v‖ * euclideanNorm (shellGradient g x) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul (show |v i| ≤ ‖v‖ by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
        (abs_coordinate_le_euclideanNorm (shellGradient g x) i)
        (abs_nonneg _) (norm_nonneg _)
    _ = ((d : ℝ) * euclideanNorm (shellGradient g x)) * ‖v‖ := by
      simp [mul_assoc, mul_comm]

private theorem norm_sub_le_cubeScale {m : ℕ} {x y : Vec d}
    (hx : x ∈ cube d m) (hy : y ∈ cube d m) :
    ‖x - y‖ ≤ (3 : ℝ) ^ m := by
  rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ m)]
  intro i
  have hxi := (mem_openCubeSet_originCube_iff.mp hx) i
  have hyi := (mem_openCubeSet_originCube_iff.mp hy) i
  simp only [zpow_natCast] at hxi hyi
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

/-- One shell obeys the mean-value estimate on the centered scale cube. -/
theorem abs_shell_sub_le_dimension_mul_scaled_gradientSup
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (m : ℕ)
    {x y : Vec d} (hx : x ∈ cube d m) (hy : y ∈ cube d m) :
    |g x - g y| ≤
      (d : ℝ) * ((3 : ℝ) ^ m *
        vectorSupNormOn (cube d m) (shellGradient g)) := by
  have hmean := (convex_openCubeSet (originCube d (m : ℤ))).norm_image_sub_le_of_norm_fderiv_le
    (f := fun z : Vec d => g z)
    (fun z _hz => (g.hasFDerivAt z).differentiableAt)
    (fun z hz => by
      rw [(g.hasFDerivAt z).fderiv]
      exact (potentialDeriv_norm_le_dimension_mul_shellGradient g z).trans
        (mul_le_mul_of_nonneg_left
          (euclideanNorm_shellGradient_le_vectorSupNormOn_cube g m hz)
          (Nat.cast_nonneg d)))
    hx hy
  rw [Real.norm_eq_abs] at hmean
  calc
    |g x - g y| = |g y - g x| := abs_sub_comm _ _
    _ ≤ ((d : ℝ) * vectorSupNormOn (cube d m) (shellGradient g)) *
        ‖y - x‖ := hmean
    _ ≤ ((d : ℝ) * vectorSupNormOn (cube d m) (shellGradient g)) *
        (3 : ℝ) ^ m :=
      mul_le_mul_of_nonneg_left (by simpa [norm_sub_rev] using
        (norm_sub_le_cubeScale (m := m) hy hx))
        (mul_nonneg (Nat.cast_nonneg d)
          (vectorSupNormOn_shellGradient_nonneg g m))
    _ = (d : ℝ) * ((3 : ℝ) ^ m *
        vectorSupNormOn (cube d m) (shellGradient g)) := by ring

private theorem tailCoefficient_pair_ratio_eq_exp
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x y : Vec d) :
    tailCoefficient M L m omega x / tailCoefficient M L m omega y =
      Real.exp (∑ i ∈ Finset.Icc (m + 1) L, (omega i x - omega i y)) := by
  have hxL := _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x
  have hyL := _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega y
  have hxm := _root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x
  have hym := _root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega y
  have hahom := ahom_pos M m
  have hx := aCutoff_div_eq_exp_shellBlock M hmL omega x
  have hy := aCutoff_div_eq_exp_shellBlock M hmL omega y
  unfold tailCoefficient
  rw [min_eq_left hmL]
  rw [show ahom M m *
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M m omega x) /
      (ahom M m *
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega y /
          _root_.SubdiffusiveProcess.Model.aCutoff M m omega y)) =
      (_root_.SubdiffusiveProcess.Model.aCutoff M L omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M m omega x) /
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega y /
          _root_.SubdiffusiveProcess.Model.aCutoff M m omega y) by field_simp]
  rw [hx, hy, ← Real.exp_sub]
  congr 1
  unfold shellBlock
  rw [Finset.sum_sub_distrib]
  ring

private theorem abs_sum_shell_sub_le_gradientTail
    {L m : ℕ}
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {x y : Vec d} (hx : x ∈ cube d m) (hy : y ∈ cube d m)
    (hsum : Summable (fun j : ℕ => if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j))
      else 0)) :
    |∑ i ∈ Finset.Icc (m + 1) L, (omega i x - omega i y)| ≤
      (d : ℝ) * longRatioGradientTail m omega := by
  calc
    |∑ i ∈ Finset.Icc (m + 1) L, (omega i x - omega i y)| ≤
        ∑ i ∈ Finset.Icc (m + 1) L, |omega i x - omega i y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Icc (m + 1) L,
        (d : ℝ) * ((3 : ℝ) ^ m *
          vectorSupNormOn (cube d m) (shellGradient (omega i))) := by
      gcongr with i hi
      exact abs_shell_sub_le_dimension_mul_scaled_gradientSup (omega i) m hx hy
    _ = (d : ℝ) * ∑ i ∈ Finset.Icc (m + 1) L,
        ((3 : ℝ) ^ m *
          vectorSupNormOn (cube d m) (shellGradient (omega i))) := by
      rw [Finset.mul_sum]
    _ ≤ (d : ℝ) * longRatioGradientTail m omega := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      unfold longRatioGradientTail
      calc
        ∑ i ∈ Finset.Icc (m + 1) L,
            (3 : ℝ) ^ m *
              vectorSupNormOn (cube d m) (shellGradient (omega i)) =
            ∑ i ∈ Finset.Icc (m + 1) L, if m ≤ i then
              (3 : ℝ) ^ m *
                vectorSupNormOn (cube d m) (shellGradient (omega i)) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          have hmi : m ≤ i :=
            (Nat.le_add_right m 1).trans (Finset.mem_Icc.mp hi).1
          simp only [ite_eq_left hmi]
        _ ≤ ∑' j : ℕ, if m ≤ j then
              (3 : ℝ) ^ m *
                vectorSupNormOn (cube d m) (shellGradient (omega j)) else 0 := by
          apply hsum.sum_le_tsum
          intro i hi
          split
          · exact mul_nonneg (by positivity)
              (vectorSupNormOn_shellGradient_nonneg (omega i) m)
          · exact le_rfl

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

/-- Deterministic pair-ratio form of `e.long.ratio.reg`. -/
theorem tailCoefficient_pair_ratio_sub_one_le_gradientTail
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hsum : Summable (fun j : ℕ => if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j))
      else 0))
    {x y : Vec d} (hx : x ∈ cube d m) (hy : y ∈ cube d m) :
    |tailCoefficient M L m omega x / tailCoefficient M L m omega y - 1| ≤
      ((d : ℝ) * longRatioGradientTail m omega) *
        Real.exp ((d : ℝ) * longRatioGradientTail m omega) := by
  rw [tailCoefficient_pair_ratio_eq_exp M hmL omega x y]
  let r := ∑ i ∈ Finset.Icc (m + 1) L, (omega i x - omega i y)
  have hr := abs_sum_shell_sub_le_gradientTail (L := L) omega hx hy hsum
  have htail_nonneg : 0 ≤ longRatioGradientTail m omega :=
    longRatioGradientTail_nonneg m omega
  calc
    |Real.exp r - 1| ≤ |r| * Real.exp |r| := abs_exp_sub_one_le_abs_mul_exp_abs r
    _ ≤ ((d : ℝ) * longRatioGradientTail m omega) *
        Real.exp ((d : ℝ) * longRatioGradientTail m omega) := by
      exact mul_le_mul hr (Real.exp_le_exp.mpr hr)
        (Real.exp_pos _).le
        (mul_nonneg (Nat.cast_nonneg d) htail_nonneg)

/-- Average-normalized forward and reciprocal long-ratio deviations. -/
theorem tailCoefficient_average_ratio_bounds
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hsum : Summable (fun j : ℕ => if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j))
      else 0)) {y : Vec d} (hy : y ∈ cube d m) :
    |tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m omega y - 1| ≤
        ((d : ℝ) * longRatioGradientTail m omega) *
          Real.exp ((d : ℝ) * longRatioGradientTail m omega) ∧
      |tailCoefficient M L m omega y /
          tailCoefficientCubeAverage M L m omega - 1| ≤
        ((d : ℝ) * longRatioGradientTail m omega) *
          Real.exp ((d : ℝ) * longRatioGradientTail m omega) := by
  let U := Ch02.cubeDomain (originCube d (m : ℤ))
  let t := tailCoefficient M L m omega
  have ht : Continuous t := by
    unfold t tailCoefficient
    exact continuous_const.mul
      ((_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).div
        (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M (min m L) omega)
        (fun x => (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (min m L) omega x).ne'))
  have htpos : ∀ x, 0 < t x := by
    intro x
    unfold t tailCoefficient
    exact mul_pos (ahom_pos M (min m L))
      (div_pos (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x)
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (min m L) omega x))
  have hpair : ∀ x ∈ (U : Set (Vec d)), ∀ y ∈ (U : Set (Vec d)),
      |t x / t y - 1| ≤
        ((d : ℝ) * longRatioGradientTail m omega) *
          Real.exp ((d : ℝ) * longRatioGradientTail m omega) := by
    intro x hx y hy
    exact tailCoefficient_pair_ratio_sub_one_le_gradientTail M hmL omega hsum hx hy
  have havg : 0 < Ch02.average U t := by
    simpa [U, t, tailCoefficientCubeAverage] using
      tailCoefficientCubeAverage_pos M L m omega
  simpa [U, t, tailCoefficientCubeAverage] using
    tailAverage_ratio_bounds U t ht htpos hpair havg hy

/-- The two pointwise average-normalized deviations, in the literal sum and
orientation of `e.long.ratio.reg`. -/
theorem tailCoefficient_average_ratio_sum_le_gradientTail
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hsum : Summable (fun j : ℕ => if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j))
      else 0)) {y : Vec d} (hy : y ∈ cube d m) :
    |tailCoefficient M L m omega y /
          tailCoefficientCubeAverage M L m omega - 1| +
        |tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m omega y - 1| ≤
      2 * ((d : ℝ) * longRatioGradientTail m omega) *
        Real.exp ((d : ℝ) * longRatioGradientTail m omega) := by
  obtain ⟨hreverse, hforward⟩ :=
    tailCoefficient_average_ratio_bounds M hmL omega hsum hy
  linarith

/-- Supremum-norm form of the deterministic long-ratio estimate.  This is
the analytic core of `e.long.ratio.reg`; the good-event readout only has to
bound the literal `longRatioGradientTail`. -/
theorem tailCoefficient_supNorm_ratio_sum_le_gradientTail
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hsum : Summable (fun j : ℕ => if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j))
      else 0)) :
    supNormOn (cube d m) (fun y =>
        tailCoefficient M L m omega y /
          tailCoefficientCubeAverage M L m omega - 1) +
      supNormOn (cube d m) (fun y =>
        tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m omega y - 1) ≤
      2 * ((d : ℝ) * longRatioGradientTail m omega) *
        Real.exp ((d : ℝ) * longRatioGradientTail m omega) := by
  let A := ((d : ℝ) * longRatioGradientTail m omega) *
    Real.exp ((d : ℝ) * longRatioGradientTail m omega)
  have hforward : supNormOn (cube d m) (fun y =>
        tailCoefficient M L m omega y /
          tailCoefficientCubeAverage M L m omega - 1) ≤ A := by
    unfold supNormOn
    apply csSup_le
    · obtain ⟨y, hy⟩ := cube_nonempty (d := d) m
      exact ⟨|tailCoefficient M L m omega y /
        tailCoefficientCubeAverage M L m omega - 1|, y, hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (tailCoefficient_average_ratio_bounds M hmL omega hsum hy).2
  have hreverse : supNormOn (cube d m) (fun y =>
        tailCoefficientCubeAverage M L m omega /
          tailCoefficient M L m omega y - 1) ≤ A := by
    unfold supNormOn
    apply csSup_le
    · obtain ⟨y, hy⟩ := cube_nonempty (d := d) m
      exact ⟨|tailCoefficientCubeAverage M L m omega /
        tailCoefficient M L m omega y - 1|, y, hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (tailCoefficient_average_ratio_bounds M hmL omega hsum hy).1
  dsimp [A] at hforward hreverse ⊢
  linarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
