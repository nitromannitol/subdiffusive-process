module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization.LongRatio
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization

open Homogenization Homogenization.Book
open scoped BigOperators

noncomputable section

variable {d : ℕ}

private theorem shellGradient_continuous
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    Continuous (shellGradient g) := by
  unfold shellGradient
  apply continuous_pi
  intro i
  exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.deriv g).continuous.clm_apply
    continuous_const

private theorem euclideanNorm_shellGradient_continuous
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    Continuous (fun x => euclideanNorm (shellGradient g x)) := by
  rw [show (fun x => euclideanNorm (shellGradient g x)) =
      fun x => ‖HilbertVec.ofVec (shellGradient g x)‖ by
    funext x
    rw [euclideanNorm_eq_norm_ofVec]]
  exact continuous_norm.comp
    ((HilbertVec.ofVecL d).continuous.comp (shellGradient_continuous g))

private theorem shellControl_continuous
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) (j : ℕ) :
    Continuous (fun x => |g x| + (3 : ℝ) ^ j *
      euclideanNorm (shellGradient g x)) := by
  exact (continuous_abs.comp g.1.1.continuous).add
    (continuous_const.mul (euclideanNorm_shellGradient_continuous g))

private theorem bddAbove_abs_values_cube {m : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) :
    BddAbove {a : ℝ | ∃ x ∈ cube d m, a = |f x|} := by
  let Q := originCube d (m : ℤ)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      ((continuous_abs.comp hf).continuousOn)
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs, abs_abs] using!
    h.trans (le_max_right _ _)

private theorem abs_apply_le_supNormOn_cube {m : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) {x : Vec d} (hx : x ∈ cube d m) :
    |f x| ≤ supNormOn (cube d m) f := by
  unfold supNormOn
  exact le_csSup (bddAbove_abs_values_cube hf) ⟨x, hx, rfl⟩

private theorem cube_nonempty (m : ℕ) : (cube d m).Nonempty := by
  refine ⟨0, ?_⟩
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

private theorem supNormOn_cube_nonneg {m : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) : 0 ≤ supNormOn (cube d m) f := by
  obtain ⟨x, hx⟩ := cube_nonempty (d := d) m
  exact (abs_nonneg (f x)).trans (abs_apply_le_supNormOn_cube hf hx)

private theorem bddAbove_euclideanNorm_shellGradient_cube
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) (m : ℕ) :
    BddAbove {a : ℝ | ∃ x ∈ cube d m,
      a = euclideanNorm (shellGradient g x)} := by
  let Q := originCube d (m : ℤ)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      (euclideanNorm_shellGradient_continuous g).continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (euclideanNorm_nonneg _)] using! h.trans (le_max_right _ _)

private theorem vectorSupNormOn_shellGradient_nonneg
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) (m : ℕ) :
    0 ≤ vectorSupNormOn (cube d m) (shellGradient g) := by
  obtain ⟨x, hx⟩ := cube_nonempty (d := d) m
  unfold vectorSupNormOn
  exact (euclideanNorm_nonneg (shellGradient g x)).trans
    (le_csSup (bddAbove_euclideanNorm_shellGradient_cube g m) ⟨x, hx, rfl⟩)

private theorem scaled_gradientSup_le_goodFieldOne_atom
    (m q : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (3 : ℝ) ^ (m + q) *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + q))) ≤
      supNormOn (cube d (m + 1 + q)) (fun x =>
        |omega (m + q) x| + (3 : ℝ) ^ (m + q) *
          euclideanNorm (shellGradient (omega (m + q)) x)) := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (m + q) := by positivity
  rw [mul_comm]
  apply (le_div_iff₀ hpow).1
  unfold vectorSupNormOn
  apply csSup_le
  · obtain ⟨x, hx⟩ := cube_nonempty (d := d) m
    exact ⟨euclideanNorm (shellGradient (omega (m + q)) x), x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hscale : (m : ℤ) ≤ ((m + 1 + q : ℕ) : ℤ) := by
      exact_mod_cast (show m ≤ m + 1 + q by omega)
    have hxlarge : x ∈ cube d (m + 1 + q) :=
      openCubeSet_originCube_subset_of_scale_le hscale hx
    have hcontrol := abs_apply_le_supNormOn_cube
      (shellControl_continuous (omega (m + q)) (m + q)) hxlarge
    have hcontrol_nonneg : 0 ≤ |omega (m + q) x| +
        (3 : ℝ) ^ (m + q) *
          euclideanNorm (shellGradient (omega (m + q)) x) :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (euclideanNorm_nonneg _))
    rw [abs_of_nonneg hcontrol_nonneg] at hcontrol
    rw [le_div_iff₀ hpow]
    calc
      euclideanNorm (shellGradient (omega (m + q)) x) * (3 : ℝ) ^ (m + q) =
          (3 : ℝ) ^ (m + q) *
            euclideanNorm (shellGradient (omega (m + q)) x) := mul_comm _ _
      _ ≤ |omega (m + q) x| + (3 : ℝ) ^ (m + q) *
            euclideanNorm (shellGradient (omega (m + q)) x) :=
        le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ supNormOn (cube d (m + 1 + q)) (fun x =>
          |omega (m + q) x| + (3 : ℝ) ^ (m + q) *
            euclideanNorm (shellGradient (omega (m + q)) x)) := hcontrol

private theorem goodFieldOne_atom_nonneg
    (m q i : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    0 ≤ supNormOn (cube d (m + 1 + q)) (fun x =>
      |omega i x| + (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x)) :=
  supNormOn_cube_nonneg (shellControl_continuous (omega i) i)

private theorem three_rpow_eighth_le_two {s : ℝ} (hs : s ≤ 1 / 2) :
    (3 : ℝ) ^ (s / 8) ≤ 2 := by
  have hexponent : s / 8 ≤ (1 : ℝ) / 2 := by linarith
  have hmono : (3 : ℝ) ^ (s / 8) ≤ (3 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hsqrt : (3 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 3 :=
    (Real.sqrt_eq_rpow 3).symm
  have hsqrt_le : Real.sqrt 3 ≤ 2 :=
    calc
      Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  exact hmono.trans (hsqrt.trans_le hsqrt_le)

private theorem goodFieldOne_gradient_atom_le_geometric
    (m q : ℕ) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs : s ≤ 1 / 2) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    (3 : ℝ) ^ m *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + q))) ≤
      epsilon * ((2 : ℝ) / 3) ^ q := by
  have hfield :
      (∑ i ∈ Finset.Icc (m - q) (m + q),
        supNormOn (cube d (m + 1 + q)) (fun x =>
          |omega i x| + (3 : ℝ) ^ i *
            euclideanNorm (shellGradient (omega i) x))) ≤
        epsilon * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) := by
    simpa [translatedCube] using! hgood q
  have hmem : m + q ∈ Finset.Icc (m - q) (m + q) :=
    Finset.mem_Icc.mpr
      ⟨(Nat.sub_le m q).trans (Nat.le_add_right m q), le_rfl⟩
  have hatom :
      supNormOn (cube d (m + 1 + q)) (fun x =>
          |omega (m + q) x| + (3 : ℝ) ^ (m + q) *
            euclideanNorm (shellGradient (omega (m + q)) x)) ≤
        ∑ i ∈ Finset.Icc (m - q) (m + q),
          supNormOn (cube d (m + 1 + q)) (fun x =>
            |omega i x| + (3 : ℝ) ^ i *
              euclideanNorm (shellGradient (omega i) x)) := by
    exact Finset.single_le_sum
      (fun i _hi => goodFieldOne_atom_nonneg m q i omega) hmem
  have hscaled : (3 : ℝ) ^ (m + q) *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + q))) ≤
      epsilon * (3 : ℝ) ^ ((s * (q : ℝ)) / 8) :=
    (scaled_gradientSup_le_goodFieldOne_atom m q omega).trans (hatom.trans hfield)
  have hrpow : (3 : ℝ) ^ ((s * (q : ℝ)) / 8) =
      ((3 : ℝ) ^ (s / 8)) ^ q := by
    rw [show (s * (q : ℝ)) / 8 = (s / 8) * (q : ℝ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  have hrpow_le : (3 : ℝ) ^ ((s * (q : ℝ)) / 8) ≤ (2 : ℝ) ^ q := by
    rw [hrpow]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
      (three_rpow_eighth_le_two hs) q
  have hscaled' : (3 : ℝ) ^ (m + q) *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + q))) ≤
      epsilon * (2 : ℝ) ^ q :=
    hscaled.trans (mul_le_mul_of_nonneg_left hrpow_le hepsilon)
  have hpowq : (0 : ℝ) < (3 : ℝ) ^ q := by positivity
  have hrewrite : (3 : ℝ) ^ m *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + q))) =
      ((3 : ℝ) ^ (m + q) *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + q)))) /
          (3 : ℝ) ^ q := by
    rw [pow_add]
    field_simp
  rw [hrewrite]
  calc
    ((3 : ℝ) ^ (m + q) *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + q)))) /
          (3 : ℝ) ^ q ≤
        (epsilon * (2 : ℝ) ^ q) / (3 : ℝ) ^ q :=
      div_le_div_of_nonneg_right hscaled' hpowq.le
    _ = epsilon * ((2 : ℝ) / 3) ^ q := by
      rw [div_pow]
      ring

/-- Membership in `GoodFieldOne` makes the literal real gradient-tail family
summable; its `tsum` is therefore not Lean's junk value. -/
theorem summable_longRatioGradientTail_of_goodFieldOne
    (m : ℕ) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs : s ≤ 1 / 2) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    Summable (fun j : ℕ => if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j))
      else 0) := by
  let F : ℕ → ℝ := fun j => if m ≤ j then
    (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j)) else 0
  have hshift : Summable (fun q : ℕ => F (q + m)) := by
    have hnonneg : ∀ q : ℕ, 0 ≤ F (q + m) := by
      intro q
      dsimp [F]
      rw [if_pos (by omega : m ≤ q + m)]
      exact mul_nonneg (by positivity)
        (vectorSupNormOn_shellGradient_nonneg (omega (q + m)) m)
    have hdom : ∀ q : ℕ, F (q + m) ≤ epsilon * ((2 : ℝ) / 3) ^ q := by
      intro q
      dsimp [F]
      rw [if_pos (by omega : m ≤ q + m)]
      simpa only [Nat.add_comm] using!
        goodFieldOne_gradient_atom_le_geometric m q hepsilon hs omega hgood
    exact Summable.of_nonneg_of_le hnonneg hdom
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 : ℝ) / 3 < 1)).mul_left epsilon)
  exact (summable_nat_add_iff m).mp hshift

/-- The value half of the `GoodFieldOne` reading: the literal gradient tail is
at most `3 * epsilon`, uniformly in the scale and in `s <= 1/2`. -/
theorem longRatioGradientTail_le_three_mul_of_goodFieldOne
    (m : ℕ) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs : s ≤ 1 / 2) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    longRatioGradientTail m omega ≤ 3 * epsilon := by
  let F : ℕ → ℝ := fun j => if m ≤ j then
    (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j)) else 0
  let G : ℕ → ℝ := fun q => epsilon * ((2 : ℝ) / 3) ^ q
  have hF : Summable F :=
    summable_longRatioGradientTail_of_goodFieldOne m hepsilon hs omega hgood
  have hshift : Summable (fun q : ℕ => F (q + m)) :=
    (summable_nat_add_iff m).2 hF
  have hG : Summable G :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num : (2 : ℝ) / 3 < 1)).mul_left epsilon
  have hterm : ∀ q : ℕ, F (q + m) ≤ G q := by
    intro q
    dsimp [F, G]
    rw [if_pos (by omega : m ≤ q + m)]
    simpa only [Nat.add_comm] using!
      goodFieldOne_gradient_atom_le_geometric m q hepsilon hs omega hgood
  have htail : ∑' q : ℕ, F (q + m) ≤ ∑' q : ℕ, G q :=
    Summable.tsum_le_tsum hterm hshift hG
  have hGsum : ∑' q : ℕ, G q = 3 * epsilon := by
    unfold G
    rw [tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 : ℝ) / 3 < 1)]
    norm_num
    ring
  have hprefix : ∑ j ∈ Finset.range m, F j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    dsimp [F]
    rw [if_neg (Nat.not_le_of_lt (Finset.mem_range.mp hj))]
  have hsplit := hF.sum_add_tsum_nat_add m
  rw [hprefix, zero_add] at hsplit
  unfold longRatioGradientTail
  change ∑' j : ℕ, F j ≤ 3 * epsilon
  rw [hsplit, hGsum] at htail
  exact htail

/-- The two `L^infinity` deviations in `e.long.ratio.reg`. -/
def longRatioDeviation
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L m : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : ℝ :=
  supNormOn (cube d m) (fun y =>
      tailCoefficient M L m omega y /
        tailCoefficientCubeAverage M L m omega - 1) +
    supNormOn (cube d m) (fun y =>
      tailCoefficientCubeAverage M L m omega /
        tailCoefficient M L m omega y - 1)

/-- One explicit dimension-only constant for both conclusions of
`e.long.ratio.reg`. -/
def longRatioGoodEventConstant (d : ℕ) : ℝ :=
  max 3 (6 * (d : ℝ) * Real.exp (3 * (d : ℝ)))

theorem longRatioGoodEventConstant_pos (d : ℕ) :
    0 < longRatioGoodEventConstant d := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (le_max_left _ _)

/-- The manuscript's `C min {1,S_m}` estimate, conditional only on the first
frozen good-field condition. -/
theorem longRatioDeviation_le_constant_mul_min_of_goodFieldOne
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hs : s ≤ 1 / 2) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hgood : GoodFieldOne m 0 epsilon s omega) :
    longRatioDeviation M L m omega ≤
      longRatioGoodEventConstant d * min 1 (longRatioGradientTail m omega) := by
  let S := longRatioGradientTail m omega
  let E := Real.exp (3 * (d : ℝ))
  have hsum :=
    summable_longRatioGradientTail_of_goodFieldOne m hepsilon hs omega hgood
  have hdet := tailCoefficient_supNorm_ratio_sum_le_gradientTail
    M hmL omega hsum
  have hS0 : 0 ≤ S := longRatioGradientTail_nonneg m omega
  have hSε : S ≤ 3 * epsilon :=
    longRatioGradientTail_le_three_mul_of_goodFieldOne
      m hepsilon hs omega hgood
  have hS3 : S ≤ 3 := hSε.trans (by nlinarith only [hepsilon1])
  have hexp : Real.exp ((d : ℝ) * S) ≤ E := by
    apply Real.exp_le_exp.mpr
    simpa only [mul_comm] using!
      mul_le_mul_of_nonneg_left hS3 (Nat.cast_nonneg d)
  have hde : 0 ≤ (d : ℝ) * E :=
    mul_nonneg (Nat.cast_nonneg d) (Real.exp_pos _).le
  have hrough : longRatioDeviation M L m omega ≤ 2 * ((d : ℝ) * E) * S := by
    unfold longRatioDeviation
    calc
      supNormOn (cube d m) (fun y =>
            tailCoefficient M L m omega y /
              tailCoefficientCubeAverage M L m omega - 1) +
          supNormOn (cube d m) (fun y =>
            tailCoefficientCubeAverage M L m omega /
              tailCoefficient M L m omega y - 1) ≤
          2 * ((d : ℝ) * S) * Real.exp ((d : ℝ) * S) := by
        simpa only [S] using! hdet
      _ ≤ 2 * ((d : ℝ) * S) * E := by
        exact mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (by positivity)
            (mul_nonneg (Nat.cast_nonneg d) hS0))
      _ = 2 * ((d : ℝ) * E) * S := by ring
  have hcore : longRatioDeviation M L m omega ≤
      (6 * (d : ℝ) * E) * min 1 S := by
    by_cases hS1 : S ≤ 1
    · rw [min_eq_right hS1]
      exact hrough.trans (by
        apply mul_le_mul_of_nonneg_right _ hS0
        nlinarith only [hde])
    · have h1S : 1 ≤ S := le_of_not_ge hS1
      rw [min_eq_left h1S]
      simpa only [mul_one] using! hrough.trans (by
        calc
          2 * ((d : ℝ) * E) * S ≤ 2 * ((d : ℝ) * E) * 3 :=
            mul_le_mul_of_nonneg_left hS3
              (mul_nonneg (by norm_num) hde)
          _ = 6 * (d : ℝ) * E := by ring)
  have hmin0 : 0 ≤ min 1 S := le_min zero_le_one hS0
  exact hcore.trans <| by
    apply mul_le_mul_of_nonneg_right (le_max_right 3 (6 * (d : ℝ) * E)) hmin0

/-- On the actual frozen good event, the long gradient tail is summable. -/
theorem summable_longRatioGradientTail_of_mem_goodEvent
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) {s : ℝ}
    (hs : s ≤ 1 / 2) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (homega : omega ∈ goodEvent M none m 0 1 s) :
    Summable (fun j : ℕ => if m ≤ j then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega j))
      else 0) :=
  summable_longRatioGradientTail_of_goodFieldOne m zero_le_one hs omega homega.1

/-- Literal indicator form of `S_m 1_{G_m} <= C(d)`. -/
theorem indicatorValue_longRatioGradientTail_le_goodEventConstant
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) {s : ℝ}
    (hs : s ≤ 1 / 2) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    indicatorValue (goodEvent M none m 0 1 s)
        (longRatioGradientTail m) omega ≤ longRatioGoodEventConstant d := by
  by_cases homega : omega ∈ goodEvent M none m 0 1 s
  · rw [indicatorValue, if_pos homega]
    exact (longRatioGradientTail_le_three_mul_of_goodFieldOne
      m zero_le_one hs omega homega.1).trans <| by
        simpa only [mul_one] using! le_max_left 3
          (6 * (d : ℝ) * Real.exp (3 * (d : ℝ)))
  · rw [indicatorValue, if_neg homega]
    exact (longRatioGoodEventConstant_pos d).le

/-- Literal indicator form of the two-sided long-ratio display
`e.long.ratio.reg`. -/
theorem indicatorValue_longRatioDeviation_le_constant_mul_min
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hmL : m ≤ L)
    {s : ℝ} (hs : s ≤ 1 / 2)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    indicatorValue (goodEvent M none m 0 1 s)
        (longRatioDeviation M L m) omega ≤
      longRatioGoodEventConstant d * min 1 (longRatioGradientTail m omega) := by
  by_cases homega : omega ∈ goodEvent M none m 0 1 s
  · rw [indicatorValue, if_pos homega]
    exact longRatioDeviation_le_constant_mul_min_of_goodFieldOne
      M hmL zero_le_one le_rfl hs omega homega.1
  · rw [indicatorValue, if_neg homega]
    exact mul_nonneg (longRatioGoodEventConstant_pos d).le
      (le_min zero_le_one (longRatioGradientTail_nonneg m omega))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Localization
