module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.CoefficientRatio
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.GoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS

@[expose] public section

/-!
# Hölder Step 3: reading a lower good scale on the parent suffix

`GoodFieldOne q z` controls increasingly large cubes as its annulus parameter
grows.  Consequently any good scale `q ≤ m` supplies genuine summability of
the gradient suffix on the scale-`m` parent cube.  This is the cross-scale
certificate needed before the `tsum` stored in `accumulatedError` can bound
finite cutoff suffixes.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder

open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance
open scoped BigOperators

noncomputable section

variable {L : ℕ}
attribute [local instance] Classical.propDecidable


private theorem shellGradient_continuous_cut {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    Continuous (shellGradient g) := by
  unfold shellGradient
  apply continuous_pi
  intro i
  exact (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g).continuous.clm_apply
    continuous_const

private theorem euclideanNorm_shellGradient_continuous_cut {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) :
    Continuous (fun x => euclideanNorm (shellGradient g x)) := by
  rw [show (fun x => euclideanNorm (shellGradient g x)) =
      fun x => ‖HilbertVec.ofVec (shellGradient g x)‖ by
    funext x
    rw [euclideanNorm_eq_norm_ofVec]]
  exact continuous_norm.comp
    ((HilbertVec.ofVecL d).continuous.comp (shellGradient_continuous_cut g))

private theorem shellControl_continuous_cut {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (j : ℕ) :
    Continuous (fun x => |g x| + (3 : ℝ) ^ j *
      euclideanNorm (shellGradient g x)) := by
  exact (continuous_abs.comp g.1.1.continuous).add
    (continuous_const.mul (euclideanNorm_shellGradient_continuous_cut g))

private theorem cube_nonempty_cut {d : ℕ} (m : ℕ) : (cube d m).Nonempty := by
  refine ⟨0, ?_⟩
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (m : ℤ) := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

private theorem bddAbove_abs_values_cube_cut {d : ℕ} {m : ℕ} {f : Vec d → ℝ}
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

private theorem abs_apply_le_supNormOn_cube_cut {d : ℕ} {m : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) {x : Vec d} (hx : x ∈ cube d m) :
    |f x| ≤ supNormOn (cube d m) f := by
  unfold supNormOn
  exact le_csSup (bddAbove_abs_values_cube_cut hf) ⟨x, hx, rfl⟩

private theorem supNormOn_cube_nonneg_cut {d : ℕ} {m : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) : 0 ≤ supNormOn (cube d m) f := by
  obtain ⟨x, hx⟩ := cube_nonempty_cut (d := d) m
  exact (abs_nonneg (f x)).trans (abs_apply_le_supNormOn_cube_cut hf hx)

private theorem bddAbove_euclideanNorm_shellGradient_cube_cut {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (m : ℕ) :
    BddAbove {a : ℝ | ∃ x ∈ cube d m,
      a = euclideanNorm (shellGradient g x)} := by
  let Q := originCube d (m : ℤ)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
      (euclideanNorm_shellGradient_continuous_cut g).continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  have hx' : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q (openCubeSet_subset_cubeSet Q hx)
  have h := hC x hx'
  simpa only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (euclideanNorm_nonneg _)] using! h.trans (le_max_right _ _)

private theorem vectorSupNormOn_shellGradient_nonneg_cut {d : ℕ}
    (g : _root_.SubdiffusiveProcess.Model.PotentialField d) (m : ℕ) :
    0 ≤ vectorSupNormOn (cube d m) (shellGradient g) := by
  obtain ⟨x, hx⟩ := cube_nonempty_cut (d := d) m
  unfold vectorSupNormOn
  exact (euclideanNorm_nonneg (shellGradient g x)).trans
    (le_csSup (bddAbove_euclideanNorm_shellGradient_cube_cut g m) ⟨x, hx, rfl⟩)

private theorem scaled_parentGradientSup_le_atom_cut {d : ℕ}
    (m t : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (3 : ℝ) ^ (m + t) *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + t))) ≤
      supNormOn (cube d (m + t + 1)) (fun x =>
        |omega (m + t) x| + (3 : ℝ) ^ (m + t) *
          euclideanNorm (shellGradient (omega (m + t)) x)) := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (m + t) := by positivity
  rw [mul_comm]
  apply (le_div_iff₀ hpow).1
  unfold vectorSupNormOn
  apply csSup_le
  · obtain ⟨x, hx⟩ := cube_nonempty_cut (d := d) m
    exact ⟨euclideanNorm (shellGradient (omega (m + t)) x), x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hscale : (m : ℤ) ≤ ((m + t + 1 : ℕ) : ℤ) := by exact_mod_cast (by omega : m ≤ m + t + 1)
    have hxlarge : x ∈ cube d (m + t + 1) :=
      openCubeSet_originCube_subset_of_scale_le hscale hx
    have hcontrol := abs_apply_le_supNormOn_cube_cut
      (shellControl_continuous_cut (omega (m + t)) (m + t)) hxlarge
    have hcontrol0 : 0 ≤ |omega (m + t) x| + (3 : ℝ) ^ (m + t) *
        euclideanNorm (shellGradient (omega (m + t)) x) :=
      add_nonneg (abs_nonneg _)
        (mul_nonneg (by positivity) (euclideanNorm_nonneg _))
    rw [abs_of_nonneg hcontrol0] at hcontrol
    rw [le_div_iff₀ hpow]
    calc
      euclideanNorm (shellGradient (omega (m + t)) x) * (3 : ℝ) ^ (m + t) =
          (3 : ℝ) ^ (m + t) *
            euclideanNorm (shellGradient (omega (m + t)) x) := mul_comm _ _
      _ ≤ |omega (m + t) x| + (3 : ℝ) ^ (m + t) *
            euclideanNorm (shellGradient (omega (m + t)) x) :=
        le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ _ := hcontrol

private theorem goodFieldOne_atom_nonneg_cut {d : ℕ}
    (r i : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ supNormOn (cube d r) (fun x =>
      |omega i x| + (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x)) :=
  supNormOn_cube_nonneg_cut (shellControl_continuous_cut (omega i) i)

private theorem three_rpow_eighth_le_two_cut {s : ℝ} (hs : s ≤ 1 / 2) :
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

/-- One parent-suffix atom read from a lower good scale. -/
theorem parentGradientAtom_le_of_goodFieldOne_cut {d : ℕ}
    {q m t : ℕ} (hqm : q ≤ m) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs : s ≤ 1 / 2) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne q 0 epsilon s omega) :
    (3 : ℝ) ^ m *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + t))) ≤
      epsilon * (2 : ℝ) ^ (m - q) * ((2 : ℝ) / 3) ^ t := by
  let J := m - q + t
  have hqJ : q + J = m + t := by dsimp [J]; omega
  let A : ℕ → ℝ := fun i => supNormOn (cube d (q + 1 + J)) (fun x =>
    |omega i x| + (3 : ℝ) ^ i * euclideanNorm (shellGradient (omega i) x))
  have hzeroCube : translatedCube d ((q : ℤ) + 1 + (J : ℤ)) 0 =
      cube d ((q : ℤ) + 1 + (J : ℤ)) := by
    ext x
    simp [translatedCube]
  have hfield : (∑ i ∈ Finset.Icc (q - J) (q + J), A i) ≤
      epsilon * (3 : ℝ) ^ ((s * (J : ℝ)) / 8) := by
    have hJ := hgood J
    rw [hzeroCube] at hJ
    simpa only [A] using! hJ
  have hcube : q + 1 + J = m + t + 1 := by dsimp [J]; omega
  have hmem : m + t ∈ Finset.Icc (q - J) (q + J) := by
    rw [hqJ]
    exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hA0 : ∀ i, 0 ≤ A i := fun i =>
    goodFieldOne_atom_nonneg_cut (q + 1 + J) i omega
  have hatomA : A (m + t) ≤ ∑ i ∈ Finset.Icc (q - J) (q + J), A i :=
    Finset.single_le_sum (fun i _hi => hA0 i) hmem
  have hcubeZ : (q : ℤ) + 1 + (J : ℤ) = (m : ℤ) + (t : ℤ) + 1 := by
    exact_mod_cast hcube
  have hAeq : A (m + t) = supNormOn (cube d (m + t + 1)) (fun x =>
      |omega (m + t) x| + (3 : ℝ) ^ (m + t) *
        euclideanNorm (shellGradient (omega (m + t)) x)) := by
    dsimp only [A]
    rw [hcubeZ]
  have hatom : supNormOn (cube d (m + t + 1)) (fun x =>
        |omega (m + t) x| + (3 : ℝ) ^ (m + t) *
          euclideanNorm (shellGradient (omega (m + t)) x)) ≤
      ∑ i ∈ Finset.Icc (q - J) (q + J), A i := by
    rw [← hAeq]
    exact hatomA
  have hscaled : (3 : ℝ) ^ (m + t) *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + t))) ≤
      epsilon * (3 : ℝ) ^ ((s * (J : ℝ)) / 8) :=
    (scaled_parentGradientSup_le_atom_cut m t omega).trans (hatom.trans hfield)
  have hrpow : (3 : ℝ) ^ ((s * (J : ℝ)) / 8) =
      ((3 : ℝ) ^ (s / 8)) ^ J := by
    rw [show s * (J : ℝ) / 8 = (s / 8) * (J : ℝ) by ring,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  have htwo : (3 : ℝ) ^ ((s * (J : ℝ)) / 8) ≤ (2 : ℝ) ^ J := by
    rw [hrpow]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
      (three_rpow_eighth_le_two_cut hs) J
  have hscaled' : (3 : ℝ) ^ (m + t) *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + t))) ≤
      epsilon * (2 : ℝ) ^ J :=
    hscaled.trans (mul_le_mul_of_nonneg_left htwo hepsilon)
  have hpow : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
  have hre : (3 : ℝ) ^ m *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + t))) =
      ((3 : ℝ) ^ (m + t) *
        vectorSupNormOn (cube d m) (shellGradient (omega (m + t)))) /
          (3 : ℝ) ^ t := by
    rw [pow_add]
    field_simp
  rw [hre]
  calc
    _ ≤ (epsilon * (2 : ℝ) ^ J) / (3 : ℝ) ^ t :=
      div_le_div_of_nonneg_right hscaled' hpow.le
    _ = epsilon * (2 : ℝ) ^ (m - q) * ((2 : ℝ) / 3) ^ t := by
      dsimp [J]
      rw [pow_add, div_pow]
      ring

/-- A good scale anywhere below the parent makes the parent's literal
gradient-tail family summable. -/
theorem summable_parentGradientTail_of_goodFieldOne_cut {d : ℕ}
    {q m : ℕ} (hqm : q ≤ m) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs : s ≤ 1 / 2) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne q 0 epsilon s omega) :
    Summable (fun i : ℕ => if m ≤ i then
      (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega i)) else 0) := by
  let F : ℕ → ℝ := fun i => if m ≤ i then
    (3 : ℝ) ^ m * vectorSupNormOn (cube d m) (shellGradient (omega i)) else 0
  have hshift : Summable (fun t : ℕ => F (t + m)) := by
    refine Summable.of_nonneg_of_le
      (f := fun t => epsilon * (2 : ℝ) ^ (m - q) * ((2 : ℝ) / 3) ^ t) ?_ ?_ ?_
    · intro t
      dsimp [F]
      rw [ite_eq_left (by omega : m ≤ t + m)]
      exact mul_nonneg (by positivity)
        (vectorSupNormOn_shellGradient_nonneg_cut (omega (t + m)) m)
    · intro t
      dsimp [F]
      rw [ite_eq_left (by omega : m ≤ t + m)]
      simpa only [Nat.add_comm] using!
        parentGradientAtom_le_of_goodFieldOne_cut hqm hepsilon hs omega hgood
    · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 : ℝ) / 3 < 1)).mul_left
          (epsilon * (2 : ℝ) ^ (m - q))
  exact (summable_nat_add_iff m).mp hshift

private theorem vectorSupNormOn_translatedCube_shellGradient_cut {d : ℕ}
    (m i : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    vectorSupNormOn (translatedCube d (m : ℤ) z) (shellGradient (omega i)) =
      vectorSupNormOn (cube d m)
        (shellGradient (translatePotentialSample z omega i)) := by
  unfold vectorSupNormOn
  congr 1
  ext r
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by
      simp only [translatePotentialSample, shellGradient_translate]
      rw [add_comm z y]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨z + y, ⟨y, hy, rfl⟩, by
      simp only [translatePotentialSample, shellGradient_translate]
      rw [add_comm z y]⟩

/-- The translated literal suffix is the centered `LongRatio` carrier of the
translated sample. -/
theorem translatedGradientSuffix_eq_longRatioGradientTail_cut {d : ℕ}
    (m : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (∑' i : ℕ, if m ≤ i then
      (3 : ℝ) ^ m *
        vectorSupNormOn (translatedCube d (m : ℤ) z) (shellGradient (omega i))
      else 0) =
      Section6Localization.longRatioGradientTail m
        (translatePotentialSample z omega) := by
  unfold Section6Localization.longRatioGradientTail
  congr 1
  funext i
  split
  · congr 1
    exact vectorSupNormOn_translatedCube_shellGradient_cut m i z omega
  · rfl

/-- Accumulated error controls the translated `LongRatio` suffix whenever a
lower good scale has supplied the summability certificate. -/
theorem longRatioGradientTail_translate_le_accumulatedError_cut {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Section6Localization.longRatioGradientTail m
        (translatePotentialSample z omega) ≤
      accumulatedError M cutoff m z s omega := by
  rw [← translatedGradientSuffix_eq_longRatioGradientTail_cut]
  exact gradientSuffix_le_accumulatedError M cutoff s m z omega

theorem longRatioGradientTail_le_accumulatedError_zero_cut {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (cutoff : Option ℕ)
    (s : ℝ) (m : ℕ) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Section6Localization.longRatioGradientTail m omega ≤
      accumulatedError M cutoff m 0 s omega := by
  simpa only [translatePotentialSample_zero] using!
    longRatioGradientTail_translate_le_accumulatedError_cut
      M cutoff s m 0 omega

/-- Translated-parent version consumed by the stopped spatial argument. -/
theorem summable_translatedParentGradientTail_of_goodFieldOne_cut {d : ℕ}
    {q m : ℕ} (hqm : q ≤ m) {epsilon s : ℝ} (hepsilon : 0 ≤ epsilon)
    (hs : s ≤ 1 / 2) (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hgood : GoodFieldOne q z epsilon s omega) :
    Summable (fun i : ℕ => if m ≤ i then
      (3 : ℝ) ^ m *
        vectorSupNormOn (translatedCube d (m : ℤ) z) (shellGradient (omega i))
      else 0) := by
  have hgood0 : GoodFieldOne q 0 epsilon s (translatePotentialSample z omega) :=
    (goodFieldOne_translatePotentialSample q 0 epsilon s z omega).2 (by
      simpa only [add_zero] using! hgood)
  have hsum := summable_parentGradientTail_of_goodFieldOne_cut
    hqm hepsilon hs (translatePotentialSample z omega) hgood0
  convert hsum using 1
  funext i
  split
  · congr 1
    exact vectorSupNormOn_translatedCube_shellGradient_cut m i z omega
  · rfl

/-- A strict subunit density of failures leaves at least one good scale in a
nontrivial interval.  This is the finite combinatorial read used twice in
`e.ratio.of.bs`, at the centre `z` and at the origin. -/
theorem exists_goodEvent_of_badCount_lt_cut {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (epsilon s lambda : ℝ)
    {n m : ℕ} (hnm : n < m) (hlambda : lambda < 1)
    (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hbad : (∑ j ∈ Finset.Icc n m,
        (1 - if omega ∈ goodEvent M (some L) j z epsilon s then (1 : ℝ) else 0)) <
      1 + lambda * ((m : ℝ) - (n : ℝ))) :
    ∃ q ∈ Finset.Icc n m, omega ∈ goodEvent M (some L) q z epsilon s := by
  by_contra hnone
  push Not at hnone
  have hsum : (∑ j ∈ Finset.Icc n m,
      (1 - if omega ∈ goodEvent M (some L) j z epsilon s then (1 : ℝ) else 0)) =
      ((Finset.Icc n m).card : ℝ) := by
    calc
      _ = ∑ _j ∈ Finset.Icc n m, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ite_eq_right (hnone j hj)]
        norm_num
      _ = ((Finset.Icc n m).card : ℝ) := by simp
  have hcard : ((Finset.Icc n m).card : ℝ) =
      (m : ℝ) - (n : ℝ) + 1 := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega : n ≤ m + 1), Nat.cast_add]
    norm_num
    ring
  rw [hsum, hcard] at hbad
  have hnmR : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hgap : 0 < (m : ℝ) - (n : ℝ) := by linarith
  nlinarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.RowsHolder
