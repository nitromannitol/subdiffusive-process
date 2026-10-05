module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMeasurableForcing
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellW1pMoment

@[expose] public section

/-!
# Joint measurability of the differentiated one-step shell forcing

The `PotentialField` carrier stores its first derivative as a continuous-map
coordinate.  Joint continuous evaluation of that coordinate, followed by the
finite shell sum and the exact exponential chain rule, makes the literal
forcing Jacobian jointly Borel in the sample and spatial variables.  This is
the Tonelli prerequisite for the cellwise fourth-moment aggregation in Step 1
of `l.one.step.upper` and `l.one.step.lower`.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- The stored derivative of one potential field is jointly continuous in
the field and the spatial point. -/
theorem continuous_potentialFieldDeriv_uncurry {d : ℕ} :
    Continuous fun q : _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d =>
      _root_.SubdiffusiveProcess.Model.PotentialField.deriv q.1 q.2 := by
  exact ContinuousEval.continuous_eval.comp
    (((continuous_subtype_val.comp continuous_fst).snd).prodMk continuous_snd)

/-- The finite suffix-block derivative is jointly Borel. -/
theorem measurable_oneStepShellDerivative_uncurry {d : ℕ} (n h : ℕ) :
    Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      oneStepShellDerivative n h q.1 q.2 := by
  unfold oneStepShellDerivative
  apply Finset.measurable_sum
  intro k _hk
  change Measurable ((fun q :
      _root_.SubdiffusiveProcess.Model.PotentialField d × Vec d =>
        _root_.SubdiffusiveProcess.Model.PotentialField.deriv q.1 q.2) ∘
      fun a : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d => (a.1 k, a.2))
  exact continuous_potentialFieldDeriv_uncurry.measurable.comp
    ((((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd))

/-- The spatial Frechet derivative of the centered suffix multiplier is
jointly Borel. -/
theorem measurable_fderiv_oneStepMultiplierAt_uncurry {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) :
    Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      fderiv ℝ (fun y => oneStepMultiplierAt M n h y q.1) q.2 := by
  by_cases hh : 0 < h
  · have heq : (fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
        fderiv ℝ (fun y => oneStepMultiplierAt M n h y q.1) q.2) =
        fun q => (oneStepMultiplierAt M n h q.2 q.1 + 1) •
          oneStepShellDerivative n h q.1 q.2 := by
      funext q
      rw [(hasFDerivAt_oneStepMultiplierAt M n h q.1 q.2 hh).fderiv]
      congr 1
      rw [oneStepMultiplierAt]
      have hn : (-1 : ℤ) ≤ (n : ℤ) := by omega
      have hnm : (n : ℤ) < ((n + h : ℕ) : ℤ) := by
        exact_mod_cast Nat.lt_add_of_pos_right hh
      rw [cutoffRatioMinusOne_eq_exp_shell M (n + h) (n : ℤ) q.1 q.2 hn hnm]
      have hdiff : ((((n + h : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) = h := by
        push_cast
        ring
      rw [hdiff]
      ring
    rw [heq]
    exact (measurable_oneStepMultiplierAt_uncurry M n h).add_const 1 |>.smul
      (measurable_oneStepShellDerivative_uncurry n h)
  · have hh0 : h = 0 := Nat.eq_zero_of_not_pos hh
    subst h
    have heq : (fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
        fderiv ℝ (fun y => oneStepMultiplierAt M n 0 y q.1) q.2) =
        fun _ => (0 : Vec d →L[ℝ] ℝ) := by
      funext q
      have hfun : (fun y => oneStepMultiplierAt M n 0 y q.1) =
          fun _ => (0 : ℝ) := by
        funext y
        rw [oneStepMultiplierAt, cutoffRatioMinusOne, aCutoffAtInt,
          ite_eq_right (not_lt.mpr (Int.natCast_nonneg n))]
        simp only [Nat.add_zero, Int.toNat_natCast]
        field_simp [ne_of_gt (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n q.1 y)]
        norm_num
      rw [hfun]
      exact (hasFDerivAt_const (x := q.2) (c := (0 : ℝ))).fderiv
    rw [heq]
    exact measurable_const

/-- Every literal Jacobian entry of the `W^{1,4}` forcing is jointly Borel. -/
theorem measurable_oneStepShellForcingW14_jacobian_uncurry {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (i j : Fin d) :
    Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      (oneStepShellForcingW14 M n h q.1 p Q hh).jacobian q.2 i j := by
  have hderiv := measurable_fderiv_oneStepMultiplierAt_uncurry M n h
  have hscaled : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      (p i : ℝ) • fderiv ℝ (fun y => oneStepMultiplierAt M n h y q.1) q.2 :=
    by simpa using! (measurable_const (a := (p i : ℝ))).smul hderiv
  have hcomp : Measurable fun q : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d =>
      (p i • fderiv ℝ (fun y => oneStepMultiplierAt M n h y q.1) q.2)
        (basisVec j) := by
    exact ((ContinuousLinearMap.apply ℝ ℝ) (basisVec j)).continuous.measurable.comp
      hscaled
  convert hcomp using 1
  funext q
  exact oneStepShellForcingW14_jacobian_apply
    M n h q.1 p Q hh q.2 i j

/-- Tonelli transport of the fixed-point fourth-moment estimate to an
arbitrary normalized cube.  The cutoff scale and the observation cube scale
are intentionally independent; this is the large-domain form needed before
restricting a Calderon--Zygmund solution to its source cells. -/
theorem lintegral_lintegral_oneStepShellForcingW14_jacobian_four_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (Q : TriadicCube d) (i j : Fin d) (hh : 0 < h)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega, ∫⁻ x,
        ‖(3 : ℝ) ^ n *
          |(oneStepShellForcingW14 M n h omega p Q hh
            ).jacobian x i j|‖ₑ ^ (4 : ℝ)
          ∂normalizedCubeMeasure Q ∂M.P.toMeasure ≤
      (ENNReal.ofReal
        (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
          (4 : ℝ) := by
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d → ℝ := fun q =>
    (3 : ℝ) ^ n *
      |(oneStepShellForcingW14 M n h q.1 p Q hh
        ).jacobian q.2 i j|
  have hX : Measurable X := by
    exact measurable_const.mul
      (measurable_oneStepShellForcingW14_jacobian_uncurry
        M n h p Q hh i j).norm
  have hjoint : AEMeasurable
      (Function.uncurry fun omega x => ‖X (omega, x)‖ₑ ^ (4 : ℝ))
      (M.P.toMeasure.prod (normalizedCubeMeasure Q)) := by
    simpa only [Function.uncurry_apply_pair] using!
      ((hX.enorm.pow_const (4 : ℝ)).aemeasurable)
  have hswap := lintegral_lintegral_swap hjoint
  rw [hswap]
  have hpoint : ∀ᵐ x ∂normalizedCubeMeasure Q,
      (∫⁻ omega, ‖X (omega, x)‖ₑ ^ (4 : ℝ) ∂M.P.toMeasure) ≤
        (ENNReal.ofReal
          (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
            (4 : ℝ) := by
    filter_upwards [ae_openCubeSet_normalizedCubeMeasure Q]
      with x hx
    have hnorm :=
      eLpNorm_parentScale_oneStepShellForcingW14_jacobian_four_le_delta
        M n h x x p Q i j hh hscale (by
          simp only [sub_self, openCubeSet, originCube,
            cubeScaleFactor, Pi.zero_apply]
          intro k
          have hpow : 0 < (3 : ℝ) ^ (n : ℤ) := zpow_pos (by norm_num) _
          have hleft : ((0 : ℝ) - 1 / 2) * (3 : ℝ) ^ (n : ℤ) < 0 := by
            nlinarith
          have hright : 0 < ((0 : ℝ) + 1 / 2) * (3 : ℝ) ^ (n : ℤ) := by
            nlinarith
          convert And.intro hleft hright using 1 <;> norm_num)
    have hpow := ENNReal.rpow_le_rpow hnorm (by norm_num : (0 : ℝ) ≤ 4)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (by simpa only [X] using!
        (hX.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)] at hpow
    norm_num only [ENNReal.toReal_ofNat] at hpow
    have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
    rw [hquarter] at hpow
    rw [ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)] at hpow
    simpa only [X, Prod.fst, Prod.snd, ENNReal.rpow_natCast] using hpow
  calc
    (∫⁻ x, ∫⁻ omega, ‖X (omega, x)‖ₑ ^ (4 : ℝ) ∂M.P.toMeasure
        ∂normalizedCubeMeasure Q) ≤
      ∫⁻ _x, (ENNReal.ofReal
        (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
          (4 : ℝ) ∂normalizedCubeMeasure Q :=
        lintegral_mono_ae hpoint
    _ = (ENNReal.ofReal
        (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
          (4 : ℝ) := by
      rw [lintegral_const]
      simp [normalizedCubeMeasure_apply_univ]

/-- Parent-scale specialization retained for the source-facing API. -/
theorem lintegral_lintegral_parentScale_oneStepShellForcingW14_jacobian_four_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (i j : Fin d) (hh : 0 < h)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega, ∫⁻ x,
        ‖(3 : ℝ) ^ n *
          |(oneStepShellForcingW14 M n h omega p (originCube d n) hh
            ).jacobian x i j|‖ₑ ^ (4 : ℝ)
          ∂normalizedCubeMeasure (originCube d n) ∂M.P.toMeasure ≤
      (ENNReal.ofReal
        (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
          (4 : ℝ) :=
  lintegral_lintegral_oneStepShellForcingW14_jacobian_four_le
    M n h p (originCube d n) i j hh hscale

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
