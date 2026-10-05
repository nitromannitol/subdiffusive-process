module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepScales
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCumulantBound

@[expose] public section

open MeasureTheory Homogenization

/-!
# Deterministic closure of the Section 5 one-step variational bounds

This file formalizes Step 4 of the one-step upper and lower proofs at
`l.one.step.upper` and `l.one.step.lower` and `l.one.step.upper` and `l.one.step.lower`.  The analytic work in the first
three steps produces a finite-volume cell coefficient and a penultimate
variational inequality.  The lemmas here insert the finite-volume comparison,
use `tauSq <= delta^2` and `delta * h <= 1`, and obtain the exact multiplicative
one-step forms.

The statements are scalar and deterministic.  They do not encode any missing
corrector, localization, or homogenization estimate as an assumption package.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The stationary projected energy in the common leading term of the upper
and lower one-step variational arguments. -/
def oneStepProjectedEnergy {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h) : ℝ :=
  ‖oneStepPotentialProjection M n h p hh‖ ^ 2

theorem oneStepProjectedEnergy_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h) :
    0 ≤ oneStepProjectedEnergy M n h p hh := by
  exact sq_nonneg _

/-- The stationary potential energy is bounded by the full suffix forcing
energy. -/
theorem oneStepProjectedEnergy_le_forcingEnergy {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h) :
    oneStepProjectedEnergy M n h p hh ≤
      ‖oneStepOriginForcingL2 M n h p hh‖ ^ 2 := by
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_oneStepPotentialProjection_le M n h p hh) 2

/-- The square norm of the literal vector forcing is the scalar suffix energy
times the Euclidean square norm of the probe. -/
theorem norm_oneStepOriginForcingL2_sq {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h) :
    ‖oneStepOriginForcingL2 M n h p hh‖ ^ 2 =
      ((oneShellCenteredExpTwoMoment M) ^ h - 1) *
        Homogenization.vecNormSq p := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  have hae : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      inner ℝ
        ((oneStepOriginForcingL2 M n h p hh :
          _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega)
        ((oneStepOriginForcingL2 M n h p hh :
          _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega)) =ᵐ[M.P.toMeasure]
      fun omega => (oneStepOriginMultiplier M n h omega) ^ 2 * vecNormSq p := by
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp
      (memLp_two_oneStepOriginForcing M n h p hh)] with omega homega
    change ((oneStepOriginForcingL2 M n h p hh :
      _root_.SubdiffusiveProcess.Model.PotentialSample d → HilbertVec d) omega) = _ at homega
    rw [homega]
    change vecNormSq (oneStepOriginMultiplier M n h omega • p) =
      oneStepOriginMultiplier M n h omega ^ 2 * vecNormSq p
    exact vecNormSq_smul _ _
  rw [MeasureTheory.integral_congr_ae hae]
  rw [MeasureTheory.integral_mul_const]
  rw [integral_oneStepOriginMultiplier_sq M n h hh]

/-- For a unit probe, the stationary projected energy is bounded by the exact
scalar suffix variance. -/
theorem oneStepProjectedEnergy_le_suffixVariance {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h)
    (hp : Homogenization.vecNormSq p = 1) :
    oneStepProjectedEnergy M n h p hh ≤
      (oneShellCenteredExpTwoMoment M) ^ h - 1 := by
  calc
    oneStepProjectedEnergy M n h p hh ≤
        ‖oneStepOriginForcingL2 M n h p hh‖ ^ 2 :=
      oneStepProjectedEnergy_le_forcingEnergy M n h p hh
    _ = ((oneShellCenteredExpTwoMoment M) ^ h - 1) *
        Homogenization.vecNormSq p :=
      norm_oneStepOriginForcingL2_sq M n h p hh
    _ = (oneShellCenteredExpTwoMoment M) ^ h - 1 := by rw [hp, mul_one]

/-- Exact Weyl energy split for the one-step forcing: the scalar suffix
variance is the sum of the stationary potential energy and the squared norm
of its solenoidal remainder. -/
theorem oneStepProjectedEnergy_add_solenoidalRemainder_eq_suffixVariance
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h)
    (hp : Homogenization.vecNormSq p = 1) :
    oneStepProjectedEnergy M n h p hh +
        ‖oneStepOriginForcingL2 M n h p hh -
          oneStepPotentialProjection M n h p hh‖ ^ 2 =
      (oneShellCenteredExpTwoMoment M) ^ h - 1 := by
  let := potentialSequenceVAddInvariant M
  let F := oneStepOriginForcingL2 M n h p hh
  let S := Stationary.stationaryPotentialSubspace
    (mu := M.P.toMeasure) (d := d)
  have hcomp : Sᗮ.starProjection F = F - S.starProjection F := by
    rw [Submodule.starProjection_orthogonal']
    rfl
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection F S
  rw [hcomp] at hpyth
  change ‖S.starProjection F‖ ^ 2 + ‖F - S.starProjection F‖ ^ 2 = _
  rw [← hpyth]
  exact (norm_oneStepOriginForcingL2_sq M n h p hh).trans (by rw [hp, mul_one])

/-- The exact stationary forcing energy has the manuscript's logarithmic
one-step expansion.  The remaining sharp `1 / d` factor belongs solely to
the stationary potential projection. -/
theorem abs_log_oneStepOriginForcing_energy_add_one_sub_two_tauSq_mul_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h)
    (hp : Homogenization.vecNormSq p = 1) :
    |Real.log (‖oneStepOriginForcingL2 M n h p hh‖ ^ 2 + 1) -
        2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ)| ≤
      256 * M.delta ^ 4 * (h : ℝ) := by
  rw [norm_oneStepOriginForcingL2_sq M n h p hh, hp, mul_one,
    sub_add_cancel]
  exact abs_log_oneShellCentered_pow_sub_two_tauSq_mul_le M h

/-- The stationary potential projection is bounded by the exact exponential
of the one-step cumulant. -/
theorem oneStepProjectedEnergy_le_exp_cumulant_sub_one {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h)
    (hp : Homogenization.vecNormSq p = 1) :
    oneStepProjectedEnergy M n h p hh ≤
      Real.exp ((h : ℝ) * oneStepCumulant M) - 1 := by
  calc
    oneStepProjectedEnergy M n h p hh ≤
        (oneShellCenteredExpTwoMoment M) ^ h - 1 :=
      oneStepProjectedEnergy_le_suffixVariance M n h p hh hp
    _ = Real.exp ((h : ℝ) * oneStepCumulant M) - 1 := by
      rw [oneShellCenteredExpTwoMoment_eq_exp_oneStepCumulant,
        ← Real.exp_nat_mul]

/-- The completed unconditional transport of the fourth-order cumulant bound
to the stationary-projection carrier.  It records exactly what projection
contraction supplies before the separate spectral `1 / d` trace identity. -/
theorem log_oneStepProjectedEnergy_add_one_mem_Icc {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h)
    (hp : Homogenization.vecNormSq p = 1) :
    Real.log (oneStepProjectedEnergy M n h p hh + 1) ∈
      Set.Icc 0
        (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) +
          256 * M.delta ^ 4 * (h : ℝ)) := by
  have henergy0 : 0 ≤ oneStepProjectedEnergy M n h p hh :=
    oneStepProjectedEnergy_nonneg M n h p hh
  have hone : 1 ≤ oneStepProjectedEnergy M n h p hh + 1 := by linarith
  have hleftPos : 0 < oneStepProjectedEnergy M n h p hh + 1 :=
    zero_lt_one.trans_le hone
  have hcompare : oneStepProjectedEnergy M n h p hh + 1 ≤
      (oneShellCenteredExpTwoMoment M) ^ h := by
    linarith [oneStepProjectedEnergy_le_suffixVariance M n h p hh hp]
  have hlogCompare :
      Real.log (oneStepProjectedEnergy M n h p hh + 1) ≤
        Real.log ((oneShellCenteredExpTwoMoment M) ^ h) :=
    Real.log_le_log hleftPos hcompare
  have hblock := abs_log_oneShellCentered_pow_sub_two_tauSq_mul_le M h
  rw [abs_le] at hblock
  exact ⟨Real.log_nonneg hone, hlogCompare.trans (by linarith [hblock.2])⟩

/-- Exponential form of the cumulant envelope on the projected energy. -/
theorem oneStepProjectedEnergy_le_exp_two_tauSq_add_error_sub_one {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h)
    (hp : Homogenization.vecNormSq p = 1) :
    oneStepProjectedEnergy M n h p hh ≤
      Real.exp
        (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) +
          256 * M.delta ^ 4 * (h : ℝ)) - 1 := by
  have hlog :=
    (log_oneStepProjectedEnergy_add_one_mem_Icc M n h p hh hp).2
  have henergyPos : 0 < oneStepProjectedEnergy M n h p hh + 1 := by
    have henergy0 := oneStepProjectedEnergy_nonneg M n h p hh
    linarith
  have hexp :
      oneStepProjectedEnergy M n h p hh + 1 ≤
        Real.exp
          (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) +
            256 * M.delta ^ 4 * (h : ℝ)) := by
    calc
      oneStepProjectedEnergy M n h p hh + 1 =
          Real.exp (Real.log (oneStepProjectedEnergy M n h p hh + 1)) :=
        (Real.exp_log henergyPos).symm
      _ ≤ Real.exp
          (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) +
            256 * M.delta ^ 4 * (h : ℝ)) := Real.exp_le_exp.mpr hlog
  linarith

/-- On the manuscript's one-step range `h ≤ delta⁻¹`, the stationary
projected energy has the linear scale bound needed by the corrector estimates. -/
theorem oneStepProjectedEnergy_le_linear_scale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h)
    (hp : Homogenization.vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    oneStepProjectedEnergy M n h p hh ≤
      66 * Real.exp 33 * M.delta ^ 2 * (h : ℝ) := by
  let x : ℝ :=
    2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (h : ℝ) +
      256 * M.delta ^ 4 * (h : ℝ)
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
  have htau0 : 0 ≤ _root_.SubdiffusiveProcess.Model.tauSq M.P := M.G4.tauSq_pos.le
  have hlog : Real.log 2 / 2 ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M.P ≤ M.delta ^ 2 := by
    exact (tauSq_le_delta_sq M).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hlog (sq_nonneg M.delta))
  have hdeltaSq : M.delta ^ 2 ≤ 1 / 4 := by
    nlinarith [M.shellPrefix.delta_le_half]
  have hdeltaFour : M.delta ^ 4 ≤ M.delta ^ 2 / 4 := by
    nlinarith [sq_nonneg (M.delta ^ 2)]
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxLinear : x ≤ 66 * M.delta ^ 2 * (h : ℝ) := by
    dsimp [x]
    have htauMul := mul_le_mul_of_nonneg_right htau hh0
    have hfourMul := mul_le_mul_of_nonneg_right hdeltaFour hh0
    nlinarith
  have hdeltaH : M.delta * (h : ℝ) ≤ 1 := by
    have hscale' : (h : ℝ) ≤ 1 / M.delta := by
      simpa [one_div] using hscale
    have := (le_div_iff₀ hdelta).mp hscale'
    nlinarith
  have hx33 : x ≤ 33 := by
    have hdeltaHalf := M.shellPrefix.delta_le_half
    calc
      x ≤ 66 * M.delta ^ 2 * (h : ℝ) := hxLinear
      _ = 66 * M.delta * (M.delta * (h : ℝ)) := by ring
      _ ≤ 33 := by nlinarith
  have hexpRemainder : Real.exp x - 1 ≤ x * Real.exp x := by
    have hbase := Real.add_one_le_exp (-x)
    have hmul := mul_le_mul_of_nonneg_right hbase (Real.exp_pos x).le
    rw [← Real.exp_add] at hmul
    norm_num at hmul
    linarith
  calc
    oneStepProjectedEnergy M n h p hh ≤ Real.exp x - 1 := by
      simpa [x] using
        oneStepProjectedEnergy_le_exp_two_tauSq_add_error_sub_one M n h p hh hp
    _ ≤ x * Real.exp x := hexpRemainder
    _ ≤ (66 * M.delta ^ 2 * (h : ℝ)) * Real.exp 33 := by
      exact mul_le_mul hxLinear (Real.exp_le_exp.mpr hx33)
        (Real.exp_pos _).le (by positivity)
    _ = 66 * Real.exp 33 * M.delta ^ 2 * (h : ℝ) := by ring

/-- Norm form of the stationary-projection estimate on the manuscript's
one-step range. -/
theorem norm_oneStepPotentialProjection_le_sqrt_scale {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Homogenization.Vec d) (hh : 0 < h)
    (hp : Homogenization.vecNormSq p = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ‖oneStepPotentialProjection M n h p hh‖ ≤
      Real.sqrt (66 * Real.exp 33) * M.delta * Real.sqrt (h : ℝ) := by
  have hconst : 0 ≤ 66 * Real.exp 33 := by positivity
  have hhreal : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
  apply le_of_sq_le_sq
  · change oneStepProjectedEnergy M n h p hh ≤
      (Real.sqrt (66 * Real.exp 33) * M.delta * Real.sqrt (h : ℝ)) ^ 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hconst, Real.sq_sqrt hhreal]
    exact oneStepProjectedEnergy_le_linear_scale M n h p hh hp hscale
  · exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) M.shellPrefix.delta_pos.le)
      (Real.sqrt_nonneg _)

/-- A common constant sufficient for both final variational closures. -/
def oneStepVariationalConst (A B : ℝ) : ℝ :=
  4 * A + B * (2 + 2 * A)

theorem oneStepVariationalConst_pos {A B : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) :
    0 < oneStepVariationalConst A B := by
  unfold oneStepVariationalConst
  positivity

private theorem one_step_numerical_bounds {delta tau h L d : ℝ}
    (hdelta : 0 < delta) (hhalf : delta ≤ 1 / 2)
    (htau0 : 0 ≤ tau) (htau : tau ≤ delta ^ 2)
    (hh : 0 ≤ h) (hscale : delta * h ≤ 1)
    (hL : 1 / 2 ≤ L) (hd : 2 ≤ d) :
    tau * h / d ≤ 1 / 4 ∧
      delta ^ 4 * h ^ 2 ≤ delta ^ 2 ∧
      delta ^ 15 ≤ 2 * (delta ^ 2 * L) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hT0 : 0 ≤ tau * h / d := div_nonneg (mul_nonneg htau0 hh) hdpos.le
  have hdT : d * (tau * h / d) = tau * h := by field_simp
  have htauh : tau * h ≤ delta ^ 2 * h :=
    mul_le_mul_of_nonneg_right htau hh
  have hdeltah : delta ^ 2 * h = delta * (delta * h) := by ring
  have hdeltaProduct : delta * (delta * h) ≤ delta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale hdelta.le
  have hT : tau * h / d ≤ 1 / 4 := by
    nlinarith
  have hsq : (delta * h) ^ 2 ≤ 1 := by
    have hdh0 : 0 ≤ delta * h := mul_nonneg hdelta.le hh
    nlinarith [sq_nonneg (1 - delta * h)]
  have hdelta4 : delta ^ 4 * h ^ 2 ≤ delta ^ 2 := by
    have hre : delta ^ 4 * h ^ 2 = delta ^ 2 * (delta * h) ^ 2 := by ring
    rw [hre]
    exact mul_le_of_le_one_right (sq_nonneg delta) hsq
  have hdeltaOne : delta ≤ 1 := hhalf.trans (by norm_num)
  have hpow : delta ^ 15 ≤ delta ^ 2 :=
    pow_le_pow_of_le_one hdelta.le hdeltaOne (by norm_num)
  have hLscale : delta ^ 2 ≤ 2 * (delta ^ 2 * L) := by
    have hdeltaSq : 0 ≤ delta ^ 2 := sq_nonneg delta
    nlinarith
  exact ⟨hT, hdelta4, hpow.trans hLscale⟩

/-- Close the one-step upper estimate from the penultimate primal
finite-volume inequality and the finite-volume coefficient comparison.

This is exactly the scalar algebra at `l.one.step.upper` and `l.one.step.lower`; the
penultimate inequality itself remains the output of Steps 1--3. -/
theorem one_step_upper_of_penultimate
    {delta tau h L d A B next previous cell : ℝ}
    (hdelta : 0 < delta) (hhalf : delta ≤ 1 / 2)
    (htau0 : 0 ≤ tau) (htau : tau ≤ delta ^ 2)
    (hh : 0 ≤ h) (hscale : delta * h ≤ 1)
    (hL : 1 / 2 ≤ L) (hd : 2 ≤ d)
    (hA : 0 < A) (hB : 0 ≤ B) (hprevious : 0 ≤ previous)
    (hcell : cell ≤ (1 + B * delta ^ 2 * L) * previous)
    (hpenultimate :
      (1 / 2 : ℝ) * next ≤
        (1 / 2 - tau * h / d + A * delta ^ 4 * h ^ 2) * cell +
          A * delta ^ 15 * previous) :
    next ≤ previous *
      (1 - 2 * tau * h / d +
        oneStepVariationalConst A B * delta ^ 4 * h ^ 2 +
        oneStepVariationalConst A B * delta ^ 2 * L) := by
  obtain ⟨hT, hX, hdelta15⟩ := one_step_numerical_bounds
    hdelta hhalf htau0 htau hh hscale hL hd
  let X : ℝ := delta ^ 4 * h ^ 2
  let Y : ℝ := delta ^ 2 * L
  let T : ℝ := tau * h / d
  let C : ℝ := oneStepVariationalConst A B
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hX1 : X ≤ 1 := hX.trans (by nlinarith [sq_nonneg delta])
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT' : T ≤ 1 / 4 := hT
  have hfactor0 : 0 ≤ 1 / 2 - T + A * X := by
    nlinarith [mul_nonneg hA.le hX0]
  have hAXle : A * X ≤ A := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hX1 hA.le
  have hfactor2 : 2 * (1 / 2 - T + A * X) ≤ 2 + 2 * A := by
    linarith
  have hcellStep :
      (1 / 2 - T + A * X) * cell ≤
        (1 / 2 - T + A * X) * ((1 + B * Y) * previous) :=
    mul_le_mul_of_nonneg_left (by simpa [Y, mul_assoc] using hcell) hfactor0
  have hAX : 2 * A * X ≤ C * X := by
    have hAC : 2 * A ≤ C := by
      dsimp [C, oneStepVariationalConst]
      nlinarith [mul_nonneg hB (by nlinarith : 0 ≤ 2 + 2 * A)]
    exact mul_le_mul_of_nonneg_right hAC hX0
  have hBY : B * Y * (2 * (1 / 2 - T + A * X)) ≤
      B * (2 + 2 * A) * Y := by
    have hBY0 : 0 ≤ B * Y := mul_nonneg hB hY0
    have hmul := mul_le_mul_of_nonneg_left hfactor2 hBY0
    convert hmul using 1
    all_goals ring
  have htail : 2 * A * delta ^ 15 ≤ 4 * A * Y := by
    change 2 * A * delta ^ 15 ≤ 4 * A * (delta ^ 2 * L)
    have hmul := mul_le_mul_of_nonneg_left hdelta15 (by positivity : 0 ≤ 2 * A)
    convert hmul using 1
    all_goals ring
  have herrorY : B * Y * (2 * (1 / 2 - T + A * X)) +
      2 * A * delta ^ 15 ≤ C * Y := by
    calc
      B * Y * (2 * (1 / 2 - T + A * X)) + 2 * A * delta ^ 15 ≤
          B * (2 + 2 * A) * Y + 4 * A * Y := add_le_add hBY htail
      _ = C * Y := by dsimp [C, oneStepVariationalConst]; ring
  have hdouble : next ≤
      2 * ((1 / 2 - T + A * X) * cell + A * delta ^ 15 * previous) := by
    have hpenultimate' :
        (1 / 2 : ℝ) * next ≤
          (1 / 2 - T + A * X) * cell + A * delta ^ 15 * previous := by
      simpa only [T, X, mul_assoc] using hpenultimate
    linarith
  calc
    next ≤ 2 * ((1 / 2 - T + A * X) * cell +
        A * delta ^ 15 * previous) := hdouble
    _ ≤ 2 * ((1 / 2 - T + A * X) * ((1 + B * Y) * previous) +
        A * delta ^ 15 * previous) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hcellStep le_rfl) (by norm_num)
    _ = previous *
        (1 - 2 * T + 2 * A * X +
          B * Y * (2 * (1 / 2 - T + A * X)) +
          2 * A * delta ^ 15) := by ring
    _ ≤ previous * (1 - 2 * T + C * X + C * Y) := by
      apply mul_le_mul_of_nonneg_left _ hprevious
      linarith [add_le_add hAX herrorY]
    _ = previous *
        (1 - 2 * tau * h / d + C * delta ^ 4 * h ^ 2 +
          C * delta ^ 2 * L) := by dsimp [T, X, Y]; ring

/-- Close the one-step lower estimate from the penultimate dual
finite-volume inequality, the starred finite-volume comparison, and the
Dirichlet--Neumann bracketing of the reciprocal coefficient.

This is exactly the scalar algebra at `l.one.step.upper` and `l.one.step.lower`. -/
theorem one_step_lower_of_penultimate
    {delta tau h L d A B nextInv previousInv cellStarInv annealedStarInv : ℝ}
    (hdelta : 0 < delta) (hhalf : delta ≤ 1 / 2)
    (htau0 : 0 ≤ tau) (htau : tau ≤ delta ^ 2)
    (hh : 0 ≤ h) (hscale : delta * h ≤ 1)
    (hL : 1 / 2 ≤ L) (hd : 2 ≤ d)
    (hA : 0 < A) (hB : 0 ≤ B) (hprevious : 0 ≤ previousInv)
    (hbracket : nextInv ≤ annealedStarInv)
    (hcell : cellStarInv ≤ (1 + B * delta ^ 2 * L) * previousInv)
    (hpenultimate :
      (1 / 2 : ℝ) * annealedStarInv ≤
        (1 / 2 + tau * h / d + A * delta ^ 4 * h ^ 2) * cellStarInv +
          A * delta ^ 15 * previousInv) :
    nextInv ≤ previousInv *
      (1 + 2 * tau * h / d +
        oneStepVariationalConst A B * delta ^ 4 * h ^ 2 +
        oneStepVariationalConst A B * delta ^ 2 * L) := by
  obtain ⟨hT, hX, hdelta15⟩ := one_step_numerical_bounds
    hdelta hhalf htau0 htau hh hscale hL hd
  let X : ℝ := delta ^ 4 * h ^ 2
  let Y : ℝ := delta ^ 2 * L
  let T : ℝ := tau * h / d
  let C : ℝ := oneStepVariationalConst A B
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hX1 : X ≤ 1 := hX.trans (by nlinarith [sq_nonneg delta])
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT' : T ≤ 1 / 4 := hT
  have hfactor0 : 0 ≤ 1 / 2 + T + A * X := by positivity
  have hAXle : A * X ≤ A := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hX1 hA.le
  have hfactor2 : 2 * (1 / 2 + T + A * X) ≤ 2 + 2 * A := by
    linarith
  have hcellStep :
      (1 / 2 + T + A * X) * cellStarInv ≤
        (1 / 2 + T + A * X) * ((1 + B * Y) * previousInv) :=
    mul_le_mul_of_nonneg_left (by simpa [Y, mul_assoc] using hcell) hfactor0
  have hAX : 2 * A * X ≤ C * X := by
    have hAC : 2 * A ≤ C := by
      dsimp [C, oneStepVariationalConst]
      nlinarith [mul_nonneg hB (by nlinarith : 0 ≤ 2 + 2 * A)]
    exact mul_le_mul_of_nonneg_right hAC hX0
  have hBY : B * Y * (2 * (1 / 2 + T + A * X)) ≤
      B * (2 + 2 * A) * Y := by
    have hBY0 : 0 ≤ B * Y := mul_nonneg hB hY0
    have hmul := mul_le_mul_of_nonneg_left hfactor2 hBY0
    convert hmul using 1
    all_goals ring
  have htail : 2 * A * delta ^ 15 ≤ 4 * A * Y := by
    change 2 * A * delta ^ 15 ≤ 4 * A * (delta ^ 2 * L)
    have hmul := mul_le_mul_of_nonneg_left hdelta15 (by positivity : 0 ≤ 2 * A)
    convert hmul using 1
    all_goals ring
  have herrorY : B * Y * (2 * (1 / 2 + T + A * X)) +
      2 * A * delta ^ 15 ≤ C * Y := by
    calc
      B * Y * (2 * (1 / 2 + T + A * X)) + 2 * A * delta ^ 15 ≤
          B * (2 + 2 * A) * Y + 4 * A * Y := add_le_add hBY htail
      _ = C * Y := by dsimp [C, oneStepVariationalConst]; ring
  have hdouble : annealedStarInv ≤
      2 * ((1 / 2 + T + A * X) * cellStarInv +
        A * delta ^ 15 * previousInv) := by
    have hpenultimate' :
        (1 / 2 : ℝ) * annealedStarInv ≤
          (1 / 2 + T + A * X) * cellStarInv +
            A * delta ^ 15 * previousInv := by
      simpa only [T, X, mul_assoc] using hpenultimate
    linarith
  calc
    nextInv ≤ annealedStarInv := hbracket
    _ ≤ 2 * ((1 / 2 + T + A * X) * cellStarInv +
        A * delta ^ 15 * previousInv) := hdouble
    _ ≤ 2 * ((1 / 2 + T + A * X) * ((1 + B * Y) * previousInv) +
        A * delta ^ 15 * previousInv) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hcellStep le_rfl) (by norm_num)
    _ = previousInv *
        (1 + 2 * T + 2 * A * X +
          B * Y * (2 * (1 / 2 + T + A * X)) +
          2 * A * delta ^ 15) := by ring
    _ ≤ previousInv * (1 + 2 * T + C * X + C * Y) := by
      apply mul_le_mul_of_nonneg_left _ hprevious
      linarith [add_le_add hAX herrorY]
    _ = previousInv *
        (1 + 2 * tau * h / d + C * delta ^ 4 * h ^ 2 +
          C * delta ^ 2 * L) := by dsimp [T, X, Y]; ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
