module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellJacobianMeasurability

@[expose] public section

/-!
# Mixed spatial--random fourth moments for the one-step shell

On a probability space, the spatial `L²` norm is bounded by the spatial
`L⁴` norm.  Raising to the fourth power and integrating in the random
parameter converts the joint Tonelli estimate for the shell Jacobian into
the random fourth moment consumed by the interior Hessian bound.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


/-- A jointly measurable real field has a measurable parameter-dependent
spatial `L²` seminorm. -/
theorem measurable_eLpNorm_two_prod_right
    {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    (nu : Measure X) [SFinite nu] (f : Omega → X → ℝ)
    (hf : Measurable (Function.uncurry f)) :
    Measurable fun omega => eLpNorm (f omega) 2 nu := by
  rw [show (fun omega => eLpNorm (f omega) 2 nu) =
      fun omega =>
        (∫⁻ x, ‖f omega x‖ₑ ^ (2 : ℝ) ∂nu) ^ (1 / 2 : ℝ) by
    funext omega
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (hf.of_uncurry_left).aestronglyMeasurable]
    norm_num]
  have hjoint : Measurable (Function.uncurry fun omega x =>
      ‖f omega x‖ₑ ^ (2 : ℝ)) := by
    simpa only [Function.uncurry_apply_pair] using! hf.enorm.pow_const (2 : ℝ)
  have hinner : Measurable fun omega =>
      ∫⁻ x, ‖f omega x‖ₑ ^ (2 : ℝ) ∂nu :=
    hjoint.lintegral_prod_right
  exact ENNReal.continuous_rpow_const.measurable.comp hinner

/-- Mixed-norm Lyapunov inequality in the exact `ENNReal` setting used by the
joint shell estimate. -/
theorem lintegral_eLpNorm_two_rpow_four_le_lintegral_lintegral_four
    {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    (mu : Measure Omega) (nu : Measure X) [IsProbabilityMeasure nu]
    (f : Omega → X → ℝ)
    (hf : ∀ omega, AEStronglyMeasurable (f omega) nu) :
    (∫⁻ omega, (eLpNorm (f omega) 2 nu) ^ (4 : ℝ) ∂mu) ≤
      ∫⁻ omega, ∫⁻ x, ‖f omega x‖ₑ ^ (4 : ℝ) ∂nu ∂mu := by
  apply lintegral_mono
  intro omega
  have hnorm : eLpNorm (f omega) 2 nu ≤ eLpNorm (f omega) 4 nu :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  calc
    (eLpNorm (f omega) 2 nu) ^ (4 : ℝ) ≤
        (eLpNorm (f omega) 4 nu) ^ (4 : ℝ) :=
      ENNReal.rpow_le_rpow hnorm (by norm_num)
    _ = ∫⁻ x, ‖f omega x‖ₑ ^ (4 : ℝ) ∂nu := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hf omega)]
      norm_num only [ENNReal.toReal_ofNat]
      have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num
      rw [hquarter, ENNReal.rpow_inv_rpow (by norm_num : (4 : ℝ) ≠ 0)]

/-- Each parent-scale shell-Jacobian coordinate has the required random
fourth moment in normalized spatial `L²`. -/
theorem lintegral_parentScale_eLpNorm_two_oneStepShellJacobian_four_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (i j : Fin d) (hh : 0 < h)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega,
        (eLpNorm (fun x =>
          (3 : ℝ) ^ n *
            |(oneStepShellForcingW14 M n h omega p (originCube d n) hh
              ).jacobian x i j|)
          2 (normalizedCubeMeasure (originCube d n))) ^ (4 : ℝ)
        ∂M.P.toMeasure ≤
      (ENNReal.ofReal
        (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
          (4 : ℝ) := by
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → Vec d → ℝ := fun omega x =>
    (3 : ℝ) ^ n *
      |(oneStepShellForcingW14 M n h omega p (originCube d n) hh
        ).jacobian x i j|
  have hf : ∀ omega,
      AEStronglyMeasurable (f omega)
        (normalizedCubeMeasure (originCube d n)) := by
    intro omega
    have hjoint := measurable_oneStepShellForcingW14_jacobian_uncurry
      M n h p (originCube d n) hh i j
    exact (measurable_const.mul
      ((hjoint.comp (measurable_const.prodMk measurable_id)).norm)).aestronglyMeasurable
  let : IsProbabilityMeasure (normalizedCubeMeasure (originCube d n)) :=
    ⟨normalizedCubeMeasure_apply_univ (originCube d n)⟩
  calc
    (∫⁻ omega, (eLpNorm (f omega) 2
        (normalizedCubeMeasure (originCube d n))) ^ (4 : ℝ)
        ∂M.P.toMeasure) ≤
      ∫⁻ omega, ∫⁻ x, ‖f omega x‖ₑ ^ (4 : ℝ)
        ∂normalizedCubeMeasure (originCube d n) ∂M.P.toMeasure :=
      lintegral_eLpNorm_two_rpow_four_le_lintegral_lintegral_four
        M.P.toMeasure (normalizedCubeMeasure (originCube d n)) f hf
    _ ≤ (ENNReal.ofReal
        (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
          (4 : ℝ) := by
      simpa only [f] using
        lintegral_lintegral_parentScale_oneStepShellForcingW14_jacobian_four_le
          M n h p i j hh hscale

/-- The diagonal shell-Jacobian estimates aggregate to the random fourth
moment of the normalized scalar divergence.  The factor `d^3` is precisely
the finite-dimensional inequality `(sum_i X_i)^4 <= d^3 sum_i X_i^4`. -/
theorem lintegral_parentScale_eLpNorm_two_oneStepShellDivergence_four_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (p : Vec d) (hh : 0 < h)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫⁻ omega,
        (eLpNorm (fun x =>
          (3 : ℝ) ^ n *
            |(oneStepShellForcingH1 M n h omega p (originCube d n) hh
              ).divergence x|)
          2 (normalizedCubeMeasure (originCube d n))) ^ (4 : ℝ)
        ∂M.P.toMeasure ≤
      (d : ℝ≥0∞) ^ (3 : ℝ) *
        ∑ i : Fin d,
          (ENNReal.ofReal
            (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
              (4 : ℝ) := by
  let nu := normalizedCubeMeasure (originCube d n)
  let X : Fin d → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun i omega =>
    eLpNorm (fun x =>
      (3 : ℝ) ^ n *
        |(oneStepShellForcingW14 M n h omega p (originCube d n) hh
          ).jacobian x i i|) 2 nu
  have hXmeas : ∀ i, Measurable (X i) := by
    intro i
    apply measurable_eLpNorm_two_prod_right
    exact measurable_const.mul
      (measurable_oneStepShellForcingW14_jacobian_uncurry
        M n h p (originCube d n) hh i i).norm
  have hdiv : ∀ omega,
      eLpNorm (fun x =>
          (3 : ℝ) ^ n *
            |(oneStepShellForcingH1 M n h omega p (originCube d n) hh
              ).divergence x|) 2 nu ≤
        ∑ i : Fin d, X i omega := by
    intro omega
    let f : Fin d → Vec d → ℝ := fun i x =>
      (3 : ℝ) ^ n *
        ((oneStepShellForcingH1 M n h omega p (originCube d n) hh
          ).coord i).grad x i
    have hf : ∀ i : Fin d, AEStronglyMeasurable (f i) nu := by
      intro i
      exact ((H1Function.grad_memL2_normalizedCubeMeasure
        ((oneStepShellForcingH1 M n h omega p (originCube d n) hh).coord i)
        i).aestronglyMeasurable).const_mul ((3 : ℝ) ^ n)
    have hsum := MeasureTheory.eLpNorm_sum_le
      (μ := nu) (s := Finset.univ) (f := f)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hleft : eLpNorm (fun x =>
        (3 : ℝ) ^ n *
          |(oneStepShellForcingH1 M n h omega p (originCube d n) hh
            ).divergence x|) 2 nu =
        eLpNorm (∑ i : Fin d, f i) 2 nu := by
      apply eLpNorm_congr_norm_ae
      · exact (oneStepShellForcingH1 M n h omega p (originCube d n) hh
          ).divergence_memLp_normalizedCubeMeasure.aestronglyMeasurable.norm.const_mul _
      · exact Finset.aestronglyMeasurable_sum _ (fun i _ => hf i)
      filter_upwards with x
      simp only [CubeVectorH1Function.divergence, f, Finset.sum_apply]
      rw [← Finset.mul_sum]
      simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    have hright : ∑ i : Fin d, eLpNorm (f i) 2 nu =
        ∑ i : Fin d, X i omega := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply eLpNorm_congr_norm_ae (hf i)
      · simpa only [X] using!
          ((measurable_oneStepShellForcingW14_jacobian_uncurry
            M n h p (originCube d n) hh i i).comp
              ((measurable_const (a := omega)).prodMk measurable_id)).norm.aestronglyMeasurable.const_mul
              ((3 : ℝ) ^ n)
      filter_upwards with x
      simp only [f]
      rw [oneStepShellForcing_paired_jacobian M n h omega p
        (originCube d n) hh x i i]
      simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    rw [hleft, ← hright]
    simpa only [Finset.sum_filter, Finset.mem_univ, ite_true] using hsum
  calc
    (∫⁻ omega,
        (eLpNorm (fun x =>
          (3 : ℝ) ^ n *
            |(oneStepShellForcingH1 M n h omega p (originCube d n) hh
              ).divergence x|) 2 nu) ^ (4 : ℝ)
        ∂M.P.toMeasure) ≤
      ∫⁻ omega, (∑ i : Fin d, X i omega) ^ (4 : ℝ)
        ∂M.P.toMeasure := by
      apply lintegral_mono
      intro omega
      exact ENNReal.rpow_le_rpow (hdiv omega) (by norm_num)
    _ ≤ ∫⁻ omega,
        (d : ℝ≥0∞) ^ (3 : ℝ) *
          ∑ i : Fin d, (X i omega) ^ (4 : ℝ)
        ∂M.P.toMeasure := by
      apply lintegral_mono
      intro omega
      have hpower :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow
          (s := Finset.univ) (f := fun i : Fin d => X i omega)
          (by norm_num : (1 : ℝ) ≤ 4)
      norm_num at hpower
      convert hpower using 1
      norm_num
      norm_num
    _ = (d : ℝ≥0∞) ^ (3 : ℝ) *
        ∑ i : Fin d, ∫⁻ omega, (X i omega) ^ (4 : ℝ)
          ∂M.P.toMeasure := by
      have hsummeas : Measurable fun omega =>
          ∑ i : Fin d, (X i omega) ^ (4 : ℝ) :=
        Finset.measurable_sum Finset.univ fun i _hi =>
          (hXmeas i).pow_const (4 : ℝ)
      rw [lintegral_const_mul _ hsummeas]
      have hsumint := lintegral_finsetSum (μ := M.P.toMeasure)
        Finset.univ (fun i _hi => (hXmeas i).pow_const (4 : ℝ))
      congr 1
    _ ≤ (d : ℝ≥0∞) ^ (3 : ℝ) *
        ∑ i : Fin d,
          (ENNReal.ofReal
            (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta))) ^
              (4 : ℝ) := by
      apply mul_le_mul_right
      exact Finset.sum_le_sum fun i _hi => by
        simpa only [X, nu] using
          lintegral_parentScale_eLpNorm_two_oneStepShellJacobian_four_le
            M n h p i i hh hscale

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
