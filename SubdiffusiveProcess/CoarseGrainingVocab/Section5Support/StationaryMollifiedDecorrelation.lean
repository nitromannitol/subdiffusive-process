module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryTwoScaleStream
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepProjectionOrbit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDecorrelation

@[expose] public section

/-!
# Large-scale stationary mollification from compact covariance

This is the Hilbert-space version of
`Algsuperdiff/Section3/Provider/Corrector/MollifiedDecorrelation.lean`.  A
nonnegative unit-mass kernel bounded by `K` smooths a stationary field with
covariance range `rho` to squared norm at most
`K * volume (ball rho) * ‖F‖²`.

Unlike the Superdiffusion representative-level proof, this formulation works
directly with the topology-free `Stationary.mollifyL2` carrier already used by
the GMC Hodge decomposition.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

namespace Stationary

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable [AddAction (Vec d) Omega]
variable [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]

/-- Compact covariance gives the sharp volume-times-kernel-sup bound for a
stationary Hilbert-space mollification. -/
theorem norm_sq_mollifyL2_le_of_covariance_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {kappa : Vec d → ℝ} (hkappa0 : ∀ y, 0 ≤ kappa y)
    (hkappa : Continuous kappa) (hcompact : HasCompactSupport kappa)
    (hkappa1 : ∫ y, kappa y = 1) {K : ℝ}
    (hkappaK : ∀ y, kappa y ≤ K)
    (F : Lp E 2 mu)
    (hForbit : Continuous (fun z : Vec d => koopman (mu := mu) z F))
    {rho : ℝ}
    (hcov : ∀ w : Vec d, rho ≤ ‖w‖ →
      inner ℝ (koopman (mu := mu) w F) F = 0) :
    ‖mollifyL2 (mu := mu) kappa F‖ ^ 2 ≤
      K * (volume (Metric.ball (0 : Vec d) rho)).toReal * ‖F‖ ^ 2 := by
  classical
  let A : Lp E 2 mu := mollifyL2 (mu := mu) kappa F
  let C : ℝ := ‖F‖ ^ 2
  let V : ℝ := (volume (Metric.ball (0 : Vec d) rho)).toReal
  have hK0 : 0 ≤ K := le_trans (hkappa0 0) (hkappaK 0)
  have hC0 : 0 ≤ C := sq_nonneg _
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hkappaInt : Integrable kappa volume :=
    hkappa.integrable_of_hasCompactSupport hcompact
  have hkoopNorm : ∀ z : Vec d,
      ‖koopman (mu := mu) z F‖ = ‖F‖ := fun z =>
    (koopman (mu := mu) z).norm_map F
  have hmainInt : Integrable
      (fun y : Vec d => kappa y • koopman (mu := mu) (-y) F) volume :=
    integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
      (mu := mu) hkappa hcompact F hForbit
  have hpairInt : ∀ y : Vec d, Integrable
      (fun z : Vec d => kappa z * inner ℝ
        (koopman (mu := mu) (-z) F)
        (koopman (mu := mu) (-y) F)) volume := by
    intro y
    have hcont : Continuous (fun z : Vec d => kappa z * inner ℝ
        (koopman (mu := mu) (-z) F)
        (koopman (mu := mu) (-y) F)) :=
      hkappa.mul ((hForbit.comp continuous_neg).inner continuous_const)
    refine Integrable.mono' (hkappaInt.norm.const_mul C)
      hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hinner := abs_real_inner_le_norm
      (koopman (mu := mu) (-z) F)
      (koopman (mu := mu) (-y) F)
    have hbound : |inner ℝ (koopman (mu := mu) (-z) F)
        (koopman (mu := mu) (-y) F)| ≤ C := by
      rw [hkoopNorm, hkoopNorm] at hinner
      simpa only [C, pow_two] using! hinner
    simpa only [Real.norm_eq_abs, mul_comm] using!
      mul_le_mul_of_nonneg_left hbound (abs_nonneg (kappa z))
  have hshift : ∀ y z : Vec d,
      inner ℝ (koopman (mu := mu) (-z) F)
          (koopman (mu := mu) (-y) F) =
        inner ℝ (koopman (mu := mu) (z - y) F) F := by
    intro y z
    calc
      inner ℝ (koopman (mu := mu) (-z) F)
          (koopman (mu := mu) (-y) F) =
        inner ℝ F (koopman (mu := mu) z
          (koopman (mu := mu) (-y) F)) :=
            by
              simpa using! (inner_koopman_left (-z) F
                (koopman (mu := mu) (-y) F))
      _ = inner ℝ F (koopman (mu := mu) ((-y) + z) F) := by
            rw [koopman_koopman]
      _ = inner ℝ (koopman (mu := mu) (z - y) F) F := by
            rw [real_inner_comm]
            congr 3
            abel
  have hkey : ∀ y : Vec d,
      inner ℝ (koopman (mu := mu) (-y) F) A ≤ K * C * V := by
    intro y
    have hrepr : inner ℝ (koopman (mu := mu) (-y) F) A =
        ∫ z : Vec d, kappa z * inner ℝ
          (koopman (mu := mu) (-z) F)
          (koopman (mu := mu) (-y) F) := by
      have hcomm := ContinuousLinearMap.integral_comp_comm
        (innerSL ℝ (koopman (mu := mu) (-y) F)) hmainInt
      have hleft : (innerSL ℝ (koopman (mu := mu) (-y) F)) A =
          inner ℝ A (koopman (mu := mu) (-y) F) := by
        rw [innerSL_apply_apply, real_inner_comm]
      rw [real_inner_comm, ← hleft]
      change (innerSL ℝ (koopman (mu := mu) (-y) F))
          (∫ z : Vec d, kappa z • koopman (mu := mu) (-z) F) = _
      rw [← hcomm]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      change (innerSL ℝ (koopman (mu := mu) (-y) F))
          (kappa z • koopman (mu := mu) (-z) F) = _
      rw [innerSL_apply_apply, real_inner_smul_right, real_inner_comm]
    have hindic : Integrable
        (Set.indicator (Metric.ball y rho)
          (fun _ : Vec d => K * C)) volume :=
      (integrable_indicator_iff measurableSet_ball).2
        (integrableOn_const (measure_ball_lt_top).ne)
    have hbd : ∀ z : Vec d,
        kappa z * inner ℝ
            (koopman (mu := mu) (-z) F)
            (koopman (mu := mu) (-y) F) ≤
          Set.indicator (Metric.ball y rho)
            (fun _ : Vec d => K * C) z := by
      intro z
      by_cases hz : z ∈ Metric.ball y rho
      · rw [Set.indicator_of_mem hz]
        have hinner : inner ℝ
            (koopman (mu := mu) (-z) F)
            (koopman (mu := mu) (-y) F) ≤ C := by
          have hcs := real_inner_le_norm
            (koopman (mu := mu) (-z) F)
            (koopman (mu := mu) (-y) F)
          rw [hkoopNorm, hkoopNorm] at hcs
          simpa only [C, pow_two] using! hcs
        calc
          kappa z * inner ℝ
              (koopman (mu := mu) (-z) F)
              (koopman (mu := mu) (-y) F) ≤ kappa z * C :=
            mul_le_mul_of_nonneg_left hinner (hkappa0 z)
          _ ≤ K * C := mul_le_mul_of_nonneg_right (hkappaK z) hC0
      · rw [Set.indicator_of_notMem hz, hshift]
        have hnorm : rho ≤ ‖z - y‖ := by
          simpa only [Metric.mem_ball, dist_eq_norm, not_lt]
            using! hz
        rw [hcov _ hnorm, mul_zero]
    rw [hrepr]
    calc
      (∫ z : Vec d, kappa z * inner ℝ
          (koopman (mu := mu) (-z) F)
          (koopman (mu := mu) (-y) F)) ≤
          ∫ z : Vec d, Set.indicator (Metric.ball y rho)
            (fun _ : Vec d => K * C) z :=
        integral_mono (hpairInt y) hindic hbd
      _ = K * C * V := by
        rw [integral_indicator_const (K * C) measurableSet_ball,
          measureReal_def, Measure.addHaar_ball_center volume y rho,
          smul_eq_mul]
        dsimp only [V]
        ring
  have houterInt : Integrable (fun y : Vec d =>
      kappa y * inner ℝ (koopman (mu := mu) (-y) F) A) volume := by
    have hcont : Continuous (fun y : Vec d =>
        kappa y * inner ℝ (koopman (mu := mu) (-y) F) A) :=
      hkappa.mul ((hForbit.comp continuous_neg).inner continuous_const)
    refine Integrable.mono' (hkappaInt.norm.const_mul (‖F‖ * ‖A‖))
      hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hinner := abs_real_inner_le_norm
      (koopman (mu := mu) (-y) F) A
    have hbound : |inner ℝ (koopman (mu := mu) (-y) F) A| ≤
        ‖F‖ * ‖A‖ := by simpa only [hkoopNorm] using! hinner
    simpa only [Real.norm_eq_abs, mul_comm] using!
      mul_le_mul_of_nonneg_left hbound (abs_nonneg (kappa y))
  have hnormrepr : ‖A‖ ^ 2 = ∫ y : Vec d,
      kappa y * inner ℝ (koopman (mu := mu) (-y) F) A := by
    rw [← real_inner_self_eq_norm_sq]
    have hcomm := ContinuousLinearMap.integral_comp_comm (innerSL ℝ A) hmainInt
    have hleft : (innerSL ℝ A) A = inner ℝ A A := by
      rw [innerSL_apply_apply, real_inner_comm]
    rw [← hleft]
    change (innerSL ℝ A)
        (∫ y : Vec d, kappa y • koopman (mu := mu) (-y) F) = _
    rw [← hcomm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change (innerSL ℝ A)
        (kappa y • koopman (mu := mu) (-y) F) = _
    rw [innerSL_apply_apply, real_inner_smul_right, real_inner_comm]
  change ‖A‖ ^ 2 ≤ K * V * C
  rw [hnormrepr]
  calc
    (∫ y : Vec d,
        kappa y * inner ℝ (koopman (mu := mu) (-y) F) A) ≤
        ∫ y : Vec d, kappa y * (K * C * V) := by
      refine integral_mono houterInt (hkappaInt.mul_const _) fun y => ?_
      exact mul_le_mul_of_nonneg_left (hkey y) (hkappa0 y)
    _ = K * V * C := by
      rw [integral_mul_const, hkappa1, one_mul]
      ring

end Stationary


namespace Stationary

variable {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}
variable [AddAction (Vec d) Omega]
variable [MeasurableConstVAdd (Vec d) Omega]
variable [VAddInvariantMeasure (Vec d) Omega mu]

/-- Stationary mollification commutes with the orthogonal projection onto
the stationary potential subspace.  This is the Hilbert-space form of the
Helmholtz-multiplier commutation used in the Superdiffusion large-scale
decorrelation argument. -/
theorem stationaryPotentialProjection_mollifyL2
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa)
    (F : VectorL2 d mu)
    (hF : Continuous (fun z : Vec d => koopman (mu := mu) z F)) :
    stationaryPotentialProjection (mu := mu)
        (mollifyL2 (mu := mu) kappa F) =
      mollifyL2 (mu := mu) kappa
        (stationaryPotentialProjection (mu := mu) F) := by
  have hmain : Integrable
      (fun y : Vec d => kappa y • koopman (mu := mu) (-y) F) volume :=
    integrable_mollifyL2_integrand_of_continuous_koopmanOrbit
      (mu := mu) hkappa hcompact F hF
  have hcomm := ContinuousLinearMap.integral_comp_comm
    (stationaryPotentialProjection (mu := mu) (d := d)) hmain
  rw [mollifyL2, mollifyL2, ← hcomm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [map_smul, koopman_stationaryPotentialProjection]

/-- Mollification of the solenoidal Helmholtz component is the complementary
projection of the mollified original field. -/
theorem mollifyL2_sub_stationaryPotentialProjection
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa)
    (F : VectorL2 d mu)
    (hF : Continuous (fun z : Vec d => koopman (mu := mu) z F)) :
    mollifyL2 (mu := mu) kappa
        (F - stationaryPotentialProjection (mu := mu) F) =
      mollifyL2 (mu := mu) kappa F -
        stationaryPotentialProjection (mu := mu)
          (mollifyL2 (mu := mu) kappa F) := by
  have hPF : Continuous (fun z : Vec d => koopman (mu := mu) z
      (stationaryPotentialProjection (mu := mu) F)) := by
    have hc := stationaryPotentialProjection.continuous.comp hF
    convert hc using 1
    funext z
    exact koopman_stationaryPotentialProjection z F
  rw [mollifyL2_sub_of_continuous hkappa hcompact _ _ hF hPF,
    stationaryPotentialProjection_mollifyL2 hkappa hcompact F hF]

/-- The complementary stationary Helmholtz projection is contractive after
mollification. -/
theorem norm_mollifyL2_sub_stationaryPotentialProjection_le
    {kappa : Vec d → ℝ} (hkappa : Continuous kappa)
    (hcompact : HasCompactSupport kappa)
    (F : VectorL2 d mu)
    (hF : Continuous (fun z : Vec d => koopman (mu := mu) z F)) :
    ‖mollifyL2 (mu := mu) kappa
        (F - stationaryPotentialProjection (mu := mu) F)‖ ≤
      ‖mollifyL2 (mu := mu) kappa F‖ := by
  rw [mollifyL2_sub_stationaryPotentialProjection hkappa hcompact F hF]
  let K := stationaryPotentialSubspace (mu := mu) (d := d)
  have hsplit := K.starProjection_add_starProjection_orthogonal
    (mollifyL2 (mu := mu) kappa F)
  have heq : mollifyL2 (mu := mu) kappa F -
      K.starProjection (mollifyL2 (mu := mu) kappa F) =
      Kᗮ.starProjection (mollifyL2 (mu := mu) kappa F) := by
    rw [sub_eq_iff_eq_add]
    simpa only [add_comm] using! hsplit.symm
  change ‖mollifyL2 (mu := mu) kappa F -
      K.starProjection (mollifyL2 (mu := mu) kappa F)‖ ≤ _
  rw [heq]
  exact Kᗮ.norm_starProjection_apply_le _

end Stationary

/-- Inner product of two scalar stationary fields embedded in the same fixed
Euclidean direction. -/
theorem inner_scalarToVectorL2_same_direction {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p : Vec d)
    (X Y : Stationary.ScalarL2 M.P.toMeasure) :
    inner ℝ (scalarToVectorL2 M.P.toMeasure p X)
        (scalarToVectorL2 M.P.toMeasure p Y) =
      vecNormSq p * inner ℝ X Y := by
  rw [Stationary.inner_vectorL2_eq_sum_inner_coord]
  simp_rw [vectorL2Coord_scalarToVectorL2, real_inner_smul_left,
    real_inner_smul_right]
  simp_rw [← mul_assoc, ← pow_two]
  rw [← Finset.sum_mul]
  have hp : (∑ i : Fin d, p i ^ 2) = vecNormSq p := by
    simp [vecNormSq, vecDot, pow_two]
  rw [hp]

/-- The vector one-step forcing inherits the compact covariance range of its
scalar fresh-shell multiplier. -/
theorem inner_koopman_oneStepOriginForcingL2_eq_zero_of_cutoffRange_lt_norm
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (hh : 0 < h) {z : Vec d}
    (hz : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) < ‖z‖) :
    letI := potentialSequenceVAddInvariant M
    inner ℝ
        (Stationary.koopman (mu := M.P.toMeasure) z
          (oneStepOriginForcingL2 M n h p hh))
        (oneStepOriginForcingL2 M n h p hh) = 0 := by
  letI := potentialSequenceVAddInvariant M
  rw [koopman_oneStepOriginForcingL2,
    oneStepOriginForcingL2_eq_scalarToVectorL2,
    inner_scalarToVectorL2_same_direction,
    inner_oneStepMultiplierAtL2_eq_zero_of_cutoffRange_lt_norm
      M n h hh (x := z) (y := 0) (by simpa only [sub_zero] using! hz),
    mul_zero]

/-- A product smoothing at scale `s` of the raw one-step forcing has the
finite-range covariance bound.  The harmless `+1` turns the strict cutoff
range from the model into the closed support radius required by the abstract
decorrelation lemma. -/
theorem norm_sq_mollifyL2_oneStepOriginForcing_le
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (hh : 0 < h)
    {s : ℝ} (hs : 0 < s) :
    letI := potentialSequenceVAddInvariant M
    let rho := Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) + 1
    ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
        (streamProductDensity d hs)
        (oneStepOriginForcingL2 M n h p hh)‖ ^ 2 ≤
      (1 / s ^ d) *
        (volume (Metric.ball (0 : Vec d) rho)).toReal *
        ‖oneStepOriginForcingL2 M n h p hh‖ ^ 2 := by
  letI := potentialSequenceVAddInvariant M
  let rho := Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) + 1
  apply Stationary.norm_sq_mollifyL2_le_of_covariance_support
    (streamProductDensity_nonneg d hs)
    (continuous_streamProductDensity d hs)
    (hasCompactSupport_streamProductDensity d hs)
    (integral_streamProductDensity d hs)
    (streamProductDensity_le d hs)
    (oneStepOriginForcingL2 M n h p hh)
    (continuous_koopman_oneStepOriginForcingL2 M n h p hh)
  intro z hz
  apply inner_koopman_oneStepOriginForcingL2_eq_zero_of_cutoffRange_lt_norm
    M n h p hh
  linarith

/-- The same quantitative large-scale decay holds for the solenoidal
Helmholtz component, by commutation and contraction of the complementary
projection. -/
theorem norm_sq_mollifyL2_oneStepSolenoidalRemainder_le
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (hh : 0 < h)
    {s : ℝ} (hs : 0 < s) :
    letI := potentialSequenceVAddInvariant M
    let rho := Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) + 1
    ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
        (streamProductDensity d hs)
        (oneStepOriginForcingL2 M n h p hh -
          oneStepPotentialProjection M n h p hh)‖ ^ 2 ≤
      (1 / s ^ d) *
        (volume (Metric.ball (0 : Vec d) rho)).toReal *
        ‖oneStepOriginForcingL2 M n h p hh‖ ^ 2 := by
  letI := potentialSequenceVAddInvariant M
  let F := oneStepOriginForcingL2 M n h p hh
  have hnorm :
      ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hs)
          (F - Stationary.stationaryPotentialProjection
            (mu := M.P.toMeasure) F)‖ ≤
        ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hs) F‖ :=
    Stationary.norm_mollifyL2_sub_stationaryPotentialProjection_le
      (continuous_streamProductDensity d hs)
      (hasCompactSupport_streamProductDensity d hs) F
      (continuous_koopman_oneStepOriginForcingL2 M n h p hh)
  have hsquared :
      ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hs)
          (F - Stationary.stationaryPotentialProjection
            (mu := M.P.toMeasure) F)‖ ^ 2 ≤
        ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hs) F‖ ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  exact hsquared.trans
    (norm_sq_mollifyL2_oneStepOriginForcing_le M n h p hh hs)

/-- Product mollification kills the one-step solenoidal remainder at a
sufficiently large spatial scale.  This is the quantitative replacement for
the mean-ergodic step in the printed stream construction. -/
theorem exists_streamProduct_scale_norm_mollifyL2_oneStepSolenoidalRemainder_lt
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (p : Vec d) (hh : 0 < h)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ s : ℝ, ∃ hs : 0 < s,
      letI := potentialSequenceVAddInvariant M
      ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hs)
          (oneStepOriginForcingL2 M n h p hh -
            oneStepPotentialProjection M n h p hh)‖ < epsilon := by
  letI := potentialSequenceVAddInvariant M
  let rho : ℝ := Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) + 1
  let C : ℝ := (volume (Metric.ball (0 : Vec d) rho)).toReal *
    ‖oneStepOriginForcingL2 M n h p hh‖ ^ 2
  have hd : d ≠ 0 := by
    have := M.shellPrefix.dimension
    omega
  have hbase : (1 : ℝ) < (2 : ℝ) ^ d :=
    one_lt_pow₀ (by norm_num) hd
  have htInv : Filter.Tendsto
      (fun N : ℕ => (((2 : ℝ) ^ d) ^ N)⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt hbase)
  have ht : Filter.Tendsto
      (fun N : ℕ => (((2 : ℝ) ^ d) ^ N)⁻¹ * C)
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using! htInv.mul_const C
  have hepsSq : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  obtain ⟨N, hN⟩ := (ht.eventually_lt_const hepsSq).exists
  let s : ℝ := (2 : ℝ) ^ N
  have hs : 0 < s := by dsimp only [s]; positivity
  refine ⟨s, hs, ?_⟩
  have hbound := norm_sq_mollifyL2_oneStepSolenoidalRemainder_le
    M n h p hh hs
  have hrhs :
      (1 / s ^ d) *
          (volume (Metric.ball (0 : Vec d) rho)).toReal *
          ‖oneStepOriginForcingL2 M n h p hh‖ ^ 2 =
        (((2 : ℝ) ^ d) ^ N)⁻¹ * C := by
    dsimp only [s, C]
    rw [one_div, ← pow_mul, Nat.mul_comm]
    ring
  have hbound' :
      ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hs)
          (oneStepOriginForcingL2 M n h p hh -
            oneStepPotentialProjection M n h p hh)‖ ^ 2 ≤
        (1 / s ^ d) *
          (volume (Metric.ball (0 : Vec d) rho)).toReal *
          ‖oneStepOriginForcingL2 M n h p hh‖ ^ 2 := by
    simpa only using! hbound
  rw [hrhs] at hbound'
  have hsq :
      ‖Stationary.mollifyL2 (mu := M.P.toMeasure)
          (streamProductDensity d hs)
          (oneStepOriginForcingL2 M n h p hh -
            oneStepPotentialProjection M n h p hh)‖ ^ 2 < epsilon ^ 2 :=
    hbound'.trans_lt hN
  nlinarith [norm_nonneg
    (Stationary.mollifyL2 (mu := M.P.toMeasure)
      (streamProductDensity d hs)
      (oneStepOriginForcingL2 M n h p hh -
        oneStepPotentialProjection M n h p hh))]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
