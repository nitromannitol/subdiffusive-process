module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDecorrelation
public import Mathlib.Analysis.InnerProductSpace.MeanErgodic

@[expose] public section

/-!
# Vanishing translation-invariant component of the one-step multiplier

Compact covariance support makes widely separated translates of the centered
one-step multiplier orthogonal in scalar `L²`.  Consequently their Birkhoff
averages converge to zero.  Von Neumann's mean ergodic theorem then identifies
the fixed-point projection for any translation beyond the cutoff range with
zero.

This is the zero-frequency input left implicit in the spectral sentence.  It does not assert the separate trace-one
identity for the stationary Helmholtz projection.
-/

open Filter MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section


private theorem tendsto_birkhoffAverage_linearIsometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →ₗᵢ[ℝ] E) (x : E) :
    Tendsto (fun N => birkhoffAverage ℝ T.toContinuousLinearMap id N x) atTop
      (nhds ((LinearMap.eqLocus T.toContinuousLinearMap.toLinearMap (ContinuousLinearMap.id ℝ E).toLinearMap).orthogonalProjectionOnto x)) :=
  ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
    T.toContinuousLinearMap T.norm_toContinuousLinearMap_le x

/-- Spatially separated scalar `L²` evaluations are orthogonal. -/
theorem inner_oneStepMultiplierAtL2_eq_zero_of_cutoffRange_lt_norm {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h)
    {x y : Vec d}
    (hxy : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) < ‖x - y‖) :
    inner ℝ (oneStepMultiplierAtL2 M n h x hh)
      (oneStepMultiplierAtL2 M n h y hh) = 0 := by
  rw [L2.inner_def]
  have hae : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      inner ℝ
        ((oneStepMultiplierAtL2 M n h x hh : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega)
        ((oneStepMultiplierAtL2 M n h y hh : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega)) =ᵐ[M.P.toMeasure]
      fun omega => oneStepMultiplierAt M n h x omega *
        oneStepMultiplierAt M n h y omega := by
    filter_upwards
      [MemLp.coeFn_toLp (memLp_two_oneStepMultiplierAt M n h x hh),
        MemLp.coeFn_toLp (memLp_two_oneStepMultiplierAt M n h y hh)]
      with omega hxrep hyrep
    have hxrep' :
        (oneStepMultiplierAtL2 M n h x hh : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega =
          oneStepMultiplierAt M n h x omega := by
      simpa only [oneStepMultiplierAtL2] using! hxrep
    have hyrep' :
        (oneStepMultiplierAtL2 M n h y hh : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega =
          oneStepMultiplierAt M n h y omega := by
      simpa only [oneStepMultiplierAtL2] using! hyrep
    rw [hxrep', hyrep']
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [integral_congr_ae hae]
  exact integral_oneStepMultiplierAt_mul_eq_zero_of_cutoffRange_lt_norm
    M n h hh hxy

/-- Every spatial evaluation has the exact suffix variance as its squared
scalar `L²` norm. -/
theorem norm_sq_oneStepMultiplierAtL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (x : Vec d) (hh : 0 < h) :
    ‖oneStepMultiplierAtL2 M n h x hh‖ ^ 2 =
      (oneShellCenteredExpTwoMoment M) ^ h - 1 := by
  let := potentialSequenceVAddInvariant M
  have horbit := koopman_oneStepMultiplierAtL2 M n h x 0 hh
  simp only [zero_add] at horbit
  rw [← horbit, LinearIsometry.norm_map]
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hae : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      inner ℝ
        ((oneStepMultiplierAtL2 M n h 0 hh : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega)
        ((oneStepMultiplierAtL2 M n h 0 hh : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega)) =ᵐ[M.P.toMeasure]
      fun omega => (oneStepOriginMultiplier M n h omega) ^ 2 := by
    filter_upwards
      [MemLp.coeFn_toLp (memLp_two_oneStepMultiplierAt M n h 0 hh)]
      with omega hrep
    have hrep' :
        (oneStepMultiplierAtL2 M n h 0 hh : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ) omega =
          oneStepMultiplierAt M n h 0 omega := by
      simpa only [oneStepMultiplierAtL2] using! hrep
    rw [hrep']
    simp only [RCLike.inner_apply, conj_trivial]
    simp [oneStepMultiplierAt, oneStepOriginMultiplier, pow_two]
  rw [integral_congr_ae hae]
  exact integral_oneStepOriginMultiplier_sq M n h hh

private theorem one_le_abs_natCast_sub {r s : ℕ} (hrs : r ≠ s) :
    (1 : ℝ) ≤ |(r : ℝ) - (s : ℝ)| := by
  rcases lt_or_gt_of_ne hrs with hrs | hrs
  · have hcast : (r : ℝ) + 1 ≤ (s : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hrs)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hcast : (s : ℝ) + 1 ≤ (r : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hrs)
    rw [abs_of_nonneg (by linarith)]
    linarith

private theorem cutoffRange_lt_norm_nat_smul_sub
    {d : ℕ} {rho : ℝ} {z : Vec d}
    (hz : rho < ‖z‖) {r s : ℕ} (hrs : r ≠ s) :
    rho < ‖(r : ℝ) • z - (s : ℝ) • z‖ := by
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  have hfactor := one_le_abs_natCast_sub hrs
  have hznorm : 0 ≤ ‖z‖ := norm_nonneg z
  have := mul_le_mul_of_nonneg_right hfactor hznorm
  nlinarith

/-- Iterating a fixed Koopman translation gives the corresponding arithmetic
progression of spatial evaluations. -/
theorem iterate_koopman_oneStepMultiplierAtL2 {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (z : Vec d) (hh : 0 < h) (r : ℕ) :
    letI := potentialSequenceVAddInvariant M
    ((Stationary.koopman (mu := M.P.toMeasure) z).toContinuousLinearMap ^[r])
        (oneStepMultiplierAtL2 M n h 0 hh) =
      oneStepMultiplierAtL2 M n h ((r : ℝ) • z) hh := by
  let := potentialSequenceVAddInvariant M
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', ih]
      change Stationary.koopman (mu := M.P.toMeasure) z
          (oneStepMultiplierAtL2 M n h ((r : ℝ) • z) hh) = _
      rw [koopman_oneStepMultiplierAtL2]
      congr 2
      push_cast
      module

/-- Widely spaced points on one translation orbit form an orthogonal family. -/
theorem inner_oneStepMultiplierAtL2_nat_smul_eq_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h)
    {z : Vec d}
    (hz : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) < ‖z‖)
    {r s : ℕ} (hrs : r ≠ s) :
    inner ℝ (oneStepMultiplierAtL2 M n h ((r : ℝ) • z) hh)
      (oneStepMultiplierAtL2 M n h ((s : ℝ) • z) hh) = 0 := by
  apply inner_oneStepMultiplierAtL2_eq_zero_of_cutoffRange_lt_norm M n h hh
  exact cutoffRange_lt_norm_nat_smul_sub hz hrs

/-- Exact Pythagoras formula for a finite sum of widely separated
translations. -/
theorem norm_sq_sum_oneStepMultiplierAtL2_nat_smul {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h N : ℕ) (hh : 0 < h)
    {z : Vec d}
    (hz : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) < ‖z‖) :
    ‖∑ r ∈ Finset.range N,
        oneStepMultiplierAtL2 M n h ((r : ℝ) • z) hh‖ ^ 2 =
      (N : ℝ) * ((oneShellCenteredExpTwoMoment M) ^ h - 1) := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum]
  calc
    ∑ x ∈ Finset.range N, ∑ x_1 ∈ Finset.range N,
        inner ℝ (oneStepMultiplierAtL2 M n h ((x_1 : ℝ) • z) hh)
          (oneStepMultiplierAtL2 M n h ((x : ℝ) • z) hh) =
      ∑ x ∈ Finset.range N,
        ((oneShellCenteredExpTwoMoment M) ^ h - 1) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_eq_single r]
          · rw [real_inner_self_eq_norm_sq,
              norm_sq_oneStepMultiplierAtL2 M n h ((r : ℝ) • z) hh]
          · intro s hs _hsr
            exact inner_oneStepMultiplierAtL2_nat_smul_eq_zero
              M n h hh hz _hsr
          · exact fun hrnot => absurd hr hrnot
    _ = (N : ℝ) * ((oneShellCenteredExpTwoMoment M) ^ h - 1) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The scalar Birkhoff averages along any translation beyond the covariance
range converge strongly to zero. -/
theorem tendsto_birkhoffAverage_oneStepMultiplierAtL2_zero {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (hh : 0 < h)
    {z : Vec d}
    (hz : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) < ‖z‖) :
    letI := potentialSequenceVAddInvariant M
    Tendsto
      (fun N => birkhoffAverage ℝ
        (Stationary.koopman (mu := M.P.toMeasure) z).toContinuousLinearMap
        id N (oneStepMultiplierAtL2 M n h 0 hh))
      atTop (nhds 0) := by
  let := potentialSequenceVAddInvariant M
  let V : ℝ := (oneShellCenteredExpTwoMoment M) ^ h - 1
  have hV : 0 ≤ V := by
    dsimp only [V]
    rw [← norm_sq_oneStepMultiplierAtL2 M n h 0 hh]
    positivity
  have havg : ∀ N : ℕ, 0 < N →
      ‖birkhoffAverage ℝ
        (Stationary.koopman (mu := M.P.toMeasure) z).toContinuousLinearMap
        id N (oneStepMultiplierAtL2 M n h 0 hh)‖ =
        Real.sqrt (V / (N : ℝ)) := by
    intro N hN
    have hiter : ∀ r ∈ Finset.range N,
        (((Stationary.koopman (mu := M.P.toMeasure) z).toContinuousLinearMap ^[r])
          (oneStepMultiplierAtL2 M n h 0 hh)) =
        oneStepMultiplierAtL2 M n h ((r : ℝ) • z) hh := by
      intro r _
      exact iterate_koopman_oneStepMultiplierAtL2 M n h z hh r
    have hsum : birkhoffSum
        (Stationary.koopman (mu := M.P.toMeasure) z).toContinuousLinearMap
        id N (oneStepMultiplierAtL2 M n h 0 hh) =
        ∑ r ∈ Finset.range N,
          oneStepMultiplierAtL2 M n h ((r : ℝ) • z) hh := by
      unfold birkhoffSum
      apply Finset.sum_congr rfl
      intro r hr
      simpa only [id_eq] using! hiter r hr
    have hsquare :
        ‖birkhoffAverage ℝ
          (Stationary.koopman (mu := M.P.toMeasure) z).toContinuousLinearMap
          id N (oneStepMultiplierAtL2 M n h 0 hh)‖ ^ 2 = V / (N : ℝ) := by
      rw [birkhoffAverage, hsum, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)), mul_pow,
        norm_sq_sum_oneStepMultiplierAtL2_nat_smul M n h N hh hz]
      dsimp only [V]
      have hNreal : (N : ℝ) ≠ 0 := by positivity
      field_simp
    have hright : 0 ≤ V / (N : ℝ) := div_nonneg hV (Nat.cast_nonneg N)
    have hsqrtSq := Real.sq_sqrt hright
    nlinarith [norm_nonneg (birkhoffAverage ℝ
      (Stationary.koopman (mu := M.P.toMeasure) z).toContinuousLinearMap
      id N (oneStepMultiplierAtL2 M n h 0 hh)), Real.sqrt_nonneg (V / (N : ℝ))]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hquot : Tendsto (fun N : ℕ => V / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (V / (N : ℝ)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using!
      Real.continuous_sqrt.continuousAt.tendsto.comp hquot
  exact hsqrt.congr' <| (eventually_gt_atTop (0 : ℕ)).mono fun N hN =>
    (havg N hN).symm

/-- The mean-ergodic fixed component of the fresh-shell multiplier vanishes
for every translation longer than the covariance range. -/
theorem orthogonalProjection_eqLocus_koopman_oneStepMultiplierAtL2_eq_zero
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (hh : 0 < h) {z : Vec d}
    (hz : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + h) < ‖z‖) :
    letI := potentialSequenceVAddInvariant M
    (LinearMap.eqLocus
      (Stationary.koopman (mu := M.P.toMeasure) z).toContinuousLinearMap.toLinearMap (ContinuousLinearMap.id ℝ (Lp ℝ 2 M.P.toMeasure)).toLinearMap
      ).orthogonalProjectionOnto (oneStepMultiplierAtL2 M n h 0 hh) = 0 := by
  let := potentialSequenceVAddInvariant M
  have hmean : Tendsto
      (fun N => birkhoffAverage ℝ
        (Stationary.koopman
          (mu := M.P.toMeasure) z).toContinuousLinearMap id N
        (oneStepMultiplierAtL2 M n h 0 hh)) atTop
      (nhds ((LinearMap.eqLocus
        (Stationary.koopman
          (mu := M.P.toMeasure) z).toContinuousLinearMap.toLinearMap (ContinuousLinearMap.id ℝ (Lp ℝ 2 M.P.toMeasure)).toLinearMap).orthogonalProjectionOnto
        (oneStepMultiplierAtL2 M n h 0 hh))) :=
    tendsto_birkhoffAverage_linearIsometry
      (E := Stationary.ScalarL2 M.P.toMeasure)
      (Stationary.koopman (mu := M.P.toMeasure) z)
      (oneStepMultiplierAtL2 M n h 0 hh)
  have hzero : Tendsto
      (fun N => birkhoffAverage ℝ
        (Stationary.koopman
          (mu := M.P.toMeasure) z).toContinuousLinearMap id N
        (oneStepMultiplierAtL2 M n h 0 hh)) atTop (nhds 0) := by
    exact tendsto_birkhoffAverage_oneStepMultiplierAtL2_zero M n h hh hz
  apply Subtype.ext
  exact tendsto_nhds_unique
    (f := fun N => birkhoffAverage ℝ
      (Stationary.koopman
        (mu := M.P.toMeasure) z).toContinuousLinearMap id N
      (oneStepMultiplierAtL2 M n h 0 hh))
    (l := atTop) hmean hzero

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
