module

public import SubdiffusiveProcess.Dirichlet.RestrictedResponseMeasurability
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FinalRandomFactor
public import SubdiffusiveProcess.Frozen.Section5.HomogenizedCoefficientReciprocalLower

@[expose] public section

/-!
# `σ(A_{L,N})`-measurability of the cutoff Dirichlet random factor

The random factor `Z_{L,N}` of `t.cutoff.Dirichlet.homogenization` is a fixed polynomial in the
coarse-grained response errors `ℰ(𝒞_N; a_L, ahom_L)`.  Those errors depend on `a_L|_{𝒞_N}` only
(`RestrictedResponseMeasurability.lean`), and `a_L|_{𝒞_N}` is the same information as
`A_{L,N}|_{𝒞_0}` because `A_{L,N}(x) = ahom⁻¹ a_L(3^N x)`.  Hence `Z_{L,N}` is measurable for
`restrictedCoefficientSigma (rescaledCutoffCoefficient M L N) (cube d 0)`.
-/

namespace SubdiffusiveProcess.RestrictedResponse

open Filter MeasureTheory
open Homogenization hiding Vec TriadicCube Mat
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped BigOperators ENNReal

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

/-- The centered cube is the sup-norm ball of radius `3^m / 2`. -/
theorem cube_eq_ball (m : ℤ) :
    cube d m = Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2) := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ m / 2 := by positivity
  ext x
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hpos]
  simp only [cube, openCubeSet, originCube, cubeScaleFactor, Set.mem_setOf_eq, Real.norm_eq_abs,
    abs_lt, Pi.zero_apply, Int.cast_zero]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- Coordinatewise clamp of `ℝ^d` to the closed centered cube `[-3^m/2, 3^m/2]^d`, as a
retraction into `closure (cube d m)`. -/
def clampRetract (d : ℕ) (m : ℤ) : ClosureRetract (cube d m) where
  toFun x := fun i => max (-((3 : ℝ) ^ m / 2)) (min ((3 : ℝ) ^ m / 2) (x i))
  continuous_toFun :=
    continuous_pi fun i =>
      continuous_const.max (continuous_const.min (continuous_apply i))
  mem_closure x := by
    have hpos : (0 : ℝ) < (3 : ℝ) ^ m / 2 := by positivity
    rw [cube_eq_ball, closure_ball _ hpos.ne', Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg hpos.le]
    intro i
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- The clamp fixes the open cube pointwise. -/
theorem clampRetract_apply_of_mem_cube (m : ℤ) {x : Vec d} (hx : x ∈ cube d m) :
    (clampRetract d m).toFun x = x := by
  rw [cube_eq_ball, Metric.mem_ball, dist_zero_right,
    pi_norm_lt_iff (by positivity)] at hx
  funext i
  have hi := hx i
  rw [Real.norm_eq_abs, abs_lt] at hi
  show max (-((3 : ℝ) ^ m / 2)) (min ((3 : ℝ) ^ m / 2) (x i)) = x i
  rw [min_eq_right hi.2.le, max_eq_right hi.1.le]

/-- The first full response error is measurable for the `𝒞_N`-restricted cutoff sigma-field. -/
theorem measurable_dirichletFullResponseOne_restricted
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ) (s : ℝ) :
    Measurable[restrictedCoefficientSigma (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L)
      (cube d (N : ℤ))] (dirichletFullResponseOne M L N s) :=
  (measurable_paperHomogenizationError_infinity_finite_aCutoffFamily_restricted
    M L (clampRetract d (N : ℤ)) (originCube d (N : ℤ)) (N : ℤ) le_rfl
    (fun _ hx => clampRetract_apply_of_mem_cube (N : ℤ) hx) s 1).ennreal_toReal

/-- The second full response error is measurable for the `𝒞_N`-restricted cutoff sigma-field. -/
theorem measurable_dirichletFullResponseTwo_restricted
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ) (s : ℝ) :
    Measurable[restrictedCoefficientSigma (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L)
      (cube d (N : ℤ))] (dirichletFullResponseTwo M L N s) :=
  (measurable_paperHomogenizationError_infinity_finite_aCutoffFamily_restricted
    M L (clampRetract d (N : ℤ)) (originCube d (N : ℤ)) (N : ℤ) le_rfl
    (fun _ hx => clampRetract_apply_of_mem_cube (N : ℤ) hx) (s / 2) 2).ennreal_toReal

/-- The raw cutoff on `𝒞_N` carries no more information than the rescaled coefficient on
`𝒞_0`. -/
theorem restrictedCoefficientSigma_aCutoff_cube_le_rescaled
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ) :
    restrictedCoefficientSigma (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L) (cube d (N : ℤ)) ≤
      restrictedCoefficientSigma (fun omega => rescaledCutoffCoefficient M L N omega)
        (cube d 0) := by
  have hahom : ahom M L ≠ 0 := ne_of_gt ((Real.exp_pos _).trans_le
    (SubdiffusiveProcess.Frozen.Section5.homogenized_coefficient_reciprocal_lower M L))
  have hc : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  refine iSup_le fun ⟨x, hxcube⟩ => ?_
  have hy : ((3 : ℝ) ^ N)⁻¹ • (x : Vec d) ∈ cube d 0 := by
    have hxball := hxcube
    rw [cube_eq_ball, Metric.mem_ball, dist_zero_right, zpow_natCast] at hxball
    rw [cube_eq_ball, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hc), zpow_zero]
    calc ((3 : ℝ) ^ N)⁻¹ * ‖(x : Vec d)‖ < ((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ N / 2) :=
          mul_lt_mul_of_pos_left hxball (inv_pos.2 hc)
      _ = 1 / 2 := by field_simp
  have hmeas : Measurable[restrictedCoefficientSigma
      (fun omega => rescaledCutoffCoefficient M L N omega) (cube d 0)]
      (fun omega => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x : Vec d)) := by
    have h0 := measurable_eval_restrictedCoefficientSigma
      (a := fun omega => rescaledCutoffCoefficient M L N omega) hy
    have heq : (fun omega => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x : Vec d)) =
        fun omega => ahom M L *
          rescaledCutoffCoefficient M L N omega (((3 : ℝ) ^ N)⁻¹ • (x : Vec d)) := by
      funext omega
      unfold rescaledCutoffCoefficient
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
      field_simp
    rw [heq]
    exact h0.const_mul _
  exact hmeas.comap_le

/-- **`Z_{L,N}` is `σ(A_{L,N}|_{𝒞_0})`-measurable.** -/
theorem measurable_cutoffDirichletRandomFactor_restricted
    [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
    (C vartheta : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1) :
    @Measurable (Sample d) ℝ
      (restrictedCoefficientSigma (fun omega => rescaledCutoffCoefficient M L N omega)
        (cube d 0))
      (borel ℝ) (cutoffDirichletRandomFactor M L N C vartheta hvartheta) := by
  letI : MeasurableSpace (Sample d) :=
    restrictedCoefficientSigma (fun omega => rescaledCutoffCoefficient M L N omega) (cube d 0)
  have hle := restrictedCoefficientSigma_aCutoff_cube_le_rescaled M L N
  have hE1 : Measurable (dirichletFullResponseOne M L N (dirichletS1 vartheta)) :=
    (measurable_dirichletFullResponseOne_restricted M L N (dirichletS1 vartheta)).mono hle le_rfl
  have hE2 : Measurable (dirichletFullResponseTwo M L N (dirichletS1 vartheta)) :=
    (measurable_dirichletFullResponseTwo_restricted M L N (dirichletS1 vartheta)).mono hle le_rfl
  have hY : Measurable (dirichletEllipticityEnvelope M L N (dirichletS1 vartheta)) := by
    unfold dirichletEllipticityEnvelope
    exact measurable_const.add (measurable_const.mul hE2)
  change Measurable (cutoffDirichletRandomFactor M L N C vartheta hvartheta)
  unfold cutoffDirichletRandomFactor dirichletReadoutRandomFactor
    dirichletUniversalRandomFactor dirichletRandomFactor
  refine measurable_const.add (measurable_const.mul ?_)
  have hFirst : Measurable fun omega =>
      Real.rpow 3 (dirichletS1 vartheta *
          (dirichletBalanceScale vartheta M.delta : ℝ)) *
        dirichletFullResponseOne M L N (dirichletS1 vartheta) omega *
          dirichletEllipticityEnvelope M L N (dirichletS1 vartheta) omega :=
    (measurable_const.mul hE1).mul hY
  have hSecond : Measurable fun omega =>
      Real.rpow 3 (-dirichletS2 vartheta *
          (dirichletBalanceScale vartheta M.delta : ℝ)) *
        (1 + Real.rpow 3 (dirichletS1 vartheta *
          (dirichletBalanceScale vartheta M.delta : ℝ)) *
            (dirichletFullResponseTwo M L N (dirichletS1 vartheta) omega) ^ 2) :=
    measurable_const.mul
      (measurable_const.add (measurable_const.mul (hE2.pow_const 2)))
  exact (measurable_const.add
    ((measurable_const.mul measurable_const).mul (hFirst.add hSecond))).add
      (((measurable_const.mul measurable_const).mul hE1).mul hY)

end

end SubdiffusiveProcess.RestrictedResponse
