import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellDerivativeAggregation
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellW1pPackaging

/-!
# Fixed-point moments for the literal shell `W^{1,4}` datum

This file transfers the differentiated-multiplier estimate to every literal
Jacobian entry of the vector forcing used by the Dirichlet and Neumann
Calderon--Zygmund packages.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Exact Jacobian formula for the literal suffix forcing. -/
theorem oneStepShellForcingW14_jacobian_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (x : Vec d) (i j : Fin d) :
    (oneStepShellForcingW14 M n h omega p Q hh).jacobian x i j =
      (p i • fderiv ℝ (fun y => oneStepMultiplierAt M n h y omega) x)
        (basisVec j) := by
  change
    (fderiv ℝ (fun y => oneStepMultiplierAt M n h y omega * p i) x)
        (basisVec j) = _
  rw [(hasFDerivAt_oneStepMultiplierAt M n h omega x hh).mul_const (p i) |>.fderiv]
  rw [(hasFDerivAt_oneStepMultiplierAt M n h omega x hh).fderiv]

private theorem norm_basisVec_oneStep {d : ℕ} (i : Fin d) :
    ‖(basisVec i : Vec d)‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).2 ?_
    intro j
    by_cases hji : j = i
    · subst j
      simp [basisVec]
    · simp [basisVec, hji]
  · have hi : ‖basisVec i i‖ ≤ ‖(basisVec i : Vec d)‖ :=
      norm_le_pi_norm (basisVec i) i
    simpa [basisVec] using hi

/-- The parent-scale size of each literal Jacobian entry is bounded by the
fixed-point differentiated-multiplier observable. -/
theorem parentScale_mul_abs_oneStepShellForcingW14_jacobian_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (p : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (x : Vec d) (i j : Fin d) :
    (3 : ℝ) ^ n *
        |(oneStepShellForcingW14 M n h omega p Q hh).jacobian x i j| ≤
      |p i| * ((3 : ℝ) ^ n *
        ‖fderiv ℝ (fun y => oneStepMultiplierAt M n h y omega) x‖) := by
  rw [oneStepShellForcingW14_jacobian_apply]
  have hbasis : ‖(basisVec j : Vec d)‖ = 1 := norm_basisVec_oneStep j
  let L := fderiv ℝ (fun y => oneStepMultiplierAt M n h y omega) x
  have happ := ContinuousLinearMap.le_opNorm
    L (basisVec j)
  rw [hbasis, mul_one] at happ
  change (3 : ℝ) ^ n * |p i * L (basisVec j)| ≤
    |p i| * ((3 : ℝ) ^ n * ‖L‖)
  rw [abs_mul]
  have hpow : 0 ≤ (3 : ℝ) ^ n := by positivity
  calc
    (3 : ℝ) ^ n * (|p i| * |L (basisVec j)|) =
        |p i| * ((3 : ℝ) ^ n * |L (basisVec j)|) := by ring
    _ ≤ |p i| * ((3 : ℝ) ^ n * ‖L‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using happ) hpow)
        (abs_nonneg _)

/-- Uniform random `L^4` estimate for every entry of the literal shell
Jacobian on a translated scale-`n` parent cube. -/
theorem eLpNorm_parentScale_oneStepShellForcingW14_jacobian_four_le_delta
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (z x : Vec d) (p : Vec d) (Q : TriadicCube d) (i j : Fin d)
    (hh : 0 < h) (hscale : (h : ℝ) ≤ M.delta⁻¹)
    (hx : x - z ∈ openCubeSet (originCube d (n : ℤ))) :
    eLpNorm (fun omega : Sample d =>
        (3 : ℝ) ^ n *
          |(oneStepShellForcingW14 M n h omega p Q hh).jacobian x i j|)
      4 M.P.toMeasure ≤
        ENNReal.ofReal
          (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta)) := by
  let D : Sample d → ℝ := fun omega =>
    (3 : ℝ) ^ n *
      ‖fderiv ℝ (fun y => oneStepMultiplierAt M n h y omega) x‖
  calc
    eLpNorm (fun omega : Sample d =>
        (3 : ℝ) ^ n *
          |(oneStepShellForcingW14 M n h omega p Q hh).jacobian x i j|)
        4 M.P.toMeasure ≤
      eLpNorm (fun omega : Sample d => |p i| * D omega)
        4 M.P.toMeasure := by
      apply eLpNorm_mono_ae
      exact Filter.Eventually.of_forall fun omega => by
        have hD : 0 ≤ D omega := by
          dsimp [D]
          exact mul_nonneg (by positivity) (norm_nonneg _)
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (abs_nonneg (p i)) hD)]
        have hlhs : 0 ≤ (3 : ℝ) ^ n *
            |(oneStepShellForcingW14 M n h omega p Q hh).jacobian x i j| :=
          mul_nonneg (by positivity) (abs_nonneg _)
        rw [abs_of_nonneg hlhs]
        exact parentScale_mul_abs_oneStepShellForcingW14_jacobian_le
          M n h omega p Q hh x i j
    _ = ENNReal.ofReal |p i| * eLpNorm D 4 M.P.toMeasure := by
      rw [show (fun omega : Sample d => |p i| * D omega) = |p i| • D by rfl,
        eLpNorm_const_smul]
      rw [Real.enorm_eq_ofReal (abs_nonneg _)]
    _ ≤ ENNReal.ofReal |p i| *
        ENNReal.ofReal (oneStepMultiplierDerivativeFourthConst * M.delta) := by
      have hderiv :=
        eLpNorm_parentScale_fderiv_oneStepMultiplierAt_four_le_delta
          M n h z x hh hscale hx
      exact mul_le_mul_right (by simpa only [D] using hderiv) _
    _ = ENNReal.ofReal
        (|p i| * (oneStepMultiplierDerivativeFourthConst * M.delta)) := by
      rw [ENNReal.ofReal_mul (abs_nonneg _)]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
