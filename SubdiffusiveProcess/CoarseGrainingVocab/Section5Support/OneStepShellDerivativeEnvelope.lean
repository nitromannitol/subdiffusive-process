import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepShellDerivativeMoment




open MeasureTheory Homogenization
open SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem deriv_spatialScale (r : ℝ) (g : PotentialField d) (x : Vec d) :
    PotentialField.deriv (PotentialField.spatialScale r g) x =
      r • PotentialField.deriv g (r • x) := by
  have hcomp : HasFDerivAt (fun y : Vec d => g (r • y))
      (r • PotentialField.deriv g (r • x)) x := by
    have h := (g.hasFDerivAt (r • x)).comp x ((hasFDerivAt_id x).const_smul r)
    simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
      Function.comp_def] using h
  have hstored : HasFDerivAt (fun y : Vec d => g (r • y))
      (PotentialField.deriv (PotentialField.spatialScale r g) x) x := by
    simpa only [PotentialField.spatialScale_apply] using
      (PotentialField.spatialScale r g).hasFDerivAt x
  exact hstored.unique hcomp

private theorem deriv_translate (z : Vec d) (g : PotentialField d) (x : Vec d) :
    PotentialField.deriv (PotentialField.translate z g) x =
      PotentialField.deriv g (x + z) := by
  have hcomp : HasFDerivAt (fun y : Vec d => g (y + z))
      (PotentialField.deriv g (x + z)) x := by
    have h := (g.hasFDerivAt (x + z)).comp x ((hasFDerivAt_id x).add_const z)
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using h
  have hstored : HasFDerivAt (fun y : Vec d => g (y + z))
      (PotentialField.deriv (PotentialField.translate z g) x) x := by
    simpa only [PotentialField.translate_apply] using
      (PotentialField.translate z g).hasFDerivAt x
  exact hstored.unique hcomp

private theorem deriv_unscalePotential (k : ℕ) (g : PotentialField d) (x : Vec d) :
    PotentialField.deriv (unscalePotential k g) (((3 : ℝ) ^ k)⁻¹ • x) =
      (3 : ℝ) ^ k • PotentialField.deriv g x := by
  have h3 : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  rw [unscalePotential, deriv_spatialScale, smul_smul,
    mul_inv_cancel₀ h3, one_smul]

private theorem deriv_eq_smul_deriv_unscalePotential (k : ℕ)
    (g : PotentialField d) (x : Vec d) :
    PotentialField.deriv g x = (((3 : ℝ) ^ k)⁻¹) •
      PotentialField.deriv (unscalePotential k g) ((((3 : ℝ) ^ k)⁻¹) • x) := by
  have h3 : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  rw [deriv_unscalePotential, smul_smul, inv_mul_cancel₀ h3, one_smul]

private theorem scaled_mem_unitCube {k : ℤ} {j : ℕ} (hkj : k ≤ (j : ℤ))
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d k)) :
    (((3 : ℝ) ^ j)⁻¹) • x ∈ openCubeSet (originCube d 0) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hscale : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (j : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) hkj
  have hxi := hx i
  simp only [Pi.smul_apply, smul_eq_mul, zpow_zero, mul_one]
  constructor
  · rw [← div_eq_inv_mul, lt_div_iff₀ h3j]
    calc
      -(1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ k := by
        exact mul_le_mul_of_nonpos_left hscale (by norm_num)
      _ < x i := hxi.1
  · rw [← div_eq_inv_mul, div_lt_iff₀ h3j]
    calc
      x i < (1 / 2 : ℝ) * (3 : ℝ) ^ k := hxi.2
      _ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ j :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)

/-- One physical shell derivative on a scale-`n` translated parent is
bounded by its own-scale `(g2)` observable with the geometric scale ratio. -/
theorem parentScale_mul_norm_shellDerivative_le_gauge {d : ℕ}
    (n k : ℕ) (z x : Vec d) (omega : Sample d)
    (hx : x - z ∈ openCubeSet (originCube d (n : ℤ))) :
    (3 : ℝ) ^ n * ‖PotentialField.deriv (omega (n + 1 + k)) x‖ ≤
      ((3 : ℝ) ^ (k + 1))⁻¹ *
        translatedShellG2 (n + 1 + k)
          ((((3 : ℝ) ^ (n + 1 + k))⁻¹) • z) omega := by
  let j : ℕ := n + 1 + k
  let z' : Vec d := (((3 : ℝ) ^ j)⁻¹) • z
  let u : Vec d := (((3 : ℝ) ^ j)⁻¹) • (x - z)
  let g : PotentialField d := PotentialField.translate z' (unscalePotential j (omega j))
  have hnj : (n : ℤ) ≤ (j : ℤ) := by
    dsimp [j]
    omega
  have hu : u ∈ openCubeSet (originCube d 0) := by
    exact scaled_mem_unitCube hnj hx
  have hg := PotentialField.norm_deriv_le_g2Observable g hu
  have harg : u + z' = (((3 : ℝ) ^ j)⁻¹) • x := by
    dsimp [u, z']
    rw [← smul_add]
    congr 1
    abel
  rw [deriv_translate, harg] at hg
  have hphysical := deriv_eq_smul_deriv_unscalePotential j (omega j) x
  have hnorm : ‖PotentialField.deriv (omega j) x‖ ≤
      ((3 : ℝ) ^ j)⁻¹ * translatedShellG2 j z' omega := by
    rw [hphysical, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (pow_pos (by norm_num) _))]
    exact mul_le_mul_of_nonneg_left hg (by positivity)
  calc
    (3 : ℝ) ^ n * ‖PotentialField.deriv (omega (n + 1 + k)) x‖ =
        (3 : ℝ) ^ n * ‖PotentialField.deriv (omega j) x‖ := by rfl
    _ ≤ (3 : ℝ) ^ n *
        (((3 : ℝ) ^ j)⁻¹ * translatedShellG2 j z' omega) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = ((3 : ℝ) ^ (k + 1))⁻¹ * translatedShellG2 j z' omega := by
      dsimp [j, z']
      rw [pow_add, pow_add]
      field_simp
      ring

/-- Range-indexed form of the literal one-step derivative. -/
theorem oneStepShellDerivative_eq_sum_range {d : ℕ}
    (n h : ℕ) (omega : Sample d) (x : Vec d) :
    oneStepShellDerivative n h omega x =
      ∑ k ∈ Finset.range h, PotentialField.deriv (omega (n + 1 + k)) x := by
  unfold oneStepShellDerivative cutoffShellIndices
  rw [show Int.toNat ((n : ℤ) + 1) = n + 1 by omega]
  rw [show Finset.Icc (n + 1) (n + h) = Finset.Ico (n + 1) (n + h + 1) by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : n + h + 1 - (n + 1) = h := by omega
  rw [hlen]

/-- Parent-side times the norm of the complete shell-block derivative is
bounded by the geometric gauge. -/
theorem parentScale_mul_norm_oneStepShellDerivative_le_gauge {d : ℕ}
    (n h : ℕ) (z x : Vec d) (omega : Sample d)
    (hx : x - z ∈ openCubeSet (originCube d (n : ℤ))) :
    (3 : ℝ) ^ n * ‖oneStepShellDerivative n h omega x‖ ≤
      oneStepShellDerivativeGauge n h z omega := by
  rw [oneStepShellDerivative_eq_sum_range]
  calc
    (3 : ℝ) ^ n * ‖∑ k ∈ Finset.range h,
        PotentialField.deriv (omega (n + 1 + k)) x‖ ≤
      (3 : ℝ) ^ n * ∑ k ∈ Finset.range h,
        ‖PotentialField.deriv (omega (n + 1 + k)) x‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ k ∈ Finset.range h,
        ((3 : ℝ) ^ n * ‖PotentialField.deriv (omega (n + 1 + k)) x‖) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range h,
        (((3 : ℝ) ^ (k + 1))⁻¹ *
          translatedShellG2 (n + 1 + k)
            ((((3 : ℝ) ^ (n + 1 + k))⁻¹) • z) omega) := by
      exact Finset.sum_le_sum fun k _ =>
        parentScale_mul_norm_shellDerivative_le_gauge n k z x omega hx
    _ = oneStepShellDerivativeGauge n h z omega := by
      rfl

/-- The literal multiplier derivative inherits the same envelope, multiplied
by the positive lognormal shell ratio. -/
theorem parentScale_mul_norm_fderiv_oneStepMultiplierAt_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (z x : Vec d) (omega : Sample d) (hh : 0 < h)
    (hx : x - z ∈ openCubeSet (originCube d (n : ℤ))) :
    (3 : ℝ) ^ n * ‖fderiv ℝ (fun y => oneStepMultiplierAt M n h y omega) x‖ ≤
      Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
        (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        oneStepShellDerivativeGauge n h z omega := by
  rw [(hasFDerivAt_oneStepMultiplierAt M n h omega x hh).fderiv,
    norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have henv := parentScale_mul_norm_oneStepShellDerivative_le_gauge
    n h z x omega hx
  nlinarith [Real.exp_pos
    (cutoffShellSum (n + h) (n : ℤ) x omega -
      (h : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
