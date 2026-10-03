module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFractionalMultiplier
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The dual norm of the supremum norm on `Vec d` is the sum of the absolute
values of the coordinates of the functional. -/
theorem fluxRowFractional_opNorm_le_sum (L : Vec d →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, |L (basisVec i)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have hx : x = ∑ i, x i • basisVec i := by
    funext j
    simp [basisVec, Finset.sum_apply, Pi.single_apply]
  have hL : L x = ∑ i, x i * L (basisVec i) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, smul_eq_mul]
  calc ‖L x‖ = |∑ i, x i * L (basisVec i)| := by rw [hL, Real.norm_eq_abs]
    _ ≤ ∑ i, |x i * L (basisVec i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖x‖ * |L (basisVec i)| := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i) (abs_nonneg _)
    _ = (∑ i, |L (basisVec i)|) * ‖x‖ := by rw [← Finset.mul_sum, mul_comm]

/-- The Lipschitz constant of the cutoff adapted to a cell of side `3 ^ n`. -/
def fluxRowFractionalCellLipschitz (d : ℕ) (n : ℤ) : ℝ :=
  32 * (d : ℝ) * ((3 : ℝ) ^ n)⁻¹

theorem fluxRowFractionalCellLipschitz_pos (hd : 0 < d) (n : ℤ) :
    0 < fluxRowFractionalCellLipschitz d n := by
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold fluxRowFractionalCellLipschitz
  positivity

open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay in
/-- **The smooth cutoff subordinate to a stopping cell.**  It is `1` on the
cell `z + □_n`, vanishes outside the centred threefold enlargement
`z + □_{n+1}`, takes values in `[0,1]`, and is Lipschitz with constant
`32 d / 3 ^ n`. -/
theorem exists_fluxRowFractionalCellCutoff (d : ℕ) (n : ℤ) (z : Vec d) :
    ∃ chi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧
      (∀ x, 0 ≤ chi x) ∧ (∀ x, chi x ≤ 1) ∧
      (∀ x ∈ translatedCube d n z, chi x = 1) ∧
      (∀ x, x ∉ translatedCube d (n + 1) z → chi x = 0) ∧
      (∀ x y, |chi x - chi y| ≤
        fluxRowFractionalCellLipschitz d n * ‖x - y‖) := by
  classical
  set r : ℝ := (1 / 2 : ℝ) * 3 ^ n with hr_def
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hr : 0 < r := by rw [hr_def]; positivity
  have hle : (fun i ↦ z i - r) ≤ (fun i ↦ z i + r) := by
    intro i
    dsimp only
    linarith
  obtain ⟨eta, hsmooth, hIcc, hone, hzero, hderiv, _hsq, _hvol⟩ :=
    exists_smoothBoxCutoff (fun i ↦ z i - r) (fun i ↦ z i + r) r hr hle
  have hsucc : (3 : ℝ) ^ (n + 1) = 3 ^ n * 3 := zpow_add_one₀ (by norm_num) n
  refine ⟨eta, hsmooth, fun x ↦ (hIcc x).1, fun x ↦ (hIcc x).2,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun x y ↦ ?_⟩
  · refine hone x ?_
    rw [mem_translatedCube_iff, cube, mem_openCubeSet_originCube_iff] at hx
    refine Set.mem_Icc.2 ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · have := (hx i).1
      simp only [Pi.sub_apply] at this
      simp only [hr_def]
      linarith
    · have := (hx i).2
      simp only [Pi.sub_apply] at this
      simp only [hr_def]
      linarith
  · refine hzero x fun hmem ↦ hx ?_
    rw [Set.mem_Icc] at hmem
    rw [mem_translatedCube_iff, cube, mem_openCubeSet_originCube_iff]
    intro i
    have h1 := hmem.1 i
    have h2 := hmem.2 i
    simp only at h1 h2
    simp only [Pi.sub_apply, hsucc]
    constructor <;> [skip; skip] <;> rw [hr_def] at h1 h2 <;> nlinarith
  · -- the mean value inequality with the dual-norm bound
    have hdiff : Differentiable ℝ eta := hsmooth.differentiable (by norm_num)
    have hbound : ∀ w : Vec d, ‖fderiv ℝ eta w‖ ≤
        fluxRowFractionalCellLipschitz d n := by
      intro w
      refine (fluxRowFractional_opNorm_le_sum (fderiv ℝ eta w)).trans ?_
      have hstep : ∀ i : Fin d, |fderiv ℝ eta w (basisVec i)| ≤ 16 / r := by
        intro i
        simpa [basisVec] using hderiv w i
      refine (Finset.sum_le_sum fun i _ ↦ hstep i).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold fluxRowFractionalCellLipschitz
      rw [hr_def]
      field_simp
      linarith
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := eta) (s := (Set.univ : Set (Vec d)))
      (C := fluxRowFractionalCellLipschitz d n) (x := y) (y := x)
      (fun w _ ↦ hdiff w) (fun w _ ↦ hbound w) convex_univ
      (Set.mem_univ y) (Set.mem_univ x)
    simpa [Real.norm_eq_abs] using hmv

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
