import SubdiffusiveProcess.Variance.NormFacts
import Mathlib.Probability.Moments.Variance

/-!
# The variance algebra of `l.var.bounds`

For a random matrix `M` on a probability space, `varE P M = 𝔼|M - 𝔼M|²` (operator norm, entrywise
mean) as an extended nonnegative number.  If `X ≤ Y ≤ X + w Id` in the Loewner order almost surely
then `varE P X ≤ 2 varE P Y + 8 𝔼 w²`.  The proof is `var X ≤ 2 var Y + 2 𝔼|D - 𝔼D|²` and
`|D - 𝔼D| ≤ w + 𝔼 w`; when `𝔼 w² = ∞` or `varE P Y = ∞` there is nothing to prove.
-/

open MeasureTheory Homogenization Homogenization.Book.Ch02
open scoped ENNReal

namespace SubdiffusiveProcess.Variance

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The entrywise mean of a random matrix. -/
noncomputable def meanMat (P : Measure Ω) (M : Ω → Mat d) : Mat d :=
  Matrix.of fun i j => ∫ b, M b i j ∂P

/-- `var[M] = 𝔼|M - 𝔼M|²` (operator norm), extended-nonnegative valued. -/
noncomputable def varE (P : Measure Ω) (M : Ω → Mat d) : ℝ≥0∞ :=
  ∫⁻ a, ENNReal.ofReal (matrixNorm (M a - meanMat P M) ^ 2) ∂P

theorem quad_meanMat (P : Measure Ω) (M : Ω → Mat d) (hM : ∀ i j, Integrable (fun ω => M ω i j) P)
    (v : Vec d) :
    vecDot v (matVecMul (meanMat P M) v) = ∫ ω, vecDot v (matVecMul (M ω) v) ∂P := by
  unfold vecDot matVecMul meanMat
  simp only [Matrix.of_apply]
  rw [integral_finset_sum _ (fun i _ => ?_)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_finset_sum _ (fun j _ => ?_)]
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const]
    · exact (hM i j).mul_const (v j)
  · exact (integrable_finset_sum _ fun j _ => (hM i j).mul_const (v j)).const_mul (v i)

theorem integrable_quad (P : Measure Ω) (M : Ω → Mat d) (hM : ∀ i j, Integrable (fun ω => M ω i j) P)
    (v : Vec d) : Integrable (fun ω => vecDot v (matVecMul (M ω) v)) P := by
  unfold vecDot matVecMul
  exact integrable_finset_sum _ fun i _ =>
    (integrable_finset_sum _ fun j _ => (hM i j).mul_const (v j)).const_mul (v i)

theorem isSymm_meanMat (P : Measure Ω) (M : Ω → Mat d) (hsym : ∀ᵐ ω ∂P, (M ω).IsSymm) :
    (meanMat P M).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, meanMat, Matrix.of_apply]
  refine integral_congr_ae ?_
  filter_upwards [hsym] with ω hω
  have := congrFun (congrFun hω j) i
  simpa [Matrix.transpose_apply] using this.symm

theorem ae_matrixNorm_le [NeZero d] (P : Measure Ω) (D : Ω → Mat d) (w : Ω → ℝ)
    (hsym : ∀ᵐ ω ∂P, (D ω).IsSymm)
    (hlow : ∀ᵐ ω ∂P, ∀ v, 0 ≤ vecDot v (matVecMul (D ω) v))
    (hup : ∀ᵐ ω ∂P, ∀ v, vecDot v (matVecMul (D ω) v) ≤ w ω * vecNormSq v) :
    ∀ᵐ ω ∂P, matrixNorm (D ω) ≤ w ω := by
  filter_upwards [hsym, hlow, hup] with ω h1 h2 h3
  exact matrixNorm_le_of_quad_le_const h1 h2 h3

theorem ae_nonneg_of_sandwich [NeZero d] (P : Measure Ω) (D : Ω → Mat d) (w : Ω → ℝ)
    (hlow : ∀ᵐ ω ∂P, ∀ v, 0 ≤ vecDot v (matVecMul (D ω) v))
    (hup : ∀ᵐ ω ∂P, ∀ v, vecDot v (matVecMul (D ω) v) ≤ w ω * vecNormSq v) :
    ∀ᵐ ω ∂P, 0 ≤ w ω := by
  filter_upwards [hlow, hup] with ω h2 h3
  have h := h2 (Pi.single (0 : Fin d) 1)
  have h1 := h3 (Pi.single (0 : Fin d) 1)
  have h4 : vecNormSq (Pi.single (0 : Fin d) (1 : ℝ) : Vec d) = 1 := by
    classical
    simp [vecNormSq, vecDot, Pi.single_apply]
  rw [h4] at h1
  linarith

/-- The mean of a random matrix `0 ≤ D ≤ w Id` has operator norm at most `𝔼 w`. -/
theorem matrixNorm_meanMat_le [NeZero d] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → Mat d) (w : Ω → ℝ) (hD : ∀ i j, Integrable (fun ω => D ω i j) P)
    (hw : Integrable w P) (hsym : ∀ᵐ ω ∂P, (D ω).IsSymm)
    (hlow : ∀ᵐ ω ∂P, ∀ v, 0 ≤ vecDot v (matVecMul (D ω) v))
    (hup : ∀ᵐ ω ∂P, ∀ v, vecDot v (matVecMul (D ω) v) ≤ w ω * vecNormSq v) :
    matrixNorm (meanMat P D) ≤ ∫ ω, w ω ∂P := by
  refine matrixNorm_le_of_quad_le_const (isSymm_meanMat P D hsym) (fun v => ?_) (fun v => ?_)
  · rw [quad_meanMat P D hD]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hlow] with ω h using h v
  · rw [quad_meanMat P D hD, ← integral_mul_const]
    refine integral_mono_ae (integrable_quad P D hD v) (hw.mul_const _) ?_
    filter_upwards [hup] with ω h using h v

theorem matrixNorm_nonneg' (A : Mat d) : 0 ≤ matrixNorm A := by
  unfold matrixNorm
  exact norm_nonneg _

/-- The integrable case: `X ≤ Y ≤ X + w Id` a.s., `Y` integrable, `𝔼 w² < ∞`. -/
theorem var_le_of_integrable [NeZero d] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → Mat d) (w : Ω → ℝ) (hXm : ∀ i j, AEMeasurable (fun ω => X ω i j) P)
    (hwm : AEMeasurable w P) (hXs : ∀ᵐ ω ∂P, (X ω).IsSymm) (hYs : ∀ᵐ ω ∂P, (Y ω).IsSymm)
    (hlow : ∀ᵐ ω ∂P, ∀ v, 0 ≤ vecDot v (matVecMul (Y ω - X ω) v))
    (hup : ∀ᵐ ω ∂P, ∀ v, vecDot v (matVecMul (Y ω - X ω) v) ≤ w ω * vecNormSq v)
    (hY1 : ∀ i j, Integrable (fun ω => Y ω i j) P) (hw2 : Integrable (fun ω => w ω ^ 2) P) :
    varE P X ≤ 2 * varE P Y + 8 * ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) ∂P := by
  set D : Ω → Mat d := fun ω => Y ω - X ω with hD
  have hDs : ∀ᵐ ω ∂P, (D ω).IsSymm := by
    filter_upwards [hXs, hYs] with ω h1 h2
    exact Matrix.IsSymm.sub h2 h1
  have hw_nn := ae_nonneg_of_sandwich P D w hlow hup
  have hmem : MemLp w 2 P := (memLp_two_iff_integrable_sq hwm.aestronglyMeasurable).mpr hw2
  have hwint : Integrable w P := hmem.integrable one_le_two
  have hDnorm := ae_matrixNorm_le P D w hDs hlow hup
  have hD1 : ∀ i j, Integrable (fun ω => D ω i j) P := by
    intro i j
    refine Integrable.mono' hwint
      ((hY1 i j).aestronglyMeasurable.sub (hXm i j).aestronglyMeasurable) ?_
    filter_upwards [hDnorm] with ω h
    rw [Real.norm_eq_abs]
    exact (abs_entry_le_matrixNorm _ i j).trans h
  have hmean : meanMat P X = meanMat P Y - meanMat P D := by
    ext i j
    simp only [meanMat, Matrix.of_apply, Matrix.sub_apply]
    rw [← integral_sub (hY1 i j) (hD1 i j)]
    congr 1
    funext ω
    simp [hD]
  have hmD : matrixNorm (meanMat P D) ≤ ∫ ω, w ω ∂P :=
    matrixNorm_meanMat_le P D w hD1 hwint hDs hlow hup
  set E := ∫ ω, w ω ∂P with hE
  have hpt : ∀ᵐ ω ∂P, matrixNorm (X ω - meanMat P X) ^ 2 ≤
      2 * matrixNorm (Y ω - meanMat P Y) ^ 2 + (4 * w ω ^ 2 + 4 * E ^ 2) := by
    filter_upwards [hDnorm, hw_nn] with ω h1 h2
    have e : X ω - meanMat P X = (Y ω - meanMat P Y) - (D ω - meanMat P D) := by
      rw [hmean]; simp only [hD]; abel
    have t1 : matrixNorm (X ω - meanMat P X) ≤
        matrixNorm (Y ω - meanMat P Y) + (w ω + E) := by
      rw [e]
      exact (matrixNorm_sub_le _ _).trans
        (add_le_add le_rfl ((matrixNorm_sub_le _ _).trans (add_le_add h1 hmD)))
    have t2 := pow_le_pow_left₀ (matrixNorm_nonneg' _) t1 2
    nlinarith [sq_nonneg (matrixNorm (Y ω - meanMat P Y) - (w ω + E)), sq_nonneg (w ω - E)]
  have hE2 : ENNReal.ofReal (E ^ 2) ≤ ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) ∂P := by
    rw [← ofReal_integral_eq_lintegral_ofReal hw2 (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := ProbabilityTheory.variance_nonneg w P
    rw [ProbabilityTheory.variance_eq_sub hmem] at h
    simpa [hE] using h
  have hGm : AEMeasurable (fun ω => 4 * ENNReal.ofReal (w ω ^ 2) + 4 * ENNReal.ofReal (E ^ 2)) P :=
    ((hwm.pow_const 2).ennreal_ofReal.const_mul 4).add_const _
  have h4 : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h2 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  calc varE P X
      = ∫⁻ ω, ENNReal.ofReal (matrixNorm (X ω - meanMat P X) ^ 2) ∂P := rfl
    _ ≤ ∫⁻ ω, (2 * ENNReal.ofReal (matrixNorm (Y ω - meanMat P Y) ^ 2) +
          (4 * ENNReal.ofReal (w ω ^ 2) + 4 * ENNReal.ofReal (E ^ 2))) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpt, hw_nn] with ω h1 h2
        calc ENNReal.ofReal (matrixNorm (X ω - meanMat P X) ^ 2)
            ≤ ENNReal.ofReal (2 * matrixNorm (Y ω - meanMat P Y) ^ 2 +
                (4 * w ω ^ 2 + 4 * E ^ 2)) := ENNReal.ofReal_le_ofReal h1
          _ = 2 * ENNReal.ofReal (matrixNorm (Y ω - meanMat P Y) ^ 2) +
                (4 * ENNReal.ofReal (w ω ^ 2) + 4 * ENNReal.ofReal (E ^ 2)) := by
            have hn := matrixNorm_nonneg' (Y ω - meanMat P Y)
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_mul (by norm_num)]
            simp
    _ = 2 * varE P Y + (4 * ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) ∂P + 4 * ENNReal.ofReal (E ^ 2)) := by
        have hI : ∫⁻ ω, (4 * ENNReal.ofReal (w ω ^ 2) + 4 * ENNReal.ofReal (E ^ 2)) ∂P =
            4 * ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) ∂P + 4 * ENNReal.ofReal (E ^ 2) := by
          rw [lintegral_add_right' (fun ω => 4 * ENNReal.ofReal (w ω ^ 2))
            (aemeasurable_const (b := 4 * ENNReal.ofReal (E ^ 2))),
            lintegral_const_mul' _ _ h4, lintegral_const, measure_univ, mul_one]
        rw [lintegral_add_right' _ hGm, lintegral_const_mul' _ _ h2, hI]
        rfl
    _ ≤ 2 * varE P Y + 8 * ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) ∂P := by
        have h8 : (8 : ℝ≥0∞) * ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) ∂P =
            4 * ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) ∂P + 4 * ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) ∂P := by
          rw [← add_mul]; norm_num
        rw [h8]
        gcongr

/-- A random matrix with finite `varE` has integrable entries. -/
theorem integrable_entry_of_varE_ne_top (P : Measure Ω) [IsProbabilityMeasure P] (M : Ω → Mat d)
    (hM : ∀ i j, AEMeasurable (fun ω => M ω i j) P) (hv : varE P M ≠ ⊤) (i j : Fin d) :
    Integrable (fun ω => M ω i j) P := by
  set c : ℝ := meanMat P M i j with hc
  have hym : AEMeasurable (fun ω => M ω i j - c) P := (hM i j).sub_const c
  have hle : ∫⁻ ω, ENNReal.ofReal ((M ω i j - c) ^ 2) ∂P ≤ varE P M := by
    refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
    have h := abs_entry_le_matrixNorm (M ω - meanMat P M) i j
    rw [← sq_abs]
    have : |M ω i j - c| ≤ matrixNorm (M ω - meanMat P M) := by
      simpa [hc, Matrix.sub_apply, meanMat] using h
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hy2 : Integrable (fun ω => (M ω i j - c) ^ 2) P :=
    (lintegral_ofReal_ne_top_iff_integrable (hym.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)).mp (ne_top_of_le_ne_top hv hle)
  have hy : Integrable (fun ω => M ω i j - c) P :=
    ((memLp_two_iff_integrable_sq hym.aestronglyMeasurable).mpr hy2).integrable one_le_two
  refine (hy.add (integrable_const c)).congr (Filter.Eventually.of_forall fun ω => ?_)
  simp

/-- **Variance algebra.**  If `X ≤ Y ≤ X + w Id` almost surely (`X`, `Y` symmetric) then
`var X ≤ 2 var Y + 8 𝔼 w²` in `ℝ≥0∞`. -/
theorem var_le_sandwich [NeZero d] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → Mat d) (w : Ω → ℝ) (hXm : ∀ i j, AEMeasurable (fun ω => X ω i j) P)
    (hYm : ∀ i j, AEMeasurable (fun ω => Y ω i j) P)
    (hwm : AEMeasurable w P) (hXs : ∀ᵐ ω ∂P, (X ω).IsSymm) (hYs : ∀ᵐ ω ∂P, (Y ω).IsSymm)
    (hlow : ∀ᵐ ω ∂P, ∀ v, 0 ≤ vecDot v (matVecMul (Y ω - X ω) v))
    (hup : ∀ᵐ ω ∂P, ∀ v, vecDot v (matVecMul (Y ω - X ω) v) ≤ w ω * vecNormSq v) :
    varE P X ≤ 2 * varE P Y + 8 * ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) ∂P := by
  by_cases hI : ∫⁻ ω, ENNReal.ofReal (w ω ^ 2) ∂P = ⊤
  · rw [hI]; simp
  by_cases hV : varE P Y = ⊤
  · rw [hV]; simp
  have hY1 := integrable_entry_of_varE_ne_top P Y hYm hV
  have hw2 : Integrable (fun ω => w ω ^ 2) P :=
    (lintegral_ofReal_ne_top_iff_integrable (hwm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)).mp hI
  exact var_le_of_integrable P X Y w hXm hwm hXs hYs hlow hup hY1 hw2

end SubdiffusiveProcess.Variance
