module

public import SubdiffusiveProcess.Variance.CoarseData
public import SubdiffusiveProcess.Variance.VarianceAlgebra

@[expose] public section

/-!
# Assembly of `l.var.bounds`

For a probability law `P` on the carrier `RegCoeffField d` supported on symmetric, locally uniformly
elliptic fields, `k < n`, and a positive definite `β`, the variance estimate of the paper:
`var[a_*^{-1}(cu_n)] ≤ 2 var[avg_z a_*^{-1}(z+cu_k)] + 32 𝔼[(avg_z ∑_i J(z+cu_k, β⁻¹ e_i, e_i))²]`.
Stationarity of `P` is not used.
-/

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch04
open scoped ENNReal

namespace SubdiffusiveProcess.Variance

variable {d : ℕ}

theorem varE_eq_zero_of_dim_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Mat 0) :
    varE P M = 0 := by
  have h0 : ∀ A : Mat 0, Ch02.matrixNorm A = 0 := by
    intro A
    have : A = 0 := Subsingleton.elim _ _
    subst this
    simp [Ch02.matrixNorm]
  simp [varE, h0]



theorem var_bounds (P : Measure (RegCoeffField d)) [IsProbabilityMeasure P]
    (hsymm : ∀ᵐ a ∂P, ∀ᵐ x ∂volume, (a.toFun x).IsSymm)
    (hell : AELocallyUniformlyEllipticLaw P) (n k : ℤ) (hkn : k < n) (β : Mat d) (hβ : β.PosDef) :
    varE P (fun a => (coarseBlockMatrix (openCubeSet (originCube d n)) a.toFun).lowerRight) ≤
      2 * varE P (fun a =>
        ((descendantsAtScale (originCube d n) k).card : ℝ)⁻¹ •
          ∑ R ∈ descendantsAtScale (originCube d n) k,
            (coarseBlockMatrix (openCubeSet R) a.toFun).lowerRight) +
      32 * ∫⁻ a, ENNReal.ofReal
        ((((descendantsAtScale (originCube d n) k).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtScale (originCube d n) k,
            ∑ i : Fin d, ResponseJ (cubeSet R) (matVecMul β⁻¹ (Pi.single i 1)) (Pi.single i 1)
              a.toFun) ^ 2) ∂P := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [varE_eq_zero_of_dim_zero]
    exact bot_le
  have : NeZero d := ⟨hd.ne'⟩
  have hP : RestrictionLawCarrier P := lawCarrier_of_aeLocallyUniformlyElliptic hell
  have hbr : ∀ (R : TriadicCube d) (a : RegCoeffField d),
      (coarseBlockMatrix (openCubeSet R) a.toFun).lowerRight =
        (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight := fun R a => by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R a.toFun]
  simp only [hbr]
  set Q : TriadicCube d := originCube d n with hQ
  set s := descendantsAtScale Q k with hs
  have hk : k ≤ Q.scale := hkn.le
  set LR : TriadicCube d → RegCoeffField d → Mat d :=
    fun R a => (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight with hLR
  set W : RegCoeffField d → ℝ := fun a => (s.card : ℝ)⁻¹ * ∑ R ∈ s, ∑ i : Fin d,
    ResponseJ (cubeSet R) (matVecMul β⁻¹ (Pi.single i 1)) (Pi.single i 1) a.toFun with hW
  have hXm : ∀ i j, AEMeasurable (fun a => LR Q a i j) P := fun i j =>
    hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet Q i j
  have hYm : ∀ i j, AEMeasurable (fun a => (avgMat s (fun R => LR R a)) i j) P := by
    intro i j
    have : (fun a => (avgMat s (fun R => LR R a)) i j) =
        fun a => (s.card : ℝ)⁻¹ * ∑ R ∈ s, LR R a i j := by
      funext a
      simp [avgMat, Matrix.sum_apply]
    rw [this]
    exact (Finset.aemeasurable_fun_sum s fun R _ =>
      hP.aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet R i j).const_mul _
  have hwm : AEMeasurable (fun a => 2 * W a) P :=
    (((Finset.aemeasurable_fun_sum s fun R _ => Finset.aemeasurable_fun_sum Finset.univ
      fun i _ => hP.aemeasurable_ResponseJ_cubeSet R _ _).const_mul _).const_mul _)
  have hae : ∀ᵐ a ∂P, AELocallyUniformlyEllipticField a ∧ ∀ᵐ x ∂volume, (a.toFun x).IsSymm := by
    filter_upwards [hell, hsymm] with a h1 h2 using ⟨h1, h2⟩
  have hXs : ∀ᵐ a ∂P, (LR Q a).IsSymm := by
    filter_upwards [hell] with a ha
    exact isSymm_of_posDef (lowerRight_posDef ha Q)
  have hYs : ∀ᵐ a ∂P, (avgMat s (fun R => LR R a)).IsSymm := by
    filter_upwards [hell] with a ha
    exact isSymm_avgMat s _ fun R _ => isSymm_of_posDef (lowerRight_posDef ha R)
  have hchain : ∀ᵐ a ∂P, ∀ v, 0 ≤ vecDot v (matVecMul (avgMat s (fun R => LR R a) - LR Q a) v) ∧
      vecDot v (matVecMul (avgMat s (fun R => LR R a) - LR Q a) v) ≤ (2 * W a) * vecNormSq v := by
    filter_upwards [hae] with a ha v
    exact coarse_chain ha.1 ha.2 Q hk β hβ v
  have key := var_le_sandwich P (fun a => LR Q a) (fun a => avgMat s (fun R => LR R a))
    (fun a => 2 * W a) hXm hYm hwm hXs hYs
    (by filter_upwards [hchain] with a h v using (h v).1)
    (by filter_upwards [hchain] with a h v using (h v).2)
  have hfin : (8 : ℝ≥0∞) * ∫⁻ a, ENNReal.ofReal ((2 * W a) ^ 2) ∂P =
      32 * ∫⁻ a, ENNReal.ofReal (W a ^ 2) ∂P := by
    have h : ∀ a, ENNReal.ofReal ((2 * W a) ^ 2) = 4 * ENNReal.ofReal (W a ^ 2) := fun a => by
      rw [mul_pow, ENNReal.ofReal_mul (by norm_num)]
      norm_num
    simp_rw [h]
    rw [lintegral_const_mul' _ _ (by norm_num), ← mul_assoc]
    norm_num
  rw [hfin] at key
  exact key

end SubdiffusiveProcess.Variance
