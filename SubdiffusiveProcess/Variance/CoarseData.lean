module

public import SubdiffusiveProcess.Variance.MatrixChain
public import Homogenization.Book.Ch04.Theorems.Expectations
public import Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.BlockLoewner
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch04

namespace SubdiffusiveProcess.Variance

variable {d : ℕ}

/-- For an a.e. locally uniformly elliptic field, `J` is the doubled-`Mu` quadratic form of the
coarse block matrix (pointwise version of the Chapter 4 a.e. identity). -/
theorem responseJ_eq_block [NeZero d] {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) (p q : Vec d) :
    ResponseJ (cubeSet Q) p q a.toFun =
      (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft p) := by
  have hResponse : ResponseJ (cubeSet Q) p q a.toFun =
      Mu (cubeSet Q) (-p, q) a.toFun - vecDot p q := by
    have hId := Ch02.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot
      (Q := Q) (a := coeffOnOfAEEllipticOn a Q (ha Q)) p q
    simpa [coeffOnOfAEEllipticOn_toCoeffField] using hId
  have hex := RestrictionLawCarrier.exists_coarseBlockMatrix_openCubeSet_of_aelocallyUniformlyEllipticField ha Q
  have hCoarse :
      IsCoarseBlockMatrix (openCubeSet Q) a.toFun (coarseBlockMatrix (openCubeSet Q) a.toFun) :=
    isCoarseBlockMatrix_coarseBlockMatrix hex
  calc
    ResponseJ (cubeSet Q) p q a.toFun = Mu (cubeSet Q) (-p, q) a.toFun - vecDot p q := hResponse
    _ = Mu (openCubeSet Q) (-p, q) a.toFun - vecDot p q := by
      rw [Mu_cubeSet_eq_openCubeSet_of_triadicCube (Q := Q) (P := (-p, q)) (a := a.toFun)]
    _ = (1 / 2 : ℝ) * blockVecDot (-p, q)
          (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun) (-p, q)) - vecDot p q := by
        rw [Mu_eq_half_blockVecDot_coarseBlockMatrix hex (-p, q)]
    _ = (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerRight q) -
          vecDot p q -
          vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerLeft p) +
          (1 / 2 : ℝ) *
            vecDot p (matVecMul (coarseBlockMatrix (openCubeSet Q) a.toFun).upperLeft p) := by
        rw [magic_half_blockVecDot_neg_left_of_isSymmetricBlockMat hCoarse.1 p q]
        ring
    _ = _ := by rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a.toFun]

theorem coarse_eq_ch02 [NeZero d] {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) :
    coarseBlockMatrix (cubeSet Q) a.toFun =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain Q) (coeffOnOfAEEllipticOn a Q (ha Q)) :=
  RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
    ha Q

/-- For a symmetric field the coarse block matrix is block diagonal: `κ = 0`. -/
theorem lowerLeft_eq_zero [NeZero d] {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a)
    (hsymm : ∀ᵐ x ∂volume, (a.toFun x).IsSymm) (Q : TriadicCube d) :
    (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft = 0 := by
  rw [coarse_eq_ch02 ha Q, Ch02.coarseBlockMatrix_lowerLeft]
  have hsym : Ch02.CoeffOn.IsSymmetric (coeffOnOfAEEllipticOn a Q (ha Q)) :=
    ae_restrict_of_ae hsymm
  have hk := (Ch02.responseSymmetricDirichletNeumannTheory _ _ hsym).kappa_eq_zero
  rw [hk]
  simp

theorem upperLeft_posDef [NeZero d] {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) : (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft.PosDef := by
  rw [coarse_eq_ch02 ha Q, Ch02.coarseBlockMatrix_upperLeft]
  exact Ch02.bCoarse_posDef _ _

theorem lowerRight_posDef [NeZero d] {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a)
    (Q : TriadicCube d) : (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight.PosDef := by
  rw [coarse_eq_ch02 ha Q, Ch02.coarseBlockMatrix_lowerRight]
  exact Ch02.sigmaStarInvCoarse_posDef _ _

/-- The plug identity `J(U,p,q) = ½ p·a(U)p + ½ q·a_*^{-1}(U)q - p·q` for a symmetric field. -/
theorem responseJ_eq_sym [NeZero d] {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a)
    (hsymm : ∀ᵐ x ∂volume, (a.toFun x).IsSymm) (Q : TriadicCube d) (p q : Vec d) :
    ResponseJ (cubeSet Q) p q a.toFun =
      (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft p) +
        (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight q) -
          vecDot p q := by
  rw [responseJ_eq_block ha Q p q, lowerLeft_eq_zero ha hsymm Q]
  simp [vecDot, matVecMul]
  ring

theorem avgMat_eq_descendantsAverageMat (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → Mat d) :
    avgMat (descendantsAtDepth Q j) F = descendantsAverageMat Q j F := by
  ext i k
  simp [avgMat, descendantsAverageMat, descendantsAverage, Matrix.sum_apply]

theorem quad_blockLE_left {A B : BlockMat d} (h : BlockMatLoewnerLE A B) (x : Vec d) :
    vecDot x (matVecMul A.upperLeft x) ≤ vecDot x (matVecMul B.upperLeft x) := by
  have := h (x, 0)
  simp [blockVecDot, blockMatVecMul, vecDot, matVecMul] at this
  simpa [vecDot, matVecMul] using this

theorem quad_blockLE_right {A B : BlockMat d} (h : BlockMatLoewnerLE A B) (x : Vec d) :
    vecDot x (matVecMul A.lowerRight x) ≤ vecDot x (matVecMul B.lowerRight x) := by
  have := h (0, x)
  simp [blockVecDot, blockMatVecMul, vecDot, matVecMul] at this
  simpa [vecDot, matVecMul] using this

theorem isSymm_sandwich {B U : Mat d} (hB : B.IsSymm) (hU : U.IsSymm) : (B * U * B).IsSymm := by
  unfold Matrix.IsSymm at *
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hB, hU]
  simp [Matrix.mul_assoc]

/-- The matrix `K_R = a_*^{-1}(R) - 2B + B a(R) B` has quadratic form `2 J(R, Bv, v)`. -/
theorem quad_K_eq [NeZero d] {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a)
    (hsymm : ∀ᵐ x ∂volume, (a.toFun x).IsSymm) (R : TriadicCube d) {B : Mat d} (hB : B.IsSymm) (v : Vec d) :
    vecDot v (matVecMul ((coarseBlockMatrix (cubeSet R) a.toFun).lowerRight - (2 : ℝ) • B +
        B * (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft * B) v) =
      2 * ResponseJ (cubeSet R) (matVecMul B v) v a.toFun := by
  rw [responseJ_eq_sym ha hsymm R, quad_add, quad_sub, quad_smul, quad_sandwich _ _ hB,
    SubdiffusiveProcess.Lfgc.vecDot_comm' (matVecMul B v) v]
  ring

/-- The deterministic chain of `l.var.bounds`:
`0 ≤ avg_R a_*^{-1}(R) - a_*^{-1}(Q) ≤ 2 (avg_R ∑_i J(R, β⁻¹ e_i, e_i)) Id` in the quadratic-form
order, for a symmetric locally uniformly elliptic field. -/
theorem coarse_chain [NeZero d] {a : RegCoeffField d} (ha : AELocallyUniformlyEllipticField a)
    (hsymm : ∀ᵐ x ∂volume, (a.toFun x).IsSymm) (Q : TriadicCube d) {k : ℤ} (hk : k ≤ Q.scale)
    (β : Mat d) (hβ : β.PosDef) (v : Vec d) :
    0 ≤ vecDot v (matVecMul (avgMat (descendantsAtScale Q k)
        (fun R => (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight) -
        (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight) v) ∧
    vecDot v (matVecMul (avgMat (descendantsAtScale Q k)
        (fun R => (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight) -
        (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight) v) ≤
      2 * (((descendantsAtScale Q k).card : ℝ)⁻¹ * ∑ R ∈ descendantsAtScale Q k, ∑ i : Fin d,
        ResponseJ (cubeSet R) (matVecMul β⁻¹ (Pi.single i 1)) (Pi.single i 1) a.toFun) *
        vecNormSq v := by
  classical
  have hs : (descendantsAtScale Q k).Nonempty := descendantsAtScale_nonempty Q hk
  set B : Mat d := β⁻¹ with hBdef
  have hB : B.IsSymm := isSymm_inv_of_posDef hβ
  have hK : ∀ R ∈ descendantsAtScale Q k,
      ((coarseBlockMatrix (cubeSet R) a.toFun).lowerRight - (2 : ℝ) • B +
        B * (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft * B).PosSemidef := by
    intro R _
    refine posSemidef_of_quad ?_ ?_
    · refine Matrix.IsSymm.add (Matrix.IsSymm.sub (isSymm_of_posDef (lowerRight_posDef ha R))
        (Matrix.IsSymm.smul hB _)) (isSymm_sandwich hB (isSymm_of_posDef (upperLeft_posDef ha R)))
    · intro v
      rw [quad_K_eq ha hsymm R hB v]
      exact mul_nonneg (by norm_num) (responseJ_nonneg _ _ _ _)
  have hK0 : ((coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight -
      (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft⁻¹).PosSemidef := by
    set U0 := (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft with hU0def
    have hU0 : U0.PosDef := upperLeft_posDef ha Q
    have hdet : IsUnit U0.det := (Matrix.isUnit_iff_isUnit_det U0).mp hU0.isUnit
    refine posSemidef_of_quad
      (Matrix.IsSymm.sub (isSymm_of_posDef (lowerRight_posDef ha Q)) (isSymm_inv_of_posDef hU0)) ?_
    intro v
    have hJ := responseJ_nonneg (cubeSet Q) (matVecMul U0⁻¹ v) v a.toFun
    rw [responseJ_eq_sym ha hsymm Q] at hJ
    have h1 : matVecMul U0 (matVecMul U0⁻¹ v) = v := by
      simp only [matVecMul_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv U0 hdet,
        Matrix.one_mulVec]
    rw [← hU0def] at hJ
    rw [h1, SubdiffusiveProcess.Lfgc.vecDot_comm' (matVecMul U0⁻¹ v) v] at hJ
    rw [quad_sub]
    linarith
  have hsub := coarseBlockMatrix_le_descendantsAverageBlockMat_cubeSet_of_aelocallyUniformlyEllipticField
    ha Q hk
  have hdesc := descendantsAtScale_eq_descendantsAtDepth Q hk
  have hchain := chain (descendantsAtScale Q k) hs
    (fun R => (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft)
    (fun R => (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight)
    (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft
    (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight B hB
    (fun R _ => upperLeft_posDef ha R) (upperLeft_posDef ha Q) hK hK0
    (fun x => by
      have := quad_blockLE_left hsub x
      rw [hdesc, avgMat_eq_descendantsAverageMat]
      exact this)
    (fun x => by
      have := quad_blockLE_right hsub x
      rw [hdesc, avgMat_eq_descendantsAverageMat]
      exact this) v
  have htr : ∀ R ∈ descendantsAtScale Q k,
      Matrix.trace ((coarseBlockMatrix (cubeSet R) a.toFun).lowerRight - (2 : ℝ) • B +
        B * (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft * B) =
      2 * ∑ i : Fin d, ResponseJ (cubeSet R) (matVecMul B (Pi.single i 1)) (Pi.single i 1)
        a.toFun := by
    intro R _
    rw [trace_eq_sum_quad, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => quad_K_eq ha hsymm R hB _
  refine ⟨hchain.1, hchain.2.trans (le_of_eq ?_)⟩
  rw [Finset.sum_congr rfl htr, ← Finset.mul_sum]
  ring

end SubdiffusiveProcess.Variance
