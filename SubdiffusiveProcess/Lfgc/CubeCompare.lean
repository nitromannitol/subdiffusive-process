import SubdiffusiveProcess.Sobolev.CoeffCompare
import Homogenization.Book.Ch02.Theorems.MatrixPositivity
import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import SubdiffusiveProcess.Lfgc.PsdNorm

/-!
# One-cube comparison of coarse-grained matrices under a multiplicative perturbation

Let `a, b` be symmetric coefficients on a domain `U` with `e^{-ε} κ b ≤ a ≤ e^{ε} κ b`
almost everywhere (Loewner order), `κ > 0`.  Then `σ(a)` lies between `e^{∓ε} κ σ(b)`,
`σ_*^{-1}(a)` lies between `e^{∓ε} κ^{-1} σ_*^{-1}(b)`, their operator norms compare in
the same way, and the scalar response `J(U; e, e; a/α)` with `α' = κ α` satisfies
`J' ≤ e^{ε} J + (e^{ε} - 1)`.  This file makes no probabilistic statement.
-/

open Homogenization Homogenization.Book.Ch02

namespace SubdiffusiveProcess.Lfgc
variable {d : ℕ}

theorem quad_eq_dotProduct (A : Mat d) (v : Vec d) :
    vecDot v (matVecMul A v) = dotProduct v (Matrix.mulVec A v) := rfl

theorem quad_nonneg_of_posDef {A : Mat d} (hA : A.PosDef) (v : Vec d) :
    0 ≤ vecDot v (matVecMul A v) := by
  rw [quad_eq_dotProduct]
  have h := hA.posSemidef.dotProduct_mulVec_nonneg v
  simpa using h

theorem quad_le_of_loewner {A B : Mat d} (h : MatLoewnerLE A B) (v : Vec d) :
    vecDot v (matVecMul A v) ≤ vecDot v (matVecMul B v) := by
  have := h v
  linarith

theorem quad_smul (c : ℝ) (A : Mat d) (v : Vec d) :
    vecDot v (matVecMul (c • A) v) = c * vecDot v (matVecMul A v) := by
  unfold vecDot matVecMul
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem matrixNorm_smul' (c : ℝ) (A : Mat d) : matrixNorm (c • A) = |c| * matrixNorm A := by
  unfold matrixNorm
  rw [map_smul, norm_smul, Real.norm_eq_abs]

/-- Norm bound from a Loewner upper bound by a positive multiple. -/
theorem matrixNorm_le_of_loewner_smul {A B : Mat d} (hA : A.IsSymm)
    (hpos : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul A v)) {c : ℝ} (hc : 0 ≤ c)
    (h : MatLoewnerLE A (c • B)) : matrixNorm A ≤ c * matrixNorm B := by
  have := matrixNorm_le_of_quad_le A (c • B) hA hpos (quad_le_of_loewner h)
  rwa [matrixNorm_smul', abs_of_nonneg hc] at this

/-- Loewner sandwich of the coarse matrices of `a` against those of `b`. -/
theorem coarse_sandwich {U : Domain d} (a b : CoeffOn U)
    (hsa : CoeffOn.IsSymmetric a) (hsb : CoeffOn.IsSymmetric b) (κ ε : ℝ) (hκ : 0 < κ)
    (hhi : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (a.toCoeffField x) (Real.exp ε • (κ • b.toCoeffField x)))
    (hlo : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (Real.exp (-ε) • (κ • b.toCoeffField x)) (a.toCoeffField x)) :
    MatLoewnerLE (Book.Ch02.sigmaCoarse U a) (Real.exp ε • (κ • Book.Ch02.sigmaCoarse U b)) ∧
    MatLoewnerLE (Real.exp (-ε) • (κ • Book.Ch02.sigmaCoarse U b)) (Book.Ch02.sigmaCoarse U a) ∧
    MatLoewnerLE (Book.Ch02.sigmaStarInvCoarse U a) (Real.exp ε • (κ⁻¹ • Book.Ch02.sigmaStarInvCoarse U b)) ∧
    MatLoewnerLE (Real.exp (-ε) • (κ⁻¹ • Book.Ch02.sigmaStarInvCoarse U b)) (Book.Ch02.sigmaStarInvCoarse U a) := by
  set b' := CoeffOn.scale κ hκ b
  have hsb' : CoeffOn.IsSymmetric b' := Paper.CoeffOn.isSymmetric_scale κ hκ hsb
  have hσ : Book.Ch02.sigmaCoarse U b' = κ • Book.Ch02.sigmaCoarse U b :=
    (responseSubadditivityAndScalingTheory U b).sigma_homogeneous hκ
      (CoeffOn.aeScaled_scale κ hκ b)
  have hσs : Book.Ch02.sigmaStarInvCoarse U b' = κ⁻¹ • Book.Ch02.sigmaStarInvCoarse U b :=
    Paper.aux_sigmaStarInvCoarse_scaled κ hκ b
  have hmain := Paper.aux_sigma_exp_comparison' a b' hsa hsb' ε
    (by simpa [b', CoeffOn.scale_toCoeffField] using hhi)
    (by simpa [b', CoeffOn.scale_toCoeffField] using hlo)
  rw [hσ, hσs] at hmain
  exact hmain

/-- Symmetric coefficient: the `σ` quadratic form is nonnegative. -/
theorem sigma_quad_nonneg {U : Domain d} (a : CoeffOn U) (v : Vec d) :
    0 ≤ vecDot v (matVecMul (Book.Ch02.sigmaCoarse U a) v) := by
  have h1 := quad_le_of_loewner (Book.Ch02.sigmaStarCoarse_le_sigmaCoarse U a) v
  have h2 := quad_nonneg_of_posDef (Book.Ch02.sigmaStarCoarse_posDef U a) v
  linarith

/-- Operator norms of `σ` compare under the sandwich. -/
theorem sigma_norm_compare {U : Domain d} (a b : CoeffOn U)
    (hsa : CoeffOn.IsSymmetric a) (hsb : CoeffOn.IsSymmetric b) (κ ε : ℝ) (hκ : 0 < κ)
    (hhi : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (a.toCoeffField x) (Real.exp ε • (κ • b.toCoeffField x)))
    (hlo : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (Real.exp (-ε) • (κ • b.toCoeffField x)) (a.toCoeffField x)) :
    matrixNorm (Book.Ch02.sigmaCoarse U a) ≤ Real.exp ε * κ * matrixNorm (Book.Ch02.sigmaCoarse U b) ∧
    matrixNorm (Book.Ch02.sigmaStarInvCoarse U a) ≤
      Real.exp ε * κ⁻¹ * matrixNorm (Book.Ch02.sigmaStarInvCoarse U b) := by
  obtain ⟨h1, -, h3, -⟩ := coarse_sandwich a b hsa hsb κ ε hκ hhi hlo
  refine ⟨?_, ?_⟩
  · have h1' : MatLoewnerLE (Book.Ch02.sigmaCoarse U a) ((Real.exp ε * κ) • Book.Ch02.sigmaCoarse U b) := by
      simpa [smul_smul] using h1
    exact matrixNorm_le_of_loewner_smul (Book.Ch02.sigmaCoarse_isSymm U a) (sigma_quad_nonneg a)
      (by positivity) h1'
  · have h3' : MatLoewnerLE (Book.Ch02.sigmaStarInvCoarse U a)
        ((Real.exp ε * κ⁻¹) • Book.Ch02.sigmaStarInvCoarse U b) := by
      simpa [smul_smul] using h3
    exact matrixNorm_le_of_loewner_smul (Book.Ch02.sigmaStarInvCoarse_isSymm U a)
      (quad_nonneg_of_posDef (Book.Ch02.sigmaStarInvCoarse_posDef U a)) (by positivity) h3'

/-- The symmetric scalar response in terms of `σ` and `σ_*^{-1}`. -/
theorem responseJ_scalar_eq {U : Domain d} (a : CoeffOn U) (hsa : CoeffOn.IsSymmetric a)
    (α : ℝ) (hα : 0 < α) (e : Vec d) :
    responseJ U a ((Real.sqrt α)⁻¹ • e) (Real.sqrt α • e) =
      (1 / 2 : ℝ) * α⁻¹ * vecDot e (matVecMul (Book.Ch02.sigmaCoarse U a) e) +
        (1 / 2 : ℝ) * α * vecDot e (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) e) - vecDot e e := by
  have T := responseSymmetricDirichletNeumannTheory U a hsa
  rw [T.response_dirichlet_neumann_split, T.dirichlet_value_by_sigma,
    T.neumann_value_by_sigmaStarInv]
  have hs : Real.sqrt α ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
  have hsq : Real.sqrt α * Real.sqrt α = α := Real.mul_self_sqrt hα.le
  have hmv : ∀ (c : ℝ) (A : Mat d), matVecMul A (c • e) = c • matVecMul A e := by
    intro c A; funext i; unfold matVecMul
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdot : ∀ (c c' : ℝ) (v w : Vec d), vecDot (c • v) (c' • w) = c * c' * vecDot v w := by
    intro c c' v w; unfold vecDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hmv, hmv, hdot, hdot, hdot]
  have hinv : (Real.sqrt α)⁻¹ * (Real.sqrt α)⁻¹ = α⁻¹ := by
    rw [← mul_inv, hsq]
  rw [hinv, hsq, inv_mul_cancel₀ hs]
  ring

/-- Scalar-response comparison: `J' ≤ e^{ε} J + (e^{ε} - 1) |e|²` when `α' = κ α`. -/
theorem responseJ_scalar_compare {U : Domain d} (a b : CoeffOn U)
    (hsa : CoeffOn.IsSymmetric a) (hsb : CoeffOn.IsSymmetric b) (κ ε : ℝ) (hκ : 0 < κ)
    (hε : 0 ≤ ε)
    (hhi : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (a.toCoeffField x) (Real.exp ε • (κ • b.toCoeffField x)))
    (hlo : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (Real.exp (-ε) • (κ • b.toCoeffField x)) (a.toCoeffField x))
    (α : ℝ) (hα : 0 < α) (e : Vec d) :
    responseJ U a ((Real.sqrt (κ * α))⁻¹ • e) (Real.sqrt (κ * α) • e) ≤
      Real.exp ε * responseJ U b ((Real.sqrt α)⁻¹ • e) (Real.sqrt α • e) +
        (Real.exp ε - 1) * vecDot e e := by
  obtain ⟨h1, -, h3, -⟩ := coarse_sandwich a b hsa hsb κ ε hκ hhi hlo
  rw [responseJ_scalar_eq a hsa (κ * α) (mul_pos hκ hα),
    responseJ_scalar_eq b hsb α hα]
  have q1 := quad_le_of_loewner h1 e
  have q3 := quad_le_of_loewner h3 e
  rw [quad_smul, quad_smul] at q1 q3
  have hee : 0 ≤ vecDot e e := vecNormSq_nonneg' e
  have hexp : 1 ≤ Real.exp ε := Real.one_le_exp hε
  have hA : α⁻¹ * vecDot e (matVecMul (Book.Ch02.sigmaCoarse U b) e) * 0 ≤ 0 := by simp
  have key1 : (κ * α)⁻¹ * vecDot e (matVecMul (Book.Ch02.sigmaCoarse U a) e) ≤
      Real.exp ε * (α⁻¹ * vecDot e (matVecMul (Book.Ch02.sigmaCoarse U b) e)) := by
    have hpos : 0 < (κ * α)⁻¹ := by positivity
    calc (κ * α)⁻¹ * vecDot e (matVecMul (Book.Ch02.sigmaCoarse U a) e)
        ≤ (κ * α)⁻¹ * (Real.exp ε * (κ * vecDot e (matVecMul (Book.Ch02.sigmaCoarse U b) e))) :=
          mul_le_mul_of_nonneg_left q1 hpos.le
      _ = Real.exp ε * (α⁻¹ * vecDot e (matVecMul (Book.Ch02.sigmaCoarse U b) e)) := by
          field_simp
  have key3 : (κ * α) * vecDot e (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) e) ≤
      Real.exp ε * (α * vecDot e (matVecMul (Book.Ch02.sigmaStarInvCoarse U b) e)) := by
    have hpos : 0 < κ * α := by positivity
    calc (κ * α) * vecDot e (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) e)
        ≤ (κ * α) * (Real.exp ε * (κ⁻¹ * vecDot e (matVecMul (Book.Ch02.sigmaStarInvCoarse U b) e))) :=
          mul_le_mul_of_nonneg_left q3 hpos.le
      _ = Real.exp ε * (α * vecDot e (matVecMul (Book.Ch02.sigmaStarInvCoarse U b) e)) := by
          field_simp
  clear hA
  nlinarith [key1, key3, hee, hexp]

end SubdiffusiveProcess.Lfgc
