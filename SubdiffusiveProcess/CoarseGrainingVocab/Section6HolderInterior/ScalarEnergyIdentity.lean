import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.BesovVocabularyBridge
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior.EnergyIntegrability




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior

open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec

noncomputable section

variable {d : ℕ}

/-- The scalar coefficient quadratic form. -/
theorem vecDot_matVecMul_scalarCoeffField (a : Vec d → ℝ) (x v : Vec d) :
    vecDot v (matVecMul (scalarCoeffField a x) v) = a x * vecNormSq v := by
  simp only [scalarCoeffField, scalarMatrix, matVecMul, vecDot, vecNormSq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  simp [Matrix.one_apply, Finset.sum_ite_eq]
  ring

/-- **The scalar coefficient energy is the weighted gradient energy.**  Combining
with `euclideanNorm_sqrt_smul_sq`, the integrand of `coarsePoincareRaw`'s right
side is pointwise the squared Euclidean norm of `sqrt a • v`. -/
theorem vecDot_matVecMul_scalarCoeffField_eq_sq (a : Vec d → ℝ)
    (ha : ∀ x, 0 ≤ a x) (v : Vec d → Vec d) (x : Vec d) :
    vecDot (v x) (matVecMul (scalarCoeffField a x) (v x)) =
      Homogenization.euclideanNorm (Real.sqrt (a x) • v x) ^ 2 := by
  rw [vecDot_matVecMul_scalarCoeffField,
    euclideanNorm_sqrt_smul_sq a v ha x]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderInterior
