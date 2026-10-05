module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Schauder
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.BallCaccioppoli

@[expose] public section

/-!
# Scalar coefficient bridges for small-contrast Schauder

These lemmas convert the scalar normalized coefficient used in the bounded
multiplier argument to the matrix-valued carriers of `smallContrastSchauder`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open Filter MeasureTheory Homogenization
open Homogenization.Book.Ch02
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The operator-norm distance of a scalar matrix from the identity is exactly
the absolute scalar distance. -/
theorem matrixOperatorNorm_scalarCoeffField_sub_one [NeZero d]
    (s : Vec d → ℝ) (x : Vec d) :
    matrixOperatorNorm (scalarCoeffField s x - (1 : Mat d)) = |s x - 1| := by
  have hmat : scalarCoeffField s x - (1 : Mat d) =
      (s x - 1) • (1 : Mat d) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [scalarCoeffField, scalarMatrix]
    · simp [scalarCoeffField, scalarMatrix, hij]
  rw [hmat, matrixOperatorNorm_smul_one_eq_abs]

/-- A scalar coefficient continuous on a measurable window and bounded between
positive constants gives the matrix ellipticity carrier used by Schauder. -/
theorem isEllipticFieldOn_scalarCoeffField_of_continuousOn
    {W : Set (Vec d)} (hW : MeasurableSet W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) {lam Lam : ℝ} (hlam : 0 < lam)
    (hbounds : ∀ x ∈ W, lam ≤ s x ∧ s x ≤ Lam) :
    IsEllipticFieldOn lam Lam W (scalarCoeffField s) := by
  have hpiece : Measurable (W.piecewise s fun _ ↦ (0 : ℝ)) :=
    hs.measurable_piecewise continuous_const.continuousOn hW
  constructor
  · refine measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ ?_
    by_cases hij : i = j
    · subst j
      simpa [Set.piecewise, scalarCoeffField, scalarMatrix] using! hpiece
    · have hzero : (fun x : Vec d ↦ if x ∈ W then
          scalarCoeffField s x i j else 0) = fun _ ↦ (0 : ℝ) := by
        funext x
        simp [scalarCoeffField, scalarMatrix, hij]
      rw [hzero]
      exact measurable_const
  · intro x hx
    have hspos : 0 < s x := hlam.trans_le (hbounds x hx).1
    exact (isEllipticMatrix_scalarMatrix hspos).mono hlam
      (hbounds x hx).1 (hbounds x hx).2

/-- Pointwise scalar closeness to one is the matrix coefficient-distance
hypothesis expected by `smallContrastSchauder`. -/
theorem coefficientIdentityDistanceLE_scalarCoeffField [NeZero d]
    {W : Set (Vec d)} {s : Vec d → ℝ} {delta : ℝ}
    (hW : MeasurableSet W)
    (hs : ∀ x ∈ W, |s x - 1| ≤ delta) :
    CoefficientIdentityDistanceLE W (scalarCoeffField s) delta := by
  filter_upwards [ae_restrict_mem hW] with x hx
  rw [matrixOperatorNorm_scalarCoeffField_sub_one]
  exact hs x hx

/-- Scalar weak harmonicity is the matrix divergence-form equation with zero
forcing after applying `scalarCoeffField`. -/
theorem isMatrixDivFormWeakSolutionOn_zero_of_isWeaklyHarmonicOn
    {W : Set (Vec d)} {s : Vec d → ℝ} {u : H1Function W}
    (hu : IsWeaklyHarmonicOn s W u) :
    IsMatrixDivFormWeakSolutionOn (scalarCoeffField s) W u (fun _ ↦ 0) := by
  intro phi
  have h := hu phi
  have hleft :
      (∫ x in W, vecDot (matVecMul (scalarCoeffField s x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume) =
        ∫ x in W, vecDot (s x • u.grad x)
          (phi.toH1Function.grad x) ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [scalarCoeffField, Homogenization.matVecMul_scalarMatrix]
  rw [hleft, h]
  simp [vecDot]

/-- Zero forcing belongs to every finite vector `L^p` carrier. -/
theorem memVectorLpOn_zero (W : Set (Vec d)) (p : ℝ) :
    MemVectorLpOn W p (fun _ ↦ (0 : Vec d)) := by
  simp [MemVectorLpOn]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
