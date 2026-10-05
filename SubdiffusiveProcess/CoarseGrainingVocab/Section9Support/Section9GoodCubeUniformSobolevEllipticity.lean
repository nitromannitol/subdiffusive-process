module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevCoefficient
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import Homogenization.Deterministic.CoarsePoincare.Setup.UniformBounds

@[expose] public section

/-!
# A prescribed local lower bound pays inverse multiscale ellipticity

The Chapter 2 inverse lower ellipticity is bounded by `4 * d / c` whenever
the coefficient on the parent cube admits lower ellipticity `c`. A change
of the recorded ellipticity constants preserves the actual coefficient
representatives on every cube and hence preserves multiscale ellipticity.
-/

set_option autoImplicit false
open Homogenization Homogenization.Book MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The recorded lower ellipticity of the parent cube controls its inverse
multiscale ellipticity, with a dimensional loss. -/
theorem goodCube_lambdaSq_inv_le_coeffOn_lam
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    {s : ℝ} (hs : 0 < s) :
    (Ch02.lambdaSq Q s (.finite 1) a)⁻¹ ≤
      4 * (d : ℝ) * (a.coeffOn Q).lam⁻¹ := by
  let Apw : CoeffField d :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)
  let C : ℝ := 4 * (d : ℝ) * (a.coeffOn Q).lam⁻¹
  have hEll : IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (openCubeSet Q) Apw := by
    simpa [Apw] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Ch02.cubeDomain Q) (a.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q Apw := by
    simpa [Apw] using Ch02.pointwiseCoeffField_openCube_descendant_data Q (a.coeffOn Q)
  have hmax (n : ℕ) :
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a ≤ C := by
    have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le n)
    have hmatrix :=
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
        a Q hk
    have hblock :
        Homogenization.maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) Apw ≤ C := by
      simpa [C] using
        maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
          Q Apw hEll hData n
    exact hmatrix.trans hblock
  have hsum :=
    Ch02.summable_geometricWeight_one_mul_maxDescendantSigmaStarInvMatrixNormAtScale Q a hs
  have hconst : Summable (fun n : ℕ => Ch02.geometricWeight s 1 n * C) := by
    simpa only [Ch02.geometricWeight_eq_old] using
      (Homogenization.summable_geometricWeight (s := s) (q := 1) (by simpa using hs)).mul_right C
  calc (Ch02.lambdaSq Q s (.finite 1) a)⁻¹
      ≤ ∑' n : ℕ, Ch02.geometricWeight s 1 n *
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a :=
        Ch02.lambdaSq_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
          Q a hs
    _ ≤ ∑' n : ℕ, Ch02.geometricWeight s 1 n * C := by
      refine Summable.tsum_le_tsum (fun n => ?_) hsum hconst
      apply mul_le_mul_of_nonneg_left (hmax n)
      simpa only [Ch02.geometricWeight_eq_old] using
        Homogenization.geometricWeight_nonneg n (show 0 ≤ s * 1 by simpa using hs.le)
    _ = C := by
      simp_rw [Ch02.geometricWeight_eq_old]
      rw [tsum_mul_right, Homogenization.tsum_geometricWeight_eq_one (by simpa using hs), one_mul]

/-- A local factor-two pointwise bound controls the actual cutoff family.
Only its ellipticity certificates are replaced; the representatives remain
the actual cutoff coefficient on every cube. -/
theorem goodCube_cutoff_lambdaSq_inv_le_of_bounds
    {d : ℕ} [NeZero d] (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (Q : TriadicCube d) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ openCubeSet Q,
      c ≤ aCutoff M L omega x ∧ aCutoff M L omega x ≤ 2 * c)
    {s : ℝ} (hs : 0 < s) :
    (Ch02.lambdaSq Q s (.finite 1) (aCutoffFamily M L omega))⁻¹ ≤
      4 * (d : ℝ) * c⁻¹ := by
  classical
  let a := aCutoffFamily M L omega
  let coeff : (R : TriadicCube d) → Ch02.CoeffOn (Ch02.cubeDomain R) := fun R =>
    { a.coeffOn R with
      lam := if R = Q then c else (a.coeffOn R).lam
      Lam := if R = Q then 2 * c else (a.coeffOn R).Lam
      lam_pos := by split_ifs; exact hc; exact (a.coeffOn R).lam_pos
      lam_le_Lam := by split_ifs; linarith only [hc]; exact (a.coeffOn R).lam_le_Lam
      aeElliptic := by
        by_cases hR : R = Q
        · subst R
          simp only [reduceIte]
          change ∀ᵐ x ∂volume.restrict (openCubeSet Q),
            IsEllipticMatrix c (2 * c) (scalarMatrix (aCutoff M L omega x))
          filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
          exact (isEllipticMatrix_scalarMatrix (aCutoff_pos M L omega x)).mono
            hc (hbound x hx).1 (hbound x hx).2
        · simpa only [ite_eq_right hR] using (a.coeffOn R).aeElliptic }
  let F : Ch02.TriadicCoeffFamily d :=
    { coeffOn := coeff
      restrictsTo_of_subset := by
        intro R S hRS
        exact a.restrictsTo_of_subset hRS }
  have hAE : Ch02.TriadicCoeffFamily.AEEq a F := by
    intro R
    exact Filter.EventuallyEq.rfl
  rw [show aCutoffFamily M L omega = a from rfl, Ch02.lambdaSq_eq_ofAEEq hAE Q s (.finite 1)]
  simpa only [F, coeff, ite_true] using! goodCube_lambdaSq_inv_le_coeffOn_lam Q F hs

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
