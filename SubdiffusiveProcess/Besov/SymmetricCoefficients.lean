module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.JBoundByBesov
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Homogenization.Book.Ch02.Theorems.GradientUniqueness

@[expose] public section

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]

/-- Pointwise symmetry passes to each coefficient restriction. -/
theorem restrictedCoefficient_isSymmetric (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (hsym : ∀ x : Vec d, (a.toFun x).IsSymm) (Q : TriadicCube d) :
    Ch02.CoeffOn.IsSymmetric
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) :=
  Filter.Eventually.of_forall hsym

/-- The mixed coarse matrix vanishes for the paper's symmetric coefficients. -/
theorem restrictedCoefficient_kappa_eq_zero (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (hsym : ∀ x : Vec d, (a.toFun x).IsSymm) (Q : TriadicCube d) :
    Ch02.kappaCoarse (Ch02.cubeDomain Q)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) = 0 :=
  (Ch02.responseSymmetricDirichletNeumannTheory _ _
    (restrictedCoefficient_isSymmetric a ha hsym Q)).kappa_eq_zero

/-- The comparison vector in the literal symmetric-coefficient display. -/
theorem coarseScaleSeparation_eq_symmetric (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (hsym : ∀ x : Vec d, (a.toFun x).IsSymm) (Q : TriadicCube d) (p q : Vec d) :
    coarseScaleSeparation a ha Q p q =
      matVecMul (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q)
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)) q - p := by
  unfold coarseScaleSeparation
  rw [restrictedCoefficient_kappa_eq_zero a ha hsym Q]
  have hz : matVecMul (0 : Mat d) p = 0 := by
    ext i
    simp [matVecMul]
  rw [hz, add_zero]

/-- The two comparison vectors differ by the difference of inverse star matrices. -/
theorem coarseMatrixVariationSq_eq_symmetric (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (hsym : ∀ x : Vec d, (a.toFun x).IsSymm) (Q R : TriadicCube d) (p q : Vec d) :
    coarseMatrixVariationSq a ha Q p q R =
      vecNormSq (matVecMul
        (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain Q)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) -
          Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)) q) := by
  unfold coarseMatrixVariationSq
  rw [coarseScaleSeparation_eq_symmetric a ha hsym Q,
    coarseScaleSeparation_eq_symmetric a ha hsym R]
  congr 1
  ext i
  simp only [Pi.sub_apply, matVecMul, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/-- An arbitrary response maximizer has the canonical gradient in normalized measure. -/
theorem maximizer_gradient_eq_canonical (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d)
    (v : Ch02.Solution (Ch02.cubeDomain Q)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q))
    (hv : Ch02.IsResponseMaximizer (Ch02.cubeDomain Q)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q v) :
    v.toH1.grad =ᵐ[normalizedCubeMeasure Q]
      (canonicalCubeMaximizerSolution a ha Q p q).toH1.grad := by
  have h := (Ch02.canonicalMaximizer_sameGradientAE_of_isResponseMaximizer hv).symm
  change v.toH1.grad =ᵐ[volume.restrict (openCubeSet Q)]
    (canonicalCubeMaximizerSolution a ha Q p q).toH1.grad at h
  change v.toH1.grad =ᵐ[normalizedCubeMeasure Q] _
  rw [normalizedCubeMeasure, cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact Measure.ae_smul_measure h _

end
end SubdiffusiveProcess.Besov
