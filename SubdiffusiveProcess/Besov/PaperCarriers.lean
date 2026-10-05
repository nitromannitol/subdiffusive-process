module

public import SubdiffusiveProcess.Besov.SymmetricCoefficients

@[expose] public section

namespace SubdiffusiveProcess.Besov
open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch05.Section53
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov
open scoped BigOperators ENNReal
noncomputable section
variable {d : ℕ} [NeZero d]

/-- The coefficient-field lower ellipticity carrier is the paper's finite-one carrier. -/
theorem lambdaSqCoeffField_one_eq (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (s : ℝ) :
    Ch04.lambdaSqCoeffField Q s (.finite 1) a =
      Ch02.lambdaS Q s (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) := by
  simp only [Ch04.lambdaSqCoeffField, dite_eq_left ha, Ch02.lambdaS]

/-- The library's partition defect is the literal average over paper subcubes. -/
theorem responseDefectAverageAtScale_eq_paper (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) {m n : ℤ} (hn : n ≤ m) (p q : Vec d) :
    WeakNormsMaximizer.responseDefectAverageAtScale m n p q a =
      (((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d m) n,
          Ch02.responseJ (Ch02.cubeDomain R)
            ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R) p q) -
      Ch02.responseJ (Ch02.cubeDomain (originCube d m))
        ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn (originCube d m)) p q := by
  simp only [WeakNormsMaximizer.responseDefectAverageAtScale, descendantsAtScale,
    show (originCube d m).scale = m from rfl, dite_eq_left hn, descendantsAverage,
    JUpperBoundWeakNorms.responseJOnDependentFamily_eq_restrictionResponseJObservableCubeSet a ha]

/-- The library matrix-variation average is the paper's inverse-star matrix average. -/
theorem coarseVariationAverage_eq_paper (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a)
    (hsym : ∀ x : Vec d, (a.toFun x).IsSymm) {m n : ℤ} (hn : n ≤ m) (p q : Vec d) :
    descendantsAverage (originCube d m) (m - n).toNat
      (coarseMatrixVariationSq a ha (originCube d m) p q) =
      ((descendantsAtScale (originCube d m) n).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtScale (originCube d m) n,
          vecNormSq (matVecMul
            (Ch02.sigmaStarInvCoarse (Ch02.cubeDomain (originCube d m))
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn (originCube d m)) -
              Ch02.sigmaStarInvCoarse (Ch02.cubeDomain R)
                ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn R)) q) := by
  simp only [descendantsAtScale, show (originCube d m).scale = m from rfl,
    dite_eq_left hn, descendantsAverage, coarseMatrixVariationSq_eq_symmetric a ha hsym]

/-- The canonical energy norm is the paper energy of any supplied maximizer. -/
theorem maximizerEnergyL2Norm_eq_paper (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d)
    (v : Ch02.Solution (Ch02.cubeDomain Q)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q))
    (hv : Ch02.IsResponseMaximizer (Ch02.cubeDomain Q)
      ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q) p q v) :
    maximizerEnergyL2Norm a ha Q p q =
      Real.sqrt (cubeAverage Q (fun x =>
        vecDot (v.toH1.grad x) (matVecMul (a.toFun x) (v.toH1.grad x)))) := by
  unfold maximizerEnergyL2Norm maximizerEnergyL2NormSq
  congr 1
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  apply integral_congr_ae
  filter_upwards [maximizer_gradient_eq_canonical a ha Q p q v hv] with x hx
  change vecDot ((canonicalCubeMaximizerSolution a ha Q p q).toH1.grad x)
    (matVecMul (symmPart (a.toFun x))
      ((canonicalCubeMaximizerSolution a ha Q p q).toH1.grad x)) = _
  rw [← hx, vecDot_matVecMul_symmPart]

end
end SubdiffusiveProcess.Besov
