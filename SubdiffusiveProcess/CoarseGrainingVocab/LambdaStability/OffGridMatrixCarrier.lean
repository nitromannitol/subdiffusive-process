
module

public import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridMatrixAssembly
public import Homogenization.Internal.Ch02.MatrixExtraction
public import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Foundation.Basic

@[expose] public section

/-!
# Source matrices on an arbitrary translated cube

The paper's off-grid `lambda` and `Lambda` read the same canonical set-level
matrices as the grid definitions.  These observables use CoarseGraining's
existing `sigmaStarInvCoarse`, `sigmaCoarse`, `sigmaStarCoarse`,
`kappaCoarse`, and `bCoarse`; no parallel matrix is introduced.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

open Homogenization Homogenization.Book Homogenization.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The off-grid inverse dual coarse-matrix norm. -/
def offGridSigmaStarInvMatrixNorm (w : Vec d) (P : TriadicCube d)
    (g : CoeffField d) : ℝ :=
  Ch02.matrixNorm (Homogenization.sigmaStarInvCoarse (offGridCube w P) g)

/-- The off-grid upper coarse-matrix norm. -/
def offGridBMatrixNorm (w : Vec d) (P : TriadicCube d)
    (g : CoeffField d) : ℝ :=
  Ch02.matrixNorm
    (Homogenization.bCoarse
      (Homogenization.sigmaCoarse (offGridCube w P) g)
      (Homogenization.sigmaStarCoarse (offGridCube w P) g)
      (Homogenization.kappaCoarse (offGridCube w P) g))

private theorem offGridCube_isOpenBoundedConvexDomain (w : Vec d) (P : TriadicCube d) :
    IsOpenBoundedConvexDomain (offGridCube w P) := by
  exact (isOpenBoundedConvexDomain_openCubeSet P).translateSet w

private theorem offGridCube_volume_pos (w : Vec d) (P : TriadicCube d) :
    0 < (volume (offGridCube w P)).toReal := by
  rw [volume_offGridCube_toReal]
  exact cubeVolume_pos P

/-! ## Grid-cell adapters -/

/-- The set-level inverse-dual matrix used by the countable cover is exactly
the Chapter 2 one-cube carrier when both read the same coefficient field. -/
theorem matrixNorm_sigmaStarInvCoarse_openCube_eq_coarseSigmaStarInvMatrixNorm
    (A : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) (g : CoeffField d)
    (hg : (A.coeffOn Q).toCoeffField = g) :
    Ch02.matrixNorm (Homogenization.sigmaStarInvCoarse (openCubeSet Q) g) =
      Ch02.coarseSigmaStarInvMatrixNorm Q A := by
  unfold Ch02.coarseSigmaStarInvMatrixNorm Ch02.cubeDomain
  rw [← hg]
  exact congrArg Ch02.matrixNorm
    (Homogenization.Internal.Ch02.book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse
      _ _).symm

/-- The canonical inverse dual matrix on an off-grid cube is PSD. -/
theorem offGridSigmaStarInv_posSemidef {w : Vec d} {P : TriadicCube d}
    [NeZero d] {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w P) g) :
    (Homogenization.sigmaStarInvCoarse (offGridCube w P) g).PosSemidef := by
  let hConv := offGridCube_isOpenBoundedConvexDomain w P
  let : IsFiniteMeasure (volumeMeasureOn (offGridCube w P)) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  rcases Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        hConv hEll (offGridCube_volume_pos w P) with
    ⟨_, _, _, _, _, hS, _, _, _⟩
  exact sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse_local hS

/-- The pure-flux response is the quadratic form of the off-grid inverse dual
matrix. -/
theorem responseJ_offGrid_zero_eq_sigmaStarInv {w : Vec d} {P : TriadicCube d}
    [NeZero d] {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w P) g) (q : Vec d) :
    ResponseJ (offGridCube w P) 0 q g = (1 / 2 : ℝ) *
      vecDot q (matVecMul (Homogenization.sigmaStarInvCoarse (offGridCube w P) g) q) := by
  let hConv := offGridCube_isOpenBoundedConvexDomain w P
  let : IsFiniteMeasure (volumeMeasureOn (offGridCube w P)) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  rcases Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        hConv hEll (offGridCube_volume_pos w P) with
    ⟨_, _, _, _, hSInv, _, _, _, _⟩
  exact hSInv.2 q

/-- The canonical upper matrix on an off-grid cube is PSD. -/
theorem offGridB_posSemidef {w : Vec d} {P : TriadicCube d}
    [NeZero d] {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w P) g) :
    (Homogenization.bCoarse
      (Homogenization.sigmaCoarse (offGridCube w P) g)
      (Homogenization.sigmaStarCoarse (offGridCube w P) g)
      (Homogenization.kappaCoarse (offGridCube w P) g)).PosSemidef := by
  let hConv := offGridCube_isOpenBoundedConvexDomain w P
  let : IsFiniteMeasure (volumeMeasureOn (offGridCube w P)) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  rcases Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        hConv hEll (offGridCube_volume_pos w P) with
    ⟨R, sigma0, compat, _, _, hS, hK, hSigma, _⟩
  have hdet :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      R hConv hEll (offGridCube_volume_pos w P) compat hS
  exact bCoarse_canonical_posSemidef_of_isSigmaCoarse hS hK hSigma hdet

/-- The pure-gradient response is the quadratic form of the canonical off-grid
upper matrix. -/
theorem responseJ_offGrid_zero_eq_b {w : Vec d} {P : TriadicCube d}
    [NeZero d] {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w P) g) (p : Vec d) :
    ResponseJ (offGridCube w P) p 0 g = (1 / 2 : ℝ) * vecDot p
      (matVecMul
        (Homogenization.bCoarse
          (Homogenization.sigmaCoarse (offGridCube w P) g)
          (Homogenization.sigmaStarCoarse (offGridCube w P) g)
          (Homogenization.kappaCoarse (offGridCube w P) g)) p) := by
  let hConv := offGridCube_isOpenBoundedConvexDomain w P
  let : IsFiniteMeasure (volumeMeasureOn (offGridCube w P)) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  rcases Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        hConv hEll (offGridCube_volume_pos w P) with
    ⟨R, sigma0, compat, _, _, hS, hK, hSigma, _⟩
  have hdet :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      R hConv hEll (offGridCube_volume_pos w P) compat hS
  exact basic_cg_identities_responseJ_zero_formula_canonical_of_isSigmaCoarse
    (offGridCube w P) g hS hK hSigma hdet p

/-! ## Countable maximal-cover assemblies for the canonical matrices -/

/-- The inverse dual off-grid norm is subadditive over the maximal grid
cover, with exactly the paper's volume normalization. -/
theorem offGridSigmaStarInvMatrixNorm_le_tsum_maximalCubes
    [NeZero d] {w : Vec d} {P : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w P) g)
    (hsummable : Summable fun Q : maximalCubes (offGridCube w P) =>
      cubeVolume (Q : TriadicCube d) *
        Ch02.matrixNorm (Homogenization.sigmaStarInvCoarse
          (openCubeSet (Q : TriadicCube d)) g)) :
    offGridSigmaStarInvMatrixNorm w P g ≤ (cubeVolume P)⁻¹ *
      ∑' Q : maximalCubes (offGridCube w P),
        cubeVolume (Q : TriadicCube d) *
          Ch02.matrixNorm (Homogenization.sigmaStarInvCoarse
            (openCubeSet (Q : TriadicCube d)) g) := by
  let cellM : TriadicCube d → Mat d := fun Q =>
    Homogenization.sigmaStarInvCoarse (openCubeSet Q) g
  have hEllQ : ∀ Q : maximalCubes (offGridCube w P),
      IsEllipticFieldOn lam Lam (openCubeSet (Q : TriadicCube d)) g := by
    intro Q
    exact hEll.mono (measurableSet_openCubeSet _)
      ((openCubeSet_subset_cubeSet _).trans Q.2.1)
  apply sigmaStarInvMatrixNorm_le_tsum_maximalCubes_of_response_quadratic
    hEll (Homogenization.sigmaStarInvCoarse (offGridCube w P) g)
      (offGridSigmaStarInv_posSemidef hEll) cellM
  · intro Q
    have hEllZero : IsEllipticFieldOn lam Lam
        (offGridCube (0 : Vec d) (Q : TriadicCube d)) g := by
      simpa [offGridCube, translateSet_zero] using hEllQ Q
    have h := offGridSigmaStarInv_posSemidef (w := (0 : Vec d)) (P := (Q : TriadicCube d))
      hEllZero
    simpa [offGridCube, translateSet_zero] using h
  · intro x
    exact responseJ_offGrid_zero_eq_sigmaStarInv hEll x
  · intro Q x
    have hEllZero : IsEllipticFieldOn lam Lam
        (offGridCube (0 : Vec d) (Q : TriadicCube d)) g := by
      simpa [offGridCube, translateSet_zero] using hEllQ Q
    have h := responseJ_offGrid_zero_eq_sigmaStarInv
      (w := (0 : Vec d)) (P := (Q : TriadicCube d)) hEllZero x
    simpa [offGridCube, translateSet_zero, cellM] using h
  · simpa [cellM] using hsummable

/-- The upper off-grid norm is subadditive over the maximal grid cover, with
exactly the paper's volume normalization. -/
theorem offGridBMatrixNorm_le_tsum_maximalCubes
    [NeZero d] {w : Vec d} {P : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w P) g)
    (hsummable : Summable fun Q : maximalCubes (offGridCube w P) =>
      cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm
        (Homogenization.bCoarse
          (Homogenization.sigmaCoarse (openCubeSet (Q : TriadicCube d)) g)
          (Homogenization.sigmaStarCoarse (openCubeSet (Q : TriadicCube d)) g)
          (Homogenization.kappaCoarse (openCubeSet (Q : TriadicCube d)) g))) :
    offGridBMatrixNorm w P g ≤ (cubeVolume P)⁻¹ *
      ∑' Q : maximalCubes (offGridCube w P),
        cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm
          (Homogenization.bCoarse
            (Homogenization.sigmaCoarse (openCubeSet (Q : TriadicCube d)) g)
            (Homogenization.sigmaStarCoarse (openCubeSet (Q : TriadicCube d)) g)
            (Homogenization.kappaCoarse (openCubeSet (Q : TriadicCube d)) g)) := by
  let cellM : TriadicCube d → Mat d := fun Q =>
    Homogenization.bCoarse
      (Homogenization.sigmaCoarse (openCubeSet Q) g)
      (Homogenization.sigmaStarCoarse (openCubeSet Q) g)
      (Homogenization.kappaCoarse (openCubeSet Q) g)
  have hEllQ : ∀ Q : maximalCubes (offGridCube w P),
      IsEllipticFieldOn lam Lam (openCubeSet (Q : TriadicCube d)) g := by
    intro Q
    exact hEll.mono (measurableSet_openCubeSet _)
      ((openCubeSet_subset_cubeSet _).trans Q.2.1)
  apply bMatrixNorm_le_tsum_maximalCubes_of_response_quadratic hEll
    (Homogenization.bCoarse
      (Homogenization.sigmaCoarse (offGridCube w P) g)
      (Homogenization.sigmaStarCoarse (offGridCube w P) g)
      (Homogenization.kappaCoarse (offGridCube w P) g))
      (offGridB_posSemidef hEll) cellM
  · intro Q
    have hEllZero : IsEllipticFieldOn lam Lam
        (offGridCube (0 : Vec d) (Q : TriadicCube d)) g := by
      simpa [offGridCube, translateSet_zero] using hEllQ Q
    have h := offGridB_posSemidef (w := (0 : Vec d)) (P := (Q : TriadicCube d))
      hEllZero
    simpa [offGridCube, translateSet_zero, cellM] using h
  · intro x
    exact responseJ_offGrid_zero_eq_b hEll x
  · intro Q x
    have hEllZero : IsEllipticFieldOn lam Lam
        (offGridCube (0 : Vec d) (Q : TriadicCube d)) g := by
      simpa [offGridCube, translateSet_zero] using hEllQ Q
    have h := responseJ_offGrid_zero_eq_b
      (w := (0 : Vec d)) (P := (Q : TriadicCube d)) hEllZero x
    simpa [offGridCube, translateSet_zero, cellM] using h
  · simpa [cellM] using hsummable

end

end SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
