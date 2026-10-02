import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJSupport
import Homogenization.Book.Ch04.Theorems.Scalarization

/-!
# Characterization of the infinite-volume annealed coefficient

This file identifies the `sInf` definition of `ahom` with the limit of the
finite-volume scalar readouts.  The convergence argument follows the
monotonicity/plateau decomposition in
`Algsuperdiff/Section3/Provider/Annealed/Monotonicity.lean` and
`Algsuperdiff/Section3/Provider/Base/AnnealedPlateau.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped Matrix.Norms.Elementwise

noncomputable section

private def rotatePotentialSequence {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
  fun k => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR (ω k)

private theorem measurable_rotatePotentialSequence {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measurable (rotatePotentialSequence (d := d) R hR) := by
  apply measurable_pi_iff.mpr
  intro k
  exact (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_rotate R hR).comp
    (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k)

theorem aux_dedup_d094_rotate_triadicScale {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (k : ℕ)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k g) =
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR g) := by
  apply SubdiffusiveProcess.Frozen.Assumptions.PotentialField.ext
  intro x
  simp [matVecMul_smul]

private theorem rotate_triadicScale {d : ℕ} (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (k : ℕ)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k g) =
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR g) := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d094_rotate_triadicScale (d := d) (R := R) (hR := hR) (k := k) (g := g)

-- PROVENANCE: mirrors the marginal-law transport in
-- `Algsuperdiff/Section3/Provider/Corrector/ShellSumLayerFlip.lean`.
theorem aux_dedup_d099_potentialMarginalLaw_isotropic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR)
        (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure =
      (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := by
  have hscale := congrArg ProbabilityMeasure.toMeasure
    (M.shellPrefix.marginal_scaling k)
  have hzero := congrArg ProbabilityMeasure.toMeasure
    (M.G3.signed_coordinate_permutations R hR)
  change (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure =
    Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure at hscale
  change Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR)
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure =
    (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure at hzero
  calc
    Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR)
        (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure =
      Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR)
        (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) := by rw [hscale]
    _ = Measure.map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR ∘
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
      Measure.map_map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_rotate R hR)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k)
    _ = Measure.map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k ∘
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by
      apply congrArg (fun f : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d →
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          Measure.map f (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)
      funext g
      exact rotate_triadicScale R hR k g
    _ = Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
        (Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR)
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) :=
      (Measure.map_map
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_rotate R hR)).symm
    _ = Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure := by rw [hzero]
    _ = (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := by
      rw [hscale]

private theorem potentialMarginalLaw_isotropic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (k : ℕ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR)
        (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure =
      (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := by exact SubdiffusiveProcess.CoarseGrainingVocab.aux_dedup_d099_potentialMarginalLaw_isotropic (d := d) (M := M) (k := k) (R := R) (hR := hR)

-- PROVENANCE: the product-measure uniqueness step mirrors
-- `Algsuperdiff/Section3/Provider/Corrector/ShellSumLayerFlip.lean`.
private theorem potentialSequenceLaw_isotropic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) :
    Measure.map (rotatePotentialSequence (d := d) R hR) M.P.toMeasure =
      M.P.toMeasure := by
  have hprod := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k : ℕ => SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k)).mp
      M.shellPrefix.independent
  have hrotInd : iIndepFun
      (fun k : ℕ => fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
        SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR (ω k)) M.P.toMeasure :=
    M.shellPrefix.independent.comp
      (fun _ => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR)
      (fun _ => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_rotate R hR)
  have hrotProd := (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun _ : ℕ =>
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_rotate R hR).comp
        (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate _))).mp hrotInd
  calc
    Measure.map (rotatePotentialSequence (d := d) R hR) M.P.toMeasure =
      Measure.infinitePi (fun k : ℕ =>
        Measure.map (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
          SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR (ω k))
          M.P.toMeasure) := by
      simpa only [rotatePotentialSequence, Function.comp_apply] using hrotProd
    _ = Measure.infinitePi (fun k : ℕ =>
        Measure.map (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => ω k)
          M.P.toMeasure) := by
      apply congrArg Measure.infinitePi
      funext k
      calc
        Measure.map (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
            SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR (ω k)) M.P.toMeasure =
          Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR)
            (Measure.map (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => ω k)
              M.P.toMeasure) := by
            change Measure.map
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.rotate R hR ∘
                fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => ω k)
              M.P.toMeasure = _
            rw [Measure.map_map
              (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_rotate R hR)
              (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k)]
        _ = Measure.map (fun ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => ω k)
            M.P.toMeasure := potentialMarginalLaw_isotropic M k R hR
    _ = Measure.map (fun ω (k : ℕ) => ω k) M.P.toMeasure := hprod.symm
    _ = M.P.toMeasure := Measure.map_id'

private theorem aCutoff_rotatePotentialSequence {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
        (rotatePotentialSequence (d := d) R hR ω) x =
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω (matVecMul R x) := by
  simp [SubdiffusiveProcess.Frozen.Assumptions.aCutoff, rotatePotentialSequence]

private theorem scalarCoeffField_aCutoff_rotatePotentialSequence {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (R : Mat d)
    (hR : IsSignedPermutationMatrix R)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
        (rotatePotentialSequence (d := d) R hR ω)) =
      rotateCoeffField R
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) := by
  funext x
  change Homogenization.scalarMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
        (rotatePotentialSequence (d := d) R hR ω) x) =
    matTranspose R * Homogenization.scalarMatrix
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω (matVecMul R x)) * R
  rw [aCutoff_rotatePotentialSequence M L R hR ω x]
  simp [Homogenization.scalarMatrix, hR.transpose_mul_self]

theorem isCoarseBlockMatrix_ch02_aCutoff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) :
    IsCoarseBlockMatrix (openCubeSet Q)
      (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω))
      (Ch02.coarseBlockMatrix (Ch02.cubeDomain Q)
        (aCutoffCoeffOnData M L ω (Ch02.cubeDomain Q)).toCoeffOn) := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let hdata := aCutoffCoeffOnData M L ω U
  let aQ : Ch02.CoeffOn U := hdata.toCoeffOn
  refine ⟨Ch02.isSymmetricBlockMat_coarseBlockMatrix U aQ, ?_⟩
  intro P
  calc
    Mu (openCubeSet Q) P
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) =
      Mu (U : Set (Vec d)) P aQ.toCoeffField := by
        simp [U, aQ, Ch02.cubeDomain_coe, ScalarCoeffOnData.toCoeffOn]
    _ = Ch02.doubledMu U aQ P := by
      exact (Homogenization.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu U aQ P).symm
    _ = (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (Ch02.coarseBlockMatrix U aQ) P) :=
      (Ch02.doubledMuTheory U aQ).doubledMu_eq_coarseBlockMatrix P

private theorem exists_coarseBlockMatrix_aCutoff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) :
    ∃ Abar : BlockMat d,
      IsCoarseBlockMatrix (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) Abar :=
  ⟨_, isCoarseBlockMatrix_ch02_aCutoff M L ω Q⟩

private theorem randomAMatrix_eq_rawSigmaCoarse {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) :
    randomAMatrix M L (Ch02.cubeDomain Q) ω =
      Homogenization.sigmaCoarse (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) := by
  let hdata := aCutoffCoeffOnData M L ω (Ch02.cubeDomain Q)
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    (Ch02.cubeDomain Q) hdata.toCoeffOn hdata.isSymmetric
  calc
    randomAMatrix M L (Ch02.cubeDomain Q) ω =
        Ch02.sigmaCoarse (Ch02.cubeDomain Q) hdata.toCoeffOn :=
      hTheory.derived_matrices.1
    _ = Homogenization.sigmaCoarse (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) := by
      simpa [hdata, ScalarCoeffOnData.toCoeffOn] using
        Homogenization.Internal.Ch02.book_sigmaCoarse_eq_sigmaCoarse
          (Ch02.cubeDomain Q) hdata.toCoeffOn

theorem coarseBlockMatrix_upperLeft_eq_sigmaCoarse_aCutoff {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (Q : TriadicCube d) :
    (coarseBlockMatrix (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω))).upperLeft =
      sigmaCoarse (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let hdata := aCutoffCoeffOnData M L ω U
  let aQ : Ch02.CoeffOn U := hdata.toCoeffOn
  have hcoarse := isCoarseBlockMatrix_ch02_aCutoff M L ω Q
  have hEq : Ch02.coarseBlockMatrix U aQ =
      coarseBlockMatrix (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) :=
    eq_coarseBlockMatrix_of_isCoarseBlockMatrix hcoarse
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U aQ hdata.isSymmetric
  calc
    (coarseBlockMatrix (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω))).upperLeft =
      (Ch02.coarseBlockMatrix U aQ).upperLeft := by rw [hEq]
    _ = Ch02.bCoarse U aQ := Ch02.coarseBlockMatrix_upperLeft U aQ
    _ = Ch02.sigmaCoarse U aQ := hTheory.derived_matrices.2.2
    _ = sigmaCoarse (openCubeSet Q)
        (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)) := by
      simpa [U, aQ, ScalarCoeffOnData.toCoeffOn] using
        Homogenization.Internal.Ch02.book_sigmaCoarse_eq_sigmaCoarse U aQ

private theorem randomAMatrix_rotatePotentialSequence_signFlip {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (n : ℤ) (i : Fin d) :
    randomAMatrix M L (Ch02.cubeDomain (originCube d n))
        (rotatePotentialSequence (signFlipMatrix i)
          (isSignedPermutationMatrix_signFlipMatrix i) ω) =
      signFlipMatrix i *
        randomAMatrix M L (Ch02.cubeDomain (originCube d n)) ω *
          signFlipMatrix i := by
  let a : CoeffField d :=
    scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
  let R : Mat d := signFlipMatrix i
  let hR : IsSignedPermutationMatrix R :=
    isSignedPermutationMatrix_signFlipMatrix i
  have hfield : scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
      (rotatePotentialSequence R hR ω)) = rotateCoeffField R a :=
    scalarCoeffField_aCutoff_rotatePotentialSequence M L R hR ω
  have hex := exists_coarseBlockMatrix_aCutoff M L ω (originCube d n)
  rw [randomAMatrix_eq_rawSigmaCoarse, randomAMatrix_eq_rawSigmaCoarse, hfield]
  calc
    sigmaCoarse (openCubeSet (originCube d n)) (rotateCoeffField R a) =
        (coarseBlockMatrix (openCubeSet (originCube d n))
          (rotateCoeffField R a)).upperLeft :=
      (by
        rw [← hfield]
        exact (coarseBlockMatrix_upperLeft_eq_sigmaCoarse_aCutoff M L
          (rotatePotentialSequence R hR ω) (originCube d n)).symm)
    _ = R * (coarseBlockMatrix (openCubeSet (originCube d n)) a).upperLeft * R := by
      simpa [R] using
        coarseBlockMatrix_upperLeft_signFlip_openCubeSet_originCube_of_exists hex i
    _ = R * sigmaCoarse (openCubeSet (originCube d n)) a * R := by
      rw [coarseBlockMatrix_upperLeft_eq_sigmaCoarse_aCutoff M L ω (originCube d n)]

private theorem randomAMatrix_rotatePotentialSequence_swap {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (n : ℤ) (i j : Fin d) :
    randomAMatrix M L (Ch02.cubeDomain (originCube d n))
        (rotatePotentialSequence (Matrix.swap ℝ i j)
          (isSignedPermutationMatrix_swap i j) ω) =
      Matrix.swap ℝ i j *
        randomAMatrix M L (Ch02.cubeDomain (originCube d n)) ω *
          Matrix.swap ℝ i j := by
  let a : CoeffField d :=
    scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L ω)
  let R : Mat d := Matrix.swap ℝ i j
  let hR : IsSignedPermutationMatrix R := isSignedPermutationMatrix_swap i j
  have hfield : scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L
      (rotatePotentialSequence R hR ω)) = rotateCoeffField R a :=
    scalarCoeffField_aCutoff_rotatePotentialSequence M L R hR ω
  have hex := exists_coarseBlockMatrix_aCutoff M L ω (originCube d n)
  rw [randomAMatrix_eq_rawSigmaCoarse, randomAMatrix_eq_rawSigmaCoarse, hfield]
  calc
    sigmaCoarse (openCubeSet (originCube d n)) (rotateCoeffField R a) =
        (coarseBlockMatrix (openCubeSet (originCube d n))
          (rotateCoeffField R a)).upperLeft :=
      (by
        rw [← hfield]
        exact (coarseBlockMatrix_upperLeft_eq_sigmaCoarse_aCutoff M L
          (rotatePotentialSequence R hR ω) (originCube d n)).symm)
    _ = R * (coarseBlockMatrix (openCubeSet (originCube d n)) a).upperLeft * R := by
      simpa [R] using
        coarseBlockMatrix_upperLeft_swap_openCubeSet_originCube_of_exists hex i j
    _ = R * sigmaCoarse (openCubeSet (originCube d n)) a * R := by
      rw [coarseBlockMatrix_upperLeft_eq_sigmaCoarse_aCutoff M L ω (originCube d n)]

private theorem swap_mul_mul_swap_apply {d : ℕ} (i j r c : Fin d) (A : Mat d) :
    (Matrix.swap ℝ i j * A * Matrix.swap ℝ i j) r c =
      A (Equiv.swap i j r) (Equiv.swap i j c) := by
  by_cases hr_i : r = i
  · subst r
    by_cases hc_i : c = i
    · subst c
      simp
    · by_cases hc_j : c = j
      · subst c
        simp
      · simp [Matrix.mul_swap_of_ne hc_i hc_j, Equiv.swap_apply_of_ne_of_ne hc_i hc_j]
  · by_cases hr_j : r = j
    · subst r
      by_cases hc_i : c = i
      · subst c
        simp
      · by_cases hc_j : c = j
        · subst c
          simp
        · simp [Matrix.mul_swap_of_ne hc_i hc_j, Equiv.swap_apply_of_ne_of_ne hc_i hc_j]
    · by_cases hc_i : c = i
      · subst c
        simp [Matrix.swap_mul_of_ne hr_i hr_j, Equiv.swap_apply_of_ne_of_ne hr_i hr_j]
      · by_cases hc_j : c = j
        · subst c
          simp [Matrix.swap_mul_of_ne hr_i hr_j, Equiv.swap_apply_of_ne_of_ne hr_i hr_j]
        · simp [Matrix.swap_mul_of_ne hr_i hr_j, Matrix.mul_swap_of_ne hc_i hc_j,
            Equiv.swap_apply_of_ne_of_ne hr_i hr_j,
            Equiv.swap_apply_of_ne_of_ne hc_i hc_j]

private theorem abar_originCube_isSignFlipInvariant {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ) :
    IsSignFlipInvariant
      (abar M m (Ch02.cubeDomain (originCube d n))) := by
  intro i
  let R : Mat d := signFlipMatrix i
  let hR : IsSignedPermutationMatrix R :=
    isSignedPermutationMatrix_signFlipMatrix i
  let T := rotatePotentialSequence (d := d) R hR
  let F := randomAMatrix M m (Ch02.cubeDomain (originCube d n))
  have hmap : Measure.map T M.P.toMeasure = M.P.toMeasure :=
    potentialSequenceLaw_isotropic M R hR
  have hFint : Integrable F M.P.toMeasure :=
    integrable_randomAMatrix M m (Ch02.cubeDomain (originCube d n))
  change R * (∫ ω, F ω ∂M.P.toMeasure) * R = ∫ ω, F ω ∂M.P.toMeasure
  ext r c
  set s : ℝ :=
    (if r = i then (-1 : ℝ) else 1) * (if c = i then (-1 : ℝ) else 1) with hs
  calc
    (R * (∫ ω, F ω ∂M.P.toMeasure) * R) r c =
        s * ∫ ω, F ω r c ∂M.P.toMeasure := by
      rw [show R = signFlipMatrix i by rfl,
        signFlipMatrix_mul_mul_signFlipMatrix_apply,
        Homogenization.integral_matrix_apply hFint r c, hs]
      ring
    _ = ∫ ω, s * F ω r c ∂M.P.toMeasure :=
      (MeasureTheory.integral_const_mul s _).symm
    _ = ∫ ω, F (T ω) r c ∂M.P.toMeasure := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      have hentry := congrArg (fun A : Mat d => A r c)
        (randomAMatrix_rotatePotentialSequence_signFlip M m ω n i)
      change F (T ω) r c =
        (signFlipMatrix i * F ω * signFlipMatrix i) r c at hentry
      rw [signFlipMatrix_mul_mul_signFlipMatrix_apply] at hentry
      rw [hentry, hs]
      ring
    _ = ∫ ω, F ω r c ∂M.P.toMeasure :=
      Homogenization.integral_comp_eq_of_map_eq
        (measurable_rotatePotentialSequence R hR) hmap
        (fun ω => F ω r c) (((hFint.eval r).eval c).aestronglyMeasurable)
    _ = (∫ ω, F ω ∂M.P.toMeasure) r c :=
      (Homogenization.integral_matrix_apply hFint r c).symm

private theorem abar_originCube_isSwapInvariant {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (n : ℤ) :
    IsSwapInvariant (abar M m (Ch02.cubeDomain (originCube d n))) := by
  intro i j
  let R : Mat d := Matrix.swap ℝ i j
  let hR : IsSignedPermutationMatrix R := isSignedPermutationMatrix_swap i j
  let T := rotatePotentialSequence (d := d) R hR
  let F := randomAMatrix M m (Ch02.cubeDomain (originCube d n))
  have hmap : Measure.map T M.P.toMeasure = M.P.toMeasure :=
    potentialSequenceLaw_isotropic M R hR
  have hFint : Integrable F M.P.toMeasure :=
    integrable_randomAMatrix M m (Ch02.cubeDomain (originCube d n))
  change R * (∫ ω, F ω ∂M.P.toMeasure) * R = ∫ ω, F ω ∂M.P.toMeasure
  ext r c
  calc
    (R * (∫ ω, F ω ∂M.P.toMeasure) * R) r c =
        ∫ ω, F ω (Equiv.swap i j r) (Equiv.swap i j c) ∂M.P.toMeasure := by
      rw [show R = Matrix.swap ℝ i j by rfl, swap_mul_mul_swap_apply,
        Homogenization.integral_matrix_apply hFint]
    _ = ∫ ω, F (T ω) r c ∂M.P.toMeasure := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      have hentry := congrArg (fun A : Mat d => A r c)
        (randomAMatrix_rotatePotentialSequence_swap M m ω n i j)
      change F (T ω) r c =
        (Matrix.swap ℝ i j * F ω * Matrix.swap ℝ i j) r c at hentry
      rw [swap_mul_mul_swap_apply] at hentry
      exact hentry.symm
    _ = ∫ ω, F ω r c ∂M.P.toMeasure :=
      Homogenization.integral_comp_eq_of_map_eq
        (measurable_rotatePotentialSequence R hR) hmap
        (fun ω => F ω r c) (((hFint.eval r).eval c).aestronglyMeasurable)
    _ = (∫ ω, F ω ∂M.P.toMeasure) r c :=
      (Homogenization.integral_matrix_apply hFint r c).symm

theorem randomAMatrix_posSemidef {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (U : Ch02.Domain d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (randomAMatrix M m U ω).PosSemidef := by
  let hdata := aCutoffCoeffOnData M m ω U
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  change (aMatrix U hdata.toCoeffOn).PosSemidef
  change (Ch02.aCoarse U hdata.toCoeffOn).PosSemidef
  rw [hTheory.derived_matrices.1, ← hTheory.derived_matrices.2.2]
  exact Ch02.bCoarse_posSemidef U hdata.toCoeffOn

private theorem randomAMatrix_isSymm {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (U : Ch02.Domain d)
    (ω : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) :
    (randomAMatrix M m U ω).IsSymm := by
  let hdata := aCutoffCoeffOnData M m ω U
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  change (Ch02.aCoarse U hdata.toCoeffOn).IsSymm
  rw [hTheory.derived_matrices.1]
  exact Ch02.sigmaCoarse_isSymm U hdata.toCoeffOn

private theorem integral_randomAMatrix_quadratic_full {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (U : Ch02.Domain d)
    (p : Vec d) :
    (∫ ω, vecDot p (matVecMul (randomAMatrix M m U ω) p) ∂M.P.toMeasure) =
      vecDot p (matVecMul (abar M m U) p) := by
  simp only [vecDot, matVecMul]
  rw [MeasureTheory.integral_finset_sum Finset.univ]
  · congr 1
    ext i
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum Finset.univ]
    · simp_rw [MeasureTheory.integral_mul_const]
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      change (∫ ω, randomAMatrix M m U ω i j ∂M.P.toMeasure) * p j =
        (∫ ω, randomAMatrix M m U ω ∂M.P.toMeasure) i j * p j
      rw [Homogenization.integral_matrix_apply
        (integrable_randomAMatrix M m U) i j]
    · intro j _hj
      exact (((integrable_randomAMatrix M m U).eval i).eval j).mul_const (p j)
  · intro i _hi
    exact (MeasureTheory.integrable_finset_sum Finset.univ fun j _hj =>
      (((integrable_randomAMatrix M m U).eval i).eval j).mul_const (p j)).const_mul (p i)

/-- The annealed primal matrix is positive semidefinite. -/
theorem abar_posSemidef {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (U : Ch02.Domain d) :
    (abar M m U).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using (show (abar M m U).IsSymm by
      rw [Matrix.IsSymm]
      ext i j
      simp only [Matrix.transpose_apply]
      rw [abar, Homogenization.integral_matrix_apply (integrable_randomAMatrix M m U) j i,
        Homogenization.integral_matrix_apply (integrable_randomAMatrix M m U) i j]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      exact (randomAMatrix_isSymm M m U ω).apply i j)
  · intro p
    change 0 ≤ vecDot p (matVecMul (abar M m U) p)
    rw [← integral_randomAMatrix_quadratic_full M m U p]
    exact MeasureTheory.integral_nonneg fun ω => by
      simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
        (randomAMatrix_posSemidef M m U ω).dotProduct_mulVec_nonneg p

private theorem antitone_abar_quadratic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (p : Vec d) :
    Antitone (fun n : ℕ => vecDot p (matVecMul
      (abar M m (Ch02.cubeDomain (originCube d (n : ℤ)))) p)) := by
  intro n k hnk
  induction hnk with
  | refl => exact le_rfl
  | @step k hnk ih =>
      have h := matLoewnerLE_abar_originCube_succ M m k p
      have hstep : vecDot p (matVecMul
          (abar M m (Ch02.cubeDomain (originCube d ((k + 1 : ℕ) : ℤ)))) p) ≤
          vecDot p (matVecMul
            (abar M m (Ch02.cubeDomain (originCube d (k : ℤ)))) p) := by
        linarith
      exact hstep.trans ih

private theorem exists_tendsto_abar_quadratic {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (p : Vec d) :
    ∃ q : ℝ, Tendsto (fun n : ℕ => vecDot p (matVecMul
      (abar M m (Ch02.cubeDomain (originCube d (n : ℤ)))) p)) atTop (nhds q) := by
  apply Real.tendsto_of_bddBelow_antitone
  · refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
      (abar_posSemidef M m
        (Ch02.cubeDomain (originCube d (n : ℤ)))).dotProduct_mulVec_nonneg p
  · exact antitone_abar_quadratic M m p

private theorem matrix_apply_eq_polarization {d : ℕ} (A : Mat d)
    (hA : A.IsSymm) (i j : Fin d) :
    A i j = (1 / 2 : ℝ) *
      (vecDot (Pi.single i 1 + Pi.single j 1)
          (matVecMul A (Pi.single i 1 + Pi.single j 1)) -
        vecDot (Pi.single i 1) (matVecMul A (Pi.single i 1)) -
        vecDot (Pi.single j 1) (matVecMul A (Pi.single j 1))) := by
  rw [matVecMul_add, vecDot_add_left, vecDot_add_right, vecDot_add_right]
  simp only [vecDot_single_left, matVecMul_single]
  rw [hA.apply j i]
  ring

private theorem exists_tendsto_abar_entry {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (i j : Fin d) :
    ∃ a : ℝ, Tendsto (fun n : ℕ =>
      abar M m (Ch02.cubeDomain (originCube d (n : ℤ))) i j) atTop (nhds a) := by
  obtain ⟨qij, hqij⟩ := exists_tendsto_abar_quadratic M m
    (Pi.single i 1 + Pi.single j 1)
  obtain ⟨qi, hqi⟩ := exists_tendsto_abar_quadratic M m (Pi.single i 1)
  obtain ⟨qj, hqj⟩ := exists_tendsto_abar_quadratic M m (Pi.single j 1)
  refine ⟨(1 / 2 : ℝ) * (qij - qi - qj), ?_⟩
  have hconst : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hlim := hconst.mul ((hqij.sub hqi).sub hqj)
  apply hlim.congr'
  filter_upwards with n
  exact (matrix_apply_eq_polarization
    (abar M m (Ch02.cubeDomain (originCube d (n : ℤ))))
    (by
      rw [Matrix.IsSymm]
      ext r c
      simp only [Matrix.transpose_apply]
      rw [abar,
        Homogenization.integral_matrix_apply
          (integrable_randomAMatrix M m
            (Ch02.cubeDomain (originCube d (n : ℤ)))) c r,
        Homogenization.integral_matrix_apply
          (integrable_randomAMatrix M m
            (Ch02.cubeDomain (originCube d (n : ℤ)))) r c]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      exact (randomAMatrix_isSymm M m
        (Ch02.cubeDomain (originCube d (n : ℤ))) ω).apply r c)
    i j).symm

/-- The centered-cube annealed primal matrices have an entrywise (equivalently,
matrix-topology) limit.  The proof uses monotone quadratic forms and
polarization; it does not incorrectly treat off-diagonal entries as monotone. -/
theorem exists_tendsto_abar_originCube {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    ∃ A_lim : Mat d, Tendsto (fun n : ℕ =>
      abar M m (Ch02.cubeDomain (originCube d (n : ℤ)))) atTop (nhds A_lim) := by
  let A_lim : Mat d := fun i j => Classical.choose (exists_tendsto_abar_entry M m i j)
  refine ⟨A_lim, ?_⟩
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact Classical.choose_spec (exists_tendsto_abar_entry M m i j)

/-- The trace readout inherits the Löwner monotonicity of the annealed primal
matrix on centered cubes. -/
theorem antitone_abarScalarReadout {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    Antitone (abarScalarReadout M m) := by
  intro n k hnk
  apply (div_le_div_iff_of_pos_right (by
    exact_mod_cast lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)).2
  unfold Matrix.trace
  apply Finset.sum_le_sum
  intro i _hi
  induction hnk with
  | refl => exact le_rfl
  | @step k hnk ih =>
      exact le_trans
        (by
          have h := matLoewnerLE_abar_originCube_succ M m k (Pi.single i 1)
          simpa [matVecMul_single, vecDot_single_left] using h)
        ih

/-- The `sInf` definition of `ahom` is the indexed infimum of the centered-cube
scalar readouts. -/
theorem ahom_eq_iInf_abarScalarReadout {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    ahom M m = ⨅ n : ℕ, abarScalarReadout M m n := by
  rfl

/-- The scalar readout converges to the `sInf` used to define `ahom`.  No
strict positivity of `ahom` is used. -/
theorem tendsto_abarScalarReadout_ahom {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    Tendsto (abarScalarReadout M m) atTop (nhds (ahom M m)) := by
  have hbdd : BddBelow (Set.range (abarScalarReadout M m)) :=
    ⟨0, by
      rintro x ⟨n, rfl⟩
      exact abarScalarReadout_nonneg M m n⟩
  simpa only [ahom, iInf] using
    tendsto_atTop_ciInf (antitone_abarScalarReadout M m) hbdd

/-- G3 signed-coordinate-permutation symmetry makes the annealed primal
matrix on every centered cube a scalar matrix.  The whole sample-law symmetry
is derived from the zero-layer symmetry, marginal scaling, and independence. -/
theorem abar_originCube_isScalarMatrix {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ) :
    IsScalarMatrix
      (abar M m (Ch02.cubeDomain (originCube d (n : ℤ)))) := by
  letI : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  exact isScalarMatrix_of_isSignFlipInvariant_of_isSwapInvariant
    (abar_originCube_isSignFlipInvariant M m n)
    (abar_originCube_isSwapInvariant M m n)

/-- The G3-scalarized annealed primal matrix is exactly its trace readout
times the identity. -/
theorem abar_eq_abarScalarReadout_smul_one {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m n : ℕ) :
    abar M m (Ch02.cubeDomain (originCube d (n : ℤ))) =
      abarScalarReadout M m n • (1 : Mat d) := by
  obtain ⟨c, hc⟩ := abar_originCube_isScalarMatrix M m n
  have hdNat : d ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)
  have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hdNat
  have hreadout : abarScalarReadout M m n = c := by
    rw [abarScalarReadout, hc]
    simp [Matrix.trace, hdReal]
  rw [hc, hreadout]

/-- Once G3 scalarization is supplied, the scalar readout characterization
upgrades immediately to convergence of the annealed matrices. -/
theorem tendsto_abar_originCube_ahom_of_scalarization {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ)
    (hscalar : ∀ n : ℕ,
      abar M m (Ch02.cubeDomain (originCube d (n : ℤ))) =
        abarScalarReadout M m n • (1 : Mat d)) :
    Tendsto (fun n : ℕ =>
      abar M m (Ch02.cubeDomain (originCube d (n : ℤ))))
      atTop (nhds (ahom M m • (1 : Mat d))) := by
  have hlim := (tendsto_abarScalarReadout_ahom M m).smul_const (1 : Mat d)
  apply hlim.congr'
  filter_upwards with n
  exact (hscalar n).symm

/-- The annealed primal matrices on centered cubes converge to the scalar
infinite-volume coefficient. -/
theorem tendsto_abar_originCube_ahom {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) :
    Tendsto (fun n : ℕ =>
      abar M m (Ch02.cubeDomain (originCube d (n : ℤ))))
      atTop (nhds (ahom M m • (1 : Mat d))) :=
  tendsto_abar_originCube_ahom_of_scalarization M m
    (abar_eq_abarScalarReadout_smul_one M m)

end

end SubdiffusiveProcess.CoarseGrainingVocab
