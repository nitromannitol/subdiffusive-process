import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsOffGridEllipticity

/-! General exponent versions of the existing maximal-cube matrix caps. -/

open Homogenization Homogenization.Book Homogenization.Book.Ch02 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

noncomputable section
namespace SubdiffusiveProcess.LambdaStability
variable {d : ℕ} [NeZero d]

theorem offGridSigmaStarInvMatrixNorm_le_cap
    {w : Vec d} {R K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A : Ch02.TriadicCoeffFamily d) {q : Ch02.MultiscaleExponent} (hq : q.IsAdmissible)
    {u : ℝ} (hu0 : 0 < u) (hu : u < 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w R) g)
    (hKsub : offGridCube w R ⊆ cubeSet K) (hRK : R.scale ≤ K.scale) :
    offGridSigmaStarInvMatrixNorm w R g ≤
      12 * (d : ℝ) / (1 - 2 * u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
          (Ch02.lambdaSq K u q A)⁻¹) := by
  classical
  set L : ℝ := (Ch02.lambdaSq K u q A)⁻¹ with hL
  have hLnn : 0 ≤ L := inv_nonneg.mpr
    (Ch02.lambdaSq_nonneg K A hu0 hq)
  set c : ℝ := (3 : ℝ) ^
      (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) * L with hc
  have hcnn : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hLnn
  set B : TriadicCube d → ℝ := fun Q =>
    c * (3 : ℝ) ^ (2 * u * (((R.scale - Q.scale).toNat : ℕ) : ℝ)) with hB
  have hcap : ∀ Q : TriadicCube d, MaximalCubeIn (offGridCube w R) Q →
      Ch02.matrixNorm (Homogenization.sigmaStarInvCoarse (openCubeSet Q) g) ≤ B Q := by
    intro Q hQ
    have hQR : Q.scale ≤ R.scale := scale_le_of_maximalCubeIn_offGridCube hQ
    have hQK : Q.scale ≤ K.scale := hQR.trans hRK
    have hQsub : cubeSet Q ⊆ cubeSet K := hQ.1.trans hKsub
    have hQdesc : Q ∈ descendantsAtScale K Q.scale :=
      mem_descendantsAtScale_of_cubeSet_subset hQsub hQK
    have hone : Ch02.coarseSigmaStarInvMatrixNorm Q A ≤ (Ch02.lambdaSq Q u q A)⁻¹ := by
      cases q with
      | finite q => exact Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv Q A hu0 hq
      | infinity => exact Ch02.oneCube_sigmaStarInv_le_lambdaSq_infinity_inv Q A hu0
    have hdesc := Ch02.descendant_lambdaSq_inv_le
      (Q := K) (R := Q) (k := Q.scale) A hQdesc hu0
      hq
    have hraw : Ch02.coarseSigmaStarInvMatrixNorm Q A ≤
        Ch02.multiscaleDescendantWeight K Q.scale u * L := hone.trans (by simpa [hL] using hdesc)
    rw [matrixNorm_sigmaStarInvCoarse_openCube_eq_coarseSigmaStarInvMatrixNorm A Q g (hg Q)]
    have hKR : (K.scale - R.scale).toNat + (R.scale - Q.scale).toNat =
        (K.scale - Q.scale).toNat := by omega
    have hweight : Ch02.multiscaleDescendantWeight K Q.scale u =
        (3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
          (3 : ℝ) ^ (2 * u * (((R.scale - Q.scale).toNat : ℕ) : ℝ)) := by
      rw [Ch02.multiscaleDescendantWeight, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      have hKQ : ((K.scale - Q.scale : ℤ) : ℝ) =
          (((K.scale - Q.scale).toNat : ℕ) : ℝ) := by
        norm_cast
        exact (Int.toNat_of_nonneg (sub_nonneg.mpr hQK)).symm
      rw [hKQ, ← hKR]
      push_cast
      congr 1
      ring
    calc
      Ch02.coarseSigmaStarInvMatrixNorm Q A ≤
          Ch02.multiscaleDescendantWeight K Q.scale u * L := hraw
      _ = B Q := by rw [hweight, hB, hc]; ring
  obtain ⟨hBsum, hBtle⟩ := summable_and_tsum_maximalCubes_cap_le w R hu0 hu hcnn
  have hdirectSum : Summable fun Q : maximalCubes (offGridCube w R) =>
      cubeVolume (Q : TriadicCube d) *
        Ch02.matrixNorm (Homogenization.sigmaStarInvCoarse
          (openCubeSet (Q : TriadicCube d)) g) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hBsum
    · intro Q
      exact mul_nonneg (cubeVolume_nonneg _) (Ch02.matrixNorm_nonneg _)
    · intro Q
      exact mul_le_mul_of_nonneg_left (hcap Q Q.2) (cubeVolume_nonneg _)
  have hcover := offGridSigmaStarInvMatrixNorm_le_tsum_maximalCubes hEll hdirectSum
  have hsumle : (∑' Q : maximalCubes (offGridCube w R),
      cubeVolume (Q : TriadicCube d) *
        Ch02.matrixNorm (Homogenization.sigmaStarInvCoarse
          (openCubeSet (Q : TriadicCube d)) g)) ≤
      c * (12 * (d : ℝ) * cubeVolume R / (1 - 2 * u)) := by
    refine (Summable.tsum_le_tsum ?_ hdirectSum hBsum).trans hBtle
    intro Q
    exact mul_le_mul_of_nonneg_left (hcap Q Q.2) (cubeVolume_nonneg _)
  have hinv : 0 ≤ (cubeVolume R)⁻¹ := inv_nonneg.mpr (cubeVolume_pos R).le
  calc
    offGridSigmaStarInvMatrixNorm w R g ≤
        (cubeVolume R)⁻¹ * ∑' Q : maximalCubes (offGridCube w R),
          cubeVolume (Q : TriadicCube d) *
            Ch02.matrixNorm (Homogenization.sigmaStarInvCoarse
              (openCubeSet (Q : TriadicCube d)) g) := hcover
    _ ≤ (cubeVolume R)⁻¹ *
        (c * (12 * (d : ℝ) * cubeVolume R / (1 - 2 * u))) :=
      mul_le_mul_of_nonneg_left hsumle hinv
    _ = 12 * (d : ℝ) / (1 - 2 * u) * c := by
      have hv : cubeVolume R ≠ 0 := (cubeVolume_pos R).ne'
      have hden : 1 - 2 * u ≠ 0 := (by linarith only [hu] : 0 < 1 - 2 * u).ne'
      field_simp
    _ = _ := by rw [hc]


theorem offGridBMatrixNorm_le_cap
    {w : Vec d} {R K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A : Ch02.TriadicCoeffFamily d) {q : Ch02.MultiscaleExponent} (hq : q.IsAdmissible)
    {u : ℝ} (hu0 : 0 < u) (hu : u < 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w R) g)
    (hKsub : offGridCube w R ⊆ cubeSet K) (hRK : R.scale ≤ K.scale) :
    offGridBMatrixNorm w R g ≤
      12 * (d : ℝ) / (1 - 2 * u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
          Ch02.LambdaSq K u q A) := by
  classical
  set L : ℝ := Ch02.LambdaSq K u q A with hL
  have hLnn : 0 ≤ L := Ch02.LambdaSq_nonneg K A hu0 hq
  set c : ℝ := (3 : ℝ) ^
      (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) * L with hc
  have hcnn : 0 ≤ c := mul_nonneg (Real.rpow_nonneg (by norm_num) _) hLnn
  set B : TriadicCube d → ℝ := fun Q =>
    c * (3 : ℝ) ^ (2 * u * (((R.scale - Q.scale).toNat : ℕ) : ℝ)) with hB
  have hcap : ∀ Q : TriadicCube d, MaximalCubeIn (offGridCube w R) Q →
      Ch02.matrixNorm
        (Homogenization.bCoarse
          (Homogenization.sigmaCoarse (openCubeSet Q) g)
          (Homogenization.sigmaStarCoarse (openCubeSet Q) g)
          (Homogenization.kappaCoarse (openCubeSet Q) g)) ≤ B Q := by
    intro Q hQ
    have hQR : Q.scale ≤ R.scale := scale_le_of_maximalCubeIn_offGridCube hQ
    have hQK : Q.scale ≤ K.scale := hQR.trans hRK
    have hQsub : cubeSet Q ⊆ cubeSet K := hQ.1.trans hKsub
    have hQdesc : Q ∈ descendantsAtScale K Q.scale :=
      mem_descendantsAtScale_of_cubeSet_subset hQsub hQK
    have hEllQ : IsEllipticFieldOn lam Lam (openCubeSet Q) g :=
      hEll.mono (measurableSet_openCubeSet Q)
        ((openCubeSet_subset_cubeSet Q).trans hQ.1)
    have hone := Ch02.oneCube_b_le_LambdaSq Q A hu0 hq
    have hdesc := Ch02.descendant_LambdaSq_le
      (Q := K) (R := Q) (k := Q.scale) A hQdesc hu0
      hq
    have hraw : Ch02.coarseBMatrixNorm Q A ≤
        Ch02.multiscaleDescendantWeight K Q.scale u * L :=
      hone.trans (by simpa [hL] using hdesc)
    rw [matrixNorm_bCoarse_openCube_eq_coarseBMatrixNorm A Q g (hg Q) hEllQ]
    have hKR : (K.scale - R.scale).toNat + (R.scale - Q.scale).toNat =
        (K.scale - Q.scale).toNat := by omega
    have hweight : Ch02.multiscaleDescendantWeight K Q.scale u =
        (3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
          (3 : ℝ) ^ (2 * u * (((R.scale - Q.scale).toNat : ℕ) : ℝ)) := by
      rw [Ch02.multiscaleDescendantWeight, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      have hKQ : ((K.scale - Q.scale : ℤ) : ℝ) =
          (((K.scale - Q.scale).toNat : ℕ) : ℝ) := by
        norm_cast
        exact (Int.toNat_of_nonneg (sub_nonneg.mpr hQK)).symm
      rw [hKQ, ← hKR]
      push_cast
      congr 1
      ring
    calc
      Ch02.coarseBMatrixNorm Q A ≤
          Ch02.multiscaleDescendantWeight K Q.scale u * L := hraw
      _ = B Q := by rw [hweight, hB, hc]; ring
  obtain ⟨hBsum, hBtle⟩ := summable_and_tsum_maximalCubes_cap_le w R hu0 hu hcnn
  have hdirectSum : Summable fun Q : maximalCubes (offGridCube w R) =>
      cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm
        (Homogenization.bCoarse
          (Homogenization.sigmaCoarse (openCubeSet (Q : TriadicCube d)) g)
          (Homogenization.sigmaStarCoarse (openCubeSet (Q : TriadicCube d)) g)
          (Homogenization.kappaCoarse (openCubeSet (Q : TriadicCube d)) g)) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hBsum
    · intro Q
      exact mul_nonneg (cubeVolume_nonneg _) (Ch02.matrixNorm_nonneg _)
    · intro Q
      exact mul_le_mul_of_nonneg_left (hcap Q Q.2) (cubeVolume_nonneg _)
  have hcover := offGridBMatrixNorm_le_tsum_maximalCubes hEll hdirectSum
  have hsumle : (∑' Q : maximalCubes (offGridCube w R),
      cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm
        (Homogenization.bCoarse
          (Homogenization.sigmaCoarse (openCubeSet (Q : TriadicCube d)) g)
          (Homogenization.sigmaStarCoarse (openCubeSet (Q : TriadicCube d)) g)
          (Homogenization.kappaCoarse (openCubeSet (Q : TriadicCube d)) g))) ≤
      c * (12 * (d : ℝ) * cubeVolume R / (1 - 2 * u)) := by
    refine (Summable.tsum_le_tsum ?_ hdirectSum hBsum).trans hBtle
    intro Q
    exact mul_le_mul_of_nonneg_left (hcap Q Q.2) (cubeVolume_nonneg _)
  have hinv : 0 ≤ (cubeVolume R)⁻¹ := inv_nonneg.mpr (cubeVolume_pos R).le
  calc
    offGridBMatrixNorm w R g ≤
        (cubeVolume R)⁻¹ * ∑' Q : maximalCubes (offGridCube w R),
          cubeVolume (Q : TriadicCube d) * Ch02.matrixNorm
            (Homogenization.bCoarse
              (Homogenization.sigmaCoarse (openCubeSet (Q : TriadicCube d)) g)
              (Homogenization.sigmaStarCoarse (openCubeSet (Q : TriadicCube d)) g)
              (Homogenization.kappaCoarse (openCubeSet (Q : TriadicCube d)) g)) := hcover
    _ ≤ (cubeVolume R)⁻¹ *
        (c * (12 * (d : ℝ) * cubeVolume R / (1 - 2 * u))) :=
      mul_le_mul_of_nonneg_left hsumle hinv
    _ = 12 * (d : ℝ) / (1 - 2 * u) * c := by
      have hv : cubeVolume R ≠ 0 := (cubeVolume_pos R).ne'
      have hden : 1 - 2 * u ≠ 0 := (by linarith only [hu] : 0 < 1 - 2 * u).ne'
      field_simp
    _ = _ := by rw [hc]


end SubdiffusiveProcess.LambdaStability
