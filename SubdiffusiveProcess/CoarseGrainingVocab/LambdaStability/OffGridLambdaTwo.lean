-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/Regularity/StepSevenLambdaStability.lean
/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridMatrixCarrier
import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridStabilityCap
import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridComposeDepth
import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability.OffGridStabilityArith
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties
import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Localization

/-!
# The arbitrary-translate lambda stability estimate at q = 2

This composes the countable PSD inverse-dual matrix assembly with the same
maximal-cube depth sum and outer geometric sum used by the proved error
specialization.  It is the pole-free lambda slot needed by the boundary
Caccioppoli conversion.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

open Homogenization Homogenization.Book Homogenization.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem translateSet_subset_lambda {w : Vec d} {S T : Set (Vec d)}
    (h : S ⊆ T) : translateSet w S ⊆ translateSet w T := fun _ hx =>
  mem_translateSet_iff_sub_mem.2 (h (mem_translateSet_iff_sub_mem.1 hx))

/-- PROVENANCE: public specialization of the volume comparison used privately
in `OffGridComposeAssembly.lean`. -/
private theorem scale_le_of_translateSet_cubeSet_subset_lambda
    {w : Vec d} {P K : TriadicCube d}
    (h : translateSet w (cubeSet P) ⊆ cubeSet K) : P.scale ≤ K.scale := by
  have hvol : (volume (translateSet w (cubeSet P))).toReal ≤
      (volume (cubeSet K)).toReal :=
    ENNReal.toReal_mono (volume_cubeSet_lt_top K).ne (measure_mono h)
  rw [volume_translateSet_eq, volume_cubeSet_toReal, volume_cubeSet_toReal,
    cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale] at hvol
  by_contra hcon
  push_neg at hcon
  have hlt : (3 : ℝ) ^ K.scale < (3 : ℝ) ^ P.scale :=
    zpow_lt_zpow_right₀ (by norm_num) hcon
  exact absurd hvol (not_le.2
    (pow_lt_pow_left₀ hlt (zpow_pos (by norm_num) K.scale).le (NeZero.ne d)))

/-- The inverse-dual matrix norm on an arbitrary translated cube is controlled
by the enclosing grid cube's `lambda_{u,2}^{-1}`. -/
theorem offGridSigmaStarInvMatrixNorm_le_cap_two
    {w : Vec d} {R K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A : Ch02.TriadicCoeffFamily d) {u : ℝ} (hu0 : 0 < u) (hu : u < 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w R) g)
    (hKsub : offGridCube w R ⊆ cubeSet K) (hRK : R.scale ≤ K.scale) :
    offGridSigmaStarInvMatrixNorm w R g ≤
      12 * (d : ℝ) / (1 - 2 * u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
          (Ch02.lambdaSq K u (.finite 2) A)⁻¹) := by
  classical
  set L : ℝ := (Ch02.lambdaSq K u (.finite 2) A)⁻¹ with hL
  have hLnn : 0 ≤ L := inv_nonneg.mpr
    (Ch02.lambdaSq_finite_nonneg K A hu0 (by norm_num))
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
    have hone := Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv
      Q A hu0 (by norm_num : (1 : ℝ) ≤ 2)
    have hdesc := Ch02.descendant_lambdaSq_inv_le
      (Q := K) (R := Q) (k := Q.scale) A hQdesc hu0
      (by norm_num : (Ch02.MultiscaleExponent.finite 2).IsAdmissible)
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

/-- The shell maximum in the translated definition of
`lambda_{t,2}^{-1}`. -/
def offGridSigmaStarInvShellMax (w : Vec d) (P : TriadicCube d) (k : ℤ)
    (g : CoeffField d) : ℝ :=
  Ch02.finsetSupReal (descendantsAtScale P k)
    (fun R => offGridSigmaStarInvMatrixNorm w R g)

omit [NeZero d] in
theorem offGridSigmaStarInvShellMax_nonneg (w : Vec d) (P : TriadicCube d)
    (k : ℤ) (g : CoeffField d) : 0 ≤ offGridSigmaStarInvShellMax w P k g :=
  Ch02.finsetSupReal_nonneg _ _ fun _ _ => Ch02.matrixNorm_nonneg _

omit [NeZero d] in
theorem offGridSigmaStarInvShellMax_le {w : Vec d} {P : TriadicCube d}
    {k : ℤ} {g : CoeffField d} {C : ℝ} (hk : k ≤ P.scale)
    (h : ∀ R ∈ descendantsAtScale P k, offGridSigmaStarInvMatrixNorm w R g ≤ C) :
    offGridSigmaStarInvShellMax w P k g ≤ C :=
  Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty P hk) h

omit [NeZero d] in
/-- At zero translate the shell is exactly CoarseGraining's Chapter 2 shell. -/
theorem offGridSigmaStarInvShellMax_zero_eq (P : TriadicCube d) (k : ℤ)
    (A : Ch02.TriadicCoeffFamily d) (g : CoeffField d)
    (hg : ∀ Q : TriadicCube d, (A.coeffOn Q).toCoeffField = g) :
    offGridSigmaStarInvShellMax (0 : Vec d) P k g =
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale P k A := by
  unfold offGridSigmaStarInvShellMax Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
  refine congrArg (Ch02.finsetSupReal (descendantsAtScale P k)) ?_
  funext R
  rw [offGridSigmaStarInvMatrixNorm, offGridCube, translateSet_zero,
    matrixNorm_sigmaStarInvCoarse_openCube_eq_coarseSigmaStarInvMatrixNorm A R g (hg R)]

/-- The literal finite-`q=2` translated carrier `lambda_{t,2}^{-1}`. -/
def offGridLambdaSqInvTwo (w : Vec d) (P : TriadicCube d) (t : ℝ)
    (g : CoeffField d) : ℝ :=
  ∑' l : ℕ, Ch02.geometricWeight t 2 l *
    offGridSigmaStarInvShellMax w P (P.scale - (l : ℤ)) g

/-- At zero translate the new carrier is definitionally conservative: it is
CoarseGraining's `lambda_{t,2}^{-1}`. -/
theorem offGridLambdaSqInvTwo_zero_eq (P : TriadicCube d) {t : ℝ} (ht : 0 < t)
    (A : Ch02.TriadicCoeffFamily d) (g : CoeffField d)
    (hg : ∀ Q : TriadicCube d, (A.coeffOn Q).toCoeffField = g) :
    offGridLambdaSqInvTwo (0 : Vec d) P t g =
      (Ch02.lambdaSq P t (.finite 2) A)⁻¹ := by
  rw [offGridLambdaSqInvTwo]
  have hseries := Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum
    P t 2 A (by norm_num : (0 : ℝ) < 2) (by positivity : 0 ≤ t * 2)
  have hrpow : (Ch02.lambdaSqFinite P t 2 A) ^ (-1 : ℝ) =
      (Ch02.lambdaSqFinite P t 2 A)⁻¹ := Real.rpow_neg_one _
  simpa [offGridSigmaStarInvShellMax_zero_eq P _ A g hg,
    Ch02.lambdaSq, Real.rpow_one, hrpow] using hseries.symm

/-- The pole-free arbitrary-translate lambda stability estimate at `q=2`. -/
theorem offGridLambdaSqInvTwo_le
    {w : Vec d} {P K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A : Ch02.TriadicCoeffFamily d) {t u : ℝ}
    (hu0 : 0 < u) (hut : u < t) (ht : t ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    offGridLambdaSqInvTwo w P t g ≤
      offGridStabilityConst d t u *
        ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          (Ch02.lambdaSq K u (.finite 2) A)⁻¹) := by
  have hu : u < 1 / 2 := hut.trans_le ht
  have hPK : P.scale ≤ K.scale := scale_le_of_translateSet_cubeSet_subset_lambda hcontain
  set base : ℝ := (3 : ℝ) ^
      (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
        (Ch02.lambdaSq K u (.finite 2) A)⁻¹ with hbase
  have hbase0 : 0 ≤ base := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (inv_nonneg.mpr (Ch02.lambdaSq_finite_nonneg K A hu0 (by norm_num)))
  set cap : ℝ := 12 * (d : ℝ) / (1 - 2 * u) * base with hcap
  have hfac : 0 ≤ 12 * (d : ℝ) / (1 - 2 * u) :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
      (by linarith only [hu] : 0 ≤ 1 - 2 * u)
  have hcap0 : 0 ≤ cap := mul_nonneg hfac hbase0
  have hshell : ∀ l : ℕ,
      offGridSigmaStarInvShellMax w P (P.scale - (l : ℤ)) g ≤
        cap * (3 : ℝ) ^ (2 * u * (l : ℝ)) := by
    intro l
    refine offGridSigmaStarInvShellMax_le (by omega) ?_
    intro R hR
    have hRscale : R.scale = P.scale - (l : ℤ) :=
      descendant_scale_eq_of_mem_descendantsAtScale hR
    have hRsub : cubeSet R ⊆ cubeSet P :=
      cubeSet_subset_of_mem_descendantsAtScale (by omega) hR
    have hsub : offGridCube w R ⊆ translateSet w (cubeSet P) :=
      (translateSet_subset_lambda (openCubeSet_subset_cubeSet R)).trans
        (translateSet_subset_lambda hRsub)
    have hEllR := hEll.mono (isOpen_offGridCube w R).measurableSet hsub
    have hraw := offGridSigmaStarInvMatrixNorm_le_cap_two A hu0 hu hg hEllR
      (hsub.trans hcontain) (by omega : R.scale ≤ K.scale)
    have hdepth : (K.scale - R.scale).toNat =
        (K.scale - P.scale).toNat + l := by omega
    calc
      offGridSigmaStarInvMatrixNorm w R g ≤
          12 * (d : ℝ) / (1 - 2 * u) *
            ((3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
              (Ch02.lambdaSq K u (.finite 2) A)⁻¹) := hraw
      _ = cap * (3 : ℝ) ^ (2 * u * (l : ℝ)) := by
        rw [hcap, hbase, hdepth]
        push_cast
        have hsplit : (3 : ℝ) ^
              (2 * u * ((((K.scale - P.scale).toNat : ℕ) : ℝ) + (l : ℝ))) =
            (3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
              (3 : ℝ) ^ (2 * u * (l : ℝ)) := by
          rw [show 2 * u * ((((K.scale - P.scale).toNat : ℕ) : ℝ) + (l : ℝ)) =
              2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ) + 2 * u * (l : ℝ) by ring,
            Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        rw [hsplit]
        ring
  obtain ⟨_, hsum⟩ := tsum_geometricWeight_two_mul_le hu0 hut ht hcap0
    (fun l => offGridSigmaStarInvShellMax w P (P.scale - (l : ℤ)) g)
    (fun l => offGridSigmaStarInvShellMax_nonneg w P _ g) hshell
  rw [offGridLambdaSqInvTwo]
  refine hsum.trans (le_of_eq ?_)
  rw [hcap, hbase, offGridStabilityConst]
  have htu : t - u ≠ 0 := (sub_pos.mpr hut).ne'
  have hden : 1 - 2 * u ≠ 0 := (by linarith only [hu] : 0 < 1 - 2 * u).ne'
  field_simp
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
