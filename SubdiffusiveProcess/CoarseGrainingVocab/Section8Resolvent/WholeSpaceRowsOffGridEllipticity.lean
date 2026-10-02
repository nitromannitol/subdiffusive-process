/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.LambdaStability
import Homogenization.Internal.Ch02.MatrixExtraction




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization Homogenization.Book Homogenization.Book.Ch02 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport

noncomputable section

variable {d : ℕ}

/-! ## 1. The `b`-matrix adapter on a triadic cube -/

open Homogenization.Internal.Ch02.BookCh02 in
/-- The set-level upper matrix used by the off-grid cover is exactly the
Chapter 2 one-cube carrier when both read the same coefficient field.

This is the `b` analogue of
`LambdaStabilitySupport.matrixNorm_sigmaStarInvCoarse_openCube_eq_coarseSigmaStarInvMatrixNorm`;
unlike the inverse-dual one it needs the canonical `sigmaStar` witness, hence
the ellipticity hypothesis. -/
theorem matrixNorm_bCoarse_openCube_eq_coarseBMatrixNorm [NeZero d]
    {lam Lam : ℝ} (A : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d)
    (g : CoeffField d) (hg : (A.coeffOn Q).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) g) :
    Ch02.matrixNorm
        (Homogenization.bCoarse
          (Homogenization.sigmaCoarse (openCubeSet Q) g)
          (Homogenization.sigmaStarCoarse (openCubeSet Q) g)
          (Homogenization.kappaCoarse (openCubeSet Q) g)) =
      Ch02.coarseBMatrixNorm Q A := by
  have hConv : IsOpenBoundedConvexDomain (openCubeSet Q) :=
    isOpenBoundedConvexDomain_openCubeSet Q
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using hConv.isFiniteMeasure_restrict_volume
  have hEll' : IsEllipticFieldOn lam Lam (openCubeSet Q)
      (A.coeffOn Q).toCoeffField := by rw [hg]; exact hEll
  rcases exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain hConv hEll' hvol with
    ⟨_, _, _, _, _, hS, _, _, _⟩
  unfold Ch02.coarseBMatrixNorm Ch02.cubeDomain
  rw [← hg]
  exact congrArg Ch02.matrixNorm
    (Homogenization.Internal.Ch02.book_coarseMatrices_b_eq_bCoarse_of_isSigmaStarCoarse
      _ _ hS).symm

/-! ## 2. The upper-ellipticity cap on one translated cube -/

/-- The upper off-grid matrix norm on a translated cube is controlled by the
enclosing grid cube's `Lambda_{u,2}`.

This is the `b` mirror of
`LambdaStabilitySupport.offGridSigmaStarInvMatrixNorm_le_cap_two`; the two
proofs differ only in which one-cube and descendant bound is quoted. -/
theorem offGridBMatrixNorm_le_cap_two [NeZero d]
    {w : Vec d} {R K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A : Ch02.TriadicCoeffFamily d) {u : ℝ} (hu0 : 0 < u) (hu : u < 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w R) g)
    (hKsub : offGridCube w R ⊆ cubeSet K) (hRK : R.scale ≤ K.scale) :
    offGridBMatrixNorm w R g ≤
      12 * (d : ℝ) / (1 - 2 * u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
          Ch02.LambdaSq K u (.finite 2) A) := by
  classical
  set L : ℝ := Ch02.LambdaSq K u (.finite 2) A with hL
  have hLnn : 0 ≤ L := Ch02.LambdaSq_finite_nonneg K A hu0 (by norm_num)
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
    have hone := Ch02.oneCube_b_le_LambdaSq_finite
      Q A hu0 (by norm_num : (1 : ℝ) ≤ 2)
    have hdesc := Ch02.descendant_LambdaSq_le
      (Q := K) (R := Q) (k := Q.scale) A hQdesc hu0
      (by norm_num : (Ch02.MultiscaleExponent.finite 2).IsAdmissible)
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

/-! ## 3. The off-grid upper carrier `Lambda_{t,2}` -/

/-- The shell maximum in the translated definition of `Lambda_{t,2}`. -/
def offGridBShellMax (w : Vec d) (P : TriadicCube d) (k : ℤ)
    (g : CoeffField d) : ℝ :=
  Ch02.finsetSupReal (descendantsAtScale P k)
    (fun R => offGridBMatrixNorm w R g)

theorem offGridBShellMax_nonneg (w : Vec d) (P : TriadicCube d) (k : ℤ)
    (g : CoeffField d) : 0 ≤ offGridBShellMax w P k g :=
  Ch02.finsetSupReal_nonneg _ _ fun _ _ => Ch02.matrixNorm_nonneg _

theorem offGridBShellMax_le {w : Vec d} {P : TriadicCube d} {k : ℤ}
    {g : CoeffField d} {C : ℝ} (hk : k ≤ P.scale)
    (h : ∀ R ∈ descendantsAtScale P k, offGridBMatrixNorm w R g ≤ C) :
    offGridBShellMax w P k g ≤ C :=
  Ch02.finsetSupReal_le _ (descendantsAtScale_nonempty P hk) h

/-- The literal finite-`q = 2` translated carrier `Lambda_{t,2}`. -/
def offGridLambdaSqTwo (w : Vec d) (P : TriadicCube d) (t : ℝ)
    (g : CoeffField d) : ℝ :=
  ∑' l : ℕ, Ch02.geometricWeight t 2 l *
    offGridBShellMax w P (P.scale - (l : ℤ)) g

/-! ## 4. The translation dictionary -/

/-- Ellipticity of `g` on a translated set is ellipticity of the translated
field on the set itself.  Derived from the public converse at translate
`-w`. -/
theorem isEllipticFieldOn_translateCoeffField {lam Lam : ℝ} {U : Set (Vec d)}
    {g : CoeffField d} (w : Vec d)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w U) g) :
    IsEllipticFieldOn lam Lam U (translateCoeffField w g) := by
  have hfield : translateCoeffField (-w) (translateCoeffField w g) = g := by
    funext x
    simp [translateCoeffField]
  have hset : translateSet (-w) (translateSet w U) = U := by
    ext x
    simp [mem_translateSet_iff_sub_mem, sub_neg_eq_add]
  have hEll' : IsEllipticFieldOn lam Lam (translateSet w U)
      (translateCoeffField (-w) (translateCoeffField w g)) := by
    rw [hfield]; exact hEll
  have := IsEllipticFieldOn.translateSet_of_translateCoeffField (-w) hEll'
  rwa [hset] at this

/-- The off-grid inverse-dual norm at translate `w` is the on-grid norm of the
translated family. -/
theorem offGridSigmaStarInvMatrixNorm_eq_translated
    (Aw : Ch02.TriadicCoeffFamily d) (w : Vec d) (R : TriadicCube d)
    (g : CoeffField d)
    (hgw : (Aw.coeffOn R).toCoeffField = translateCoeffField w g) :
    offGridSigmaStarInvMatrixNorm w R g =
      Ch02.coarseSigmaStarInvMatrixNorm R Aw := by
  rw [offGridSigmaStarInvMatrixNorm, offGridCube,
    sigmaStarInvCoarse_translateSet_eq_translateCoeffField]
  exact matrixNorm_sigmaStarInvCoarse_openCube_eq_coarseSigmaStarInvMatrixNorm
    Aw R _ hgw

/-- The off-grid upper norm at translate `w` is the on-grid norm of the
translated family. -/
theorem offGridBMatrixNorm_eq_translated [NeZero d] {lam Lam : ℝ}
    (Aw : Ch02.TriadicCoeffFamily d) (w : Vec d) (R : TriadicCube d)
    (g : CoeffField d)
    (hgw : (Aw.coeffOn R).toCoeffField = translateCoeffField w g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (openCubeSet R)) g) :
    offGridBMatrixNorm w R g = Ch02.coarseBMatrixNorm R Aw := by
  rw [offGridBMatrixNorm, offGridCube, bCoarse_translateSet_eq_translateCoeffField]
  exact matrixNorm_bCoarse_openCube_eq_coarseBMatrixNorm Aw R _ hgw
    (isEllipticFieldOn_translateCoeffField w hEll)

theorem offGridSigmaStarInvShellMax_eq_translated
    (Aw : Ch02.TriadicCoeffFamily d) (w : Vec d) (P : TriadicCube d) (k : ℤ)
    (g : CoeffField d)
    (hgw : ∀ S : TriadicCube d,
      (Aw.coeffOn S).toCoeffField = translateCoeffField w g) :
    offGridSigmaStarInvShellMax w P k g =
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale P k Aw := by
  unfold offGridSigmaStarInvShellMax
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
  refine congrArg (Ch02.finsetSupReal (descendantsAtScale P k)) ?_
  funext R
  exact offGridSigmaStarInvMatrixNorm_eq_translated Aw w R g (hgw R)

theorem offGridBShellMax_eq_translated [NeZero d] {lam Lam : ℝ}
    (Aw : Ch02.TriadicCoeffFamily d) (w : Vec d) (P : TriadicCube d) {k : ℤ}
    (g : CoeffField d)
    (hgw : ∀ S : TriadicCube d,
      (Aw.coeffOn S).toCoeffField = translateCoeffField w g)
    (hk : k ≤ P.scale)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g) :
    offGridBShellMax w P k g =
      Ch02.maxDescendantBMatrixNormAtScale P k Aw := by
  unfold offGridBShellMax Ch02.maxDescendantBMatrixNormAtScale
  refine Ch02.finsetSupReal_congr _ ?_
  intro R hR
  have hRsub : cubeSet R ⊆ cubeSet P :=
    cubeSet_subset_of_mem_descendantsAtScale hk hR
  have hsub : translateSet w (openCubeSet R) ⊆ translateSet w (cubeSet P) := by
    intro x hx
    exact mem_translateSet_iff_sub_mem.2
      (hRsub (openCubeSet_subset_cubeSet R (mem_translateSet_iff_sub_mem.1 hx)))
  have hEllR : IsEllipticFieldOn lam Lam (translateSet w (openCubeSet R)) g := by
    refine hEll.mono ?_ hsub
    have : IsOpen (translateSet w (openCubeSet R)) := by
      simpa [offGridCube] using isOpen_offGridCube w R
    exact this.measurableSet
  exact offGridBMatrixNorm_eq_translated Aw w R g (hgw R) hEllR

/-! ## 5. The two carriers as on-grid quantities of the translated family -/

theorem offGridLambdaSqInvTwo_eq_translated [NeZero d]
    (Aw : Ch02.TriadicCoeffFamily d) (w : Vec d) (P : TriadicCube d) {t : ℝ}
    (ht : 0 < t) (g : CoeffField d)
    (hgw : ∀ S : TriadicCube d,
      (Aw.coeffOn S).toCoeffField = translateCoeffField w g) :
    offGridLambdaSqInvTwo w P t g = (Ch02.lambdaSq P t (.finite 2) Aw)⁻¹ := by
  rw [offGridLambdaSqInvTwo]
  have hseries := Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum
    P t 2 Aw (by norm_num : (0 : ℝ) < 2) (by positivity : 0 ≤ t * 2)
  have hrpow : (Ch02.lambdaSqFinite P t 2 Aw) ^ (-1 : ℝ) =
      (Ch02.lambdaSqFinite P t 2 Aw)⁻¹ := Real.rpow_neg_one _
  simpa [offGridSigmaStarInvShellMax_eq_translated Aw w P _ g hgw,
    Ch02.lambdaSq, Real.rpow_one, hrpow] using hseries.symm

theorem offGridLambdaSqTwo_eq_translated [NeZero d] {lam Lam : ℝ}
    (Aw : Ch02.TriadicCoeffFamily d) (w : Vec d) (P : TriadicCube d) {t : ℝ}
    (ht : 0 < t) (g : CoeffField d)
    (hgw : ∀ S : TriadicCube d,
      (Aw.coeffOn S).toCoeffField = translateCoeffField w g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g) :
    offGridLambdaSqTwo w P t g = Ch02.LambdaSq P t (.finite 2) Aw := by
  have hshell : ∀ l : ℕ,
      offGridBShellMax w P (P.scale - (l : ℤ)) g =
        Ch02.maxDescendantBMatrixNormAtScale P (P.scale - (l : ℤ)) Aw :=
    fun l => offGridBShellMax_eq_translated Aw w P g hgw (by omega) hEll
  have hseries := Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum
    P t 2 Aw (by norm_num : (0 : ℝ) < 2) (by positivity : 0 ≤ t * 2)
  have h22 : (2 : ℝ) / 2 = 1 := by norm_num
  rw [h22] at hseries
  have hone : ∀ x : ℝ, Real.rpow x 1 = x := fun x => Real.rpow_one x
  simp only [hone] at hseries
  rw [offGridLambdaSqTwo]
  simp only [hshell]
  exact hseries.symm

/-! ## 6. The upper-ellipticity off-grid stability estimate -/

private theorem scale_le_of_translateSet_cubeSet_subset'
    {w : Vec d} {P K : TriadicCube d} [NeZero d]
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

/-- The pole-free arbitrary-translate `Lambda` stability estimate at `q = 2`:
the exact mirror of `LambdaStabilitySupport.offGridLambdaSqInvTwo_le`. -/
theorem offGridLambdaSqTwo_le [NeZero d]
    {w : Vec d} {P K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A : Ch02.TriadicCoeffFamily d) {t u : ℝ}
    (hu0 : 0 < u) (hut : u < t) (ht : t ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    offGridLambdaSqTwo w P t g ≤
      offGridStabilityConst d t u *
        ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          Ch02.LambdaSq K u (.finite 2) A) := by
  have hu : u < 1 / 2 := hut.trans_le ht
  have hPK : P.scale ≤ K.scale := scale_le_of_translateSet_cubeSet_subset' hcontain
  set base : ℝ := (3 : ℝ) ^
      (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
        Ch02.LambdaSq K u (.finite 2) A with hbase
  have hbase0 : 0 ≤ base := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Ch02.LambdaSq_finite_nonneg K A hu0 (by norm_num))
  set cap : ℝ := 12 * (d : ℝ) / (1 - 2 * u) * base with hcap
  have hfac : 0 ≤ 12 * (d : ℝ) / (1 - 2 * u) :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
      (by linarith only [hu] : 0 ≤ 1 - 2 * u)
  have hcap0 : 0 ≤ cap := mul_nonneg hfac hbase0
  have hshell : ∀ l : ℕ,
      offGridBShellMax w P (P.scale - (l : ℤ)) g ≤
        cap * (3 : ℝ) ^ (2 * u * (l : ℝ)) := by
    intro l
    refine offGridBShellMax_le (by omega) ?_
    intro R hR
    have hRscale : R.scale = P.scale - (l : ℤ) :=
      descendant_scale_eq_of_mem_descendantsAtScale hR
    have hRsub : cubeSet R ⊆ cubeSet P :=
      cubeSet_subset_of_mem_descendantsAtScale (by omega) hR
    have hsub : offGridCube w R ⊆ translateSet w (cubeSet P) := by
      intro x hx
      exact mem_translateSet_iff_sub_mem.2
        (hRsub (openCubeSet_subset_cubeSet R (mem_translateSet_iff_sub_mem.1 hx)))
    have hEllR := hEll.mono (isOpen_offGridCube w R).measurableSet hsub
    have hraw := offGridBMatrixNorm_le_cap_two A hu0 hu hg hEllR
      (hsub.trans hcontain) (by omega : R.scale ≤ K.scale)
    have hdepth : (K.scale - R.scale).toNat =
        (K.scale - P.scale).toNat + l := by omega
    calc
      offGridBMatrixNorm w R g ≤
          12 * (d : ℝ) / (1 - 2 * u) *
            ((3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
              Ch02.LambdaSq K u (.finite 2) A) := hraw
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
    (fun l => offGridBShellMax w P (P.scale - (l : ℤ)) g)
    (fun l => offGridBShellMax_nonneg w P _ g) hshell
  rw [offGridLambdaSqTwo]
  refine hsum.trans (le_of_eq ?_)
  rw [hcap, hbase, offGridStabilityConst]
  have htu : t - u ≠ 0 := (sub_pos.mpr hut).ne'
  have hden : 1 - 2 * u ≠ 0 := (by linarith only [hu] : 0 < 1 - 2 * u).ne'
  field_simp
  ring

/-! ## 7. The two transfer theorems

These are the exact analogues of `Ch02.descendant_lambdaSq_inv_le` and
`Ch02.descendant_LambdaSq_le` with "descendant of `K`" weakened to "arbitrary
translate of a triadic cube, contained in `K`".  They are what a mesoscopic
cell family built from half-grid translates needs, and together they discharge
the second alternative of the author item recorded in the P-226 section §5 of
`ledger/reports/provider-77-whole-space-provider.md`.

`Aw` is the coefficient family of the translated field, i.e. the family the
analysis sees after the change of variables that moves the cell `w + P` onto
the triadic cube `P`. -/

/-- **Lower coarse ellipticity of a translate of a triadic cube.** -/
theorem lambdaSq_translated_inv_le [NeZero d]
    {w : Vec d} {P K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A Aw : Ch02.TriadicCoeffFamily d) {t u : ℝ}
    (hu0 : 0 < u) (hut : u < t) (ht : t ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hgw : ∀ S : TriadicCube d,
      (Aw.coeffOn S).toCoeffField = translateCoeffField w g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    (Ch02.lambdaSq P t (.finite 2) Aw)⁻¹ ≤
      offGridStabilityConst d t u *
        ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          (Ch02.lambdaSq K u (.finite 2) A)⁻¹) := by
  rw [← offGridLambdaSqInvTwo_eq_translated Aw w P (hu0.trans hut) g hgw]
  exact SubdiffusiveProcess.CoarseGrainingVocab.lambdaSq_stability_two_of_exact_representative
    A hu0 hut ht hg hEll hcontain

/-- **Upper coarse ellipticity of a translate of a triadic cube.** -/
theorem LambdaSq_translated_le [NeZero d]
    {w : Vec d} {P K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A Aw : Ch02.TriadicCoeffFamily d) {t u : ℝ}
    (hu0 : 0 < u) (hut : u < t) (ht : t ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hgw : ∀ S : TriadicCube d,
      (Aw.coeffOn S).toCoeffField = translateCoeffField w g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    Ch02.LambdaSq P t (.finite 2) Aw ≤
      offGridStabilityConst d t u *
        ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          Ch02.LambdaSq K u (.finite 2) A) := by
  rw [← offGridLambdaSqTwo_eq_translated Aw w P (hu0.trans hut) g hgw hEll]
  exact offGridLambdaSqTwo_le A hu0 hut ht hg hEll hcontain

/-- The coarse ellipticity **ratio** of a translate of a triadic cube, at the
`q = 2` indices in which the flux clause of the coarse-grained Poincaré
inequality is stated (`WholeSpaceRowsFluxPoincare.lean`).  The two loss factors
multiply; the ratio is the quantity the Caccioppoli prefactor is built from. -/
theorem thetaRatio_two_translated_le [NeZero d]
    {w : Vec d} {P K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A Aw : Ch02.TriadicCoeffFamily d) {su tu u : ℝ}
    (hu0 : 0 < u) (hus : u < su) (hut : u < tu)
    (hs : su ≤ 1 / 2) (ht : tu ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hgw : ∀ S : TriadicCube d,
      (Aw.coeffOn S).toCoeffField = translateCoeffField w g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    Ch02.LambdaSq P su (.finite 2) Aw * (Ch02.lambdaSq P tu (.finite 2) Aw)⁻¹ ≤
      (offGridStabilityConst d su u * offGridStabilityConst d tu u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
            (3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          (Ch02.LambdaSq K u (.finite 2) A *
            (Ch02.lambdaSq K u (.finite 2) A)⁻¹)) := by
  have hU := LambdaSq_translated_le A Aw hu0 hus hs hg hgw hEll hcontain
  have hL := lambdaSq_translated_inv_le A Aw hu0 hut ht hg hgw hEll hcontain
  have hUnn : 0 ≤ Ch02.LambdaSq P su (.finite 2) Aw :=
    Ch02.LambdaSq_finite_nonneg P Aw (hu0.trans hus) (by norm_num)
  have hLnn : 0 ≤ (Ch02.lambdaSq P tu (.finite 2) Aw)⁻¹ :=
    inv_nonneg.mpr (Ch02.lambdaSq_finite_nonneg P Aw (hu0.trans hut) (by norm_num))
  have hRU : 0 ≤ offGridStabilityConst d su u *
      ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
        Ch02.LambdaSq K u (.finite 2) A) :=
    le_trans hUnn hU
  calc
    Ch02.LambdaSq P su (.finite 2) Aw *
        (Ch02.lambdaSq P tu (.finite 2) Aw)⁻¹ ≤
        (offGridStabilityConst d su u *
          ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
            Ch02.LambdaSq K u (.finite 2) A)) *
          (offGridStabilityConst d tu u *
            ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
              (Ch02.lambdaSq K u (.finite 2) A)⁻¹)) :=
      mul_le_mul hU hL hLnn hRU
    _ = _ := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
