module

public import SubdiffusiveProcess.LambdaStability.CarrierNorms

@[expose] public section

/-! Both off-grid ellipticity estimates for every admissible exponent. -/
open Homogenization Homogenization.Book Homogenization.Book.Ch02 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

noncomputable section
namespace SubdiffusiveProcess.LambdaStability
variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem translateSet_mono {w : Vec d} {S T : Set (Vec d)}
    (h : S ⊆ T) : translateSet w S ⊆ translateSet w T := fun _ hx =>
  mem_translateSet_iff_sub_mem.2 (h (mem_translateSet_iff_sub_mem.1 hx))

private theorem scale_le_of_translateSet_cubeSet_subset_lambda
    {w : Vec d} {P K : TriadicCube d}
    (h : translateSet w (cubeSet P) ⊆ cubeSet K) : P.scale ≤ K.scale := by
  have hvol : (volume (translateSet w (cubeSet P))).toReal ≤
      (volume (cubeSet K)).toReal :=
    ENNReal.toReal_mono (volume_cubeSet_lt_top K).ne (measure_mono h)
  rw [volume_translateSet_eq, volume_cubeSet_toReal, volume_cubeSet_toReal,
    cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale] at hvol
  by_contra hcon
  push Not at hcon
  have hlt : (3 : ℝ) ^ K.scale < (3 : ℝ) ^ P.scale :=
    zpow_lt_zpow_right₀ (by norm_num) hcon
  exact absurd hvol (not_le.2
    (pow_lt_pow_left₀ hlt (zpow_pos (by norm_num) K.scale).le (NeZero.ne d)))

theorem lowerInv_le
    {w : Vec d} {P K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A : Ch02.TriadicCoeffFamily d) {q : Ch02.MultiscaleExponent} (hq : q.IsAdmissible)
    {t u : ℝ}
    (hu0 : 0 < u) (hut : u < t) (ht : t ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    lowerInv w P t q g ≤
      indexFactor q u t * (12 * (d : ℝ) / (1 - 2 * u)) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          (Ch02.lambdaSq K u q A)⁻¹) := by
  have hu : u < 1 / 2 := hut.trans_le ht
  have hPK : P.scale ≤ K.scale := scale_le_of_translateSet_cubeSet_subset_lambda hcontain
  set base : ℝ := (3 : ℝ) ^
      (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
        (Ch02.lambdaSq K u q A)⁻¹ with hbase
  have hbase0 : 0 ≤ base := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (inv_nonneg.mpr (Ch02.lambdaSq_nonneg K A hu0 hq))
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
      (translateSet_mono (openCubeSet_subset_cubeSet R)).trans
        (translateSet_mono hRsub)
    have hEllR := hEll.mono (isOpen_offGridCube w R).measurableSet hsub
    have hraw := offGridSigmaStarInvMatrixNorm_le_cap A hq hu0 hu hg hEllR
      (hsub.trans hcontain) (by omega : R.scale ≤ K.scale)
    have hdepth : (K.scale - R.scale).toNat =
        (K.scale - P.scale).toNat + l := by omega
    calc
      offGridSigmaStarInvMatrixNorm w R g ≤
          12 * (d : ℝ) / (1 - 2 * u) *
            ((3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
              (Ch02.lambdaSq K u q A)⁻¹) := hraw
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
  have hnorm := shellNorm_le_of_shell_cap hu0 hut hq hcap0
    (fun l => offGridSigmaStarInvShellMax w P (P.scale - (l : ℤ)) g)
    (fun l => offGridSigmaStarInvShellMax_nonneg w P _ g) hshell
  exact hnorm.trans_eq (by rw [hcap, hbase]; ring)

theorem upper_le
    {w : Vec d} {P K : TriadicCube d} {g : CoeffField d} {lam Lam : ℝ}
    (A : Ch02.TriadicCoeffFamily d) {q : Ch02.MultiscaleExponent} (hq : q.IsAdmissible)
    {t u : ℝ}
    (hu0 : 0 < u) (hut : u < t) (ht : t ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    upper w P t q g ≤
      indexFactor q u t * (12 * (d : ℝ) / (1 - 2 * u)) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          Ch02.LambdaSq K u q A) := by
  have hu : u < 1 / 2 := hut.trans_le ht
  have hPK : P.scale ≤ K.scale := scale_le_of_translateSet_cubeSet_subset_lambda hcontain
  set base : ℝ := (3 : ℝ) ^
      (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
        Ch02.LambdaSq K u q A with hbase
  have hbase0 : 0 ≤ base := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Ch02.LambdaSq_nonneg K A hu0 hq)
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
    have hraw := offGridBMatrixNorm_le_cap A hq hu0 hu hg hEllR
      (hsub.trans hcontain) (by omega : R.scale ≤ K.scale)
    have hdepth : (K.scale - R.scale).toNat =
        (K.scale - P.scale).toNat + l := by omega
    calc
      offGridBMatrixNorm w R g ≤
          12 * (d : ℝ) / (1 - 2 * u) *
            ((3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
              Ch02.LambdaSq K u q A) := hraw
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
  have hnorm := shellNorm_le_of_shell_cap hu0 hut hq hcap0
    (fun l => offGridBShellMax w P (P.scale - (l : ℤ)) g)
    (fun l => offGridBShellMax_nonneg w P _ g) hshell
  exact hnorm.trans_eq (by rw [hcap, hbase]; ring)

end SubdiffusiveProcess.LambdaStability
