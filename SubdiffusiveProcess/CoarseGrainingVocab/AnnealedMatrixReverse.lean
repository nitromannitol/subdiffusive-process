module

public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffRatioSup
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Integral

@[expose] public section

/-!
# Reverse finite-volume annealed matrix comparisons

This module implements the reciprocal-Jensen and prefix/suffix factorization
steps in the proof of `l.annealed.matrix.bounds`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped MatrixOrder

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

private theorem inv_integral_le_integral_inv
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu] {R : Omega → ℝ}
    (hRm : Measurable R) (hRpos : ∀ omega, 0 < R omega)
    (hRint : Integrable R mu) (hRinvInt : Integrable (fun omega => (R omega)⁻¹) mu) :
    (∫ omega, R omega ∂mu)⁻¹ ≤ ∫ omega, (R omega)⁻¹ ∂mu := by
  let f : Omega → ℝ := fun omega => Real.sqrt (R omega)
  let g : Omega → ℝ := fun omega => Real.sqrt (R omega)⁻¹
  have hfm : AEStronglyMeasurable f mu :=
    (Real.continuous_sqrt.measurable.comp hRm).aestronglyMeasurable
  have hgm : AEStronglyMeasurable g mu :=
    (Real.continuous_sqrt.measurable.comp hRm.inv).aestronglyMeasurable
  have hf2 : MemLp f 2 mu := by
    apply (memLp_two_iff_integrable_sq hfm).2
    apply hRint.congr
    filter_upwards with omega
    exact (Real.sq_sqrt (hRpos omega).le).symm
  have hg2 : MemLp g 2 mu := by
    apply (memLp_two_iff_integrable_sq hgm).2
    apply hRinvInt.congr
    filter_upwards with omega
    exact (Real.sq_sqrt (inv_pos.mpr (hRpos omega)).le).symm
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (f := f) (g := g)
    Real.HolderConjugate.two_two
    (ae_of_all mu fun omega => Real.sqrt_nonneg (R omega))
    (ae_of_all mu fun omega => show 0 ≤ g omega by
      dsimp only [g]
      exact Real.sqrt_nonneg (R omega)⁻¹)
    (by simpa using hf2) (by simpa using hg2)
  have hprod : (∫ omega, f omega * g omega ∂mu) = 1 := by
    calc
      (∫ omega, f omega * g omega ∂mu) = ∫ _omega, (1 : ℝ) ∂mu := by
        apply integral_congr_ae
        filter_upwards with omega
        dsimp only [f, g]
        rw [← Real.sqrt_mul (hRpos omega).le, mul_inv_cancel₀ (hRpos omega).ne',
          Real.sqrt_one]
      _ = 1 := by simp
  have hfsq : (∫ omega, f omega ^ (2 : ℝ) ∂mu) = ∫ omega, R omega ∂mu := by
    apply integral_congr_ae
    filter_upwards with omega
    dsimp only [f]
    rw [Real.rpow_two, Real.sq_sqrt (hRpos omega).le]
  have hgsq : (∫ omega, g omega ^ (2 : ℝ) ∂mu) =
      ∫ omega, (R omega)⁻¹ ∂mu := by
    apply integral_congr_ae
    filter_upwards with omega
    dsimp only [g]
    rw [Real.rpow_two, Real.sq_sqrt (inv_pos.mpr (hRpos omega)).le]
  rw [hprod, hfsq, hgsq] at hcs
  have hroot (x : ℝ) : x ^ (1 / 2 : ℝ) = Real.sqrt x := by
    rw [← Real.sqrt_eq_rpow]
  rw [hroot, hroot] at hcs
  let A := ∫ omega, R omega ∂mu
  let B := ∫ omega, (R omega)⁻¹ ∂mu
  have hA0 : 0 ≤ A := integral_nonneg fun omega => (hRpos omega).le
  have hB0 : 0 ≤ B := integral_nonneg fun omega => (inv_pos.mpr (hRpos omega)).le
  have hAB : 1 ≤ A * B := by
    have hsquare := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1)
      (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))).2 hcs
    rw [one_pow, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0] at hsquare
    exact hsquare
  have hApos : 0 < A := by
    by_contra hA
    have : A = 0 := le_antisymm (le_of_not_gt hA) hA0
    rw [this, zero_mul] at hAB
    norm_num at hAB
  change A⁻¹ ≤ B
  exact (inv_le_iff_one_le_mul₀' hApos).2 hAB

private theorem mul_blockEnergyAverage_zeroFluxProjection_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) (r : ℝ)
    (hcoeff : ∀ x ∈ (U : Set (Vec d)),
      r * _root_.SubdiffusiveProcess.Model.aCutoff M n omega x ≤
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x)
    {p : Vec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible (U : Set (Vec d)) (-p, 0) X) :
    r * blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
        (zeroFluxProjection X) ≤
      blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))
        (zeroFluxProjection X) := by
  have hY := zeroFluxProjection_admissible hX
  have hnInt := integrableOn_blockEnergyDensity_cutoff M n omega U hY
  have hmInt := integrableOn_blockEnergyDensity_cutoff M m omega U hY
  unfold blockEnergyAverage volumeAverage
  rw [show r * ((volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x in (U : Set (Vec d)), blockEnergyDensity
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
          (zeroFluxProjection X) x) =
      (volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x in (U : Set (Vec d)), r * blockEnergyDensity
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
            (zeroFluxProjection X) x by
    rw [integral_const_mul]
    ring]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply integral_mono_ae (hnInt.const_mul r) hmInt
  filter_upwards [ae_restrict_mem U.measurableSet] with x hx
  rw [blockEnergyDensity_scalarCoeffField_of_pos _
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega),
    blockEnergyDensity_scalarCoeffField_of_pos _
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega)]
  dsimp only [zeroFluxProjection]
  simp only [Pi.zero_apply, vecDot, mul_zero, Finset.sum_const_zero, add_zero]
  have hsq : 0 ≤ ∑ i, X.potential x i * X.potential x i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  nlinarith [hcoeff x hx]

private theorem mul_blockEnergyAverage_zeroPotentialProjection_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n m : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (U : Ch02.Domain d) (r : ℝ)
    (hcoeffInv : ∀ x ∈ (U : Set (Vec d)),
      r * (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x)⁻¹ ≤
        (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x)⁻¹)
    {q : Vec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible (U : Set (Vec d)) (0, q) X) :
    r * blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
        (zeroPotentialProjection X) ≤
      blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))
        (zeroPotentialProjection X) := by
  have hY := zeroPotentialProjection_admissible hX
  have hnInt := integrableOn_blockEnergyDensity_cutoff M n omega U hY
  have hmInt := integrableOn_blockEnergyDensity_cutoff M m omega U hY
  unfold blockEnergyAverage volumeAverage
  rw [show r * ((volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x in (U : Set (Vec d)), blockEnergyDensity
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
          (zeroPotentialProjection X) x) =
      (volume (U : Set (Vec d))).toReal⁻¹ *
        ∫ x in (U : Set (Vec d)), r * blockEnergyDensity
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
            (zeroPotentialProjection X) x by
    rw [integral_const_mul]
    ring]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply integral_mono_ae (hnInt.const_mul r) hmInt
  filter_upwards [ae_restrict_mem U.measurableSet] with x hx
  rw [blockEnergyDensity_scalarCoeffField_of_pos _
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega),
    blockEnergyDensity_scalarCoeffField_of_pos _
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega)]
  dsimp only [zeroPotentialProjection]
  simp only [Pi.zero_apply, vecDot, mul_zero, Finset.sum_const_zero, zero_add]
  have hsq : 0 ≤ ∑ i, X.flux x i * X.flux x i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  nlinarith [hcoeffInv x hx]

/-- Pathwise primal variational comparison using the reciprocal of the
lower-to-higher ratio supremum. -/
theorem inv_cutoffRatioSup_mul_cutoffMu_primal_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n m : ℕ)
    (U : Ch02.Domain d) (p : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (cutoffRatioSup M n m U omega)⁻¹ *
        Mu (U : Set (Vec d)) (-p, 0)
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) ≤
      Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega)) := by
  let R := cutoffRatioSup M n m U omega
  have hRpos : 0 < R := cutoffRatioSup_pos M n m U omega
  have hr : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  apply le_Mu_of_forall_isBlockMuAdmissible
  intro X hX
  have hY := zeroFluxProjection_admissible hX
  have hbdd : BddBelow (muValueSet (U : Set (Vec d)) (-p, 0)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))) := by
    refine ⟨0, ?_⟩
    rintro value ⟨Z, hZ, rfl⟩
    exact blockEnergyAverage_cutoff_nonneg M n omega U hZ
  have hMuY : Mu (U : Set (Vec d)) (-p, 0)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) ≤
      blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
          (zeroFluxProjection X) :=
    csInf_le hbdd (muValueSet_mem hY)
  have hcoeff : ∀ x ∈ (U : Set (Vec d)),
      R⁻¹ * _root_.SubdiffusiveProcess.Model.aCutoff M n omega x ≤
        _root_.SubdiffusiveProcess.Model.aCutoff M m omega x := by
    intro x hx
    have hpoint := cutoffRatio_le_cutoffRatioSup M n m U omega hx
    have hpointPos := div_pos
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x)
    have hinv : R⁻¹ ≤
        (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M m omega x)⁻¹ :=
      (inv_le_inv₀ hRpos hpointPos).2 hpoint
    rw [inv_div] at hinv
    exact (le_div_iff₀ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x)).1 hinv
  calc
    R⁻¹ * Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) ≤
        R⁻¹ * blockEnergyAverage (U : Set (Vec d))
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
            (zeroFluxProjection X) := mul_le_mul_of_nonneg_left hMuY hr
    _ ≤ blockEnergyAverage (U : Set (Vec d))
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))
            (zeroFluxProjection X) :=
      mul_blockEnergyAverage_zeroFluxProjection_le M n m omega U R⁻¹ hcoeff hX
    _ ≤ blockEnergyAverage (U : Set (Vec d))
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega)) X :=
      blockEnergyAverage_zeroFluxProjection_le M m omega U hX

/-- Pathwise dual variational comparison using the reciprocal of the
higher-to-lower ratio supremum. -/
theorem inv_cutoffRatioSup_mul_cutoffMu_dual_le {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n m : ℕ)
    (U : Ch02.Domain d) (q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    (cutoffRatioSup M m n U omega)⁻¹ *
        Mu (U : Set (Vec d)) (0, q)
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) ≤
      Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega)) := by
  let R := cutoffRatioSup M m n U omega
  have hRpos : 0 < R := cutoffRatioSup_pos M m n U omega
  have hr : 0 ≤ R⁻¹ := (inv_pos.mpr hRpos).le
  apply le_Mu_of_forall_isBlockMuAdmissible
  intro X hX
  have hY := zeroPotentialProjection_admissible hX
  have hbdd : BddBelow (muValueSet (U : Set (Vec d)) (0, q)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))) := by
    refine ⟨0, ?_⟩
    rintro value ⟨Z, hZ, rfl⟩
    exact blockEnergyAverage_cutoff_nonneg M n omega U hZ
  have hMuY : Mu (U : Set (Vec d)) (0, q)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) ≤
      blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
          (zeroPotentialProjection X) :=
    csInf_le hbdd (muValueSet_mem hY)
  have hcoeffInv : ∀ x ∈ (U : Set (Vec d)),
      R⁻¹ * (_root_.SubdiffusiveProcess.Model.aCutoff M n omega x)⁻¹ ≤
        (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x)⁻¹ := by
    intro x hx
    have hpoint := cutoffRatio_le_cutoffRatioSup M m n U omega hx
    have hpointPos := div_pos
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M m omega x)
      (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x)
    have hinv : R⁻¹ ≤
        (_root_.SubdiffusiveProcess.Model.aCutoff M m omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega x)⁻¹ :=
      (inv_le_inv₀ hRpos hpointPos).2 hpoint
    rw [inv_div] at hinv
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x)).2
    simpa only [div_eq_mul_inv, mul_comm] using hinv
  calc
    R⁻¹ * Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) ≤
        R⁻¹ * blockEnergyAverage (U : Set (Vec d))
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
            (zeroPotentialProjection X) := mul_le_mul_of_nonneg_left hMuY hr
    _ ≤ blockEnergyAverage (U : Set (Vec d))
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))
            (zeroPotentialProjection X) :=
      mul_blockEnergyAverage_zeroPotentialProjection_le M n m omega U R⁻¹ hcoeffInv hX
    _ ≤ blockEnergyAverage (U : Set (Vec d))
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega)) X :=
      blockEnergyAverage_zeroPotentialProjection_le M m omega U hX

private theorem cutoffMu_primal_eq_responseJ {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) =
      Ch02.responseJ U (aCutoffCoeffOnData M L omega U).toCoeffOn p 0 := by
  calc
    Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) =
        Ch02.doubledMu U (aCutoffCoeffOnData M L omega U).toCoeffOn (-p, 0) := by
      rw [Ch02.doubledMu_eq_Mu]
      rfl
    _ = Ch02.responseJ U (aCutoffCoeffOnData M L omega U).toCoeffOn p 0 := by
      rw [Ch02.responseJ_eq_doubledMu_neg_left_sub_vecDot]
      simp [vecDot]

private theorem cutoffMu_dual_eq_responseJ {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) =
      Ch02.responseJ U (aCutoffCoeffOnData M L omega U).toCoeffOn 0 q := by
  calc
    Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) =
        Ch02.doubledMu U (aCutoffCoeffOnData M L omega U).toCoeffOn (0, q) := by
      rw [Ch02.doubledMu_eq_Mu]
      rfl
    _ = Ch02.responseJ U (aCutoffCoeffOnData M L omega U).toCoeffOn 0 q := by
      rw [Ch02.responseJ_eq_doubledMu_neg_left_sub_vecDot]
      simp [vecDot]

private theorem measurable_cutoffMu_primal_potentialShellIndexSigma_Iic {d : ℕ}
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (U : Ch02.Domain d) (p : Vec d) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Iic n)) inferInstance
      (fun omega => Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))) := by
  convert measurable_cutoff_responseJ_potentialShellIndexSigma_Iic M n U p 0 using 1
  funext omega
  exact cutoffMu_primal_eq_responseJ M n U p omega

private theorem measurable_cutoffMu_dual_potentialShellIndexSigma_Iic {d : ℕ}
    [NeZero d] (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (U : Ch02.Domain d) (q : Vec d) :
    @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ (potentialShellIndexSigma (Set.Iic n)) inferInstance
      (fun omega => Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))) := by
  convert measurable_cutoff_responseJ_potentialShellIndexSigma_Iic M n U 0 q using 1
  funext omega
  exact cutoffMu_dual_eq_responseJ M n U q omega

private theorem integral_cutoffMu_primal {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p : Vec d) :
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))
        ∂M.P.toMeasure) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (abar M L U) p) := by
  calc
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))
        ∂M.P.toMeasure) =
        ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (1 / 2 : ℝ) * vecDot p
          (matVecMul (randomAMatrix M L U omega) p) ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact cutoffMu_primal_eq_randomAMatrix_quadratic M L U p omega
    _ = _ := integral_randomAMatrix_quadratic M L U p

private theorem integral_cutoffMu_dual {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (q : Vec d) :
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))
        ∂M.P.toMeasure) =
      (1 / 2 : ℝ) * vecDot q (matVecMul (abarStarInv M L U) q) := by
  calc
    (∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))
        ∂M.P.toMeasure) =
        ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d, (1 / 2 : ℝ) * vecDot q
          (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q) ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      exact cutoffMu_dual_eq_randomAStarInv_quadratic M L U q omega
    _ = _ := integral_randomAStarMatrix_inv_quadratic M L U q

private theorem integral_pos_cutoffRatioSup {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (numerator denominator : ℕ)
    (U : Ch02.Domain d)
    (hInt : Integrable (cutoffRatioSup M numerator denominator U) M.P.toMeasure) :
    0 < ∫ omega, cutoffRatioSup M numerator denominator U omega ∂M.P.toMeasure := by
  rw [integral_pos_iff_support_of_nonneg
    (fun omega => (cutoffRatioSup_pos M numerator denominator U omega).le) hInt]
  have hsupp : Function.support (cutoffRatioSup M numerator denominator U) = Set.univ := by
    ext omega
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (cutoffRatioSup_pos M numerator denominator U omega).ne'
  rw [hsupp]
  simp

/-- Reverse primal annealed ordering, with the pointwise-sup convention fixed
by R35.  This is clause (2) of the Section 3 anchor. -/
theorem matLoewnerLE_abar_cutoff_reverse {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (U : Ch02.Domain d)
    {n m : ℕ} (hnm : n < m) :
    MatLoewnerLE (abar M n U)
      ((∫ omega, cutoffRatioSup M n m U omega ∂M.P.toMeasure) • abar M m U) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  intro p
  let fn : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (-p, 0)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
  let fm : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (-p, 0)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := cutoffRatioSup M n m U
  let r : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => (R omega)⁻¹
  have hratioMeas := measurable_cutoffRatioSup_potentialShellIndexSigma_Ioi M hnm U
  have hfnMeas := measurable_cutoffMu_primal_potentialShellIndexSigma_Iic M n U p
  have hrMeas : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance r := hratioMeas.2.inv
  have hIndep : IndepFun fn r M.P.toMeasure :=
    indepFun_of_measurable_potentialShellIndexSigma_of_disjoint M
      (by exact Set.disjoint_left.mpr fun _ hx hy =>
        (not_lt_of_ge (Set.mem_Iic.mp hx)) (Set.mem_Ioi.mp hy)) hfnMeas hrMeas
  have hfnInt : Integrable fn M.P.toMeasure := integrable_cutoffMu_primal M n U p
  have hfmInt : Integrable fm M.P.toMeasure := integrable_cutoffMu_primal M m U p
  have hRInt : Integrable R M.P.toMeasure := integrable_cutoffRatioSup_inverse M hnm U
  have hrInt : Integrable r M.P.toMeasure := integrable_inv_cutoffRatioSup_inverse M hnm U
  have hprodInt : Integrable (fn * r) M.P.toMeasure := hIndep.integrable_mul hfnInt hrInt
  have hpath : fn * r ≤ᵐ[M.P.toMeasure] fm := by
    filter_upwards with omega
    simpa only [fn, fm, r, R, Pi.mul_apply, mul_comm] using
      inv_cutoffRatioSup_mul_cutoffMu_primal_le M n m U p omega
  have hleRaw := integral_mono_ae hprodInt hfmInt hpath
  have hfactor := hIndep.integral_fun_mul_eq_mul_integral
    hfnInt.aestronglyMeasurable hrInt.aestronglyMeasurable
  have hle : (∫ omega, fn omega ∂M.P.toMeasure) *
      (∫ omega, r omega ∂M.P.toMeasure) ≤
      ∫ omega, fm omega ∂M.P.toMeasure := by
    rw [← hfactor]
    simpa only [Pi.mul_apply] using hleRaw
  have hJensen : (∫ omega, R omega ∂M.P.toMeasure)⁻¹ ≤
      ∫ omega, r omega ∂M.P.toMeasure :=
    inv_integral_le_integral_inv M.P.toMeasure
      (measurable_cutoffRatioSup M n m U) (cutoffRatioSup_pos M n m U)
      hRInt hrInt
  have hfn0 : 0 ≤ ∫ omega, fn omega ∂M.P.toMeasure :=
    integral_nonneg fun omega => cutoffMu_nonneg M n omega U (-p, 0)
  have hbase : (∫ omega, fn omega ∂M.P.toMeasure) *
      (∫ omega, R omega ∂M.P.toMeasure)⁻¹ ≤
      ∫ omega, fm omega ∂M.P.toMeasure :=
    (mul_le_mul_of_nonneg_left hJensen hfn0).trans hle
  have hERpos : 0 < ∫ omega, R omega ∂M.P.toMeasure :=
    integral_pos_cutoffRatioSup M n m U hRInt
  have hscaled := mul_le_mul_of_nonneg_left hbase hERpos.le
  have hfinal : (∫ omega, fn omega ∂M.P.toMeasure) ≤
      (∫ omega, R omega ∂M.P.toMeasure) *
        ∫ omega, fm omega ∂M.P.toMeasure := by
    calc
      (∫ omega, fn omega ∂M.P.toMeasure) =
          (∫ omega, R omega ∂M.P.toMeasure) *
            ((∫ omega, fn omega ∂M.P.toMeasure) *
              (∫ omega, R omega ∂M.P.toMeasure)⁻¹) := by
        field_simp
      _ ≤ _ := hscaled
  rw [integral_cutoffMu_primal M n U p, integral_cutoffMu_primal M m U p] at hfinal
  have hquad : vecDot p (matVecMul (abar M n U) p) ≤
      (∫ omega, R omega ∂M.P.toMeasure) *
        vecDot p (matVecMul (abar M m U) p) := by
    nlinarith
  simpa only [R, smul_matVecMul, vecDot_smul_right] using
    (mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 1 / 2))

/-- Reverse dual annealed ordering.  This is clause (4) of the
Section 3 anchor. -/
theorem matLoewnerLE_abarStarInv_cutoff_reverse {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (U : Ch02.Domain d)
    {n m : ℕ} (hnm : n < m) :
    MatLoewnerLE (abarStarInv M n U)
      ((∫ omega, cutoffRatioSup M m n U omega ∂M.P.toMeasure) •
        abarStarInv M m U) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  intro q
  let fn : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (0, q)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
  let fm : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (0, q)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := cutoffRatioSup M m n U
  let r : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega => (R omega)⁻¹
  have hratioMeas := measurable_cutoffRatioSup_potentialShellIndexSigma_Ioi M hnm U
  have hfnMeas := measurable_cutoffMu_dual_potentialShellIndexSigma_Iic M n U q
  have hrMeas : @Measurable (_root_.SubdiffusiveProcess.Model.PotentialSample d) ℝ
      (potentialShellIndexSigma (Set.Ioi n)) inferInstance r := hratioMeas.1.inv
  have hIndep : IndepFun fn r M.P.toMeasure :=
    indepFun_of_measurable_potentialShellIndexSigma_of_disjoint M
      (by exact Set.disjoint_left.mpr fun _ hx hy =>
        (not_lt_of_ge (Set.mem_Iic.mp hx)) (Set.mem_Ioi.mp hy)) hfnMeas hrMeas
  have hfnInt : Integrable fn M.P.toMeasure := integrable_cutoffMu_dual M n U q
  have hfmInt : Integrable fm M.P.toMeasure := integrable_cutoffMu_dual M m U q
  have hRInt : Integrable R M.P.toMeasure := integrable_cutoffRatioSup_forward M hnm U
  have hrInt : Integrable r M.P.toMeasure := integrable_inv_cutoffRatioSup_forward M hnm U
  have hprodInt : Integrable (fn * r) M.P.toMeasure := hIndep.integrable_mul hfnInt hrInt
  have hpath : fn * r ≤ᵐ[M.P.toMeasure] fm := by
    filter_upwards with omega
    simpa only [fn, fm, r, R, Pi.mul_apply, mul_comm] using
      inv_cutoffRatioSup_mul_cutoffMu_dual_le M n m U q omega
  have hleRaw := integral_mono_ae hprodInt hfmInt hpath
  have hfactor := hIndep.integral_fun_mul_eq_mul_integral
    hfnInt.aestronglyMeasurable hrInt.aestronglyMeasurable
  have hle : (∫ omega, fn omega ∂M.P.toMeasure) *
      (∫ omega, r omega ∂M.P.toMeasure) ≤
      ∫ omega, fm omega ∂M.P.toMeasure := by
    rw [← hfactor]
    simpa only [Pi.mul_apply] using hleRaw
  have hJensen : (∫ omega, R omega ∂M.P.toMeasure)⁻¹ ≤
      ∫ omega, r omega ∂M.P.toMeasure :=
    inv_integral_le_integral_inv M.P.toMeasure
      (measurable_cutoffRatioSup M m n U) (cutoffRatioSup_pos M m n U)
      hRInt hrInt
  have hfn0 : 0 ≤ ∫ omega, fn omega ∂M.P.toMeasure :=
    integral_nonneg fun omega => cutoffMu_nonneg M n omega U (0, q)
  have hbase : (∫ omega, fn omega ∂M.P.toMeasure) *
      (∫ omega, R omega ∂M.P.toMeasure)⁻¹ ≤
      ∫ omega, fm omega ∂M.P.toMeasure :=
    (mul_le_mul_of_nonneg_left hJensen hfn0).trans hle
  have hERpos : 0 < ∫ omega, R omega ∂M.P.toMeasure :=
    integral_pos_cutoffRatioSup M m n U hRInt
  have hscaled := mul_le_mul_of_nonneg_left hbase hERpos.le
  have hfinal : (∫ omega, fn omega ∂M.P.toMeasure) ≤
      (∫ omega, R omega ∂M.P.toMeasure) *
        ∫ omega, fm omega ∂M.P.toMeasure := by
    calc
      (∫ omega, fn omega ∂M.P.toMeasure) =
          (∫ omega, R omega ∂M.P.toMeasure) *
            ((∫ omega, fn omega ∂M.P.toMeasure) *
              (∫ omega, R omega ∂M.P.toMeasure)⁻¹) := by
        field_simp
      _ ≤ _ := hscaled
  rw [integral_cutoffMu_dual M n U q, integral_cutoffMu_dual M m U q] at hfinal
  have hquad : vecDot q (matVecMul (abarStarInv M n U) q) ≤
      (∫ omega, R omega ∂M.P.toMeasure) *
        vecDot q (matVecMul (abarStarInv M m U) q) := by
    nlinarith
  simpa only [R, smul_matVecMul, vecDot_smul_right] using
    (mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 1 / 2))

end

end SubdiffusiveProcess.CoarseGrainingVocab
