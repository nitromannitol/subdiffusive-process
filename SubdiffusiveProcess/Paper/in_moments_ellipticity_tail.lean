module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_moments_family_transport
public import SubdiffusiveProcess.Paper.in_moments_response_moment
public import SubdiffusiveProcess.Section4.MultiscaleResponseLargeCubes
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.BadEventEstimates
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepEllipticityFactorMoment
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import Homogenization.Book.Ch04.Theorems.DilationLaw
public import Homogenization.Book.Ch02.Theorems.SubadditivityScaling
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Book.Ch02.Matrices
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_in_moments_ellipticity_tail_field_law
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) :
    ProbabilityTheory.IdentDistrib
      (fun omega : BilateralField d =>
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) •
          aux_annealed_limit_response_transport_scalarRegCoeffField
            (aux_in_moments_response_moment_cutoffField model N omega))
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
      (chaosSampleLaw model).toMeasure model.P.toMeasure := by
  let alpha : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
  let s : ℝ := alpha⁻¹
  let r : ℝ := s * Real.exp (-(N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)
  let c : ℝ := s⁻¹
  have halpha : 0 < alpha := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N
  have hs : 0 < s := inv_pos.mpr halpha
  have hc : 0 < c := inv_pos.mpr hs
  have hcs : c * s = 1 := by
    dsimp [c, s]
    field_simp
  have hcr : c * r = Real.exp (-(N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) := by
    dsimp [r]
    rw [show c * (s * Real.exp (-(N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) =
      (c * s) * Real.exp (-(N : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) by ring]
    rw [hcs, one_mul]
  let fA : BilateralField d → C(SpatialCoordinates d, ℝ) := fun omega =>
    ⟨fun x =>
      (Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) * alpha)⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x), by
      apply continuous_const.mul
      apply Real.continuous_exp.comp
      apply continuous_finsetSum
      intro j hj
      exact (omega (-(j : ℤ))).continuous⟩
  let g0 : BilateralField d → C(SpatialCoordinates d, ℝ) := fun omega =>
    ⟨fun x => s * Real.exp (∑ j ∈ Finset.range (N + 1),
      ((omega (j : ℤ)) ((3 : ℝ) ^ N • x) -
        _root_.SubdiffusiveProcess.Model.tauSq model.P)), by
      apply continuous_const.mul
      apply Real.continuous_exp.comp
      exact continuous_finsetSum (Finset.range (N + 1)) (by
        intro j hj
        exact ((omega (j : ℤ)).continuous.comp
          (by fun_prop)).sub continuous_const)⟩
  have hnorm : ProbabilityTheory.IdentDistrib fA g0
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
    have h := aux_annealed_limit_response_transport_normalized_field_law
      (model := model) N
    simpa [fA, g0, alpha, s] using h
  let gsource : _root_.SubdiffusiveProcess.Model.PotentialSample d →
      C(SpatialCoordinates d, ℝ) := fun omega =>
    ⟨fun x => r * Real.exp ((∑ j ∈ Finset.range (N + 1),
      ((omega (j : ℕ)).1.1) ((3 : ℝ) ^ N • x)) -
        _root_.SubdiffusiveProcess.Model.tauSq model.P), by
      apply continuous_const.mul
      apply Real.continuous_exp.comp
      exact (continuous_finsetSum (Finset.range (N + 1)) (by
        intro j hj
        exact ((omega (j : ℕ)).1.1).continuous.comp
          (by fun_prop))).sub continuous_const⟩
  let dilate : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => (3 : ℝ) ^ N • x, by fun_prop⟩
  let compD : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) :=
    ContinuousMap.compRightContinuousMap ℝ dilate
  let T : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) :=
    fun f => r • compD f
  have hTmeas : Measurable T :=
    by
      apply Continuous.measurable
      dsimp only [T]
      fun_prop
  have hpos := aux_annealed_limit_response_transport_positive_field_law
    (model := model) N
  have htrans := hpos.comp hTmeas
  have hsourceT : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      T (⟨fun x => Real.exp ((∑ i : Fin (N + 1),
        (((omega (i : ℕ)).1.1) x)) - _root_.SubdiffusiveProcess.Model.tauSq model.P), by
        continuity⟩ : C(SpatialCoordinates d, ℝ))) = gsource := by
    funext omega
    ext x
    dsimp [T, compD, dilate, gsource]
    change r * Real.exp ((∑ i : Fin (N + 1),
      ((omega (i : ℕ)).1.1) ((3 : ℝ) ^ N • x)) -
        _root_.SubdiffusiveProcess.Model.tauSq model.P) = _
    congr 2
    rw [Finset.sum_fin_eq_sum_range]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [dite_eq_left (Finset.mem_range.mp hj)]
  have htargetT : (fun omega : BilateralField d =>
      T (⟨fun x => Real.exp ((∑ i : Fin (N + 1),
        ((omega (i : ℤ)) x)) - _root_.SubdiffusiveProcess.Model.tauSq model.P), by
          apply Real.continuous_exp.comp
          exact (continuous_finsetSum Finset.univ (by
            intro i hi
            exact (omega (i : ℤ)).continuous)).sub continuous_const⟩ :
        C(SpatialCoordinates d, ℝ))) = g0 := by
    funext omega
    ext x
    dsimp [T, compD, dilate, g0]
    change r * Real.exp ((∑ i : Fin (N + 1),
      (omega (i : ℤ)) ((3 : ℝ) ^ N • x)) -
        _root_.SubdiffusiveProcess.Model.tauSq model.P) = _
    have hsum : (∑ i : Fin (N + 1),
        (omega (i : ℤ)) ((3 : ℝ) ^ N • x)) =
        ∑ i ∈ Finset.range (N + 1),
          (omega (i : ℤ)) ((3 : ℝ) ^ N • x) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      rw [dite_eq_left (Finset.mem_range.mp hi)]
    rw [hsum, Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [show r = s * Real.exp (-(N : ℝ) *
        _root_.SubdiffusiveProcess.Model.tauSq model.P) by rfl]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have htrans' : ProbabilityTheory.IdentDistrib
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        T (⟨fun x => Real.exp ((∑ i : Fin (N + 1),
          (((omega (i : ℕ)).1.1) x)) - _root_.SubdiffusiveProcess.Model.tauSq model.P), by
            apply Real.continuous_exp.comp
            exact (continuous_finsetSum Finset.univ (by
              intro i hi
              exact (omega (i : ℕ)).1.1.continuous)).sub continuous_const⟩ :
          C(SpatialCoordinates d, ℝ)))
      (fun omega : BilateralField d =>
        T (⟨fun x => Real.exp ((∑ i : Fin (N + 1),
          ((omega (i : ℤ)) x)) - _root_.SubdiffusiveProcess.Model.tauSq model.P), by
            apply Real.continuous_exp.comp
            exact (continuous_finsetSum Finset.univ (by
              intro i hi
              exact (omega (i : ℤ)).continuous)).sub continuous_const⟩ :
          C(SpatialCoordinates d, ℝ)))
      model.P.toMeasure (chaosSampleLaw model).toMeasure := by
    simpa [Function.comp_def] using htrans
  rw [hsourceT, htargetT] at htrans'
  have hnormP : ProbabilityTheory.IdentDistrib fA gsource
      (chaosSampleLaw model).toMeasure model.P.toMeasure :=
    hnorm.trans htrans'.symm
  have hscalar := hnorm.comp
    aux_annealed_limit_response_transport_measurable_scalarRegCoeffField
  have hscale : Measurable (fun z : Homogenization.RegCoeffField d => c • z) := by
    apply Homogenization.measurable_of_entryTestR_transport
    · intro y i j
      simp only [Homogenization.RegCoeffField.smul_toFun]
      exact measurable_const.mul (Homogenization.measurable_apply_entry y i j)
    · intro i j φ hφ
      exact ⟨c, i, j, φ, hφ,
        fun z => Homogenization.entryTestR_smul i j c z⟩
  have hscalarP := hnormP.comp
    aux_annealed_limit_response_transport_measurable_scalarRegCoeffField
  have hscaled := hscalarP.comp hscale
  have hsource : ∀ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      c • aux_annealed_limit_response_transport_scalarRegCoeffField (gsource omega) =
        Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega) := by
    intro omega
    apply Homogenization.RegCoeffField.ext
    intro x
    rw [Homogenization.RegCoeffField.smul_toFun]
    dsimp [gsource]
    change c • Homogenization.scalarMatrix
        (r * Real.exp ((∑ j ∈ Finset.range (N + 1),
          ((omega (j : ℕ)).1.1) ((3 : ℝ) ^ N • x)) -
            _root_.SubdiffusiveProcess.Model.tauSq model.P)) = _
    have hsum : (∑ i : Fin (N + 1), ((omega (i : ℕ)).1.1) ((3 : ℝ) ^ N • x)) =
        ∑ j ∈ Finset.range (N + 1),
          ((omega (j : ℕ)).1.1) ((3 : ℝ) ^ N • x) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      rw [dite_eq_left (Finset.mem_range.mp hj)]
    rw [← hsum]
    exact aux_annealed_limit_response_transport_source_matrix model N omega
      ((3 : ℝ) ^ N • x) c r (_root_.SubdiffusiveProcess.Model.tauSq model.P) hcr rfl
  have hfield : ProbabilityTheory.IdentDistrib
      (fun omega : BilateralField d =>
        c • aux_annealed_limit_response_transport_scalarRegCoeffField (fA omega))
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
      (chaosSampleLaw model).toMeasure model.P.toMeasure := by
    have hright : (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        c • aux_annealed_limit_response_transport_scalarRegCoeffField (gsource omega)) =
        (fun omega => Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega)) := by
      funext omega
      exact hsource omega
    simpa [Function.comp_def, hright] using hscaled
  have hstat := stationary_family d hd model
  dsimp at hstat
  have hfAcut : fA = aux_in_moments_response_moment_cutoffField model N := by
    funext omega
    ext x
    simpa [fA, aux_in_moments_response_moment_cutoffField, alpha,
      SubdiffusiveProcess.cutoffCoefficient,
      SubdiffusiveProcess.cutoffPotential] using (hstat.1 N omega x).symm
  rw [hfAcut] at hfield
  simpa [c, s, alpha] using hfield

theorem aux_in_moments_ellipticity_tail_coarse_smul
    {d : ℕ} [NeZero d]
    (U : Homogenization.Book.Ch02.Domain d)
    (a b : Homogenization.Book.Ch02.CoeffOn U) (c : ℝ) (hc : 0 < c)
    (hscaled : Homogenization.Book.Ch02.CoeffOn.AEScaled c a b) :
    Homogenization.Book.Ch02.sigmaStarInvCoarse U b =
        c⁻¹ • Homogenization.Book.Ch02.sigmaStarInvCoarse U a ∧
      Homogenization.Book.Ch02.bCoarse U b =
        c • Homogenization.Book.Ch02.bCoarse U a := by
  let H := Homogenization.Book.Ch02.responseSubadditivityAndScalingTheory U a
  have hσ : Homogenization.Book.Ch02.sigmaCoarse U b =
      c • Homogenization.Book.Ch02.sigmaCoarse U a :=
    H.sigma_homogeneous hc hscaled
  have hσstar : Homogenization.Book.Ch02.sigmaStarCoarse U b =
      c • Homogenization.Book.Ch02.sigmaStarCoarse U a :=
    H.sigmaStar_homogeneous hc hscaled
  have hκ : Homogenization.Book.Ch02.kappaCoarse U b =
      c • Homogenization.Book.Ch02.kappaCoarse U a :=
    H.kappa_homogeneous hc hscaled
  have hdetA : IsUnit
      (Homogenization.Book.Ch02.sigmaStarInvCoarse U a).det :=
    Homogenization.Book.Ch02.isUnit_det_sigmaStarInvCoarse U a
  have hdetB : IsUnit
      (Homogenization.Book.Ch02.sigmaStarInvCoarse U b).det :=
    Homogenization.Book.Ch02.isUnit_det_sigmaStarInvCoarse U b
  have hinvA : (Homogenization.Book.Ch02.sigmaStarInvCoarse U a)⁻¹ =
      Homogenization.Book.Ch02.sigmaStarCoarse U a := by
    rfl
  have hinvB : (Homogenization.Book.Ch02.sigmaStarInvCoarse U b)⁻¹ =
      Homogenization.Book.Ch02.sigmaStarCoarse U b := by
    rfl
  have hstarInv : Homogenization.Book.Ch02.sigmaStarInvCoarse U b =
      c⁻¹ • Homogenization.Book.Ch02.sigmaStarInvCoarse U a := by
    have h := congrArg (fun M : Homogenization.Mat d => M⁻¹) hσstar
    change (Homogenization.Book.Ch02.sigmaStarInvCoarse U b)⁻¹⁻¹ =
      (c • (Homogenization.Book.Ch02.sigmaStarInvCoarse U a)⁻¹)⁻¹ at h
    have hdetInvA : IsUnit
        ((Homogenization.Book.Ch02.sigmaStarInvCoarse U a)⁻¹).det :=
      Matrix.isUnit_nonsing_inv_det _ hdetA
    rw [nonsing_inv_smul c hc.ne' hdetInvA] at h
    rw [Matrix.nonsing_inv_nonsing_inv _ hdetA,
      Matrix.nonsing_inv_nonsing_inv _ hdetB] at h
    exact h
  refine ⟨hstarInv, ?_⟩
  unfold Homogenization.Book.Ch02.bCoarse
  change
    (Homogenization.Book.Ch02.coarseMatrices U b).sigma +
        Matrix.transpose (Homogenization.Book.Ch02.coarseMatrices U b).kappa *
          (Homogenization.Book.Ch02.coarseMatrices U b).sigmaStarInv *
          (Homogenization.Book.Ch02.coarseMatrices U b).kappa =
      c • ((Homogenization.Book.Ch02.coarseMatrices U a).sigma +
        Matrix.transpose (Homogenization.Book.Ch02.coarseMatrices U a).kappa *
          (Homogenization.Book.Ch02.coarseMatrices U a).sigmaStarInv *
          (Homogenization.Book.Ch02.coarseMatrices U a).kappa)
  simp only [Homogenization.Book.Ch02.coarseMatrices_sigma,
    Homogenization.Book.Ch02.coarseMatrices_sigmaStarInv,
    Homogenization.Book.Ch02.coarseMatrices_kappa, hσ, hκ, hstarInv]
  have htranspose : Matrix.transpose (c •
      Homogenization.Book.Ch02.kappaCoarse U a) = c •
        Matrix.transpose (Homogenization.Book.Ch02.kappaCoarse U a) := by
    ext i j
    rfl
  rw [htranspose]
  ext i j
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp [hc.ne']

theorem aux_in_moments_ellipticity_tail_finsetSup_const_mul
    {α : Type*} (s : Finset α) (hs : s.Nonempty) (c : ℝ) (hc : 0 < c)
    (f : α → ℝ) :
    Homogenization.Book.Ch02.finsetSupReal s (fun x => c * f x) =
      c * Homogenization.Book.Ch02.finsetSupReal s f := by
  apply le_antisymm
  · exact Homogenization.Book.Ch02.finsetSupReal_const_mul_le s hs hc.le f
  · have h0 := Homogenization.Book.Ch02.finsetSupReal_const_mul_le s hs
        (inv_nonneg.mpr hc.le) (fun x => c * f x)
    have h1 := mul_le_mul_of_nonneg_left h0 hc.le
    simpa [hc.ne', mul_assoc] using h1

theorem aux_in_moments_ellipticity_tail_matrixNorm_smul
    {d : ℕ} [NeZero d] (A : Homogenization.Mat d) (c : ℝ) (hc : 0 ≤ c) :
    Homogenization.Book.Ch02.matrixNorm (c • A) =
      c * Homogenization.Book.Ch02.matrixNorm A := by
  let L : Homogenization.Mat d →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := {
    toFun := fun M => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M
    map_add' := by
      intro M N
      exact map_add (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) M N
    map_smul' := by
      intro r M
      exact map_smul (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) r M }
  have _hL := map_smul L c A
  simp [Homogenization.Book.Ch02.matrixNorm, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hc]

theorem aux_in_moments_ellipticity_tail_family_smul
    {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (s : ℝ) (hs : 0 < s)
    (A B : Homogenization.Book.Ch02.TriadicCoeffFamily d) (c : ℝ) (hc : 0 < c)
    (hscaled : ∀ R : Homogenization.TriadicCube d,
      Homogenization.Book.Ch02.CoeffOn.AEScaled c (A.coeffOn R) (B.coeffOn R)) :
    Homogenization.Book.Ch02.LambdaSq Q s
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) B =
        c * Homogenization.Book.Ch02.LambdaSq Q s
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) A ∧
      Homogenization.Book.Ch02.lambdaSq Q s
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) B =
        c * Homogenization.Book.Ch02.lambdaSq Q s
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) A := by
  have hnorm : ∀ (R : Homogenization.TriadicCube d)
      (M : Homogenization.Mat d) (r : ℝ) (hr : 0 < r),
      Homogenization.Book.Ch02.matrixNorm (r • M) =
        r * Homogenization.Book.Ch02.matrixNorm M := by
    intro R M r hr
    exact aux_in_moments_ellipticity_tail_matrixNorm_smul M r hr.le
  have hupper : ∀ n : ℕ,
      Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) B =
        c * Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) A := by
    intro n
    let S := Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ))
    have hS : S.Nonempty := by
      apply Homogenization.descendantsAtScale_nonempty
      omega
    calc
      Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) B =
          Homogenization.Book.Ch02.finsetSupReal S
            (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R B) := by
              rfl
      _ = Homogenization.Book.Ch02.finsetSupReal S
            (fun R => c * Homogenization.Book.Ch02.coarseBMatrixNorm R A) := by
              apply Homogenization.Book.Ch02.finsetSupReal_congr
              intro R hR
              have hcoarse := aux_in_moments_ellipticity_tail_coarse_smul
                (Homogenization.Book.Ch02.cubeDomain R) (A.coeffOn R)
                (B.coeffOn R) c hc (hscaled R)
              unfold Homogenization.Book.Ch02.coarseBMatrixNorm
              rw [hcoarse.2]
              exact hnorm R _ c hc
      _ = c * Homogenization.Book.Ch02.finsetSupReal S
            (fun R => Homogenization.Book.Ch02.coarseBMatrixNorm R A) :=
              aux_in_moments_ellipticity_tail_finsetSup_const_mul S hS c hc _
      _ = c * Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) A := by rfl
  have hlower : ∀ n : ℕ,
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) B =
        c⁻¹ * Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) A := by
    intro n
    let S := Homogenization.descendantsAtScale Q (Q.scale - (n : ℤ))
    have hS : S.Nonempty := by
      apply Homogenization.descendantsAtScale_nonempty
      omega
    have hcInv : 0 < c⁻¹ := inv_pos.mpr hc
    calc
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) B =
          Homogenization.Book.Ch02.finsetSupReal S
            (fun R => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R B) := by
              rfl
      _ = Homogenization.Book.Ch02.finsetSupReal S
            (fun R => c⁻¹ * Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R A) := by
              apply Homogenization.Book.Ch02.finsetSupReal_congr
              intro R hR
              have hcoarse := aux_in_moments_ellipticity_tail_coarse_smul
                (Homogenization.Book.Ch02.cubeDomain R) (A.coeffOn R)
                (B.coeffOn R) c hc (hscaled R)
              unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
              rw [hcoarse.1]
              exact hnorm R _ c⁻¹ hcInv
      _ = c⁻¹ * Homogenization.Book.Ch02.finsetSupReal S
            (fun R => Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R A) :=
              aux_in_moments_ellipticity_tail_finsetSup_const_mul S hS c⁻¹ hcInv _
      _ = c⁻¹ * Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) A := by rfl
  have hsumUpper :
      (∑' n : ℕ,
        Homogenization.Book.Ch02.geometricWeight s 1 n *
          Real.rpow
            (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) B) (1 / 2 : ℝ)) =
        Real.rpow c (1 / 2 : ℝ) *
          (∑' n : ℕ,
            Homogenization.Book.Ch02.geometricWeight s 1 n *
              Real.rpow
                (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hnonneg := Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale_nonneg
      Q (show Q.scale - (n : ℤ) ≤ Q.scale by omega) A
    rw [hupper n]
    calc
      Homogenization.Book.Ch02.geometricWeight s 1 n *
          Real.rpow (c * Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) =
          Homogenization.Book.Ch02.geometricWeight s 1 n *
            (Real.rpow c (1 / 2 : ℝ) *
              Real.rpow (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) := by
            congr 1
            exact Real.mul_rpow hc.le hnonneg
      _ = Real.rpow c (1 / 2 : ℝ) *
          (Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) := by ring
  have hsumLower :
      (∑' n : ℕ,
        Homogenization.Book.Ch02.geometricWeight s 1 n *
          Real.rpow
            (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) B) (1 / 2 : ℝ)) =
        Real.rpow c⁻¹ (1 / 2 : ℝ) *
          (∑' n : ℕ,
            Homogenization.Book.Ch02.geometricWeight s 1 n *
              Real.rpow
                (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have hnonneg := Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg
      Q (show Q.scale - (n : ℤ) ≤ Q.scale by omega) A
    rw [hlower n]
    calc
      Homogenization.Book.Ch02.geometricWeight s 1 n *
          Real.rpow (c⁻¹ * Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) =
          Homogenization.Book.Ch02.geometricWeight s 1 n *
            (Real.rpow c⁻¹ (1 / 2 : ℝ) *
              Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) := by
            congr 1
            exact Real.mul_rpow (inv_nonneg.mpr hc.le) hnonneg
      _ = Real.rpow c⁻¹ (1 / 2 : ℝ) *
          (Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) := by ring
  have hupperSq :
      Homogenization.Book.Ch02.LambdaSq Q s
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) B =
        c * Homogenization.Book.Ch02.LambdaSq Q s
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) A := by
    rw [Homogenization.Book.Ch02.LambdaSq_finite,
      Homogenization.Book.Ch02.LambdaSq_finite]
    dsimp [Homogenization.Book.Ch02.LambdaSqFinite]
    change Real.rpow
      (∑' n : ℕ,
        Homogenization.Book.Ch02.geometricWeight s 1 n *
          Real.rpow
            (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) B) (1 / 2 : ℝ)) (2 / 1 : ℝ) =
      c * Real.rpow
        (∑' n : ℕ,
          Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) (2 / 1 : ℝ)
    rw [hsumUpper]
    rw [show (2 / 1 : ℝ) = 2 by norm_num]
    change (Real.rpow c (1 / 2 : ℝ) *
        (∑' n : ℕ,
          Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ))) ^ (2 : ℝ) =
      c *
        (∑' n : ℕ,
          Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) ^ (2 : ℝ)
    have hSA : 0 ≤
        ∑' n : ℕ,
          Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) :=
      Homogenization.Book.Ch02.LambdaSqFinite_series_nonneg Q s 1 A
        (by norm_num) (by positivity)
    have hcp : 0 ≤ Real.rpow c (1 / 2 : ℝ) := Real.rpow_nonneg hc.le _
    have hmul := Real.mul_rpow (z := (2 : ℝ)) hcp hSA
    have hpowc : Real.rpow (Real.rpow c (1 / 2 : ℝ)) (2 : ℝ) = c := by
      calc
        Real.rpow (Real.rpow c (1 / 2 : ℝ)) (2 : ℝ) =
            Real.rpow c ((1 / 2 : ℝ) * 2) :=
          (Real.rpow_mul hc.le _ _).symm
        _ = Real.rpow c 1 := by congr 1 ; norm_num
        _ = c := Real.rpow_one _
    have hpowc' : (Real.rpow c (1 / 2 : ℝ)) ^ (2 : ℕ) = c := by
      exact (Real.rpow_natCast _ 2).symm.trans hpowc
    calc
      _ = (Real.rpow c (1 / 2 : ℝ)) ^ (2 : ℕ) *
          (∑' n : ℕ,
            Homogenization.Book.Ch02.geometricWeight s 1 n *
              Real.rpow
                (Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) ^ (2 : ℕ) := by
            simpa using hmul
      _ = _ := by rw [hpowc', Real.rpow_two]
  have hlowerSq :
      Homogenization.Book.Ch02.lambdaSq Q s
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) B =
        c * Homogenization.Book.Ch02.lambdaSq Q s
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) A := by
    rw [Homogenization.Book.Ch02.lambdaSq_finite,
      Homogenization.Book.Ch02.lambdaSq_finite]
    dsimp [Homogenization.Book.Ch02.lambdaSqFinite]
    change Real.rpow
      (∑' n : ℕ,
        Homogenization.Book.Ch02.geometricWeight s 1 n *
          Real.rpow
            (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) B) (1 / 2 : ℝ)) (-(2 / 1) : ℝ) =
      c * Real.rpow
        (∑' n : ℕ,
          Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) (-(2 / 1) : ℝ)
    rw [hsumLower]
    rw [show (-(2 / 1) : ℝ) = -2 by norm_num]
    change (Real.rpow c⁻¹ (1 / 2 : ℝ) *
        (∑' n : ℕ,
          Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ))) ^ (-2 : ℝ) =
      c *
        (∑' n : ℕ,
          Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) ^ (-2 : ℝ)
    have hSA : 0 ≤
        ∑' n : ℕ,
          Homogenization.Book.Ch02.geometricWeight s 1 n *
            Real.rpow
              (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ) :=
      Homogenization.Book.Ch02.lambdaSqFinite_series_nonneg Q s 1 A
        (by norm_num) (by positivity)
    have hcip : 0 ≤ Real.rpow c⁻¹ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (inv_nonneg.mpr hc.le) _
    have hmul := Real.mul_rpow (z := (-2 : ℝ)) hcip hSA
    have hpowci : Real.rpow (Real.rpow c⁻¹ (1 / 2 : ℝ)) (-2 : ℝ) = c := by
      calc
        Real.rpow (Real.rpow c⁻¹ (1 / 2 : ℝ)) (-2 : ℝ) =
            Real.rpow c⁻¹ ((1 / 2 : ℝ) * (-2)) :=
          (Real.rpow_mul (inv_nonneg.mpr hc.le) _ _).symm
        _ = Real.rpow c⁻¹ (-1) := by congr 1 ; norm_num
        _ = (c⁻¹)⁻¹ := Real.rpow_neg_one _
        _ = c := inv_inv c
    have hpowci_z : (Real.rpow c⁻¹ (1 / 2 : ℝ)) ^ (-2 : ℤ) = c := by
      exact (Real.rpow_neg_natCast (Real.rpow c⁻¹ (1 / 2 : ℝ)) 2).symm.trans hpowci
    have hmul' :
        Real.rpow
            (Real.rpow c⁻¹ (1 / 2 : ℝ) *
              (∑' n : ℕ,
                Homogenization.Book.Ch02.geometricWeight s 1 n *
                  Real.rpow
                    (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                      (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ))) (-2 : ℝ) =
          Real.rpow (Real.rpow c⁻¹ (1 / 2 : ℝ)) (-2 : ℝ) *
            Real.rpow
              (∑' n : ℕ,
                Homogenization.Book.Ch02.geometricWeight s 1 n *
                  Real.rpow
                    (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                      (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) (-2 : ℝ) := by
      exact hmul
    calc
      _ = (Real.rpow c⁻¹ (1 / 2 : ℝ)) ^ (-2 : ℝ) *
          (∑' n : ℕ,
            Homogenization.Book.Ch02.geometricWeight s 1 n *
              Real.rpow
                (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                  (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) ^ (-2 : ℝ) := by
            simpa using hmul'
      _ = _ := by
        exact congrArg
            (fun z : ℝ => z *
              Real.rpow
                (∑' n : ℕ,
                  Homogenization.Book.Ch02.geometricWeight s 1 n *
                    Real.rpow
                      (Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
                        (Q.scale - (n : ℤ)) A) (1 / 2 : ℝ)) (-2 : ℝ)) hpowci
  exact ⟨hupperSq, hlowerSq⟩

theorem aux_in_moments_ellipticity_tail_normalized_observables
    {d : ℕ} [NeZero d]
    (F : Homogenization.Book.Ch02.TriadicCoeffFamily d)
    (a b : Homogenization.RegCoeffField d) (c : ℝ) (hc : 0 < c)
    (ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a)
    (hb : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField b)
    (hF : ∀ R : Homogenization.TriadicCube d,
      ((F.coeffOn R).toCoeffField) =ᵐ[Homogenization.volumeMeasureOn
        (Homogenization.Book.Ch02.cubeDomain R : Set (Homogenization.Vec d))] a.toFun)
    (hab : ∀ x : Homogenization.Vec d, b.toFun x = c • a.toFun x)
    (Q : Homogenization.TriadicCube d) :
    Homogenization.Book.Ch02.LambdaSq Q (1 / 4)
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) F =
        c⁻¹ * Homogenization.Book.Ch04.LambdaSqCoeffField Q (1 / 4)
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) b ∧
      (Homogenization.Book.Ch02.lambdaSq Q (1 / 4)
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) F)⁻¹ =
        c * (Homogenization.Book.Ch04.lambdaSqCoeffField Q (1 / 4)
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) b)⁻¹ := by
  let A : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let B : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField b hb
  have hFA : Homogenization.Book.Ch02.TriadicCoeffFamily.AEEq F A := by
    intro R
    change (F.coeffOn R).toCoeffField =ᵐ[
      Homogenization.volumeMeasureOn (Homogenization.Book.Ch02.cubeDomain R : Set (Homogenization.Vec d))]
      (A.coeffOn R).toCoeffField
    rw [Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField]
    simpa [Homogenization.Book.Ch02.cubeDomain_coe] using hF R
  have hAB : ∀ R : Homogenization.TriadicCube d,
      Homogenization.Book.Ch02.CoeffOn.AEScaled c (A.coeffOn R) (B.coeffOn R) := by
    intro R
    change (B.coeffOn R).toCoeffField =ᵐ[
      Homogenization.volumeMeasureOn (Homogenization.Book.Ch02.cubeDomain R : Set (Homogenization.Vec d))]
        fun x => c • (A.coeffOn R).toCoeffField x
    filter_upwards [] with x
    rw [Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField]
    rw [hab]
    rw [Homogenization.Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField]
  have hscale := aux_in_moments_ellipticity_tail_family_smul
    Q (1 / 4) (by norm_num : (0 : ℝ) < 1 / 4) A B c hc hAB
  have hFupper : Homogenization.Book.Ch02.LambdaSq Q (1 / 4)
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) F =
      Homogenization.Book.Ch02.LambdaSq Q (1 / 4)
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) A :=
    Homogenization.Book.Ch02.LambdaSq_eq_ofAEEq hFA Q (1 / 4)
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 1)
  have hFlower : Homogenization.Book.Ch02.lambdaSq Q (1 / 4)
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) F =
      Homogenization.Book.Ch02.lambdaSq Q (1 / 4)
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) A :=
    Homogenization.Book.Ch02.lambdaSq_eq_ofAEEq hFA Q (1 / 4)
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 1)
  have hBupper : Homogenization.Book.Ch04.LambdaSqCoeffField Q (1 / 4)
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) b =
      Homogenization.Book.Ch02.LambdaSq Q (1 / 4)
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) B := by
    simp [Homogenization.Book.Ch04.LambdaSqCoeffField, B, hb]
  have hBlower : Homogenization.Book.Ch04.lambdaSqCoeffField Q (1 / 4)
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) b =
      Homogenization.Book.Ch02.lambdaSq Q (1 / 4)
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) B := by
    simp [Homogenization.Book.Ch04.lambdaSqCoeffField, B, hb]
  constructor
  · rw [hFupper, hBupper, hscale.1]
    field_simp
  · rw [hFlower, hBlower, hscale.2]
    have hpos : 0 < Homogenization.Book.Ch02.lambdaSq Q (1 / 4)
        (Homogenization.Book.Ch02.MultiscaleExponent.finite 1) A :=
      Homogenization.Book.Ch02.lambdaSq_finite_pos Q A (by norm_num) (by norm_num)
    field_simp [ne_of_gt hpos, ne_of_gt hc]

theorem aux_in_moments_ellipticity_tail_paper_norm_identDistrib
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    {d : ℕ}
    {f : α → Homogenization.RegCoeffField d}
    {g : β → Homogenization.RegCoeffField d}
    (h : ProbabilityTheory.IdentDistrib f g μ ν)
    (u : Homogenization.RegCoeffField d → ℝ)
    (hu : AEMeasurable u (Measure.map f μ)) (p : ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm μ p
        (fun x => ENNReal.ofReal (u (f x))) =
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm ν p
        (fun y => ENNReal.ofReal (u (g y))) := by
  have hcomp := h.comp_of_aemeasurable hu
  have hpow := hcomp.comp
    ((ENNReal.continuous_rpow_const (y := p)).measurable.comp
      ENNReal.continuous_ofReal.measurable)
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm
  congr 1
  exact hpow.lintegral_eq

theorem aux_in_moments_ellipticity_tail_markov_ae
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω}
    {xi t A : ℝ} (hxi : 0 < xi) (ht : 0 < t)
    {X : Ω → ℝ≥0∞} (hX : AEMeasurable X mu)
    (hnorm : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu xi X ≤ ENNReal.ofReal A)
    {B : Set Ω} (hB : B ⊆ {omega | ENNReal.ofReal t ≤ X omega}) :
    mu B ≤ (ENNReal.ofReal A / ENNReal.ofReal t) ^ xi := by
  let I : ℝ≥0∞ := ∫⁻ omega, X omega ^ xi ∂mu
  have hroot : I ^ xi⁻¹ ≤ ENNReal.ofReal A := by
    simpa [SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm, I] using hnorm
  have hI : I ≤ (ENNReal.ofReal A) ^ xi := by
    calc
      I = (I ^ xi⁻¹) ^ xi := by
        rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hxi.ne', ENNReal.rpow_one]
      _ ≤ (ENNReal.ofReal A) ^ xi := ENNReal.rpow_le_rpow hroot hxi.le
  have ht0 : ENNReal.ofReal t ≠ 0 := by positivity
  have httop : ENNReal.ofReal t ≠ ∞ := ENNReal.ofReal_ne_top
  have htail : mu {omega | ENNReal.ofReal t ≤ X omega} ≤
      I / (ENNReal.ofReal t) ^ xi := by
    have hpowMeas : AEMeasurable (fun omega => X omega ^ xi) mu :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hX
    have hmarkov := meas_ge_le_lintegral_div hpowMeas
      (show (ENNReal.ofReal t) ^ xi ≠ 0 by positivity)
      (ENNReal.rpow_ne_top_of_nonneg hxi.le httop)
    have hsets : {omega | (ENNReal.ofReal t) ^ xi ≤ X omega ^ xi} =
        {omega | ENNReal.ofReal t ≤ X omega} := by
      ext omega
      exact ENNReal.rpow_le_rpow_iff hxi
    simpa [I, hsets] using hmarkov
  calc
    mu B ≤ mu {omega | ENNReal.ofReal t ≤ X omega} := measure_mono hB
    _ ≤ I / (ENNReal.ofReal t) ^ xi := htail
    _ ≤ (ENNReal.ofReal A) ^ xi / (ENNReal.ofReal t) ^ xi :=
      ENNReal.div_le_div_right hI _
    _ = (ENNReal.ofReal A / ENNReal.ofReal t) ^ xi := by
      rw [ENNReal.div_rpow_of_nonneg _ _ hxi.le]

theorem aux_in_moments_ellipticity_tail_target_root_moments
    {d : ℕ} [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (xi N k : ℕ)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamily : ∀ (N : ℕ) (ω : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N ω).coeffOn Q).toCoeffField x =
          scalarMatrix
            (cutoffCoefficient model
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x))
    (hfield : ProbabilityTheory.IdentDistrib
      (fun omega : BilateralField d =>
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) •
          aux_annealed_limit_response_transport_scalarRegCoeffField
            (aux_in_moments_response_moment_cutoffField model N omega))
      (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N omega))
      (chaosSampleLaw model).toMeasure model.P.toMeasure)
    (B : ℝ) (_hB : 0 ≤ B)
    (hupper : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
      (fun source => ENNReal.ofReal (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        Homogenization.Book.Ch04.LambdaSqCoeffField
          (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
          (MultiscaleExponent.finite 1)
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source)))) ≤
      ENNReal.ofReal B)
    (hlower : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
      (fun source => ENNReal.ofReal (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) *
        (Homogenization.Book.Ch04.lambdaSqCoeffField
          (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
          (MultiscaleExponent.finite 1)
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))⁻¹))) ≤
      ENNReal.ofReal B)
    (_hxi : 0 < (xi : ℝ)) (_hxiOne : 1 ≤ (xi : ℝ)) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm (chaosSampleLaw model).toMeasure (xi : ℝ)
      (fun omega => ENNReal.ofReal (Real.sqrt
        (LambdaSq (originCube d (k : ℤ)) (1 / 4)
          (MultiscaleExponent.finite 1) (family N omega)))) ≤ ENNReal.ofReal B ∧
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm (chaosSampleLaw model).toMeasure (xi : ℝ)
      (fun omega => ENNReal.ofReal (Real.sqrt
        ((lambdaSq (originCube d (k : ℤ)) (1 / 4)
          (MultiscaleExponent.finite 1) (family N omega))⁻¹))) ≤ ENNReal.ofReal B ∧
    AEMeasurable (fun omega => ENNReal.ofReal (Real.sqrt
      (LambdaSq (originCube d (k : ℤ)) (1 / 4)
        (MultiscaleExponent.finite 1) (family N omega))))
      (chaosSampleLaw model).toMeasure ∧
    AEMeasurable (fun omega => ENNReal.ofReal (Real.sqrt
      ((lambdaSq (originCube d (k : ℤ)) (1 / 4)
        (MultiscaleExponent.finite 1) (family N omega))⁻¹)))
      (chaosSampleLaw model).toMeasure := by
  let aFun : BilateralField d → Homogenization.RegCoeffField d := fun omega =>
    aux_annealed_limit_response_transport_scalarRegCoeffField
      (aux_in_moments_response_moment_cutoffField model N omega)
  let bFun : BilateralField d → Homogenization.RegCoeffField d := fun omega =>
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) • aFun omega
  have hfield' : ProbabilityTheory.IdentDistrib bFun
      (fun source : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))
      (chaosSampleLaw model).toMeasure model.P.toMeasure := by
    simpa [aFun, bFun] using hfield
  let Pscale : Homogenization.Book.Ch04.RestrictionCoeffLaw d :=
    Homogenization.Book.Ch04.restrictionScaleNormalizedLaw N
      (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw model N)
  let hPscale : Homogenization.Book.Ch04.RestrictionLawCarrier Pscale := by
    dsimp [Pscale]
    exact (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw_lawCarrier model N).scaleNormalized N
  have hmapSource : Measure.map
      (fun source : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source)) model.P.toMeasure =
      Pscale := by
    dsimp [Pscale]
    rw [Homogenization.Book.Ch04.restrictionScaleNormalizedLaw_eq_map_rescaleReg,
      SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRestrictionLaw_eq_map]
    rw [Measure.map_map (Homogenization.measurable_rescaleReg N)
      (SubdiffusiveProcess.CoarseGrainingVocab.measurable_aCutoffRegCoeffField model N)]
    rfl
  let Q : Homogenization.TriadicCube d := originCube d (k : ℤ)
  let U : Homogenization.RegCoeffField d → ℝ := fun z =>
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
      Homogenization.Book.Ch04.LambdaSqCoeffField Q (1 / 4)
        (MultiscaleExponent.finite 1) z
  let V : Homogenization.RegCoeffField d → ℝ := fun z =>
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) *
      (Homogenization.Book.Ch04.lambdaSqCoeffField Q (1 / 4)
        (MultiscaleExponent.finite 1) z)⁻¹
  have hUbase : AEMeasurable (fun z : Homogenization.RegCoeffField d =>
      Homogenization.Book.Ch04.LambdaSqCoeffField Q (1 / 4)
        (MultiscaleExponent.finite 1) z) Pscale :=
    hPscale.aemeasurable_LambdaSqCoeffField_finite_one Q (by norm_num)
  have hVbase : AEMeasurable (fun z : Homogenization.RegCoeffField d =>
      (Homogenization.Book.Ch04.lambdaSqCoeffField Q (1 / 4)
        (MultiscaleExponent.finite 1) z)⁻¹) Pscale :=
    hPscale.aemeasurable_lambdaSqCoeffField_finite_one_inv Q (by norm_num)
  have hU : AEMeasurable U (Measure.map bFun (chaosSampleLaw model).toMeasure) := by
    rw [hfield'.map_eq, hmapSource]
    exact aemeasurable_const.mul hUbase
  have hV : AEMeasurable V (Measure.map bFun (chaosSampleLaw model).toMeasure) := by
    rw [hfield'.map_eq, hmapSource]
    exact aemeasurable_const.mul hVbase
  have hUnorm := aux_in_moments_ellipticity_tail_paper_norm_identDistrib
    hfield' U hU (xi : ℝ)
  have hVnorm := aux_in_moments_ellipticity_tail_paper_norm_identDistrib
    hfield' V hV (xi : ℝ)
  have hUrootA : AEMeasurable (fun z : Homogenization.RegCoeffField d =>
      Real.sqrt (U z)) (Measure.map bFun (chaosSampleLaw model).toMeasure) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hU
  have hVrootA : AEMeasurable (fun z : Homogenization.RegCoeffField d =>
      Real.sqrt (V z)) (Measure.map bFun (chaosSampleLaw model).toMeasure) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hV
  have hUrootNorm := aux_in_moments_ellipticity_tail_paper_norm_identDistrib
    hfield' (fun z => Real.sqrt (U z)) hUrootA (xi : ℝ)
  have hVrootNorm := aux_in_moments_ellipticity_tail_paper_norm_identDistrib
    hfield' (fun z => Real.sqrt (V z)) hVrootA (xi : ℝ)
  have hLamEq : ∀ omega : BilateralField d,
      LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (family N omega) = U (bFun omega) ∧
      (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (family N omega))⁻¹ =
        V (bFun omega) := by
    intro omega
    let a : Homogenization.RegCoeffField d := aFun omega
    let b : Homogenization.RegCoeffField d := bFun omega
    have ha : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField a := by
      apply aux_annealed_limit_response_transport_scalarRegCoeffField_elliptic
      intro x
      simpa [a, aFun, aux_in_moments_response_moment_cutoffField] using
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos model
          (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x)
    have hfpos : ∀ x : SpatialCoordinates d,
        0 < (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) •
          aux_in_moments_response_moment_cutoffField model N omega x := by
      intro x
      exact mul_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)
        (by simpa [aux_in_moments_response_moment_cutoffField] using
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffCoefficient_pos model
            (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x))
    have hb : Homogenization.Book.Ch04.AELocallyUniformlyEllipticField b := by
      let f : C(SpatialCoordinates d, ℝ) :=
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) •
          aux_in_moments_response_moment_cutoffField model N omega
      have hf := aux_annealed_limit_response_transport_scalarRegCoeffField_elliptic f
        (by simpa [f] using hfpos)
      have hba : b = aux_annealed_limit_response_transport_scalarRegCoeffField f := by
        ext x
        simp [b, bFun, aFun, f]
        ring
      rw [hba]
      exact hf
    have hF : ∀ R : Homogenization.TriadicCube d,
        ((family N omega).coeffOn R).toCoeffField =ᵐ[
          Homogenization.volumeMeasureOn
            (Homogenization.Book.Ch02.cubeDomain R : Set (Homogenization.Vec d))] a.toFun := by
      intro R
      exact hfamily N omega R
    have hab : ∀ x : Homogenization.Vec d, b.toFun x =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) • a.toFun x := by
      intro x
      rfl
    have hobs0 := aux_in_moments_ellipticity_tail_normalized_observables
      (family N omega) a b (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N) ha hb hF hab Q
    have hobs := by
      simpa only [U, V, Q, a, b] using hobs0
    exact hobs
  have hsourceEll : ∀ source : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      Homogenization.Book.Ch04.AELocallyUniformlyEllipticField
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source) := by
    intro source
    exact SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField_aeLocallyUniformlyEllipticField
      model N source
  have hUsource : ∀ source : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      U (Homogenization.rescaleReg N
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source)) =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
          Homogenization.Book.Ch04.LambdaSqCoeffField
            (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
            (MultiscaleExponent.finite 1)
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source) := by
    intro source
    dsimp [U, Q]
    rw [Homogenization.Book.Ch04.LambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      (hsourceEll source) N k (1 / 4) (MultiscaleExponent.finite 1)]
    simp only [Nat.cast_add]
  have hVsource : ∀ source : _root_.SubdiffusiveProcess.Model.PotentialSample d,
      V (Homogenization.rescaleReg N
        (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source)) =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) *
          (Homogenization.Book.Ch04.lambdaSqCoeffField
            (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
            (MultiscaleExponent.finite 1)
            (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))⁻¹ := by
    intro source
    dsimp [V, Q]
    rw [Homogenization.Book.Ch04.lambdaSqCoeffField_originCube_rescaleCoeffField_of_aelocallyUniformlyElliptic
      (hsourceEll source) N k (1 / 4) (MultiscaleExponent.finite 1)]
    simp only [Nat.cast_add]
  have hUsourceEq :
      (fun source : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        ENNReal.ofReal (Real.sqrt (U (Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))))) =
      (fun source => ENNReal.ofReal (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        Homogenization.Book.Ch04.LambdaSqCoeffField
          (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
          (MultiscaleExponent.finite 1)
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source)))) := by
    funext source
    rw [hUsource source]
  have hVsourceEq :
      (fun source : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
        ENNReal.ofReal (Real.sqrt (V (Homogenization.rescaleReg N
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))))) =
      (fun source => ENNReal.ofReal (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) *
        (Homogenization.Book.Ch04.lambdaSqCoeffField
          (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
          (MultiscaleExponent.finite 1)
          (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))⁻¹))) := by
    funext source
    rw [hVsource source]
  have hUtarget :
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm (chaosSampleLaw model).toMeasure (xi : ℝ)
          (fun omega => ENNReal.ofReal (Real.sqrt
            (LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (family N omega)))) =
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm (chaosSampleLaw model).toMeasure (xi : ℝ)
          (fun omega => ENNReal.ofReal (Real.sqrt (U (bFun omega)))) := by
    apply SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_congr_ae
      (chaosSampleLaw model).toMeasure (xi : ℝ)
    exact Filter.Eventually.of_forall (fun omega => by
      change ENNReal.ofReal (Real.sqrt
        (LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (family N omega))) =
        ENNReal.ofReal (Real.sqrt (U (bFun omega)))
      rw [hLamEq omega |>.1])
  have hVtarget :
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm (chaosSampleLaw model).toMeasure (xi : ℝ)
          (fun omega => ENNReal.ofReal (Real.sqrt
            ((lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (family N omega))⁻¹))) =
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm (chaosSampleLaw model).toMeasure (xi : ℝ)
          (fun omega => ENNReal.ofReal (Real.sqrt (V (bFun omega)))) := by
    apply SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_congr_ae
      (chaosSampleLaw model).toMeasure (xi : ℝ)
    exact Filter.Eventually.of_forall (fun omega => by
      change ENNReal.ofReal (Real.sqrt
        ((lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (family N omega))⁻¹)) =
        ENNReal.ofReal (Real.sqrt (V (bFun omega)))
      rw [hLamEq omega |>.2])
  have hRU0 : AEMeasurable (fun omega : BilateralField d =>
      Real.sqrt (U (bFun omega))) (chaosSampleLaw model).toMeasure :=
    hUrootA.comp_aemeasurable hfield'.aemeasurable_fst
  have hRL0 : AEMeasurable (fun omega : BilateralField d =>
      Real.sqrt (V (bFun omega))) (chaosSampleLaw model).toMeasure :=
    hVrootA.comp_aemeasurable hfield'.aemeasurable_fst
  have hRU : AEMeasurable (fun omega : BilateralField d =>
      ENNReal.ofReal (Real.sqrt
        (LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (family N omega))))
      (chaosSampleLaw model).toMeasure := by
    have h0 := ENNReal.continuous_ofReal.measurable.comp_aemeasurable hRU0
    refine h0.congr (Filter.Eventually.of_forall (fun omega => ?_))
    simp only [Function.comp_apply]
    rw [hLamEq omega |>.1]
  have hRL : AEMeasurable (fun omega : BilateralField d =>
      ENNReal.ofReal (Real.sqrt
        ((lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (family N omega))⁻¹)))
      (chaosSampleLaw model).toMeasure := by
    have h0 := ENNReal.continuous_ofReal.measurable.comp_aemeasurable hRL0
    refine h0.congr (Filter.Eventually.of_forall (fun omega => ?_))
    simp only [Function.comp_apply]
    rw [hLamEq omega |>.2]
  refine ⟨?_, ?_, hRU, hRL⟩
  · calc
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm (chaosSampleLaw model).toMeasure (xi : ℝ)
          (fun omega => ENNReal.ofReal (Real.sqrt
            (LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (family N omega)))) =
          SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm (chaosSampleLaw model).toMeasure (xi : ℝ)
            (fun omega => ENNReal.ofReal (Real.sqrt (U (bFun omega)))) := hUtarget
      _ = SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
            (fun source => ENNReal.ofReal (Real.sqrt (U (Homogenization.rescaleReg N
              (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))))) := hUrootNorm
      _ = SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
            (fun source => ENNReal.ofReal (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
              Homogenization.Book.Ch04.LambdaSqCoeffField
                (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
                (MultiscaleExponent.finite 1)
              (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source)))) := by
              exact congrArg
                (fun f : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ =>
                  SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ) f)
                hUsourceEq
      _ ≤ ENNReal.ofReal B := hupper
  · calc
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm (chaosSampleLaw model).toMeasure (xi : ℝ)
          (fun omega => ENNReal.ofReal (Real.sqrt
            ((lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (family N omega))⁻¹))) =
          SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm (chaosSampleLaw model).toMeasure (xi : ℝ)
            (fun omega => ENNReal.ofReal (Real.sqrt (V (bFun omega)))) := hVtarget
      _ = SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
            (fun source => ENNReal.ofReal (Real.sqrt (V (Homogenization.rescaleReg N
              (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))))) := hVrootNorm
      _ = SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
            (fun source => ENNReal.ofReal (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) *
              (Homogenization.Book.Ch04.lambdaSqCoeffField
                (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
                (MultiscaleExponent.finite 1)
                (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))⁻¹))) := by
              exact congrArg
                (fun f : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ =>
                  SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ) f)
                hVsourceEq
      _ ≤ ENNReal.ofReal B := hlower

theorem aux_in_moments_ellipticity_tail_two_root_tail
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    (xi eps B : ℝ) (_hxi : 0 < xi) (hxiTwo : 2 ≤ xi) (heps : 0 < eps)
    (hB : 0 ≤ B)
    (U V : Ω → ℝ≥0∞) (K : Ω → ℝ)
    (hU : AEMeasurable U mu) (hV : AEMeasurable V mu)
    (hUnorm : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu xi U ≤ ENNReal.ofReal B)
    (hVnorm : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu xi V ≤ ENNReal.ofReal B)
    (hK : ∀ omega, 1 + U omega ^ (2 : ℕ) + V omega ^ (2 : ℕ) =
      ENNReal.ofReal (K omega)) :
    0 < (1 + 2 * B ^ 2) / min eps 1 ∧
      mu {omega | (1 + 2 * B ^ 2) / min eps 1 < K omega} ≤ ENNReal.ofReal eps := by
  let p : ℝ := xi / 2
  have hp : 0 < p := by
    dsimp [p]
    linarith
  have hpone : 1 ≤ p := by
    dsimp [p]
    linarith
  have hsqU : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
      (fun omega => U omega ^ (2 : ℕ)) ≤ (ENNReal.ofReal B) ^ (2 : ℕ) := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_sq mu hp]
    have hroot : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu (2 * p) U ≤
        ENNReal.ofReal B := by
      rw [show 2 * p = xi by dsimp [p]; ring]
      exact hUnorm
    exact pow_le_pow_left' hroot 2
  have hsqV : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
      (fun omega => V omega ^ (2 : ℕ)) ≤ (ENNReal.ofReal B) ^ (2 : ℕ) := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_sq mu hp]
    have hroot : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu (2 * p) V ≤
        ENNReal.ofReal B := by
      rw [show 2 * p = xi by dsimp [p]; ring]
      exact hVnorm
    exact pow_le_pow_left' hroot 2
  let X : Ω → ℝ≥0∞ := fun omega =>
    1 + U omega ^ (2 : ℕ) + V omega ^ (2 : ℕ)
  have hX : AEMeasurable X mu := by
    dsimp [X]
    exact (aemeasurable_const.add (hU.pow_const 2)).add (hV.pow_const 2)
  have hXnorm : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p X ≤
      ENNReal.ofReal (1 + 2 * B ^ 2) := by
    have hOne : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) mu := aemeasurable_const
    have hOneU : AEMeasurable
        (fun omega => (1 : ℝ≥0∞) + U omega ^ (2 : ℕ)) mu :=
      hOne.add (hU.pow_const 2)
    have haddV := SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm_add_le mu hpone
      (X := fun omega => (1 : ℝ≥0∞) + U omega ^ (2 : ℕ))
      (Y := fun omega => V omega ^ (2 : ℕ)) hOneU (hV.pow_const 2)
    have haddU := SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm_add_le mu hpone
      (X := fun _ : Ω => (1 : ℝ≥0∞)) (Y := fun omega => U omega ^ (2 : ℕ))
      hOne (hU.pow_const 2)
    calc
      _ ≤ SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
            (fun omega => 1 + U omega ^ (2 : ℕ)) +
          SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
            (fun omega => V omega ^ (2 : ℕ)) := by simpa [X] using haddV
      _ ≤ (SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
            (fun _ : Ω => (1 : ℝ≥0∞)) +
          SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
            (fun omega => U omega ^ (2 : ℕ))) +
          SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
            (fun omega => V omega ^ (2 : ℕ)) := by
            simpa using add_le_add_left haddU
              (SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
                (fun omega => V omega ^ (2 : ℕ)))
      _ ≤ 1 + (ENNReal.ofReal B) ^ (2 : ℕ) +
            (ENNReal.ofReal B) ^ (2 : ℕ) := by
            rw [SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm_one]
            gcongr
      _ = ENNReal.ofReal (1 + 2 * B ^ 2) := by
        rw [add_assoc, ← ENNReal.ofReal_pow hB 2,
          ← ENNReal.ofReal_add (sq_nonneg B) (sq_nonneg B),
          ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) (by positivity)]
        congr 1
        ring
  have hsubset (A : ℝ) : {omega | A < K omega} ⊆
      {omega | ENNReal.ofReal A ≤ X omega} := by
    intro omega hω
    change ENNReal.ofReal A ≤ X omega
    rw [show X omega = ENNReal.ofReal (K omega) by simpa [X] using hK omega]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hω)
  let q : ℝ := min eps 1
  let R : ℝ := 1 + 2 * B ^ 2
  let A : ℝ := R / q
  have hqpos : 0 < q := by
    dsimp [q]
    exact lt_min heps (by norm_num)
  have hqone : q ≤ 1 := min_le_right _ _
  have hqeps : q ≤ eps := min_le_left _ _
  have hRpos : 0 < R := by
    change 0 < 1 + 2 * B ^ 2
    exact lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg B)))
  have hApos : 0 < A := by
    dsimp [A]
    exact div_pos hRpos hqpos
  have hmarkov := aux_in_moments_ellipticity_tail_markov_ae
    (mu := mu) (xi := p) (t := A) (A := R) hp hApos hX hXnorm (hsubset A)
  have hratio : ENNReal.ofReal R / ENNReal.ofReal A = ENNReal.ofReal q := by
    rw [show A = R / q by rfl, ENNReal.ofReal_div_of_pos hqpos]
    exact ENNReal.div_div_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hRpos))
      ENNReal.ofReal_ne_top
  have hpow : (ENNReal.ofReal R / ENNReal.ofReal A) ^ p ≤
      ENNReal.ofReal eps := by
    rw [hratio]
    calc
      (ENNReal.ofReal q) ^ p ≤ (ENNReal.ofReal q) ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_ge (by simpa using
          (ENNReal.ofReal_le_ofReal hqone)) hpone
      _ = ENNReal.ofReal q := by rw [ENNReal.rpow_one]
      _ ≤ ENNReal.ofReal eps := ENNReal.ofReal_le_ofReal hqeps
  refine ⟨?_, ?_⟩
  · simpa [A, R, q] using hApos
  · simpa [A, R, q] using hmarkov.trans hpow

theorem aux_in_moments_ellipticity_tail_two_root_tail_canonical
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    (xi eps B : ℝ) (hxi : 0 < xi) (hxiTwo : 2 ≤ xi) (heps : 0 < eps)
    (hB : 0 ≤ B)
    (U V : Ω → ℝ≥0∞) (K : Ω → ℝ)
    (hU : AEMeasurable U mu) (hV : AEMeasurable V mu)
    (hUnorm : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu xi U ≤ ENNReal.ofReal B)
    (hVnorm : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu xi V ≤ ENNReal.ofReal B)
    (hK : ∀ omega, 1 + U omega ^ (2 : ℕ) + V omega ^ (2 : ℕ) =
      ENNReal.ofReal (K omega)) :
    0 < (1 + 2 * B ^ 2) / min eps 1 ∧
      mu {omega | (1 + 2 * B ^ 2) / min eps 1 < K omega} ≤ ENNReal.ofReal eps := by
  exact aux_in_moments_ellipticity_tail_two_root_tail
    xi eps B hxi hxiTwo heps hB U V K hU hV hUnorm hVnorm hK

theorem aux_in_moments_ellipticity_tail_root_tail_apply
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsProbabilityMeasure mu]
    (xi eps B : ℝ) (hxi : 0 < xi) (hxiTwo : 2 ≤ xi) (heps : 0 < eps)
    (hB : 0 ≤ B) (U V : Ω → ℝ≥0∞) (K : Ω → ℝ)
    (hU : AEMeasurable U mu) (hV : AEMeasurable V mu)
    (hUnorm : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu xi U ≤
      ENNReal.ofReal B)
    (hVnorm : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu xi V ≤
      ENNReal.ofReal B)
    (hK : ∀ omega, 1 + U omega ^ (2 : ℕ) + V omega ^ (2 : ℕ) =
      ENNReal.ofReal (K omega)) :
    0 < (1 + 2 * B ^ 2) / min eps 1 ∧
      mu {omega | (1 + 2 * B ^ 2) / min eps 1 < K omega} ≤
        ENNReal.ofReal eps := by
  exact aux_in_moments_ellipticity_tail_two_root_tail_canonical
    xi eps B hxi hxiTwo heps hB U V K hU hV hUnorm hVnorm hK

theorem aux_in_moments_ellipticity_tail_event_transport
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    {K L : Ω → ℝ} (A eps : ℝ) (hKL : K = L)
    (hmeasure : mu {omega | A < K omega} ≤ ENNReal.ofReal eps) :
    mu {omega | A < L omega} ≤ ENNReal.ofReal eps := by
  have hset : {omega | A < L omega} = {omega | A < K omega} := by
    ext omega
    rw [hKL]
  rw [hset]
  exact hmeasure

theorem aux_in_moments_ellipticity_tail_threshold_transport
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    {L : Ω → ℝ} (A T eps : ℝ) (hAT : A = T)
    (hmeasure : mu {omega | A < L omega} ≤ ENNReal.ofReal eps) :
    mu {omega | T < L omega} ≤ ENNReal.ofReal eps := by
  rw [← hAT]
  exact hmeasure

theorem aux_in_moments_ellipticity_tail_final_target
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k : ℕ)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d) (eps B : ℝ)
    (hmeasure : (chaosSampleLaw model).toMeasure
      {ω : BilateralField d |
        (1 + 2 * B ^ 2) / min eps 1 <
          1 + LambdaSq (originCube d (k : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1) (family N ω) +
            (lambdaSq (originCube d (k : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1) (family N ω))⁻¹} ≤
      ENNReal.ofReal eps) :
    (chaosSampleLaw model).toMeasure
      {ω : BilateralField d |
        (1 + 2 * B ^ 2) / min eps 1 <
          1 + LambdaSq (originCube d (k : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1) (family N ω) +
            (lambdaSq (originCube d (k : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1) (family N ω))⁻¹} ≤
      ENNReal.ofReal eps := hmeasure

theorem aux_in_moments_ellipticity_tail_threshold_pos
    (eps B : ℝ) (heps : 0 < eps) :
    0 < (1 + 2 * B ^ 2) / min eps 1 := by
  have hnum : 0 < 1 + 2 * B ^ 2 := by positivity
  exact div_pos hnum (lt_min heps zero_lt_one)

theorem aux_in_moments_ellipticity_tail_xi_two
    (d xi : ℕ) (hd : 2 ≤ d) (hxiDim : 128 * d ≤ xi) :
    (2 : ℝ) ≤ (xi : ℝ) := by
  have hdimReal : (128 : ℝ) * (d : ℝ) ≤ (xi : ℝ) := by
    have hc : ((128 * d : ℕ) : ℝ) ≤ (xi : ℝ) := Nat.cast_le.mpr hxiDim
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc
  have hdReal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith

theorem aux_in_moments_ellipticity_tail_root_ellipticity_functions
    {d : ℕ} [NeZero d] (Q Q' : TriadicCube d)
    (F F' : BilateralField d → TriadicCoeffFamily d)
    (hQ : Q = Q') (hF : F = F') :
    ∃ upper lower : BilateralField d → ℝ,
      upper = (fun omega =>
        LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega)) ∧
      lower = (fun omega =>
        lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega)) ∧
      (∀ omega, 0 ≤ upper omega) ∧ (∀ omega, 0 < lower omega) ∧
      (fun omega => ENNReal.ofReal (Real.sqrt ((lower omega)⁻¹))) =
        (fun omega => ENNReal.ofReal (Real.sqrt
          ((lambdaSq Q' (1 / 4) (MultiscaleExponent.finite 1) (F' omega))⁻¹))) ∧
      (fun omega => ENNReal.ofReal (Real.sqrt
        (upper omega))) =
        (fun omega => ENNReal.ofReal (Real.sqrt
          (LambdaSq Q' (1 / 4) (MultiscaleExponent.finite 1) (F' omega)))) := by
  refine ⟨(fun omega =>
      LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega)),
    (fun omega =>
      lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega)),
    rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro omega
    exact LambdaSq_finite_nonneg _ _ (by norm_num) (by norm_num)
  · intro omega
    exact lambdaSq_finite_pos _ _ (by norm_num) (by norm_num)
  · funext omega
    rw [hQ, hF]
  · funext omega
    rw [hQ, hF]

theorem aux_in_moments_ellipticity_tail_norm_transport
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (p B : ℝ) (V W : Ω → ℝ≥0∞)
    (hVW : V = W)
    (hbound : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p W ≤
      ENNReal.ofReal B) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p V ≤
      ENNReal.ofReal B := by
  calc
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p V =
        SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p W := by
      exact congrArg
        (fun f : Ω → ℝ≥0∞ =>
          SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p f) hVW
    _ ≤ ENNReal.ofReal B := hbound

theorem aux_in_moments_ellipticity_tail_root_lower_norm_le
    {d : ℕ} [MeasurableSpace (BilateralField d)]
    (mu : Measure (BilateralField d)) (p : ℝ)
    (Q : TriadicCube d) (F : BilateralField d → TriadicCoeffFamily d)
    (lower : BilateralField d → ℝ)
    (hlower : lower = (fun omega =>
      lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega)))
    (B : ℝ)
    (hbound : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
        (fun omega => ENNReal.ofReal (Real.sqrt
          ((lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega))⁻¹))) ≤
      ENNReal.ofReal B) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
        (fun omega => ENNReal.ofReal (Real.sqrt ((lower omega)⁻¹))) ≤
      ENNReal.ofReal B := by
  have hvfun := congrArg
    (fun f : BilateralField d → ℝ =>
      fun omega => ENNReal.ofReal (Real.sqrt ((f omega)⁻¹))) hlower
  have hvnorm := congrArg
    (fun f : BilateralField d → ℝ≥0∞ =>
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p f) hvfun
  calc
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
        (fun omega => ENNReal.ofReal (Real.sqrt ((lower omega)⁻¹))) =
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
        (fun omega => ENNReal.ofReal (Real.sqrt
          ((lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega))⁻¹))) := by
            exact hvnorm
    _ ≤ ENNReal.ofReal B := hbound

theorem aux_in_moments_ellipticity_tail_norm_transport_of_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {V W : Ω → ℝ≥0∞} (mu : Measure Ω) (p B : ℝ)
    (hbound : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p W ≤
      ENNReal.ofReal B) (hVW : V = W) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p V ≤
      ENNReal.ofReal B := by
  exact aux_in_moments_ellipticity_tail_norm_transport mu p B V W hVW hbound

theorem aux_in_moments_ellipticity_tail_lambdaSq_inv_sqrt_fun_congr
    {d : ℕ} (Q Q' : TriadicCube d)
    (F F' : BilateralField d → TriadicCoeffFamily d)
    (hQ : Q = Q') (hF : F = F') :
    (fun omega => ENNReal.ofReal (Real.sqrt
      ((lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega))⁻¹))) =
    (fun omega => ENNReal.ofReal (Real.sqrt
      ((lambdaSq Q' (1 / 4) (MultiscaleExponent.finite 1) (F' omega))⁻¹))) := by
  rw [hQ, hF]

theorem aux_in_moments_ellipticity_tail_target_lower_norm_transport
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (xi N k : ℕ)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (V : BilateralField d → ℝ≥0∞) (B : ℝ)
    (hV : V = (fun omega => ENNReal.ofReal (Real.sqrt
      ((lambdaSq (originCube d (k : ℤ)) (1 / 4)
        (MultiscaleExponent.finite 1) (family N omega))⁻¹))))
    (hbound : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm
      (chaosSampleLaw model).toMeasure (xi : ℝ)
      (fun omega => ENNReal.ofReal (Real.sqrt
        ((lambdaSq (originCube d (k : ℤ)) (1 / 4)
          (MultiscaleExponent.finite 1) (family N omega))⁻¹))) ≤
      ENNReal.ofReal B) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm
      (chaosSampleLaw model).toMeasure (xi : ℝ) V ≤ ENNReal.ofReal B := by
  exact aux_in_moments_ellipticity_tail_norm_transport
    (chaosSampleLaw model).toMeasure (xi : ℝ) B V _ hV hbound

theorem aux_in_moments_ellipticity_tail_root_square_data
    {d : ℕ} [MeasurableSpace (BilateralField d)]
    (mu : Measure (BilateralField d)) (p B : ℝ)
    (upper lower : BilateralField d → ℝ)
    (hupper : ∀ omega, 0 ≤ upper omega)
    (hlower : ∀ omega, 0 < lower omega)
    {W : BilateralField d → ℝ≥0∞}
    (hvfun : (fun omega => ENNReal.ofReal (Real.sqrt ((lower omega)⁻¹))) = W)
    (hbound : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p W ≤
      ENNReal.ofReal B)
    {WU : BilateralField d → ℝ≥0∞}
    (hufun : (fun omega => ENNReal.ofReal (Real.sqrt (upper omega))) = WU)
    (hubound : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p WU ≤
      ENNReal.ofReal B)
    (humeas : AEMeasurable WU mu)
    (hvmeas : AEMeasurable W mu) :
    ∃ U V : BilateralField d → ℝ≥0∞, ∃ K : BilateralField d → ℝ,
      U = (fun omega => ENNReal.ofReal (Real.sqrt (upper omega))) ∧
      U = WU ∧
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p U ≤
        ENNReal.ofReal B ∧
      AEMeasurable U mu ∧
      V = (fun omega => ENNReal.ofReal (Real.sqrt ((lower omega)⁻¹))) ∧
      V = W ∧
      SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p V ≤
        ENNReal.ofReal B ∧
      AEMeasurable V mu ∧
      K = (fun omega => 1 + upper omega + (lower omega)⁻¹) ∧
      (∀ omega, 1 + U omega ^ (2 : ℕ) + V omega ^ (2 : ℕ) =
        ENNReal.ofReal (K omega)) := by
  let U : BilateralField d → ℝ≥0∞ :=
    fun omega => ENNReal.ofReal (Real.sqrt (upper omega))
  let V : BilateralField d → ℝ≥0∞ :=
    fun omega => ENNReal.ofReal (Real.sqrt ((lower omega)⁻¹))
  let K : BilateralField d → ℝ :=
    fun omega => 1 + upper omega + (lower omega)⁻¹
  have hUlower : U = (fun omega =>
      ENNReal.ofReal (Real.sqrt (upper omega))) := rfl
  have hUdirect : U = WU := hUlower.trans hufun
  have hUnorm := aux_in_moments_ellipticity_tail_norm_transport
    mu p B U WU hUdirect hubound
  have hUmeas : AEMeasurable U mu := by
    rw [hUdirect]
    exact humeas
  have hK : ∀ omega, 1 + U omega ^ (2 : ℕ) + V omega ^ (2 : ℕ) =
      ENNReal.ofReal (K omega) := by
    intro omega
    have hu : U omega ^ (2 : ℕ) = ENNReal.ofReal (upper omega) := by
      dsimp [U]
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
        Real.sq_sqrt (hupper omega)]
    have hv : V omega ^ (2 : ℕ) = ENNReal.ofReal ((lower omega)⁻¹) := by
      dsimp [V]
      rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
        Real.sq_sqrt (inv_nonneg.mpr (hlower omega).le)]
    rw [hu, hv, ← ENNReal.ofReal_one]
    rw [← ENNReal.ofReal_add (by norm_num) (hupper omega)]
    have hsum : 0 ≤ 1 + upper omega := by
      linarith [hupper omega]
    rw [← ENNReal.ofReal_add hsum
      (inv_nonneg.mpr (hlower omega).le)]
  have hVlower : V = (fun omega =>
      ENNReal.ofReal (Real.sqrt ((lower omega)⁻¹))) := rfl
  have hVdirect : V = W := hVlower.trans hvfun
  have hVnorm := aux_in_moments_ellipticity_tail_norm_transport
    mu p B V W hVdirect hbound
  have hVmeas : AEMeasurable V mu := by
    rw [hVdirect]
    exact hvmeas
  exact ⟨U, V, K, hUlower, hUdirect, hUnorm, hUmeas, rfl, hVdirect,
    hVnorm, hVmeas, rfl, hK⟩

theorem aux_in_moments_ellipticity_tail_root_K_direct
    {d : ℕ} (Q Q' : TriadicCube d)
    (F F' : BilateralField d → TriadicCoeffFamily d)
    (upper lower : BilateralField d → ℝ) (K : BilateralField d → ℝ)
    (hQ : Q = Q') (hF : F = F')
    (hupper : upper = (fun omega =>
      LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega)))
    (hlower : lower = (fun omega =>
      lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega)))
    (hK : K = (fun omega => 1 + upper omega + (lower omega)⁻¹)) :
    K = (fun omega => 1 + LambdaSq Q' (1 / 4)
        (MultiscaleExponent.finite 1) (F' omega) +
      (lambdaSq Q' (1 / 4) (MultiscaleExponent.finite 1) (F' omega))⁻¹) := by
  rw [hK, hupper, hlower, hQ, hF]

/-- Assemble the tail estimate from the two root moments in a scalar context. -/
theorem aux_in_moments_ellipticity_tail_root_tail_of_moments
    {d : ℕ} [NeZero d] [MeasurableSpace (BilateralField d)]
    (mu : Measure (BilateralField d)) [IsProbabilityMeasure mu]
    (Q : TriadicCube d) (F : BilateralField d → TriadicCoeffFamily d)
    (p eps B : ℝ) (hp : 0 < p) (hpTwo : 2 ≤ p) (heps : 0 < eps)
    (hB : 0 ≤ B)
    (hupperBound : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
      (fun omega => ENNReal.ofReal (Real.sqrt
        (LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega)))) ≤
      ENNReal.ofReal B)
    (hlowerBound : SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm mu p
      (fun omega => ENNReal.ofReal (Real.sqrt
        ((lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega))⁻¹))) ≤
      ENNReal.ofReal B)
    (hupperMeas : AEMeasurable (fun omega => ENNReal.ofReal (Real.sqrt
      (LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega)))) mu)
    (hlowerMeas : AEMeasurable (fun omega => ENNReal.ofReal (Real.sqrt
      ((lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega))⁻¹))) mu) :
    mu {omega | (1 + 2 * B ^ 2) / min eps 1 <
      1 + LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega) +
        (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (F omega))⁻¹} ≤
      ENNReal.ofReal eps := by
  obtain ⟨upper, lower, hupper, hlower, hupperNonneg, hlowerPos, hvfun, hufun⟩ :=
    aux_in_moments_ellipticity_tail_root_ellipticity_functions Q Q F F rfl rfl
  obtain ⟨U, V, K, _hUdef, _hUdirect, hUnorm, hU, _hVdef, _hVdirect,
      hVnorm, hV, hKdef, hK⟩ :=
    aux_in_moments_ellipticity_tail_root_square_data
      mu p B upper lower hupperNonneg hlowerPos hvfun hlowerBound
      hufun hupperBound hupperMeas hlowerMeas
  have hKdirect := aux_in_moments_ellipticity_tail_root_K_direct
    Q Q F F upper lower K rfl rfl hupper hlower hKdef
  have htail := aux_in_moments_ellipticity_tail_root_tail_apply
    (mu := mu) p eps B hp hpTwo heps hB U V K hU hV hUnorm hVnorm hK
  exact aux_in_moments_ellipticity_tail_event_transport
    mu ((1 + 2 * B ^ 2) / min eps 1) eps hKdirect htail.2



theorem in_moments_ellipticity_tail
    (d : ℕ) (hd : 2 ≤ d) (_I : _root_.SubdiffusiveProcess.Paper.in_J d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (xi : ℕ) (_hxiEven : Even xi) (hxiDim : 128 * d ≤ xi)
    (Cc disorder0 : ℝ) (_hCc : 0 < Cc)
    (_hdisorder : model.delta ≤ disorder0)
    (hlarge :
      model.delta ^ 2 ≤ Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2 ∧
      Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2 < 1 ∧
      (xi : ℝ) ≤
        Classical.choose (_root_.SubdiffusiveProcess.Section4.multiscale_response_large_cubes (d := d)) *
          (1 / 8 : ℝ) * (model.delta ^ 2)⁻¹ *
            (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2))
    (hInd : ∀ (m0 : ℕ),
      SubdiffusiveProcess.CoarseGrainingVocab.inductionHypothesis model m0 (xi : ℝ)
        (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2))
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamily : ∀ (N : ℕ) (ω : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N ω).coeffOn Q).toCoeffField x =
          scalarMatrix
            (cutoffCoefficient model
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x))
    (Jsup : ℕ → ℕ → BilateralField d → ℝ)
    (_hgreat : ∀ (N k : ℕ) (ω : BilateralField d),
      IsGreatest
        {v : ℝ | ∃ e : Fin d → ℝ,
          (∑ i : Fin d, e i ^ 2) = 1 ∧
          v = responseJ (cubeDomain (originCube d (k : ℤ)))
            ((family N ω).coeffOn (originCube d (k : ℤ))) e e}
        (Jsup N k ω))
    (_hmeas : ∀ (N k : ℕ),
      AEStronglyMeasurable (Jsup N k) (chaosSampleLaw model).toMeasure)
    (_hmoment : ∀ (N k : ℕ),
      eLpNorm (Jsup N k) (ENNReal.ofReal (xi : ℝ))
          (chaosSampleLaw model).toMeasure ≤
        ENNReal.ofReal
          (Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2))
    (_hxi : (xi : ℝ) ≤
      Cc⁻¹ * (model.delta ^ 2)⁻¹ * |Real.log model.delta|⁻¹) :
    (∀ (N : ℕ) (ω : BilateralField d) (k : ℕ),
      0 < lambdaSq (originCube d (k : ℤ)) (1 / 4)
            (MultiscaleExponent.finite 1) (family N ω) ∧
      0 ≤ LambdaSq (originCube d (k : ℤ)) (1 / 4)
            (MultiscaleExponent.finite 1) (family N ω)) ∧
    (∀ eps : ℝ, 0 < eps → ∃ A : ℝ, 0 < A ∧
      ∀ N k : ℕ,
        (chaosSampleLaw model).toMeasure
            {ω : BilateralField d |
              A < 1 +
                    LambdaSq (originCube d (k : ℤ)) (1 / 4)
                      (MultiscaleExponent.finite 1) (family N ω) +
                  (lambdaSq (originCube d (k : ℤ)) (1 / 4)
                    (MultiscaleExponent.finite 1) (family N ω))⁻¹} ≤
          ENNReal.ofReal eps) := by
  let : NeZero d := ⟨by omega⟩
  constructor
  · intro N ω k
    constructor
    · exact lambdaSq_finite_pos _ _ (by norm_num) (by norm_num)
    · exact LambdaSq_finite_nonneg _ _ (by norm_num) (by norm_num)
  · have hxiReal : 0 < (xi : ℝ) := by
      have : 0 < xi := by nlinarith [hxiDim]
      exact_mod_cast this
    have hxiOne : (1 : ℝ) ≤ (xi : ℝ) := by
      have : 1 ≤ xi := by nlinarith [hxiDim]
      exact_mod_cast this
    have hdim : 4 * (d : ℝ) * (1 / 4 : ℝ)⁻¹ ≤ (xi : ℝ) := by
      have hdim' : (128 : ℝ) * (d : ℝ) ≤ (xi : ℝ) := by
        have hc : ((128 * d : ℕ) : ℝ) ≤ (xi : ℝ) := Nat.cast_le.mpr hxiDim
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc
      calc
        4 * (d : ℝ) * (1 / 4 : ℝ)⁻¹ ≤ 128 * (d : ℝ) := by
          have hd0 : 0 ≤ (d : ℝ) := by positivity
          norm_num [div_eq_mul_inv]
          nlinarith
        _ ≤ (xi : ℝ) := hdim'
    have hlarge0 := _root_.SubdiffusiveProcess.Section4.multiscale_response_large_cubes (d := d)
    let c0 : ℝ := Classical.choose hlarge0
    let hlarge1 := Classical.choose_spec hlarge0
    let C0 : ℝ := Classical.choose hlarge1
    have hlargeSpec := Classical.choose_spec hlarge1
    have hc0 : 0 < c0 := by
      change 0 < Classical.choose hlarge0
      exact hlargeSpec.1
    have hC0 : 0 < C0 := by
      change 0 < Classical.choose (Classical.choose_spec hlarge0)
      exact hlargeSpec.2.1
    let delta1 : ℝ := Cc * (xi : ℝ) * Real.log (2 + (xi : ℝ)) * model.delta ^ 2
    have hdeltaFloor : model.delta ^ 2 ≤ delta1 := by
      simpa [delta1] using hlarge.1
    have hdeltaSmall : delta1 < 1 := by
      simpa [delta1] using hlarge.2.1
    have hxiUpper : (xi : ℝ) ≤ c0 * (1 / 4 : ℝ) *
        (model.delta ^ 2)⁻¹ * delta1 := by
      have hdeltaNonneg : 0 ≤ delta1 :=
        (sq_nonneg model.delta).trans hdeltaFloor
      have hfac : 0 ≤ c0 * (model.delta ^ 2)⁻¹ * delta1 :=
        mul_nonneg (mul_nonneg hc0.le (inv_nonneg.mpr (sq_nonneg model.delta)))
          hdeltaNonneg
      have hu : (xi : ℝ) ≤ c0 * (1 / 8 : ℝ) *
          (model.delta ^ 2)⁻¹ * delta1 := by
        change (xi : ℝ) ≤ Classical.choose hlarge0 * (1 / 8 : ℝ) *
          (model.delta ^ 2)⁻¹ * delta1
        exact hlarge.2.2
      calc
        (xi : ℝ) ≤ c0 * (1 / 8 : ℝ) *
            (model.delta ^ 2)⁻¹ * delta1 := hu
        _ = (1 / 8 : ℝ) * (c0 * (model.delta ^ 2)⁻¹ * delta1) := by ring
        _ ≤ (1 / 4 : ℝ) * (c0 * (model.delta ^ 2)⁻¹ * delta1) := by
          exact mul_le_mul_of_nonneg_right (by norm_num) hfac
        _ = c0 * (1 / 4 : ℝ) * (model.delta ^ 2)⁻¹ * delta1 := by ring
    have hxiPos : 0 < (xi : ℝ) := hxiReal
    have hsup : ∀ N k : ℕ,
        SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
          (SubdiffusiveProcess.CoarseGrainingVocab.translatedHomogenizationErrorRandom
            model N (N + k) 0 (1 / 4) 1) ≤
          ENNReal.ofReal (C0 * Real.rpow (1 / 4 : ℝ) (-(1 / (1 : ℝ))) *
            Real.sqrt delta1) := by
      intro N k
      have hlargeUse := hlargeSpec.2.2 model N (N + k) (1 / 4) delta1
        (xi : ℝ) (by norm_num) (by norm_num) hdeltaFloor hdeltaSmall
        (Nat.le_add_right N k) hdim hxiUpper (hInd (N + k))
        (N + k) (Nat.le_add_right N k) 0 1 (Or.inl rfl)
      simpa [C0] using hlargeUse
    have hsourceUpper : ∀ N k : ℕ,
        SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
          (fun source => ENNReal.ofReal (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            Homogenization.Book.Ch04.LambdaSqCoeffField
              (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1)
              (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source)))) ≤
          1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal
            (C0 * Real.rpow (1 / 4 : ℝ) (-(1 / (1 : ℝ))) * Real.sqrt delta1) := by
      intro N k
      have h := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_normalized_cutoffUpper_root_le
        model N (N + k) hxiOne
      have he := hsup N k
      calc
        _ ≤ 1 + ENNReal.ofReal (Real.sqrt 2) *
            SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
              (SubdiffusiveProcess.CoarseGrainingVocab.translatedHomogenizationErrorRandom
                model N (N + k) 0 (1 / 4) 1) := h
        _ ≤ _ := by gcongr
    have hsourceLower : ∀ N k : ℕ,
        SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
          (fun source => ENNReal.ofReal (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) *
            (Homogenization.Book.Ch04.lambdaSqCoeffField
              (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1)
              (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))⁻¹))) ≤
          1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal
            (C0 * Real.rpow (1 / 4 : ℝ) (-(1 / (1 : ℝ))) * Real.sqrt delta1) := by
      intro N k
      have h := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_normalized_cutoffLowerInv_root_le
        model N (N + k) hxiOne
      have he := hsup N k
      calc
        _ ≤ 1 + ENNReal.ofReal (Real.sqrt 2) *
            SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
              (SubdiffusiveProcess.CoarseGrainingVocab.translatedHomogenizationErrorRandom
                model N (N + k) 0 (1 / 4) 1) := h
        _ ≤ _ := by gcongr
    intro eps heps
    let E : ℝ := C0 * Real.rpow (1 / 4 : ℝ) (-(1 / (1 : ℝ))) * Real.sqrt delta1
    let B : ℝ := 1 + Real.sqrt 2 * E
    have hE : 0 ≤ E := by
      dsimp [E]
      positivity
    have hB : 0 ≤ B := by
      dsimp [B]
      positivity
    have hBpos : 0 < B := by
      dsimp [B]
      nlinarith [hE, Real.sqrt_nonneg 2]
    have hsourceUpper' : ∀ N k : ℕ,
        SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
          (fun source => ENNReal.ofReal (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            Homogenization.Book.Ch04.LambdaSqCoeffField
              (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1)
              (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source)))) ≤
          ENNReal.ofReal B := by
      intro N k
      have h := hsourceUpper N k
      have heq : 1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal E =
          ENNReal.ofReal B := by
        rw [show B = 1 + Real.sqrt 2 * E by rfl,
          ENNReal.ofReal_add (by norm_num)
            (mul_nonneg (Real.sqrt_nonneg 2) hE),
          ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
      exact h.trans_eq (by simpa [E] using heq)
    have hsourceLower' : ∀ N k : ℕ,
        SubdiffusiveProcess.CoarseGrainingVocab.paperENNRealLpNorm model.P.toMeasure (xi : ℝ)
          (fun source => ENNReal.ofReal (Real.sqrt ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) *
            (Homogenization.Book.Ch04.lambdaSqCoeffField
              (originCube d ((N + k : ℕ) : ℤ)) (1 / 4)
              (MultiscaleExponent.finite 1)
              (SubdiffusiveProcess.CoarseGrainingVocab.aCutoffRegCoeffField model N source))⁻¹))) ≤
          ENNReal.ofReal B := by
      intro N k
      have h := hsourceLower N k
      have heq : 1 + ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal E =
          ENNReal.ofReal B := by
        rw [show B = 1 + Real.sqrt 2 * E by rfl,
          ENNReal.ofReal_add (by norm_num)
            (mul_nonneg (Real.sqrt_nonneg 2) hE),
          ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
      exact h.trans_eq (by simpa [E] using heq)
    clear_value B
    let A : ℝ := (1 + 2 * B ^ 2) / min eps 1
    have hApos : 0 < A := by
      change 0 < (1 + 2 * B ^ 2) / min eps 1
      exact aux_in_moments_ellipticity_tail_threshold_pos eps B heps
    refine ⟨A, hApos, ?_⟩
    have hxiTwo := aux_in_moments_ellipticity_tail_xi_two d xi hd hxiDim
    intro N k
    have hfield := aux_in_moments_ellipticity_tail_field_law hd model N
    have htargets := aux_in_moments_ellipticity_tail_target_root_moments
      model xi N k family hfamily hfield B hB
        (hsourceUpper' N k) (hsourceLower' N k) hxiReal hxiOne
    exact aux_in_moments_ellipticity_tail_root_tail_of_moments
      (chaosSampleLaw model).toMeasure (originCube d (k : ℤ)) (family N)
      (xi : ℝ) eps B hxiReal hxiTwo heps hB
      htargets.1 htargets.2.1 htargets.2.2.1 htargets.2.2.2

end SubdiffusiveProcess.Paper
