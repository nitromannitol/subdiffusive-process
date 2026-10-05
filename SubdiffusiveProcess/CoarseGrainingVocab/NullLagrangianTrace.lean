module

public import SubdiffusiveProcess.CoarseGrainingVocab.ReciprocalLowerSupport
public import Homogenization.Sobolev.Foundations.EuclideanL2CZ
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.CanonicalFields

@[expose] public section

/-!
# Mixed-minors null Lagrangian and reciprocal Dirichlet trace bound

The argument uses a Sobolev null-Lagrangian step.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization Homogenization.Book MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## `L²` bookkeeping -/

/-- A constant matrix applied to an `L²` vector field stays in `L²`. -/
private theorem memVectorL2_matVecMul_const {U : Set (Vec d)} (H : Mat d)
    {w : Vec d → Vec d} (hw : MemVectorL2 U w) :
    MemVectorL2 U (fun x => matVecMul H (w x)) := by
  refine MeasureTheory.MemLp.of_eval ?_
  intro i
  have hcoord :
      (fun x => matVecMul H (w x) i) = fun x => ∑ j : Fin d, H i j * w x j := rfl
  rw [hcoord]
  exact memLp_finsetSum _ fun j _ => (hw.eval j).const_mul (H i j)

/-- An `L²` vector field pairs integrably against every `H^1_0` test gradient. -/
private theorem h10FluxIntegrable_of_memVectorL2 {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) : h10FluxIntegrable U F := by
  intro φ
  have hcoord : ∀ i : Fin d,
      MeasureTheory.IntegrableOn
        (fun x => F x i * φ.toH1Function.grad x i) U := by
    intro i
    simpa [Pi.mul_apply, volumeMeasureOn] using!
      (hF.eval i).integrable_mul (φ.toH1Function.gradMemL2 i)
  have hsum :
      (fun x => vecDot (F x) (φ.toH1Function.grad x)) =
        fun x => ∑ i : Fin d, F x i * φ.toH1Function.grad x i := rfl
  rw [hsum]
  exact integrable_finsetSum _ fun i _ => hcoord i

/-- Difference of two weakly divergence-free fields with integrable pairings. -/
private theorem isSolenoidalOn_sub {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : IsSolenoidalOn U F) (hG : IsSolenoidalOn U G)
    (hFint : h10FluxIntegrable U F) (hGint : h10FluxIntegrable U G) :
    IsSolenoidalOn U (fun x => F x - G x) := by
  intro φ
  have hsplit :
      (fun x => vecDot (F x - G x) (φ.toH1Function.grad x)) =
        fun x => vecDot (F x) (φ.toH1Function.grad x) -
          vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, sub_eq_add_neg]
  rw [hsplit, MeasureTheory.integral_sub (hFint φ) (hGint φ), hF φ, hG φ, sub_zero]

/-! ## The null Lagrangian -/

/-- Contracting a skew matrix against a symmetric array gives zero. -/
private theorem sum_sum_mul_eq_zero_of_transpose_eq_neg {H : Mat d}
    (hH : matTranspose H = -H) (I : Fin d → Fin d → ℝ)
    (hI : ∀ i j, I i j = I j i) :
    ∑ i : Fin d, ∑ j : Fin d, H i j * I i j = 0 := by
  have hskew : ∀ i j : Fin d, H j i = -H i j := by
    intro i j
    have h := congrFun (congrFun hH i) j
    simpa [matTranspose, Matrix.transpose_apply] using h
  have hswap :
      ∑ i : Fin d, ∑ j : Fin d, H i j * I i j =
        ∑ i : Fin d, ∑ j : Fin d, H j i * I j i :=
    Finset.sum_comm
  have hneg :
      ∑ i : Fin d, ∑ j : Fin d, H j i * I j i =
        -∑ i : Fin d, ∑ j : Fin d, H i j * I i j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hskew i j, hI j i]
    ring
  have hself := hswap.trans hneg
  linarith

/-- The constant-skew null Lagrangian: for constant skew `H` and a potential
field `f = grad u` on `U`, the field `H f` is weakly divergence free on `U`.

This is the exact vanishing that makes the shift `a |-> a - hbar` of ABK26
preserve the admissible class. -/
private theorem isSolenoidalOn_matVecMul_of_isPotentialOn_of_transpose_eq_neg
    {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpen U) {H : Mat d} (hH : matTranspose H = -H)
    {f : Vec d → Vec d} (hf : IsPotentialOn U f) :
    IsSolenoidalOn U (fun x => matVecMul H (f x)) := by
  obtain ⟨u, rfl⟩ := hf
  have hgradL2 : ∀ j : Fin d,
      MeasureTheory.MemLp (fun x => u.grad x j) 2 (volumeMeasureOn U) :=
    fun j => u.gradMemL2 j
  have hmem : MemVectorL2 U (fun x => matVecMul H (u.grad x)) :=
    memVectorL2_matVecMul_const H u.grad_memVectorL2
  refine IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hmem hU ?_
  intro ψ hψ hψs hψsub
  have hDcontDiff : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i ψ) :=
    fun i => contDiff_euclideanCoordDeriv hψ i
  have hDsupp : ∀ i : Fin d, HasCompactSupport (euclideanCoordDeriv i ψ) :=
    fun i => hasCompactSupport_euclideanCoordDeriv hψs i
  have hDsub : ∀ i : Fin d, tsupport (euclideanCoordDeriv i ψ) ⊆ U :=
    fun i => (tsupport_euclideanCoordDeriv_subset_tsupport i ψ).trans hψsub
  have hDL2 : ∀ i : Fin d,
      MeasureTheory.MemLp (euclideanCoordDeriv i ψ) 2 (volumeMeasureOn U) :=
    fun i =>
      (((hDcontDiff i).continuous).memLp_of_hasCompactSupport (hDsupp i)).restrict U
  have hInt : ∀ i j : Fin d,
      MeasureTheory.IntegrableOn
        (fun x => u.grad x j * euclideanCoordDeriv i ψ x) U := by
    intro i j
    simpa [Pi.mul_apply, volumeMeasureOn] using! (hgradL2 j).integrable_mul (hDL2 i)
  have hpoint : ∀ x : Vec d,
      vecDot (matVecMul H (u.grad x)) (fun i => (fderiv ℝ ψ x) (basisVec i)) =
        ∑ i : Fin d, ∑ j : Fin d,
          H i j * (u.grad x j * euclideanCoordDeriv i ψ x) := by
    intro x
    simp only [vecDot, matVecMul, euclideanCoordDeriv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  have hIBP : ∀ i j : Fin d,
      (∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x ∂MeasureTheory.volume) =
        -∫ x in U, u.toFun x * euclideanCoordSecondDeriv i j ψ x
          ∂MeasureTheory.volume := by
    intro i j
    have hweak :
        (∫ x in U, u.toFun x * euclideanCoordSecondDeriv i j ψ x
            ∂MeasureTheory.volume) =
          -∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x
            ∂MeasureTheory.volume :=
      u.hasWeakGradient j (euclideanCoordDeriv i ψ) (hDcontDiff i)
        (hDsupp i) (hDsub i)
    rw [hweak]
    ring
  have hIsymm : ∀ i j : Fin d,
      (∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x ∂MeasureTheory.volume) =
        ∫ x in U, u.grad x i * euclideanCoordDeriv j ψ x ∂MeasureTheory.volume := by
    intro i j
    rw [hIBP i j, hIBP j i, euclideanCoordSecondDeriv_comm_fun hψ i j]
  calc
    (∫ x in U,
        vecDot (matVecMul H (u.grad x)) (fun i => (fderiv ℝ ψ x) (basisVec i))
          ∂MeasureTheory.volume)
        = ∫ x in U,
            (∑ i : Fin d, ∑ j : Fin d,
              H i j * (u.grad x j * euclideanCoordDeriv i ψ x))
              ∂MeasureTheory.volume :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ i : Fin d, ∫ x in U,
            (∑ j : Fin d, H i j * (u.grad x j * euclideanCoordDeriv i ψ x))
              ∂MeasureTheory.volume := by
          refine integral_finsetSum _ ?_
          intro i _
          exact integrable_finsetSum _
            fun j _ => (hInt i j).const_mul (H i j)
    _ = ∑ i : Fin d, ∑ j : Fin d,
            H i j *
              ∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x
                ∂MeasureTheory.volume := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [integral_finsetSum _
            fun j _ => (hInt i j).const_mul (H i j)]
          exact Finset.sum_congr rfl fun j _ =>
            MeasureTheory.integral_const_mul _ _
    _ = 0 :=
        sum_sum_mul_eq_zero_of_transpose_eq_neg hH
          (fun i j => ∫ x in U, u.grad x j * euclideanCoordDeriv i ψ x
            ∂MeasureTheory.volume)
          hIsymm

/-! ## Coordinate mixed minors -/

private def coordinateSkew {d : ℕ} (i j : Fin d) : Mat d :=
  Matrix.single i j 1 - Matrix.single j i 1

private theorem coordinateSkew_transpose {d : ℕ} (i j : Fin d) :
    matTranspose (coordinateSkew i j) = -coordinateSkew i j := by
  ext r c
  simp [coordinateSkew, matTranspose, Matrix.transpose_apply, Matrix.single, and_comm]

private theorem vecDot_coordinateSkew_mulVec {d : ℕ} (i j : Fin d)
    (f g : Vec d) :
    vecDot (matVecMul (coordinateSkew i j) g) f =
      f i * g j - f j * g i := by
  classical
  simp only [coordinateSkew, vecDot, matVecMul, Matrix.sub_apply, sub_mul,
    Finset.sum_sub_distrib]
  simp [Matrix.single, eq_comm, and_comm, ite_and]
  ring

/-- Each polarized second minor of two zero-trace Sobolev gradients has zero
integral. -/
private theorem integral_mixed_gradient_minor_eq_zero {d : ℕ}
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpen U)
    (phi psi : H10Function U) (i j : Fin d) :
    ∫ x in U,
        (phi.toH1Function.grad x i * psi.toH1Function.grad x j -
          phi.toH1Function.grad x j * psi.toH1Function.grad x i) ∂volume = 0 := by
  have hsol := isSolenoidalOn_matVecMul_of_isPotentialOn_of_transpose_eq_neg
    hU (coordinateSkew_transpose i j) psi.toH1Function.isPotentialOn
  have hzero := hsol phi
  rw [show (fun x => vecDot
      (matVecMul (coordinateSkew i j) (psi.toH1Function.grad x))
      (phi.toH1Function.grad x)) =
      fun x => phi.toH1Function.grad x i * psi.toH1Function.grad x j -
        phi.toH1Function.grad x j * psi.toH1Function.grad x i by
    funext x
    exact vecDot_coordinateSkew_mulVec i j _ _] at hzero
  exact hzero

/-- A mixed second minor of two Dirichlet fields with affine boundary data
`e_i` and `e_j` has normalized average one. -/
private theorem volumeAverage_mixed_minor_eq_one {d : ℕ}
    (U : Ch02.Domain d) (u v : H1Function (U : Set (Vec d)))
    (i j : Fin d) (hij : i ≠ j)
    (hu : Ch02.IsSymmetricDirichletAdmissible U (basisVec i) u)
    (hv : Ch02.IsSymmetricDirichletAdmissible U (basisVec j) v) :
    volumeAverage (U : Set (Vec d)) (fun x =>
      u.grad x i * v.grad x j - u.grad x j * v.grad x i) = 1 := by
  rcases hu with ⟨huMem, phi, hphi⟩
  rcases hv with ⟨hvMem, psi, hpsi⟩
  have hphiZero := phi.isPotentialZeroTraceOn.integral_eq_zero
  have hpsiZero := psi.isPotentialZeroTraceOn.integral_eq_zero
  have hphiZeroI : ∫ x in (U : Set (Vec d)), phi.toH1Function.grad x i ∂volume = 0 := by
    simpa using congrFun hphiZero i
  have hpsiZeroJ : ∫ x in (U : Set (Vec d)), psi.toH1Function.grad x j ∂volume = 0 := by
    simpa using congrFun hpsiZero j
  have hminorZero := integral_mixed_gradient_minor_eq_zero U.isOpen phi psi i j
  have hpoint : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      u.grad x i * v.grad x j - u.grad x j * v.grad x i =
        1 + phi.toH1Function.grad x i + psi.toH1Function.grad x j +
          (phi.toH1Function.grad x i * psi.toH1Function.grad x j -
            phi.toH1Function.grad x j * psi.toH1Function.grad x i) := by
    filter_upwards [hphi, hpsi] with x hphix hpsix
    have hphic (r : Fin d) := congrFun hphix r
    have hpsic (r : Fin d) := congrFun hpsix r
    have hui : u.grad x i = phi.toH1Function.grad x i + 1 := by
      simpa [basisVec] using sub_eq_iff_eq_add.mp (hphic i)
    have huj : u.grad x j = phi.toH1Function.grad x j := by
      have hji : j ≠ i := Ne.symm hij
      simpa [basisVec, hji] using sub_eq_iff_eq_add.mp (hphic j)
    have hvj : v.grad x j = psi.toH1Function.grad x j + 1 := by
      simpa [basisVec] using sub_eq_iff_eq_add.mp (hpsic j)
    have hvi : v.grad x i = psi.toH1Function.grad x i := by
      simpa [basisVec, hij] using sub_eq_iff_eq_add.mp (hpsic i)
    rw [hui, huj, hvj, hvi]
    ring
  have hphiInt : IntegrableOn (fun x => phi.toH1Function.grad x i)
      (U : Set (Vec d)) :=
    (phi.toH1Function.gradMemL2 i).integrable (by norm_num)
  have hpsiInt : IntegrableOn (fun x => psi.toH1Function.grad x j)
      (U : Set (Vec d)) :=
    (psi.toH1Function.gradMemL2 j).integrable (by norm_num)
  have hminorInt : IntegrableOn (fun x =>
      phi.toH1Function.grad x i * psi.toH1Function.grad x j -
        phi.toH1Function.grad x j * psi.toH1Function.grad x i)
      (U : Set (Vec d)) :=
    ((phi.toH1Function.gradMemL2 i).integrable_mul
      (psi.toH1Function.gradMemL2 j)).sub
      ((phi.toH1Function.gradMemL2 j).integrable_mul
        (psi.toH1Function.gradMemL2 i))
  have honeInt : IntegrableOn (fun _ : Vec d => (1 : ℝ)) (U : Set (Vec d)) :=
    integrableOn_const (hs :=
      (U.isDomain.toBoundedMeasurableDomain U.nonempty).volume_ne_top)
  have hsplitPhi :
      (∫ x : Vec d, 1 + phi.toH1Function.grad x i
        ∂volumeMeasureOn (U : Set (Vec d))) =
      (∫ _x : Vec d, (1 : ℝ) ∂volumeMeasureOn (U : Set (Vec d))) +
        ∫ x : Vec d, phi.toH1Function.grad x i
          ∂volumeMeasureOn (U : Set (Vec d)) := by
    simpa only [Pi.add_apply] using integral_add honeInt hphiInt
  have hsplitPsi :
      (∫ x : Vec d,
          (1 + phi.toH1Function.grad x i) + psi.toH1Function.grad x j
          ∂volumeMeasureOn (U : Set (Vec d))) =
      (∫ x : Vec d, 1 + phi.toH1Function.grad x i
        ∂volumeMeasureOn (U : Set (Vec d))) +
        ∫ x : Vec d, psi.toH1Function.grad x j
          ∂volumeMeasureOn (U : Set (Vec d)) := by
    simpa only [Pi.add_apply] using integral_add (honeInt.add hphiInt) hpsiInt
  have hintegral :
      ∫ x in (U : Set (Vec d)),
          (u.grad x i * v.grad x j - u.grad x j * v.grad x i) ∂volume =
        (volume (U : Set (Vec d))).toReal := by
    rw [integral_congr_ae hpoint]
    change (∫ x : Vec d,
        ((1 + phi.toH1Function.grad x i) + psi.toH1Function.grad x j) +
          (phi.toH1Function.grad x i * psi.toH1Function.grad x j -
            phi.toH1Function.grad x j * psi.toH1Function.grad x i)
        ∂volumeMeasureOn (U : Set (Vec d))) = _
    calc
      _ = (∫ x : Vec d,
            (1 + phi.toH1Function.grad x i) + psi.toH1Function.grad x j
            ∂volumeMeasureOn (U : Set (Vec d))) +
          ∫ x : Vec d,
            (phi.toH1Function.grad x i * psi.toH1Function.grad x j -
              phi.toH1Function.grad x j * psi.toH1Function.grad x i)
            ∂volumeMeasureOn (U : Set (Vec d)) :=
        integral_add (honeInt.add hphiInt |>.add hpsiInt) hminorInt
      _ = ((∫ x : Vec d, 1 + phi.toH1Function.grad x i
              ∂volumeMeasureOn (U : Set (Vec d))) +
            ∫ x : Vec d, psi.toH1Function.grad x j
              ∂volumeMeasureOn (U : Set (Vec d))) + 0 := by
        rw [hsplitPsi, hminorZero]
      _ = (((∫ _x : Vec d, (1 : ℝ)
              ∂volumeMeasureOn (U : Set (Vec d))) + 0) + 0) + 0 := by
        rw [hsplitPhi, hphiZeroI, hpsiZeroJ]
      _ = (volume (U : Set (Vec d))).toReal := by
        simp [measureReal_def]
  unfold volumeAverage
  rw [hintegral]
  exact inv_mul_cancel₀
    (Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U).ne'

/-! ## Dirichlet-frame energies -/

-- Energy-integrability lemma.

private theorem coefficientEnergyIntegrable {d : ℕ} {U : Ch02.Domain d}
    (a : Ch02.CoeffOn U) (u : H1Function (U : Set (Vec d))) :
    IntegrableOn
      (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
      (U : Set (Vec d)) volume := by
  have hflux : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (a.toCoeffField x) (u.grad x)) :=
    (Ch05.Section53.JUpperBoundWeakNorms.ch02_coeffOn_isAEEllipticFieldOn a).memVectorL2_matVecMul
      u.grad_memVectorL2
  exact integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hflux

private theorem scalar_energy_integrand_eq {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (u : H1Function (U : Set (Vec d))) :
    (fun x => vecDot (u.grad x)
        (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x))) =
      fun x => a x * ∑ j : Fin d, (u.grad x j) ^ 2 := by
  funext x
  change vecDot (u.grad x) (matVecMul (scalarMatrix (a x)) (u.grad x)) = _
  rw [matVecMul_scalarMatrix, vecDot_smul_right]
  unfold vecDot
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  ring

private theorem volumeAverage_finset_sum_local {d : ℕ} {U : Set (Vec d)}
    {I : Type} [Fintype I] [DecidableEq I] (s : Finset I)
    (f : I → Vec d → ℝ) (hf : ∀ i ∈ s, IntegrableOn (f i) U) :
    volumeAverage U (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, volumeAverage U (f i) := by
  unfold volumeAverage
  rw [integral_finsetSum s hf, Finset.mul_sum]

private theorem volumeAverage_mono_ae_local {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → ℝ} (hf : IntegrableOn f U) (hg : IntegrableOn g U)
    (hfg : f ≤ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f ≤ volumeAverage U g := by
  unfold volumeAverage
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hfg)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

private theorem volumeAverage_scalar_gradient_sq_eq_diagonal {d : ℕ}
    {U : Ch02.Domain d} {a : Vec d → ℝ} (ha : ScalarCoeffOnData U a)
    (i : Fin d) (u : H1Function (U : Set (Vec d)))
    (hu : Ch02.IsSymmetricDirichletMinimizer U ha.toCoeffOn (basisVec i) u) :
    volumeAverage (U : Set (Vec d))
        (fun x => a x * ∑ j : Fin d, (u.grad x j) ^ 2) =
      aMatrix U ha.toCoeffOn i i := by
  let theory := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  have hscalar := scalar_energy_integrand_eq ha u
  have henergy :
      Ch02.symmetricDirichletEnergyValue U ha.toCoeffOn u =
        (1 / 2 : ℝ) * volumeAverage (U : Set (Vec d))
          (fun x => a x * ∑ j : Fin d, (u.grad x j) ^ 2) := by
    unfold Ch02.symmetricDirichletEnergyValue
    rw [show (fun x => (1 / 2 : ℝ) *
        vecDot (u.grad x) (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x))) =
      (1 / 2 : ℝ) • fun x => vecDot (u.grad x)
        (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x)) by
          funext x; simp]
    change volumeAverage (U : Set (Vec d))
        ((1 / 2 : ℝ) • fun x => vecDot (u.grad x)
          (matVecMul (ha.toCoeffOn.toCoeffField x) (u.grad x))) = _
    rw [volumeAverage_smul]
    rw [hscalar]
  have hnu :=
    Homogenization.Internal.Ch02.BookCh02.symmetricDirichletNu_eq_of_minimizer hu
  have hmatrix := theory.dirichlet_value_by_sigma (basisVec i)
  rw [henergy, hmatrix] at hnu
  rw [← theory.derived_matrices.1] at hnu
  have hdiag :
      vecDot (basisVec i) (matVecMul (aMatrix U ha.toCoeffOn) (basisVec i)) =
        aMatrix U ha.toCoeffOn i i := by
    rw [vecDot_basisVec_left]
    change (∑ j : Fin d, aMatrix U ha.toCoeffOn i j * basisVec i j) = _
    rw [Finset.sum_eq_single i]
    · simp [basisVec]
    · intro j _hj hji
      simp [basisVec, hji]
    · intro hi
      simp at hi
  rw [hdiag] at hnu
  linarith

/-! ## Sharp finite-dimensional inequality -/

private theorem two_mul_le_weighted_squares {a x y : ℝ} (ha : 0 < a) :
    2 * (x * y) ≤ a * x ^ 2 + a⁻¹ * y ^ 2 := by
  have hainv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
  have hs : 0 ≤ (a * x - y) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg ha.le hs]

private theorem sum_erase_swap {d : ℕ} (G : Fin d → Fin d → ℝ) :
    Finset.univ.sum (fun i : Fin d =>
        ((Finset.univ : Finset (Fin d)).erase i).sum (fun j => G i j)) =
      Finset.univ.sum (fun i : Fin d =>
        ((Finset.univ : Finset (Fin d)).erase i).sum (fun j => G j i)) := by
  have hexpand (i : Fin d) :
      ((Finset.univ : Finset (Fin d)).erase i).sum (fun j => G i j) =
        Finset.univ.sum (fun j => if j = i then 0 else G i j) := by
    calc
      _ = ((Finset.univ : Finset (Fin d)).erase i).sum
          (fun j => if j = i then 0 else G i j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_erase] at hj
        simp [hj.1]
      _ = _ := Finset.sum_erase (s := Finset.univ) (by simp)
  have hexpandSwap (i : Fin d) :
      ((Finset.univ : Finset (Fin d)).erase i).sum (fun j => G j i) =
        Finset.univ.sum (fun j => if j = i then 0 else G j i) := by
    calc
      _ = ((Finset.univ : Finset (Fin d)).erase i).sum
          (fun j => if j = i then 0 else G j i) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_erase] at hj
        simp [hj.1]
      _ = _ := Finset.sum_erase (s := Finset.univ) (by simp)
  simp_rw [hexpand, hexpandSwap]
  rw [Finset.sum_comm]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases h : j = i
  · subst j
    simp
  · simp [h, Ne.symm h]

private theorem sum_offDiagonal_pair_energy_le {d : ℕ} (hd : 2 ≤ d)
    (E : Fin d → Fin d → ℝ) :
    Finset.univ.sum (fun i : Fin d =>
        ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
          (E i i) ^ 2 + (E i j) ^ 2)) ≤
      (d - 1 : ℝ) * ∑ i : Fin d, ∑ j : Fin d, (E i j) ^ 2 := by
  let diag : ℝ := ∑ i : Fin d, (E i i) ^ 2
  let off : ℝ := Finset.univ.sum (fun i : Fin d =>
    ((Finset.univ : Finset (Fin d)).erase i).sum (fun j => (E i j) ^ 2))
  have hoff : 0 ≤ off := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg (E i j)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdim : (1 : ℝ) ≤ d - 1 := by linarith
  have hall : ∑ i : Fin d, ∑ j : Fin d, (E i j) ^ 2 = diag + off := by
    dsimp [diag, off]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin d))
      (fun j => (E i j) ^ 2) (Finset.mem_univ i)]
    ring
  have hpairs :
      Finset.univ.sum (fun i : Fin d =>
        ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
          (E i i) ^ 2 + (E i j) ^ 2)) =
        (d - 1 : ℝ) * diag + off := by
    dsimp [diag, off]
    simp_rw [Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  rw [hpairs, hall]
  nlinarith

private theorem mixed_minor_pair_sum_le_energy {d : ℕ} (hd : 2 ≤ d)
    (a : ℝ) (ha : 0 < a) (E F : Fin d → Fin d → ℝ) :
    2 * Finset.univ.sum (fun i : Fin d =>
      ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
        E i i * F j j - E i j * F j i)) ≤
      (d - 1 : ℝ) *
        (a * (∑ i : Fin d, ∑ j : Fin d, (E i j) ^ 2) +
          a⁻¹ * (∑ i : Fin d, ∑ j : Fin d, (F i j) ^ 2)) := by
  have hpair (i j : Fin d) :
      2 * (E i i * F j j - E i j * F j i) ≤
        a * ((E i i) ^ 2 + (E i j) ^ 2) +
          a⁻¹ * ((F j j) ^ 2 + (F j i) ^ 2) := by
    have h₁ := two_mul_le_weighted_squares (a := a) (x := E i i) (y := F j j) ha
    have h₂ := two_mul_le_weighted_squares (a := a) (x := E i j) (y := -F j i) ha
    nlinarith
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j
      (_hj : j ∈ (Finset.univ : Finset (Fin d)).erase i) => hpair i j
  have hE := sum_offDiagonal_pair_energy_le hd E
  have hFraw := sum_offDiagonal_pair_energy_le hd F
  have hF :
      Finset.univ.sum (fun i : Fin d =>
        ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
          (F j j) ^ 2 + (F j i) ^ 2)) ≤
        (d - 1 : ℝ) * ∑ i : Fin d, ∑ j : Fin d, (F i j) ^ 2 := by
    -- Swapping the dummy indices preserves the off-diagonal sum.
    rw [← sum_erase_swap (fun i j => (F i i) ^ 2 + (F i j) ^ 2)]
    exact hFraw
  have ha0 : 0 ≤ a := ha.le
  have hai0 : 0 ≤ a⁻¹ := (inv_pos.mpr ha).le
  calc
    2 * Finset.univ.sum (fun i : Fin d =>
      ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
        E i i * F j j - E i j * F j i)) =
      Finset.univ.sum (fun i : Fin d =>
        ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
          2 * (E i i * F j j - E i j * F j i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ ≤ Finset.univ.sum (fun i : Fin d =>
      ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
        a * ((E i i) ^ 2 + (E i j) ^ 2) +
          a⁻¹ * ((F j j) ^ 2 + (F j i) ^ 2))) := hsum
    _ = a * Finset.univ.sum (fun i : Fin d =>
        ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
          (E i i) ^ 2 + (E i j) ^ 2)) +
        a⁻¹ * Finset.univ.sum (fun i : Fin d =>
          ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
            (F j j) ^ 2 + (F j i) ^ 2)) := by
      calc
        _ = Finset.univ.sum (fun i : Fin d =>
              a * ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
                (E i i) ^ 2 + (E i j) ^ 2) +
              a⁻¹ * ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
                (F j j) ^ 2 + (F j i) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * ((d - 1 : ℝ) * ∑ i : Fin d, ∑ j : Fin d, (E i j) ^ 2) +
        a⁻¹ * ((d - 1 : ℝ) * ∑ i : Fin d, ∑ j : Fin d, (F i j) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hE ha0)
        (mul_le_mul_of_nonneg_left hF hai0)
    _ = _ := by ring

/-! ## Reciprocal trace lower bound -/

/-- The mixed-second-minors null Lagrangian gives the paper's sharp reciprocal
Dirichlet trace inequality. This discharges the deterministic residue at
`e.reciprocal.finite.volume.isotropy`. -/
theorem reciprocalDirichletTraceLower {d : ℕ}
    (hd : 2 ≤ d) (U : Ch02.Domain d) (a : Vec d → ℝ)
    (ha : ScalarCoeffOnData U a)
    (haInv : ScalarCoeffOnData U (fun x => (a x)⁻¹)) :
    2 * (d : ℝ) ≤
      Matrix.trace (aMatrix U ha.toCoeffOn) +
        Matrix.trace (aMatrix U haInv.toCoeffOn) := by
  let theoryA := Ch02.responseSymmetricDirichletNeumannTheory U ha.toCoeffOn ha.isSymmetric
  let theoryB := Ch02.responseSymmetricDirichletNeumannTheory U haInv.toCoeffOn haInv.isSymmetric
  choose u hu using fun i : Fin d => theoryA.dirichlet_minimizer_exists (basisVec i)
  choose v hv using fun i : Fin d => theoryB.dirichlet_minimizer_exists (basisVec i)
  let E : Vec d → Fin d → Fin d → ℝ := fun x i j => (u i).grad x j
  let F : Vec d → Fin d → Fin d → ℝ := fun x i j => (v i).grad x j
  let minorSum : Vec d → ℝ := fun x =>
    Finset.univ.sum (fun i : Fin d =>
      ((Finset.univ : Finset (Fin d)).erase i).sum (fun j =>
        E x i i * F x j j - E x i j * F x j i))
  let energyA : Vec d → ℝ := fun x =>
    ∑ i : Fin d, a x * ∑ j : Fin d, (E x i j) ^ 2
  let energyB : Vec d → ℝ := fun x =>
    ∑ i : Fin d, (a x)⁻¹ * ∑ j : Fin d, (F x i j) ^ 2
  have hminorInt : IntegrableOn minorSum (U : Set (Vec d)) := by
    dsimp [minorSum, E, F]
    refine integrable_finsetSum _ fun i _hi => integrable_finsetSum _ fun j _hj => ?_
    exact ((u i).gradMemL2 i).integrable_mul ((v j).gradMemL2 j) |>.sub
      (((u i).gradMemL2 j).integrable_mul ((v j).gradMemL2 i))
  have henergyAInt : IntegrableOn energyA (U : Set (Vec d)) := by
    dsimp [energyA, E]
    refine integrable_finsetSum _ fun i _hi => ?_
    rw [← scalar_energy_integrand_eq ha (u i)]
    exact coefficientEnergyIntegrable ha.toCoeffOn (u i)
  have henergyBInt : IntegrableOn energyB (U : Set (Vec d)) := by
    dsimp [energyB, F]
    refine integrable_finsetSum _ fun i _hi => ?_
    rw [← scalar_energy_integrand_eq haInv (v i)]
    exact coefficientEnergyIntegrable haInv.toCoeffOn (v i)
  have hpoint :
      (fun x => 2 * minorSum x) ≤ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => (d - 1 : ℝ) * (energyA x + energyB x) := by
    filter_upwards [ha.aeBounds] with x hx
    have hax : 0 < a x := lt_of_lt_of_le ha.lam_pos hx.1
    simpa only [minorSum, energyA, energyB, E, F, Finset.mul_sum] using
      mixed_minor_pair_sum_le_energy hd (a x) hax (E x) (F x)
  have havg := volumeAverage_mono_ae_local (hminorInt.const_mul 2)
    ((henergyAInt.add henergyBInt).const_mul (d - 1 : ℝ)) hpoint
  have hminorAvg :
      volumeAverage (U : Set (Vec d)) minorSum = (d : ℝ) * (d - 1 : ℝ) := by
    dsimp [minorSum]
    rw [volumeAverage_finset_sum_local Finset.univ]
    · calc
        _ = Finset.univ.sum (fun i : Fin d =>
            ((Finset.univ : Finset (Fin d)).erase i).sum (fun _j => (1 : ℝ))) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [volumeAverage_finset_sum_local
            ((Finset.univ : Finset (Fin d)).erase i)]
          · apply Finset.sum_congr rfl
            intro j hj
            rw [volumeAverage_mixed_minor_eq_one U (u i) (v j) i j
              (Ne.symm (Finset.mem_erase.mp hj).1) (hu i).1 (hv j).1]
          · intro j _hj
            exact ((u i).gradMemL2 i).integrable_mul ((v j).gradMemL2 j) |>.sub
              (((u i).gradMemL2 j).integrable_mul ((v j).gradMemL2 i))
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_erase_of_mem, Finset.mem_univ,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Nat.cast_sub (by omega : 1 ≤ d)]
          ring
    · intro i _hi
      exact integrable_finsetSum _ fun j _hj =>
        ((u i).gradMemL2 i).integrable_mul ((v j).gradMemL2 j) |>.sub
          (((u i).gradMemL2 j).integrable_mul ((v j).gradMemL2 i))
  have henergyAAvg :
      volumeAverage (U : Set (Vec d)) energyA =
        Matrix.trace (aMatrix U ha.toCoeffOn) := by
    dsimp [energyA, E]
    rw [volumeAverage_finset_sum_local Finset.univ]
    · apply Finset.sum_congr rfl
      intro i _hi
      exact volumeAverage_scalar_gradient_sq_eq_diagonal ha i (u i) (hu i)
    · intro i _hi
      rw [← scalar_energy_integrand_eq ha (u i)]
      exact coefficientEnergyIntegrable ha.toCoeffOn (u i)
  have henergyBAvg :
      volumeAverage (U : Set (Vec d)) energyB =
        Matrix.trace (aMatrix U haInv.toCoeffOn) := by
    dsimp [energyB, F]
    rw [volumeAverage_finset_sum_local Finset.univ]
    · apply Finset.sum_congr rfl
      intro i _hi
      exact volumeAverage_scalar_gradient_sq_eq_diagonal haInv i (v i) (hv i)
    · intro i _hi
      rw [← scalar_energy_integrand_eq haInv (v i)]
      exact coefficientEnergyIntegrable haInv.toCoeffOn (v i)
  have hleft :
      volumeAverage (U : Set (Vec d)) (fun x => 2 * minorSum x) =
        2 * volumeAverage (U : Set (Vec d)) minorSum := by
    rw [show (fun x => 2 * minorSum x) = (2 : ℝ) • minorSum by
      funext x; simp, volumeAverage_smul]
  have hright :
      volumeAverage (U : Set (Vec d))
          (fun x => (d - 1 : ℝ) * (energyA x + energyB x)) =
        (d - 1 : ℝ) *
          (volumeAverage (U : Set (Vec d)) energyA +
            volumeAverage (U : Set (Vec d)) energyB) := by
    rw [show (fun x => (d - 1 : ℝ) * (energyA x + energyB x)) =
        (d - 1 : ℝ) • (energyA + energyB) by funext x; simp]
    rw [volumeAverage_smul, volumeAverage_add henergyAInt henergyBInt]
  change
    volumeAverage (U : Set (Vec d)) (fun x => 2 * minorSum x) ≤
      volumeAverage (U : Set (Vec d))
        (fun x => (d - 1 : ℝ) * (energyA x + energyB x)) at havg
  rw [hleft, hright, hminorAvg, henergyAAvg, henergyBAvg] at havg
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith


end

end SubdiffusiveProcess.CoarseGrainingVocab
