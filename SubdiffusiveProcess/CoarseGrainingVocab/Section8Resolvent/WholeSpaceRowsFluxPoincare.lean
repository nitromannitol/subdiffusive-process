module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsHodge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDescendantEllipticity
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.CanonicalFields
public import Homogenization.Probability.LocalEllipticitySlices.SymmetricL2
public import Homogenization.Deterministic.CoarsePoincareRHS.ForceLocalization
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph

@[expose] public section

/-!
# The flux clause of the coarse-grained Poincare inequality with right-hand side

Work in progress.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization.Book.Ch03
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- `√(a+b) ≤ √a + √b`. -/
private theorem sqrt_add_le_sqrt_add_sqrt' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hna := Real.sqrt_nonneg a
  have hnb := Real.sqrt_nonneg b
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by nlinarith
  calc
    Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
      Real.sqrt_le_sqrt h1
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-! ## The coarse control of a solenoidal field's cube average -/



private theorem coefficientEnergyIntegrable' {U : Ch02.Domain d}
    (a : Ch02.CoeffOn U) (u : H1Function (U : Set (Vec d))) :
    IntegrableOn
      (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
      (U : Set (Vec d)) volume := by
  have hflux : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (a.toCoeffField x) (u.grad x)) :=
    (Ch05.Section53.JUpperBoundWeakNorms.ch02_coeffOn_isAEEllipticFieldOn
      a).memVectorL2_matVecMul u.grad_memVectorL2
  exact integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hflux



private theorem inverseCoefficientEnergyIntegrable' {U : Ch02.Domain d}
    (a : Ch02.CoeffOn U) (hsym : a.IsSymmetric)
    (h : Vec d → Vec d) (hh : MemVectorL2 (U : Set (Vec d)) h) :
    IntegrableOn
      (fun x => vecDot (h x) (matVecMul (a.toCoeffField x)⁻¹ (h x)))
      (U : Set (Vec d)) volume := by
  let b : Ch02.CoeffOn U := Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn U a
  have hba : Ch02.CoeffOn.AEEq b a := by
    simpa [b] using Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a
  have hEll : IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a
  have hinv : MemVectorL2 (U : Set (Vec d))
      (fun x => matVecMul (symmPart (b.toCoeffField x))⁻¹ (h x)) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hh
  have hbase : IntegrableOn
      (fun x => vecDot (h x) (matVecMul (symmPart (b.toCoeffField x))⁻¹ (h x)))
      (U : Set (Vec d)) volume :=
    integrableOn_vecDot_of_memVectorL2 hh hinv
  refine hbase.congr ?_
  filter_upwards [hsym, hba] with x hsymm hba_x
  rw [hba_x]
  have hs : symmPart (a.toCoeffField x) = a.toCoeffField x := by
    ext i j
    have hij : a.toCoeffField x j i = a.toCoeffField x i j :=
      (Matrix.IsSymm.ext_iff.mp hsymm) i j
    simp [symmPart, hij]
  rw [hs]



theorem solenoidalAverageInverseEnergyControl (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) (hsym : a.IsSymmetric)
    (h : Vec d → Vec d) (hh : MemVectorL2 (U : Set (Vec d)) h)
    (hsol : IsSolenoidalOn (U : Set (Vec d)) h) :
    vecNormSq (Ch02.averageVec U h) ≤
      Ch02.matrixNorm (Ch02.bCoarse U a) *
        Ch02.average U
          (fun x => vecDot (h x) (matVecMul (a.toCoeffField x)⁻¹ (h x))) := by
  let theory := Ch02.responseSymmetricDirichletNeumannTheory U a hsym
  let avg : Vec d := Ch02.averageVec U h
  let B : Mat d := Ch02.bCoarse U a
  let p : Vec d := matVecMul B⁻¹ avg
  obtain ⟨v, hv⟩ := theory.dirichlet_minimizer_exists p
  have hBdet : IsUnit B.det :=
    (Matrix.isUnit_iff_isUnit_det (A := B)).mp (Ch02.bCoarse_posDef U a).isUnit
  have hBmul : ∀ ξ : Vec d, matVecMul B (matVecMul B⁻¹ ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Matrix.mul_nonsing_inv B hBdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hBp : matVecMul B p = avg := by
    simpa [p] using hBmul avg
  have hBsig : B = Ch02.sigmaCoarse U a := by
    exact theory.derived_matrices.2.2
  have hminValue :
      Ch02.symmetricDirichletEnergyValue U a v =
        (1 / 2 : ℝ) * vecDot p (matVecMul B p) := by
    rw [← Homogenization.Internal.Ch02.BookCh02.symmetricDirichletNu_eq_of_minimizer hv,
      theory.dirichlet_value_by_sigma, ← hBsig]
  have henergyInt := coefficientEnergyIntegrable' a v
  have hdirichletEnergy :
      Ch02.symmetricDirichletEnergyValue U a v =
        (1 / 2 : ℝ) * Ch02.average U
          (fun x => vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x))) := by
    unfold Ch02.symmetricDirichletEnergyValue
    change volumeAverage (U : Set (Vec d))
        (fun x => 1 / 2 * vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x))) =
      1 / 2 * volumeAverage (U : Set (Vec d))
        (fun x => vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x)))
    rw [show (fun x => 1 / 2 * vecDot (v.grad x)
          (matVecMul (a.toCoeffField x) (v.grad x))) =
        (1 / 2 : ℝ) • fun x => vecDot (v.grad x)
          (matVecMul (a.toCoeffField x) (v.grad x)) by
        funext x; simp,
      volumeAverage_smul]
  have henergyEq :
      Ch02.average U
          (fun x => vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x))) =
        vecDot avg (matVecMul B⁻¹ avg) := by
    rw [hdirichletEnergy] at hminValue
    have hpquad : vecDot p (matVecMul B p) = vecDot avg (matVecMul B⁻¹ avg) := by
      rw [hBp]
      simp [p, vecDot_comm]
    rw [hpquad] at hminValue
    linarith
  have hpot : IsPotentialZeroTraceOn (U : Set (Vec d)) (fun x => v.grad x - p) :=
    Homogenization.Internal.Ch02.BookCh02.isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn
      hv.1
  have hzero : ∫ x in (U : Set (Vec d)), vecDot (h x) (v.grad x - p) = 0 := by
    obtain ⟨φ, hφ⟩ := hpot
    have hz := hsol φ
    rwa [hφ] at hz
  have hhGrad : IntegrableOn (fun x => vecDot (h x) (v.grad x))
      (U : Set (Vec d)) volume :=
    integrableOn_vecDot_of_memVectorL2 hh v.grad_memVectorL2
  have hhConst : IntegrableOn (fun x => vecDot (h x) p)
      (U : Set (Vec d)) volume :=
    (CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 p hh).congr_fun
      (fun x _hx => vecDot_comm p (h x)) U.measurableSet
  have hpairIntegral :
      (∫ x in (U : Set (Vec d)), vecDot (h x) (v.grad x)) =
        ∫ x in (U : Set (Vec d)), vecDot (h x) p := by
    have hsplit :
        (∫ x in (U : Set (Vec d)), vecDot (h x) (v.grad x - p)) =
          (∫ x in (U : Set (Vec d)), vecDot (h x) (v.grad x)) -
            ∫ x in (U : Set (Vec d)), vecDot (h x) p := by
      rw [← integral_sub hhGrad hhConst]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [vecDot, Pi.sub_apply]
        calc
          ∑ i, h x i * (v.grad x i - p i) =
              ∑ i, (h x i * v.grad x i - h x i * p i) := by
                apply Finset.sum_congr rfl
                intro i _hi
                ring
          _ = (∑ i, h x i * v.grad x i) - ∑ i, h x i * p i := by
            rw [Finset.sum_sub_distrib]
    rw [hsplit] at hzero
    linarith
  have hhCoord : ∀ i, IntegrableOn (fun x => h x i) (U : Set (Vec d)) := by
    intro i
    exact CorrectionFieldData.integrableOn_coord_of_memVectorL2 hh i
  have hpair :
      Ch02.average U (fun x => vecDot (h x) (v.grad x)) = vecDot avg p := by
    have hright :
        volumeAverage (U : Set (Vec d)) (fun x => vecDot (h x) p) = vecDot avg p := by
      simpa [Ch02.averageVec, Ch02.average, avg] using!
        volumeAverage_vecDot_right (U := (U : Set (Vec d))) h p hhCoord
    have havgPair :
        volumeAverage (U : Set (Vec d)) (fun x => vecDot (h x) (v.grad x)) =
          volumeAverage (U : Set (Vec d)) (fun x => vecDot (h x) p) := by
      unfold volumeAverage
      rw [hpairIntegral]
    simpa [Ch02.average] using! havgPair.trans hright
  have hinvInt := inverseCoefficientEnergyIntegrable' a hsym h hh
  have hyoung :
      ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
        vecDot (h x) (v.grad x) ≤
          (1 / 2 : ℝ) * vecDot (v.grad x)
              (matVecMul (a.toCoeffField x) (v.grad x)) +
            (1 / 2 : ℝ) * vecDot (h x)
              (matVecMul (a.toCoeffField x)⁻¹ (h x)) := by
    filter_upwards [a.aeElliptic, hsym] with x hxEll hxSymm
    have hy := blockMatrixOfCoeff_half_quadratic_ge_vecDot_of_isEllipticMatrix
      hxEll (v.grad x) (h x)
    rw [blockMatrixOfCoeff_quadratic_eq] at hy
    have hs : symmPart (a.toCoeffField x) = a.toCoeffField x := by
      ext i j
      have hij : a.toCoeffField x j i = a.toCoeffField x i j :=
        (Matrix.IsSymm.ext_iff.mp hxSymm) i j
      simp [symmPart, hij]
    have hk : skewPart (a.toCoeffField x) = 0 := by
      ext i j
      have hij : a.toCoeffField x j i = a.toCoeffField x i j :=
        (Matrix.IsSymm.ext_iff.mp hxSymm) i j
      simp [skewPart, hij]
    rw [hs, hk] at hy
    have hz : matVecMul (0 : Mat d) (v.grad x) = 0 := by
      ext i
      simp [matVecMul]
    rw [hz, sub_zero] at hy
    rw [vecDot_comm (v.grad x) (h x)] at hy
    nlinarith
  have hrhsInt : IntegrableOn
      (fun x =>
        (1 / 2 : ℝ) * vecDot (v.grad x)
            (matVecMul (a.toCoeffField x) (v.grad x)) +
          (1 / 2 : ℝ) * vecDot (h x)
            (matVecMul (a.toCoeffField x)⁻¹ (h x)))
      (U : Set (Vec d)) volume :=
    (henergyInt.const_mul (1 / 2 : ℝ)).add (hinvInt.const_mul (1 / 2 : ℝ))
  have hint :
      (∫ x in (U : Set (Vec d)), vecDot (h x) (v.grad x)) ≤
        ∫ x in (U : Set (Vec d)),
          ((1 / 2 : ℝ) * vecDot (v.grad x)
              (matVecMul (a.toCoeffField x) (v.grad x)) +
            (1 / 2 : ℝ) * vecDot (h x)
              (matVecMul (a.toCoeffField x)⁻¹ (h x))) :=
    integral_mono_ae hhGrad hrhsInt hyoung
  have hvolNonneg : 0 ≤ (volume (U : Set (Vec d))).toReal⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hint hvolNonneg
  have hrhsIntegralEq :
      (∫ x in (U : Set (Vec d)),
          ((1 / 2 : ℝ) * vecDot (v.grad x)
              (matVecMul (a.toCoeffField x) (v.grad x)) +
            (1 / 2 : ℝ) * vecDot (h x)
              (matVecMul (a.toCoeffField x)⁻¹ (h x)))) =
        (1 / 2 : ℝ) * (∫ x in (U : Set (Vec d)),
          vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x))) +
        (1 / 2 : ℝ) * (∫ x in (U : Set (Vec d)),
          vecDot (h x) (matVecMul (a.toCoeffField x)⁻¹ (h x))) := by
    rw [integral_add (henergyInt.const_mul (1 / 2 : ℝ))
        (hinvInt.const_mul (1 / 2 : ℝ)),
      integral_const_mul, integral_const_mul]
  have havgYoung :
      Ch02.average U (fun x => vecDot (h x) (v.grad x)) ≤
        (1 / 2 : ℝ) * Ch02.average U
            (fun x => vecDot (v.grad x) (matVecMul (a.toCoeffField x) (v.grad x))) +
          (1 / 2 : ℝ) * Ch02.average U
            (fun x => vecDot (h x) (matVecMul (a.toCoeffField x)⁻¹ (h x))) := by
    rw [hrhsIntegralEq] at hscaled
    unfold Ch02.average
    nlinarith
  have hquad :
      vecDot avg (matVecMul B⁻¹ avg) ≤
        Ch02.average U
          (fun x => vecDot (h x) (matVecMul (a.toCoeffField x)⁻¹ (h x))) := by
    rw [hpair, henergyEq] at havgYoung
    have havgp : vecDot avg p = vecDot avg (matVecMul B⁻¹ avg) := by rfl
    rw [havgp] at havgYoung
    linarith
  have hnorm :=
    Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := B⁻¹) (B := B) (Ch02.bCoarse_posDef U a).posSemidef hBmul avg
  exact hnorm.trans
    (mul_le_mul_of_nonneg_left hquad (Ch02.matrixNorm_nonneg _))

/-! ## The triadic-cube form, and the forced equation on descendants -/



theorem vecNormSq_cubeAverageVec_le_coarseBMatrixNorm_of_isSolenoidalOn [NeZero d]
    (R : TriadicCube d) (afam : Ch02.TriadicCoeffFamily d)
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (h : Vec d → Vec d) (hh : MemVectorL2 (openCubeSet R) h)
    (hsol : IsSolenoidalOn (openCubeSet R) h) :
    vecNormSq (cubeAverageVec R h) ≤
      Ch02.coarseBMatrixNorm R afam *
        cubeAverage R (fun x =>
          vecDot (h x) (matVecMul ((afam.coeffOn R).toCoeffField x)⁻¹ (h x))) := by
  have hraw := solenoidalAverageInverseEnergyControl
    (Ch02.cubeDomain R) (afam.coeffOn R) (haSymm R) h hh hsol
  have havg :
      Ch02.average (Ch02.cubeDomain R)
          (fun x => vecDot (h x)
            (matVecMul ((afam.coeffOn R).toCoeffField x)⁻¹ (h x))) =
        cubeAverage R (fun x =>
          vecDot (h x) (matVecMul ((afam.coeffOn R).toCoeffField x)⁻¹ (h x))) :=
    Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage _ _
  have havgVec : Ch02.averageVec (Ch02.cubeDomain R) h = cubeAverageVec R h := by
    funext i
    exact Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage
      R (fun x => h x i)
  rw [havgVec, havg] at hraw
  simpa [Ch02.coarseBMatrixNorm] using hraw



private theorem setIntegral_vecDot_extendByZero {U V : Set (Vec d)}
    (hU : MeasurableSet U) (hV : IsOpen V) (hUV : U ⊆ V)
    (F : Vec d → Vec d) (phi : H10Function U) :
    ∫ x in V, vecDot (F x)
        ((phi.extendByZeroToOpenSuperset hU hV hUV).grad x) ∂volume =
      ∫ x in U, vecDot (F x) (phi.grad x) ∂volume := by
  let phiV : H10Function V := phi.extendByZeroToOpenSuperset hU hV hUV
  have hgrad : phiV.grad = phi.zeroExtensionGrad := by
    simpa only [phiV] using
      H10Function.extendByZeroToOpenSuperset_grad phi hU hV hUV
  have hindicator :
      (fun x => vecDot (F x) (phiV.grad x)) =
        U.indicator (fun x => vecDot (F x) (phi.grad x)) := by
    funext x
    rw [hgrad]
    by_cases hx : x ∈ U
    · simp only [H10Function.zeroExtensionGrad_apply_of_mem _ hx,
        Set.indicator_of_mem hx]
    · simp only [H10Function.zeroExtensionGrad_apply_of_not_mem _ hx,
        Set.indicator_of_notMem hx, vecDot_zero_right]
  rw [show (phi.extendByZeroToOpenSuperset hU hV hUV).grad = phiV.grad by rfl,
    hindicator, MeasureTheory.integral_indicator hU, Measure.restrict_restrict hU,
    Set.inter_eq_left.mpr hUV]

/-- **The forced equation restricts to every descendant.**

The `Ch03` (positive-sign) counterpart of
`Homogenization.Book.Ch03.ABK26.IsForcedEquation.restrictToDescendant`: a
descendant test function extends by zero to the parent.  The coefficient field
is assumed constant along the family (the scalar case of the library). -/
theorem isForcedEquation_restrictToOpenSubcube {Q R : TriadicCube d} {j : ℕ}
    {afam : Ch03.CoeffFamily d} {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hR : R ∈ descendantsAtDepth Q j)
    (hAfam : (afam.coeffOn R).toCoeffField = (afam.coeffOn Q).toCoeffField)
    (hforced : Ch03.IsForcedEquation Q afam u g) :
    Ch03.IsForcedEquation R afam (u.restrictToOpenSubcube hR) g := by
  have hRQ : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  intro phi
  set phiQ : H10Function (openCubeSet Q) :=
    phi.extendByZeroToOpenSuperset (measurableSet_openCubeSet R)
      (isOpen_openCubeSet Q) hRQ with hphiQ
  have hflux := setIntegral_vecDot_extendByZero
    (measurableSet_openCubeSet R) (isOpen_openCubeSet Q) hRQ
    (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x)) phi
  have hforcing := setIntegral_vecDot_extendByZero
    (measurableSet_openCubeSet R) (isOpen_openCubeSet Q) hRQ g phi
  have hgradQ : phiQ.toH1Function.grad =
      (phi.extendByZeroToOpenSuperset (measurableSet_openCubeSet R)
        (isOpen_openCubeSet Q) hRQ).grad := rfl
  calc
    ∫ x in (Ch02.cubeDomain R : Set (Vec d)),
        vecDot (matVecMul ((afam.coeffOn R).toCoeffField x)
            ((u.restrictToOpenSubcube hR).grad x)) (phi.toH1Function.grad x) ∂volume
        = ∫ x in openCubeSet R,
            vecDot (matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x))
              (phi.grad x) ∂volume := by
          rw [hAfam]
          simp [Ch02.cubeDomain_coe]
    _ = ∫ x in openCubeSet Q,
            vecDot (matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x))
              (phiQ.toH1Function.grad x) ∂volume := by
          rw [hgradQ]; exact hflux.symm
    _ = ∫ x in openCubeSet Q, vecDot (g x) (phiQ.toH1Function.grad x) ∂volume := by
          simpa [Ch02.cubeDomain_coe] using hforced phiQ
    _ = ∫ x in (Ch02.cubeDomain R : Set (Vec d)),
            vecDot (g x) (phi.toH1Function.grad x) ∂volume := by
          rw [hgradQ]
          simpa only [Ch02.cubeDomain_coe] using! hforcing

/-! ## The per-cube kernel -/

/-- The dimensional constant in the library's corrector-energy estimate
`MeanZeroNeumannCorrectorData.coefficientEnergy_average_le_force_scale_noteConstants_expanded`. -/
noncomputable def correctorEnergyConstant (d : ℕ) (s : ℝ) : ℝ :=
  500 * (s⁻¹) ^ 2 * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2

theorem correctorEnergyConstant_nonneg (d : ℕ) (s : ℝ) :
    0 ≤ correctorEnergyConstant d s := by
  unfold correctorEnergyConstant; positivity

/-- **The per-cube kernel of the flux clause.**

For a solution of `−∇·(a∇u) = ∇·g` on a triadic cube `R` with a scalar
coefficient, the *cube average of the flux* obeys

```
|⟨a∇u⟩_R|² ≤ ‖b(R;a)‖ · ( 2⟨a|∇u|²⟩_R + 2 C(d,s) λ_{s/2,2}(R;a)⁻¹ [g]²_{B^{s,+}(R)} ) .
```

The mechanism is the Hodge-type decomposition `a∇u = a∇w + a∇ω` of
`WholeSpaceRowsHodge.lean` together with the **algebraic cancellation of the
corrector flux** `⟨a∇ω⟩_R = ⟨g − ⟨g⟩_R⟩_R = 0`
(`MeanZeroNeumannCorrectorData.cubeAverageVec_flux_eq_harmonicRemainderFlux_of_centered_rhs`,
manuscript Section 3.2.3): the cube average of the flux *is* the cube average of
the solenoidal part, which the coarse control
`solenoidalAverageInverseEnergyControl` prices by `‖b(R;a)‖` times its
`a⁻¹`-energy, and that energy is coarse (`⟨a|∇u−∇ω|²⟩ ≤ 2⟨a|∇u|²⟩+2⟨a|∇ω|²⟩`,
the Hodge decomposition) with the corrector energy priced by `λ⁻¹[g]²`.

No pointwise `λ_∞⁻¹`, and no `‖a‖_∞`, enters. -/
theorem vecNormSq_cubeAverageVec_flux_le_of_isForcedEquation [NeZero d]
    {R : TriadicCube d} {afam : Ch03.CoeffFamily d} {a : Vec d → ℝ} {lam Lam : ℝ}
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (hA : ∀ y, (afam.coeffOn R).toCoeffField y = scalarCoeffField a y)
    (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) ((afam.coeffOn R).toCoeffField))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {u : H1Function (openCubeSet R)} {g : Vec d → Vec d}
    (hforced : Ch03.IsForcedEquation R afam u g)
    (hreg : Ch03.ForceBesovRegularity R s g) :
    vecNormSq (cubeAverageVec R
        (fun x => matVecMul ((afam.coeffOn R).toCoeffField x) (u.grad x))) ≤
      Ch02.coarseBMatrixNorm R afam *
        (2 * cubeAverage R (fun x => a x * vecNormSq (u.grad x)) +
          2 * (correctorEnergyConstant d s *
            (lambdaSq R (s / 2) (.finite 2) ((afam.coeffOn R).toCoeffField))⁻¹ *
            (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)) := by
  have hgmem : MemVectorL2 (cubeSet R) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R hreg.memLp
  obtain ⟨ω, w, hsplit, hsol⟩ :=
    exists_hodge_decomposition_of_isForcedEquation hEll hgmem hforced
  have hguCube : MemVectorL2 (cubeSet R) u.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using u.grad_memVectorL2
  have hgwCube : MemVectorL2 (cubeSet R) w.toH1.grad := w.toH1.grad_memVectorL2
  have hgomCube : MemVectorL2 (cubeSet R) ω.toH1MeanZero.toH1Function.grad :=
    ω.toH1MeanZero.toH1Function.grad_memVectorL2
  have hfluxEq :=
    ω.cubeAverageVec_flux_eq_harmonicRemainderFlux_of_centered_rhs w hsplit hEll
      hguCube hgmem
  rw [hfluxEq]
  have hfluxMemCube : MemVectorL2 (cubeSet R)
      (fun x => matVecMul ((afam.coeffOn R).toCoeffField x) (w.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hgwCube
  have hfluxMemOpen : MemVectorL2 (openCubeSet R)
      (fun x => matVecMul ((afam.coeffOn R).toCoeffField x) (w.toH1.grad x)) := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hfluxMemCube
  have hstep1 := vecNormSq_cubeAverageVec_le_coarseBMatrixNorm_of_isSolenoidalOn
    R afam haSymm _ hfluxMemOpen hsol
  refine hstep1.trans (mul_le_mul_of_nonneg_left ?_ (Ch02.coarseBMatrixNorm_nonneg R afam))
  have hstep2 :=
    cubeAverage_inverseEnergy_solenoidalPart_le (Q := R) hA hapos hEll hguCube hgwCube
      hgomCube hsplit
  refine hstep2.trans ?_
  have hstep3 :=
    ω.coefficientEnergy_average_le_force_scale_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam) hs0 hs1 hEll hreg.memLp
      hreg.partialSeminorms_bddAbove
  have hconv : cubeAverage R
      (coefficientEnergyDensity ((afam.coeffOn R).toCoeffField)
        (fun x => ω.toH1MeanZero.toH1Function.grad x)) =
      cubeAverage R
        (fun x => a x * vecNormSq (ω.toH1MeanZero.toH1Function.grad x)) := by
    refine congrArg (cubeAverage R) ?_
    funext x
    exact coefficientEnergyDensity_scalar hA _ x
  rw [hconv] at hstep3
  have hfinal :
      cubeAverage R (fun x => a x * vecNormSq (ω.toH1MeanZero.toH1Function.grad x)) ≤
        correctorEnergyConstant d s *
          (lambdaSq R (s / 2) (.finite 2) ((afam.coeffOn R).toCoeffField))⁻¹ *
          (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2 := by
    refine hstep3.trans (le_of_eq ?_)
    unfold correctorEnergyConstant
    ring
  linarith

/-! ## The depth assembly -/



private theorem integrableOn_scalarEnergy' {Q : TriadicCube d} {A : CoeffField d}
    {a : Vec d → ℝ} {lam Lam : ℝ}
    (hA : ∀ y, A y = scalarCoeffField a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) A)
    {v : Vec d → Vec d} (hv : MemVectorL2 (cubeSet Q) v) :
    IntegrableOn (fun x => a x * vecNormSq (v x)) (cubeSet Q) volume := by
  have hflux : MemVectorL2 (cubeSet Q) (fun x => matVecMul (A x) (v x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hv
  have hint : IntegrableOn (fun x => vecDot (v x) (matVecMul (A x) (v x)))
      (cubeSet Q) volume := integrableOn_vecDot_of_memVectorL2 hv hflux
  have heq : (fun x => vecDot (v x) (matVecMul (A x) (v x))) =
      fun x => a x * vecNormSq (v x) := by
    funext x
    rw [hA x]
    simp [scalarCoeffField, matVecMul_scalarMatrix, vecDot_smul_right, vecNormSq]
  rwa [heq] at hint

/-- `⟨2 f + K⟩_Q = 2⟨f⟩_Q + K`. -/
private theorem cubeAverage_two_mul_add_const {Q : TriadicCube d} {f : Vec d → ℝ}
    (hf : IntegrableOn f (cubeSet Q) volume) (K : ℝ) :
    cubeAverage Q (fun x => 2 * f x + K) = 2 * cubeAverage Q f + K := by
  have hconst : IntegrableOn (fun _ : Vec d => K) (cubeSet Q) volume :=
    MeasureTheory.integrableOn_const (hs := (volume_cubeSet_lt_top Q).ne)
  have h1 : cubeAverage Q (fun x => 2 * f x + K) =
      cubeAverage Q (fun x => 2 * f x) + cubeAverage Q (fun _ : Vec d => K) := by
    unfold cubeAverage
    rw [MeasureTheory.integral_add (hf.const_mul 2) hconst]
    ring
  have h2 : cubeAverage Q (fun x => 2 * f x) = 2 * cubeAverage Q f := by
    unfold cubeAverage
    rw [MeasureTheory.integral_const_mul]
    ring
  rw [h1, h2, cubeAverage_const]

/-- **The depth-`n` block average of the flux is coarse.**

`⟨|⟨a∇u⟩_R|²⟩_{R ∈ desc_n(Q)} ≤ max_{R} ‖b(R;a)‖ · ⟨ 2 a|∇u|² + K ⟩_Q`, where

```
K = 2 C(d,s) λ_{s/2,2}(Q;a)⁻¹ [g]²_{B^{s,+}(Q)} .
```

Two averaging facts make the datum term *uniform in the depth*: the tower
property `⟨⟨a|∇u|²⟩_R⟩_{R∈desc_n} = ⟨a|∇u|²⟩_Q`, and the descendant-average
contraction of the positive Besov seminorm
`descendantsAverage_sq_scaled_cubeBesovPositiveVectorSeminormTwo_le`, which
gives `⟨[g]²_{B^{s,+}(R)}⟩_{R∈desc_n} ≤ 3^{-2sn}[g]²_{B^{s,+}(Q)}`.  That decay
absorbs the depth loss `3^{sn}` of the coarse lower-ellipticity localization
`hlam` — with room to spare, the net factor being `3^{-sn} ≤ 1`.  This is the
arithmetic that makes the flux clause's datum term carry `λ_{s/2,2}(Q)⁻¹` and
nothing depth-dependent. -/
theorem negativeBesovVectorDepthAverage_flux_le [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d} {a : Vec d → ℝ} {lam Lam : ℝ}
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (hAfam : ∀ S : TriadicCube d,
      (afam.coeffOn S).toCoeffField = (afam.coeffOn Q).toCoeffField)
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hforced : Ch03.IsForcedEquation Q afam u g)
    (hreg : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j, Ch03.ForceBesovRegularity R s g)
    (hGlobalBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hlam : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j,
      (lambdaSq R (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹)
    (n : ℕ) :
    Ch03.negativeBesovVectorDepthAverage Q
        (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x)) n ≤
      Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) afam *
        cubeAverage Q (fun x =>
          2 * (a x * vecNormSq (u.grad x)) +
            2 * correctorEnergyConstant d s *
              (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  classical
  set A : CoeffField d := (afam.coeffOn Q).toCoeffField with hAdef
  set C : ℝ := correctorEnergyConstant d s with hCdef
  set L : ℝ := (lambdaSq Q (s / 2) (.finite 2) A)⁻¹ with hLdef
  set G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g with hGdef
  set K : ℝ := 2 * C * L * G ^ 2 with hKdef
  have hCnn : 0 ≤ C := correctorEnergyConstant_nonneg d s
  have hLnn : 0 ≤ L := by
    refine inv_nonneg.mpr ?_
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 A (by norm_num)
      (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hMnn : 0 ≤ Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) afam :=
    Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) afam
  -- the energy density and its integrability
  have hguCubeQ : MemVectorL2 (cubeSet Q) u.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using u.grad_memVectorL2
  have hEllQ : IsEllipticFieldOn lam Lam (cubeSet Q) A := hEll
  have hintQ : IntegrableOn (fun x => a x * vecNormSq (u.grad x)) (cubeSet Q) volume :=
    integrableOn_scalarEnergy' hA hEllQ hguCubeQ
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ a x * vecNormSq (u.grad x) := by
    intro x _
    exact mul_nonneg (hapos x).le (vecNormSq_nonneg _)
  -- the per-descendant bound
  have hpoint : ∀ R ∈ descendantsAtDepth Q n,
      vecNormSq (cubeAverageVec R (fun x => matVecMul (A x) (u.grad x))) ≤
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) afam *
          (2 * cubeAverage R (fun x => a x * vecNormSq (u.grad x)) +
            2 * (C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
              (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)) := by
    intro R hR
    have hAR : (afam.coeffOn R).toCoeffField = A := hAfam R
    have hAR' : ∀ y, (afam.coeffOn R).toCoeffField y = scalarCoeffField a y := by
      intro y; rw [hAR]; exact hA y
    have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) ((afam.coeffOn R).toCoeffField) := by
      rw [hAR]
      exact IsEllipticFieldOn.mono hEll (measurableSet_cubeSet R)
        (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hforcedR : Ch03.IsForcedEquation R afam (u.restrictToOpenSubcube hR) g :=
      isForcedEquation_restrictToOpenSubcube hR hAR hforced
    have hkernel := vecNormSq_cubeAverageVec_flux_le_of_isForcedEquation
      (R := R) (afam := afam) (a := a) (lam := lam) (Lam := Lam)
      haSymm hAR' hapos hEllR hs0 hs1 hforcedR (hreg n R hR)
    rw [hAR] at hkernel
    simp only [H1Function.restrictToOpenSubcube_grad] at hkernel
    have hnn : 0 ≤ 2 * cubeAverage R (fun x => a x * vecNormSq (u.grad x)) +
        2 * (C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
          (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
      have h1 : 0 ≤ cubeAverage R (fun x => a x * vecNormSq (u.grad x)) := by
        refine cubeAverage_nonneg_of_nonneg_on ?_
        intro x _
        exact mul_nonneg (hapos x).le (vecNormSq_nonneg _)
      have h2 : 0 ≤ (lambdaSq R (s / 2) (.finite 2) A)⁻¹ := by
        refine inv_nonneg.mpr ?_
        exact multiscale_ellipticity_lambdaSq_finite_nonneg R (s / 2) 2 A (by norm_num)
          (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
      have h3 : 0 ≤ (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2 := sq_nonneg _
      have h4 : 0 ≤ C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
          (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2 :=
        mul_nonneg (mul_nonneg hCnn h2) h3
      linarith
    refine hkernel.trans (mul_le_mul_of_nonneg_right ?_ hnn)
    exact (Ch02.coarseBMatrixNorm_le_maxDescendantBMatrixNormAtScale R
        (by
          have : R.scale = Q.scale - (n : ℤ) :=
            Homogenization.descendant_scale_eq_of_mem_descendantsAtScale
              (mem_descendantsAtScale_of_mem_descendantsAtDepth hR)
          omega) afam).trans
      (Ch02.maxDescendantBMatrixNormAtScale_le_of_mem_descendantsAtScale afam
        (mem_descendantsAtScale_of_mem_descendantsAtDepth hR)
        (by
          have : R.scale = Q.scale - (n : ℤ) :=
            Homogenization.descendant_scale_eq_of_mem_descendantsAtScale
              (mem_descendantsAtScale_of_mem_descendantsAtDepth hR)
          omega))
  have hdesc := descendantsAverage_le_descendantsAverage Q n hpoint
  -- the descendants average of the right-hand side
  have hpull :
      descendantsAverage Q n (fun R =>
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) afam *
            (2 * cubeAverage R (fun x => a x * vecNormSq (u.grad x)) +
              2 * (C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
                (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2))) =
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) afam *
          descendantsAverage Q n (fun R =>
            2 * cubeAverage R (fun x => a x * vecNormSq (u.grad x)) +
              2 * (C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
                (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)) :=
    descendantsAverage_mul_left Q n _ _
  have hsplit :
      descendantsAverage Q n (fun R =>
          2 * cubeAverage R (fun x => a x * vecNormSq (u.grad x)) +
            2 * (C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
              (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)) =
        2 * descendantsAverage Q n
            (fun R => cubeAverage R (fun x => a x * vecNormSq (u.grad x))) +
          2 * descendantsAverage Q n (fun R =>
            C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
              (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
    rw [descendantsAverage_add Q n
        (fun R => 2 * cubeAverage R (fun x => a x * vecNormSq (u.grad x)))
        (fun R => 2 * (C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
          (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)),
      descendantsAverage_mul_left Q n 2
        (fun R => cubeAverage R (fun x => a x * vecNormSq (u.grad x))),
      descendantsAverage_mul_left Q n 2
        (fun R => C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
          (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)]
  have htower :
      descendantsAverage Q n
          (fun R => cubeAverage R (fun x => a x * vecNormSq (u.grad x))) =
        cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) :=
    (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q n _ hintQ).symm
  -- the datum term
  have hdatum :
      descendantsAverage Q n (fun R =>
          C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
            (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤ C * L * G ^ 2 := by
    have hstep1 : ∀ R ∈ descendantsAtDepth Q n,
        C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
            (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2 ≤
          (C * L) *
            ((Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              cubeBesovPositiveVectorSeminormTwo R s g) ^ 2 *
              Real.rpow (3 : ℝ) (-(s * (n : ℝ)))) := by
      intro R hR
      have hlamR := hlam n R hR
      have hsq : 0 ≤ (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2 := sq_nonneg _
      have hmul : C * (lambdaSq R (s / 2) (.finite 2) A)⁻¹ *
          (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2 ≤
          C * (Real.rpow (3 : ℝ) (s * (n : ℝ)) * L) *
            (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hlamR hCnn
        nlinarith
      refine hmul.trans (le_of_eq ?_)
      have hxy : Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          Real.rpow (3 : ℝ) (-(s * (n : ℝ))) = 1 := by
        have h := Real.rpow_add (x := (3 : ℝ)) (by norm_num)
          (s * (n : ℝ)) (-(s * (n : ℝ)))
        simp only [add_neg_cancel, Real.rpow_zero] at h
        exact h.symm
      have hpow : (Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2 *
          Real.rpow (3 : ℝ) (-(s * (n : ℝ))) = Real.rpow (3 : ℝ) (s * (n : ℝ)) := by
        have hrw : (Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2 *
            Real.rpow (3 : ℝ) (-(s * (n : ℝ))) =
            Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
                Real.rpow (3 : ℝ) (-(s * (n : ℝ)))) := by ring
        rw [hrw, hxy, mul_one]
      calc
        C * (Real.rpow (3 : ℝ) (s * (n : ℝ)) * L) *
            (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2
            = (C * L) * ((Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2 *
                Real.rpow (3 : ℝ) (-(s * (n : ℝ))) *
                (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
              rw [hpow]; ring
        _ = (C * L) *
              ((Real.rpow (3 : ℝ) (s * (n : ℝ)) *
                cubeBesovPositiveVectorSeminormTwo R s g) ^ 2 *
                Real.rpow (3 : ℝ) (-(s * (n : ℝ)))) := by ring
    have hmono := descendantsAverage_le_descendantsAverage Q n hstep1
    have hfactor :
        descendantsAverage Q n (fun R =>
            (C * L) *
              ((Real.rpow (3 : ℝ) (s * (n : ℝ)) *
                cubeBesovPositiveVectorSeminormTwo R s g) ^ 2 *
                Real.rpow (3 : ℝ) (-(s * (n : ℝ))))) =
          (C * L * Real.rpow (3 : ℝ) (-(s * (n : ℝ)))) *
            descendantsAverage Q n (fun R =>
              (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
                cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
      rw [← descendantsAverage_mul_left Q n
        (C * L * Real.rpow (3 : ℝ) (-(s * (n : ℝ))))
        (fun R => (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)]
      refine congrArg (descendantsAverage Q n) ?_
      funext R
      ring
    have hbesov :=
      descendantsAverage_sq_scaled_cubeBesovPositiveVectorSeminormTwo_le Q g s n
        hGlobalBdd (fun R hR => (hreg n R hR).partialSeminorms_bddAbove)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hdecay : Real.rpow (3 : ℝ) (-(s * (n : ℝ))) ≤ 1 := by
      have h0 : Real.rpow (3 : ℝ) (-(s * (n : ℝ))) ≤ Real.rpow (3 : ℝ) 0 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      simpa using h0
    have hdecay_pos : 0 ≤ Real.rpow (3 : ℝ) (-(s * (n : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have havg_nonneg : 0 ≤ descendantsAverage Q n (fun R =>
        (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) :=
      descendantsAverage_nonneg Q n _ (fun R _ => sq_nonneg _)
    rw [hfactor] at hmono
    refine hmono.trans ?_
    have hCL : 0 ≤ C * L := mul_nonneg hCnn hLnn
    have hone : C * L * Real.rpow (3 : ℝ) (-(s * (n : ℝ))) ≤ C * L :=
      mul_le_of_le_one_right hCL hdecay
    have hfirst : (C * L * Real.rpow (3 : ℝ) (-(s * (n : ℝ)))) *
        descendantsAverage Q n (fun R =>
          (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
        (C * L) * descendantsAverage Q n (fun R =>
          (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) :=
      mul_le_mul_of_nonneg_right hone havg_nonneg
    have hsecond : (C * L) * descendantsAverage Q n (fun R =>
        (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤ (C * L) * G ^ 2 :=
      mul_le_mul_of_nonneg_left hbesov hCL
    calc
      (C * L * Real.rpow (3 : ℝ) (-(s * (n : ℝ)))) *
          descendantsAverage Q n (fun R =>
            (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤ (C * L) * G ^ 2 :=
        hfirst.trans hsecond
      _ = C * L * G ^ 2 := by ring
  -- put it together
  have hgoal :
      descendantsAverage Q n (fun R =>
          vecNormSq (cubeAverageVec R (fun x => matVecMul (A x) (u.grad x)))) ≤
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) afam *
          (2 * cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) + K) := by
    refine hdesc.trans ?_
    rw [hpull, hsplit, htower]
    refine mul_le_mul_of_nonneg_left ?_ hMnn
    rw [hKdef]
    nlinarith [hdatum]
  have hunfold : Ch03.negativeBesovVectorDepthAverage Q
      (fun x => matVecMul (A x) (u.grad x)) n =
      descendantsAverage Q n (fun R =>
        vecNormSq (cubeAverageVec R (fun x => matVecMul (A x) (u.grad x)))) := rfl
  rw [hunfold]
  refine hgoal.trans (le_of_eq ?_)
  have hrhs : cubeAverage Q (fun x =>
      2 * (a x * vecNormSq (u.grad x)) + K) =
      2 * cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) + K :=
    cubeAverage_two_mul_add_const hintQ K
  rw [hrhs]

/-! ## The flux clause -/



theorem scaleNormalizedNegativeBesovVectorNorm_flux_le_of_isForcedEquation
    [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d} {a : Vec d → ℝ} {lam Lam : ℝ}
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (hAfam : ∀ S : TriadicCube d,
      (afam.coeffOn S).toCoeffField = (afam.coeffOn Q).toCoeffField)
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField))
    {s q : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hq : 1 ≤ q)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hforced : Ch03.IsForcedEquation Q afam u g)
    (hreg : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j, Ch03.ForceBesovRegularity R s g)
    (hGlobalBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hlam : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j,
      (lambdaSq R (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹) :
    Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite q)
        (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x)) ≤
      Ch03.poincareDiscountFactor s (.finite q) *
        Ch03.poincareUpperEllipticityFactor Q afam s (.finite q) *
        Real.sqrt
          (2 * cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
            2 * correctorEnergyConstant d s *
              (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  classical
  set A : CoeffField d := (afam.coeffOn Q).toCoeffField with hAdef
  set K : ℝ := 2 * correctorEnergyConstant d s *
    (lambdaSq Q (s / 2) (.finite 2) A)⁻¹ *
    (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 with hKdef
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    have hL : 0 ≤ (lambdaSq Q (s / 2) (.finite 2) A)⁻¹ := by
      refine inv_nonneg.mpr ?_
      exact multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 A (by norm_num)
        (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
    have hC : 0 ≤ correctorEnergyConstant d s := correctorEnergyConstant_nonneg d s
    have hG : 0 ≤ (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := sq_nonneg _
    have : 0 ≤ 2 * correctorEnergyConstant d s := by linarith
    exact mul_nonneg (mul_nonneg this hL) hG
  have henergy_nonneg : ∀ x ∈ cubeSet Q,
      0 ≤ 2 * (a x * vecNormSq (u.grad x)) + K := by
    intro x _
    have := mul_nonneg (hapos x).le (vecNormSq_nonneg (u.grad x))
    linarith
  have hdepth := fun n : ℕ =>
    negativeBesovVectorDepthAverage_flux_le (Q := Q) (afam := afam) (a := a)
      (lam := lam) (Lam := Lam) haSymm hAfam hA hapos hEll hs0 hs1 hforced hreg
      hGlobalBdd hlam n
  have hcube : ∀ n : ℕ,
      Ch03.negativeBesovVectorDepthAverage Q
          (fun x => matVecMul (A x) (u.grad x)) n ≤
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) afam *
          cubeAverage Q (fun x => 2 * (a x * vecNormSq (u.grad x)) + K) := hdepth
  have hres := Ch03.finite_flux_norm_le_of_cubeAverageEnergyControl Q afam s q hs0 hq
    (fun x => matVecMul (A x) (u.grad x))
    (fun x => 2 * (a x * vecNormSq (u.grad x)) + K)
    henergy_nonneg hcube
    (Ch03.summable_public_B_series Q afam hs0 hqpos)
    (Ch03.tsum_public_B_series_eq_LambdaSq Q afam hs0 hqpos)
  have hguCubeQ : MemVectorL2 (cubeSet Q) u.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using u.grad_memVectorL2
  have hEllQ : IsEllipticFieldOn lam Lam (cubeSet Q) A := hEll
  have hintQ : IntegrableOn (fun x => a x * vecNormSq (u.grad x)) (cubeSet Q) volume :=
    integrableOn_scalarEnergy' hA hEllQ hguCubeQ
  rw [cubeAverage_two_mul_add_const hintQ K] at hres
  exact hres

/-- The manuscript's two-term form :

```
‖a∇u‖_{B^{-s}_{2,q}(Q)} ≤ c_{s,q} Λ_{s,q}^{1/2} √2 ‖a^{1/2}∇u‖_{L̲²(Q)}
  + c_{s,q} Λ_{s,q}^{1/2} √(2C(d,s)) λ_{s/2,2}^{-1/2} [g]_{B^{s,+}(Q)} .
```
-/
theorem scaleNormalizedNegativeBesovVectorNorm_flux_le_two_term
    [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d} {a : Vec d → ℝ} {lam Lam : ℝ}
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (hAfam : ∀ S : TriadicCube d,
      (afam.coeffOn S).toCoeffField = (afam.coeffOn Q).toCoeffField)
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField))
    {s q : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hq : 1 ≤ q)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hforced : Ch03.IsForcedEquation Q afam u g)
    (hreg : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j, Ch03.ForceBesovRegularity R s g)
    (hGlobalBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hlam : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j,
      (lambdaSq R (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹) :
    Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite q)
        (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x)) ≤
      Ch03.poincareDiscountFactor s (.finite q) *
          Ch03.poincareUpperEllipticityFactor Q afam s (.finite q) *
          (Real.sqrt 2 *
            Real.sqrt (cubeAverage Q (fun x => a x * vecNormSq (u.grad x)))) +
        Ch03.poincareDiscountFactor s (.finite q) *
          Ch03.poincareUpperEllipticityFactor Q afam s (.finite q) *
          (Real.sqrt (2 * correctorEnergyConstant d s) *
            (Real.sqrt
                ((lambdaSq Q (s / 2) (.finite 2)
                  ((afam.coeffOn Q).toCoeffField))⁻¹) *
              |cubeBesovPositiveVectorSeminormTwo Q s g|)) := by
  have hbase := scaleNormalizedNegativeBesovVectorNorm_flux_le_of_isForcedEquation
    (Q := Q) (afam := afam) (a := a) (lam := lam) (Lam := Lam)
    haSymm hAfam hA hapos hEll hs0 hs1 hq hforced hreg hGlobalBdd hlam
  refine hbase.trans ?_
  have hDisc : 0 ≤ Ch03.poincareDiscountFactor s (.finite q) := by
    have hqq : (0 : ℝ) ≤ s * q := by nlinarith
    exact Real.rpow_nonneg (Ch02.book_geometricDiscount_nonneg hqq) _
  have hUpper : 0 ≤ Ch03.poincareUpperEllipticityFactor Q afam s (.finite q) :=
    Real.rpow_nonneg (Ch02.LambdaSq_nonneg Q afam hs0 (by simpa using hq)) _
  have hEa : 0 ≤ cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) := by
    refine cubeAverage_nonneg_of_nonneg_on ?_
    intro x _
    exact mul_nonneg (hapos x).le (vecNormSq_nonneg _)
  have hL : 0 ≤ (lambdaSq Q (s / 2) (.finite 2)
      ((afam.coeffOn Q).toCoeffField))⁻¹ := by
    refine inv_nonneg.mpr ?_
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2
      ((afam.coeffOn Q).toCoeffField) (by norm_num)
      (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hC : 0 ≤ 2 * correctorEnergyConstant d s := by
    have := correctorEnergyConstant_nonneg d s; linarith
  have hsplit :
      Real.sqrt
          (2 * cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
            2 * correctorEnergyConstant d s *
              (lambdaSq Q (s / 2) (.finite 2)
                ((afam.coeffOn Q).toCoeffField))⁻¹ *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        Real.sqrt 2 *
            Real.sqrt (cubeAverage Q (fun x => a x * vecNormSq (u.grad x))) +
          Real.sqrt (2 * correctorEnergyConstant d s) *
            (Real.sqrt ((lambdaSq Q (s / 2) (.finite 2)
                ((afam.coeffOn Q).toCoeffField))⁻¹) *
              |cubeBesovPositiveVectorSeminormTwo Q s g|) := by
    have hxnn : (0 : ℝ) ≤
        2 * cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) := by linarith
    have hynn : (0 : ℝ) ≤ 2 * correctorEnergyConstant d s *
        (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 :=
      mul_nonneg (mul_nonneg hC hL) (sq_nonneg _)
    have hadd := sqrt_add_le_sqrt_add_sqrt' hxnn hynn
    refine hadd.trans (le_of_eq ?_)
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
      Real.sqrt_mul (mul_nonneg hC hL), Real.sqrt_mul hC, Real.sqrt_sq_eq_abs]
    ring
  refine mul_le_mul_of_nonneg_left hsplit (mul_nonneg hDisc hUpper) |>.trans ?_
  exact le_of_eq (by ring)

/-- The lower-ellipticity localization hypothesis of the flux clause, discharged
from the (standard) summability of the coarse lower-ellipticity series.  This is
`Homogenization.multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale`
at `s := s/2`, `q := 2`, with the depth bookkeeping
`3^{2·(s/2)·j} = 3^{s j}`. -/
theorem lambdaSq_inv_descendant_le_of_summable
    {Q : TriadicCube d} (A : CoeffField d) {s : ℝ} (hs : 0 < s)
    (hsum : Summable (fun n : ℕ =>
      geometricWeight (s / 2) 2 n *
        Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) A)
          ((2 : ℝ) / 2))) :
    ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j,
      (lambdaSq R (s / 2) (.finite 2) A)⁻¹ ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) * (lambdaSq Q (s / 2) (.finite 2) A)⁻¹ := by
  intro j R hR
  have hscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR
  have hraw := multiscale_ellipticity_lambdaSq_finite_inv_le_of_mem_descendantsAtScale
    (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) A (s / 2) 2
    (by linarith) (by norm_num) hscale hsum
  have htoNat : Int.toNat (Q.scale - (Q.scale - (j : ℤ))) = j := by omega
  rw [htoNat] at hraw
  have hexp : 2 * (s / 2) * (j : ℝ) = s * (j : ℝ) := by ring
  rwa [hexp] at hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
