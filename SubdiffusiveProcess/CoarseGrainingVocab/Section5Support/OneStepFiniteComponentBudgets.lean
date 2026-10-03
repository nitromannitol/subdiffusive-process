module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepAveragedBudgets
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepLocalizedEnergyIdentification
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepFiniteVolumeAssembly
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.AnalyticInequalities

@[expose] public section




open MeasureTheory Homogenization
open Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Integrate and average a selected-cell oscillatory-energy majorant. -/
theorem normalized_finset_integral_oscillatory_le_of_cellBesovError
    {iota Omega : Type*} [DecidableEq iota] [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (cells : Finset iota) (hcells : cells.Nonempty)
    (Lambda A B oscillatory : iota -> Omega -> Real)
    (hLambda : ∀ i, i ∈ cells → Measurable (Lambda i))
    (hA : ∀ i, i ∈ cells → Measurable (A i))
    (hB : ∀ i, i ∈ cells → Measurable (B i))
    (hLambda0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] Lambda i)
    (hA0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] A i)
    (hB0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] B i)
    (hLambda2 : ∀ i, i ∈ cells →
      Integrable (fun omega => Lambda i omega ^ 2) mu)
    (hA4 : ∀ i, i ∈ cells →
      Integrable (fun omega => A i omega ^ 4) mu)
    (hB4 : ∀ i, i ∈ cells →
      Integrable (fun omega => B i omega ^ 4) mu)
    (hOscInt : ∀ i, i ∈ cells → Integrable (oscillatory i) mu)
    {cCell L E : Real} (hcCell : 0 ≤ cCell) (hL : 0 ≤ L)
    (hOsc : ∀ i, i ∈ cells → ∀ᵐ omega ∂mu,
      oscillatory i omega ≤ cCell * Lambda i omega *
        oneStepCellBesovError (A i omega) (B i omega))
    (hLambdaBudget : ((cells.card : Real)⁻¹) * ∑ i ∈ cells,
      ∫ omega, Lambda i omega ^ 2 ∂mu ≤ L ^ 2)
    (hCellBudget : ((cells.card : Real)⁻¹) * ∑ i ∈ cells,
      ∫ omega, A i omega ^ 4 + B i omega ^ 4 ∂mu ≤ 2 * E ^ 4) :
    ((cells.card : Real)⁻¹) * ∑ i ∈ cells,
        ∫ omega, oscillatory i omega ∂mu ≤
      6 * cCell * L * E ^ 2 := by
  have hmajorInt : ∀ i, i ∈ cells → Integrable (fun omega =>
      cCell * Lambda i omega *
        oneStepCellBesovError (A i omega) (B i omega)) mu := by
    intro i hi
    have hErrorInt := integrable_sq_oneStepCellBesovError
      (hA i hi) (hB i hi) (hA0 i hi) (hB0 i hi)
      (hA4 i hi) (hB4 i hi)
    have hErrorMeas : Measurable (fun omega =>
        oneStepCellBesovError (A i omega) (B i omega)) :=
      ((hA i hi).pow_const 2).add
        (((hA i hi).mul (Real.continuous_sqrt.measurable.comp (hA i hi))).mul
          (Real.continuous_sqrt.measurable.comp (hB i hi)))
    have hLambdaMem : MemLp (Lambda i) 2 mu :=
      (memLp_two_iff_integrable_sq (hLambda i hi).aestronglyMeasurable).2
        (hLambda2 i hi)
    have hErrorMem : MemLp (fun omega =>
        oneStepCellBesovError (A i omega) (B i omega)) 2 mu :=
      (memLp_two_iff_integrable_sq hErrorMeas.aestronglyMeasurable).2 hErrorInt
    simpa only [Pi.mul_apply, mul_assoc] using
      (hLambdaMem.integrable_mul hErrorMem).const_mul cCell
  have hIntegral : ∀ i, i ∈ cells →
      (∫ omega, oscillatory i omega ∂mu) ≤
        cCell * ∫ omega, Lambda i omega *
          oneStepCellBesovError (A i omega) (B i omega) ∂mu := by
    intro i hi
    calc
      ∫ omega, oscillatory i omega ∂mu ≤
          ∫ omega, cCell * Lambda i omega *
            oneStepCellBesovError (A i omega) (B i omega) ∂mu :=
        integral_mono_ae (hOscInt i hi) (hmajorInt i hi) (hOsc i hi)
      _ = cCell * ∫ omega, Lambda i omega *
          oneStepCellBesovError (A i omega) (B i omega) ∂mu := by
        rw [show (fun omega => cCell * Lambda i omega *
            oneStepCellBesovError (A i omega) (B i omega)) =
            fun omega => cCell * (Lambda i omega *
              oneStepCellBesovError (A i omega) (B i omega)) by
              funext omega
              ring,
          integral_const_mul]
  have hsum : ((cells.card : Real)⁻¹) * ∑ i ∈ cells,
      ∫ omega, oscillatory i omega ∂mu ≤
      cCell * (((cells.card : Real)⁻¹) * ∑ i ∈ cells,
        ∫ omega, Lambda i omega *
          oneStepCellBesovError (A i omega) (B i omega) ∂mu) := by
    calc
      _ ≤ ((cells.card : Real)⁻¹) * ∑ i ∈ cells,
          cCell * ∫ omega, Lambda i omega *
            oneStepCellBesovError (A i omega) (B i omega) ∂mu := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i hi => hIntegral i hi) (by positivity)
      _ = _ := by
        simp only [Finset.mul_sum]
        ring_nf
  calc
    _ ≤ cCell * (((cells.card : Real)⁻¹) * ∑ i ∈ cells,
        ∫ omega, Lambda i omega *
          oneStepCellBesovError (A i omega) (B i omega) ∂mu) := hsum
    _ ≤ cCell * (6 * L * E ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (normalized_finset_integral_mul_oneStepCellBesovError_le_six
          cells hcells Lambda A B hLambda hA hB hLambda0 hA0 hB0
            hLambda2 hA4 hB4 hL hLambdaBudget hCellBudget) hcCell
    _ = 6 * cCell * L * E ^ 2 := by ring

/-- The exact square-root simplification behind the manuscript's mixed
`delta^15` estimate. -/
theorem sqrt_mul_sqrt_delta_thirty_mul
    {P O delta previous : Real}
    (hP : 0 ≤ P) (hO : 0 ≤ O) (hdelta : 0 ≤ delta)
    (hprevious : 0 ≤ previous) :
    Real.sqrt (P * previous) *
        Real.sqrt (O * delta ^ 30 * previous) =
      Real.sqrt P * Real.sqrt O * delta ^ 15 * previous := by
  rw [Real.sqrt_mul hP,
    Real.sqrt_mul (mul_nonneg hO (pow_nonneg hdelta 30)),
    Real.sqrt_mul hO]
  have hsqrtPow : Real.sqrt (delta ^ 30) = delta ^ 15 := by
    rw [show delta ^ 30 = (delta ^ 15) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hdelta 15)]
  have hsqrtPrevious : Real.sqrt previous * Real.sqrt previous = previous :=
    Real.mul_self_sqrt hprevious
  rw [hsqrtPow]
  calc
    _ = Real.sqrt P * Real.sqrt O * delta ^ 15 *
        (Real.sqrt previous * Real.sqrt previous) := by ring
    _ = _ := by rw [hsqrtPrevious]

/-! ## Cellwise energy Cauchy -/

/-- Cauchy--Schwarz for a symmetric nonnegative matrix quadratic form, in
the unhalved normalization used by the one-step mixed term. -/
theorem abs_vecDot_matVecMul_le_sqrt_quad_mul_sqrt_quad
    {d : Nat} {A : Mat d} (hA : A.IsSymm)
    (hA0 : ∀ w : Vec d, 0 ≤ vecDot w (matVecMul A w))
    (u v : Vec d) :
    |vecDot u (matVecMul A v)| ≤
      Real.sqrt (vecDot u (matVecMul A u)) *
        Real.sqrt (vecDot v (matVecMul A v)) := by
  let X := vecDot u (matVecMul A u)
  let Y := vecDot v (matVecMul A v)
  let Z := vecDot u (matVecMul A v)
  have hX : 0 ≤ X := hA0 u
  have hY : 0 ≤ Y := hA0 v
  have hsq : Z ^ 2 ≤ X * Y := by
    simpa only [X, Y, Z] using
      sq_vecDot_matVecMul_le_of_isSymm_of_nonneg hA hA0 u v
  have hrhs0 : 0 ≤ Real.sqrt X * Real.sqrt Y := by positivity
  have hrhsSq : (Real.sqrt X * Real.sqrt Y) ^ 2 = X * Y := by
    rw [mul_pow, Real.sq_sqrt hX, Real.sq_sqrt hY]
  have hsq' : Z ^ 2 ≤ (Real.sqrt X * Real.sqrt Y) ^ 2 := by
    rw [hrhsSq]
    exact hsq
  simpa only [Z] using abs_le_of_sq_le_sq hsq' hrhs0

/-- Spatial Cauchy--Schwarz for the literal mixed energy on one triadic
cell.  This is the pointwise-in-sample input to the probability-space fold
below. -/
theorem abs_cubeAverage_matrix_cross_le_sqrt_energies
    {d : Nat} (Q : TriadicCube d) (A : Vec d → Mat d)
    (u v : Vec d → Vec d)
    (hCrossInt : Integrable
      (fun x => vecDot (u x) (matVecMul (A x) (v x)))
      (normalizedCubeMeasure Q))
    (hUInt : Integrable
      (fun x => vecDot (u x) (matVecMul (A x) (u x)))
      (normalizedCubeMeasure Q))
    (hVInt : Integrable
      (fun x => vecDot (v x) (matVecMul (A x) (v x)))
      (normalizedCubeMeasure Q))
    (hSymm : ∀ᵐ x ∂normalizedCubeMeasure Q, (A x).IsSymm)
    (hNonneg : ∀ᵐ x ∂normalizedCubeMeasure Q,
      ∀ w : Vec d, 0 ≤ vecDot w (matVecMul (A x) w)) :
    |cubeAverage Q (fun x => vecDot (u x) (matVecMul (A x) (v x)))| ≤
      Real.sqrt (cubeAverage Q
        (fun x => vecDot (u x) (matVecMul (A x) (u x)))) *
      Real.sqrt (cubeAverage Q
        (fun x => vecDot (v x) (matVecMul (A x) (v x)))) := by
  let EU : Vec d → Real := fun x => vecDot (u x) (matVecMul (A x) (u x))
  let EV : Vec d → Real := fun x => vecDot (v x) (matVecMul (A x) (v x))
  have hEU0 : 0 ≤ᵐ[normalizedCubeMeasure Q] EU := by
    filter_upwards [hNonneg] with x hx
    exact hx (u x)
  have hEV0 : 0 ≤ᵐ[normalizedCubeMeasure Q] EV := by
    filter_upwards [hNonneg] with x hx
    exact hx (v x)
  have hSqrtU : MemLp (fun x => Real.sqrt (EU x)) (2 : ENNReal)
      (normalizedCubeMeasure Q) :=
    memLp_sqrt_two_of_integrable_of_ae_nonneg
      (by simpa only [EU] using hUInt) hEU0
  have hSqrtV : MemLp (fun x => Real.sqrt (EV x)) (2 : ENNReal)
      (normalizedCubeMeasure Q) :=
    memLp_sqrt_two_of_integrable_of_ae_nonneg
      (by simpa only [EV] using hVInt) hEV0
  apply
    abs_cubeAverage_le_sqrt_cubeAverage_mul_sqrt_cubeAverage_of_ae_abs_le_sqrt_mul_sqrt
      Q hCrossInt hEU0 hEV0 hSqrtU hSqrtV
  filter_upwards [hSymm, hNonneg] with x hsymm hnonneg
  simpa only [EU, EV] using
    abs_vecDot_matVecMul_le_sqrt_quad_mul_sqrt_quad
      hsymm hnonneg (u x) (v x)

/-- Open-cell `volumeAverage` form of
`abs_cubeAverage_matrix_cross_le_sqrt_energies`, matching the selected-cell
gluing identities literally. -/
theorem abs_volumeAverage_openCubeSet_matrix_cross_le_sqrt_energies
    {d : Nat} (Q : TriadicCube d) (A : Vec d → Mat d)
    (u v : Vec d → Vec d)
    (hCrossInt : Integrable
      (fun x => vecDot (u x) (matVecMul (A x) (v x)))
      (normalizedCubeMeasure Q))
    (hUInt : Integrable
      (fun x => vecDot (u x) (matVecMul (A x) (u x)))
      (normalizedCubeMeasure Q))
    (hVInt : Integrable
      (fun x => vecDot (v x) (matVecMul (A x) (v x)))
      (normalizedCubeMeasure Q))
    (hSymm : ∀ᵐ x ∂normalizedCubeMeasure Q, (A x).IsSymm)
    (hNonneg : ∀ᵐ x ∂normalizedCubeMeasure Q,
      ∀ w : Vec d, 0 ≤ vecDot w (matVecMul (A x) w)) :
    |volumeAverage (openCubeSet Q)
        (fun x => vecDot (u x) (matVecMul (A x) (v x)))| ≤
      Real.sqrt (volumeAverage (openCubeSet Q)
        (fun x => vecDot (u x) (matVecMul (A x) (u x)))) *
      Real.sqrt (volumeAverage (openCubeSet Q)
        (fun x => vecDot (v x) (matVecMul (A x) (v x)))) := by
  rw [oneStep_volumeAverage_openCubeSet_eq_cubeAverage,
    oneStep_volumeAverage_openCubeSet_eq_cubeAverage,
    oneStep_volumeAverage_openCubeSet_eq_cubeAverage]
  exact abs_cubeAverage_matrix_cross_le_sqrt_energies
    Q A u v hCrossInt hUInt hVInt hSymm hNonneg

/-- The actual selected primal cell minimizers satisfy the manuscript's
mixed-energy Cauchy estimate.  All spatial integrability obligations are
discharged from their `L²` fields and the coefficient ellipticity. -/
theorem abs_oneStepSelectedDirichletCell_mixed_le_sqrt_energies
    {d : Nat} [NeZero d] {Q R : TriadicCube d} {j : Nat}
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    {lam Lam : Real}
    (ha : IsSymmetricCoeffField a)
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ descendantsAtDepth Q j) :
    let principal := oneStepSelectedDirichletCell a P hEll hP R hR
    let oscillatory := oneStepSelectedDirichletCell a F hEll hF R hR
    |volumeAverage (openCubeSet R) (fun x =>
        vecDot (principal.field x) (matVecMul (a x) (oscillatory.field x)))| ≤
      Real.sqrt (volumeAverage (openCubeSet R) (fun x =>
        vecDot (principal.field x) (matVecMul (a x) (principal.field x)))) *
      Real.sqrt (volumeAverage (openCubeSet R) (fun x =>
        vecDot (oscillatory.field x)
          (matVecMul (a x) (oscillatory.field x)))) := by
  let principal := oneStepSelectedDirichletCell a P hEll hP R hR
  let oscillatory := oneStepSelectedDirichletCell a F hEll hF R hR
  have hpMem : MemVectorL2 (openCubeSet R) principal.field := by
    exact (hP R hR).add principal.correction.toH1Function.grad_memVectorL2
  have hoMem : MemVectorL2 (openCubeSet R) oscillatory.field := by
    exact (hF R hR).add oscillatory.correction.toH1Function.grad_memVectorL2
  have hpFlux : MemVectorL2 (openCubeSet R)
      (fun x => matVecMul (a x) (principal.field x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn (hEll R hR) hpMem
  have hoFlux : MemVectorL2 (openCubeSet R)
      (fun x => matVecMul (a x) (oscillatory.field x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn (hEll R hR) hoMem
  have hCrossOpen : IntegrableOn (fun x =>
      vecDot (principal.field x) (matVecMul (a x) (oscillatory.field x)))
      (openCubeSet R) :=
    integrableOn_vecDot_of_memVectorL2 hpMem hoFlux
  have hPOpen : IntegrableOn (fun x =>
      vecDot (principal.field x) (matVecMul (a x) (principal.field x)))
      (openCubeSet R) :=
    integrableOn_vecDot_of_memVectorL2 hpMem hpFlux
  have hOOpen : IntegrableOn (fun x =>
      vecDot (oscillatory.field x) (matVecMul (a x) (oscillatory.field x)))
      (openCubeSet R) :=
    integrableOn_vecDot_of_memVectorL2 hoMem hoFlux
  have hCrossInt : Integrable (fun x =>
      vecDot (principal.field x) (matVecMul (a x) (oscillatory.field x)))
      (normalizedCubeMeasure R) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hCrossOpen)
  have hPInt : Integrable (fun x =>
      vecDot (principal.field x) (matVecMul (a x) (principal.field x)))
      (normalizedCubeMeasure R) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hPOpen)
  have hOInt : Integrable (fun x =>
      vecDot (oscillatory.field x) (matVecMul (a x) (oscillatory.field x)))
      (normalizedCubeMeasure R) :=
    integrable_normalizedCubeMeasure_of_integrableOn_cubeSet R
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hOOpen)
  have hEllCube : IsAEEllipticFieldOn lam Lam (cubeSet R) a :=
    (IsAEEllipticFieldOn.of_isEllipticFieldOn (hEll R hR)).cubeSet_of_openCubeSet
  have hEllNorm : ∀ᵐ x ∂normalizedCubeMeasure R,
      IsEllipticMatrix lam Lam (a x) := by
    change ∀ᵐ x ∂ENNReal.ofReal ((cubeVolume R)⁻¹) •
        volume.restrict (cubeSet R), IsEllipticMatrix lam Lam (a x)
    exact Measure.ae_smul_measure
      (by simpa [volumeMeasureOn] using hEllCube.ae_isEllipticMatrix)
      (ENNReal.ofReal ((cubeVolume R)⁻¹))
  have hSymm : ∀ᵐ x ∂normalizedCubeMeasure R, (a x).IsSymm :=
    Filter.Eventually.of_forall ha
  have hNonneg : ∀ᵐ x ∂normalizedCubeMeasure R,
      ∀ w : Vec d, 0 ≤ vecDot w (matVecMul (a x) w) := by
    filter_upwards [hEllNorm] with x hx
    intro w
    have hlower := lowerBound_symmPart_of_isEllipticMatrix hx w
    rw [symmPart_eq_self_of_isSymmetricCoeffField ha x] at hlower
    exact hlower.trans' <| mul_nonneg hx.1.le (vecNormSq_nonneg w)
  exact abs_volumeAverage_openCubeSet_matrix_cross_le_sqrt_energies
    R a principal.field oscillatory.field hCrossInt hPInt hOInt hSymm hNonneg

/-- Dual selected-cell Cauchy estimate for the inverse lower-right block.
Symmetry and positivity of the inverse block are discharged from coefficient
ellipticity; the three normalized spatial integrability facts remain explicit
because the public library has no packaged `L²` transport through
`(symmPart a)⁻¹`. -/
theorem abs_oneStepSelectedNeumannCell_mixed_le_sqrt_energies
    {d : Nat} {Q R : TriadicCube d} {j : Nat}
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    {lam Lam : Real}
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ descendantsAtDepth Q j)
    (hCrossInt : Integrable (fun x =>
      let principal := oneStepSelectedNeumannCell a P hEll hP R hR
      let oscillatory := oneStepSelectedNeumannCell a F hEll hF R hR
      vecDot (principal.flux x)
        (matVecMul (blockMatrixOfCoeff (a x)).lowerRight
          (oscillatory.flux x))) (normalizedCubeMeasure R))
    (hPInt : Integrable (fun x =>
      let principal := oneStepSelectedNeumannCell a P hEll hP R hR
      vecDot (principal.flux x)
        (matVecMul (blockMatrixOfCoeff (a x)).lowerRight
          (principal.flux x))) (normalizedCubeMeasure R))
    (hOInt : Integrable (fun x =>
      let oscillatory := oneStepSelectedNeumannCell a F hEll hF R hR
      vecDot (oscillatory.flux x)
        (matVecMul (blockMatrixOfCoeff (a x)).lowerRight
          (oscillatory.flux x))) (normalizedCubeMeasure R)) :
    let principal := oneStepSelectedNeumannCell a P hEll hP R hR
    let oscillatory := oneStepSelectedNeumannCell a F hEll hF R hR
    |volumeAverage (openCubeSet R) (fun x =>
        vecDot (principal.flux x)
          (matVecMul (blockMatrixOfCoeff (a x)).lowerRight
            (oscillatory.flux x)))| ≤
      Real.sqrt (volumeAverage (openCubeSet R) (fun x =>
        vecDot (principal.flux x)
          (matVecMul (blockMatrixOfCoeff (a x)).lowerRight
            (principal.flux x)))) *
      Real.sqrt (volumeAverage (openCubeSet R) (fun x =>
        vecDot (oscillatory.flux x)
          (matVecMul (blockMatrixOfCoeff (a x)).lowerRight
            (oscillatory.flux x)))) := by
  let principal := oneStepSelectedNeumannCell a P hEll hP R hR
  let oscillatory := oneStepSelectedNeumannCell a F hEll hF R hR
  let Ainv : Vec d → Mat d := fun x => (blockMatrixOfCoeff (a x)).lowerRight
  have hEllCube : IsAEEllipticFieldOn lam Lam (cubeSet R) a :=
    (IsAEEllipticFieldOn.of_isEllipticFieldOn (hEll R hR)).cubeSet_of_openCubeSet
  have hEllNorm : ∀ᵐ x ∂normalizedCubeMeasure R,
      IsEllipticMatrix lam Lam (a x) := by
    change ∀ᵐ x ∂ENNReal.ofReal ((cubeVolume R)⁻¹) •
        volume.restrict (cubeSet R), IsEllipticMatrix lam Lam (a x)
    exact Measure.ae_smul_measure
      (by simpa [volumeMeasureOn] using hEllCube.ae_isEllipticMatrix)
      (ENNReal.ofReal ((cubeVolume R)⁻¹))
  have hSymm : ∀ᵐ x ∂normalizedCubeMeasure R, (Ainv x).IsSymm := by
    filter_upwards with x
    exact blockMatrixOfCoeff_lowerRight_isSymm (a x)
  have hNonneg : ∀ᵐ x ∂normalizedCubeMeasure R,
      ∀ w : Vec d, 0 ≤ vecDot w (matVecMul (Ainv x) w) := by
    filter_upwards [hEllNorm] with x hx
    intro w
    simpa only [Ainv, blockMatrixOfCoeff] using
      symmPart_inv_nonneg_of_isEllipticMatrix hx w
  exact abs_volumeAverage_openCubeSet_matrix_cross_le_sqrt_energies
    R Ainv principal.flux oscillatory.flux
      (by simpa only [principal, oscillatory, Ainv] using hCrossInt)
      (by simpa only [principal, Ainv] using hPInt)
      (by simpa only [oscillatory, Ainv] using hOInt)
      hSymm hNonneg

/-- Probability-space Cauchy--Schwarz for one cell's mixed energy.  The
pointwise premise is the energy Cauchy inequality for the principal and
oscillatory minimizers. -/
theorem abs_integral_mixed_le_sqrt_integral_mul_sqrt_integral
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {mixed principal oscillatory : Omega -> Real}
    (hmixedInt : Integrable mixed mu)
    (hprincipalInt : Integrable principal mu)
    (hoscillatoryInt : Integrable oscillatory mu)
    (hprincipal0 : 0 ≤ᵐ[mu] principal)
    (hoscillatory0 : 0 ≤ᵐ[mu] oscillatory)
    (hmixed : ∀ᵐ omega ∂mu, |mixed omega| ≤
      Real.sqrt (principal omega) * Real.sqrt (oscillatory omega)) :
    |∫ omega, mixed omega ∂mu| ≤
      Real.sqrt (∫ omega, principal omega ∂mu) *
        Real.sqrt (∫ omega, oscillatory omega ∂mu) := by
  calc
    |∫ omega, mixed omega ∂mu| <= ∫ omega, |mixed omega| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤ ∫ omega, Real.sqrt (principal omega) *
        Real.sqrt (oscillatory omega) ∂mu := by
      have hproduct : Integrable (fun omega => Real.sqrt (principal omega) *
          Real.sqrt (oscillatory omega)) mu := by
        have hprincipalMem : MemLp (fun omega => Real.sqrt (principal omega)) 2 mu :=
          (memLp_two_iff_integrable_sq
            (Real.continuous_sqrt.comp_aestronglyMeasurable
              hprincipalInt.aestronglyMeasurable)).2 <|
            hprincipalInt.congr <| by
              filter_upwards [hprincipal0] with omega homega
              rw [Real.sq_sqrt homega]
        have hoscillatoryMem : MemLp (fun omega => Real.sqrt (oscillatory omega)) 2 mu :=
          (memLp_two_iff_integrable_sq
            (Real.continuous_sqrt.comp_aestronglyMeasurable
              hoscillatoryInt.aestronglyMeasurable)).2 <|
            hoscillatoryInt.congr <| by
              filter_upwards [hoscillatory0] with omega homega
              rw [Real.sq_sqrt homega]
        exact hprincipalMem.integrable_mul hoscillatoryMem
      exact integral_mono_ae hmixedInt.abs hproduct hmixed
    _ ≤ Real.sqrt (∫ omega, principal omega ∂mu) *
        Real.sqrt (∫ omega, oscillatory omega ∂mu) :=
      integral_sqrt_mul_sqrt_le hprincipalInt hoscillatoryInt
        hprincipal0 hoscillatory0

/-- Finite-family mixed component bound after inserting a principal budget
and the `delta^30` oscillatory budget. -/
theorem normalized_finset_sum_mixed_le_delta_fifteen
    {iota : Type*} [DecidableEq iota]
    (cells : Finset iota) (hcells : cells.Nonempty)
    (mixed principal oscillatory : iota -> Real)
    (hprincipal0 : ∀ i, i ∈ cells → 0 ≤ principal i)
    (hoscillatory0 : ∀ i, i ∈ cells → 0 ≤ oscillatory i)
    (hmixed : ∀ i, i ∈ cells → mixed i ≤
      Real.sqrt (principal i) * Real.sqrt (oscillatory i))
    {P O delta previous : Real}
    (hP : 0 ≤ P) (hO : 0 ≤ O) (hdelta : 0 ≤ delta)
    (hprevious : 0 ≤ previous)
    (hprincipalBudget : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, principal i ≤ P * previous)
    (hoscillatoryBudget : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, oscillatory i ≤ O * delta ^ 30 * previous) :
    ((cells.card : Real)⁻¹) * ∑ i ∈ cells, mixed i ≤
      Real.sqrt P * Real.sqrt O * delta ^ 15 * previous := by
  calc
    _ ≤ Real.sqrt (P * previous) *
        Real.sqrt (O * delta ^ 30 * previous) :=
      normalized_finset_sum_mixed_le_of_budgets cells hcells
        mixed principal oscillatory hprincipal0 hoscillatory0 hmixed
        hprincipalBudget hoscillatoryBudget
    _ = _ := sqrt_mul_sqrt_delta_thirty_mul hP hO hdelta hprevious

/-- The complete mixed-term fold used in both one-step variational arguments:
cellwise energy Cauchy, Cauchy in probability, finite-family Cauchy, and the
`delta^30`-to-`delta^15` square-root simplification. -/
theorem normalized_finset_abs_integral_mixed_le_delta_fifteen
    {iota Omega : Type*} [DecidableEq iota] [MeasurableSpace Omega]
    {mu : Measure Omega}
    (cells : Finset iota) (hcells : cells.Nonempty)
    (mixed principal oscillatory : iota → Omega → Real)
    (hmixedInt : ∀ i, i ∈ cells → Integrable (mixed i) mu)
    (hprincipalInt : ∀ i, i ∈ cells → Integrable (principal i) mu)
    (hoscillatoryInt : ∀ i, i ∈ cells → Integrable (oscillatory i) mu)
    (hprincipal0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] principal i)
    (hoscillatory0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] oscillatory i)
    (hmixed : ∀ i, i ∈ cells → ∀ᵐ omega ∂mu, |mixed i omega| ≤
      Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega))
    {P O delta previous : Real}
    (hP : 0 ≤ P) (hO : 0 ≤ O) (hdelta : 0 ≤ delta)
    (hprevious : 0 ≤ previous)
    (hprincipalBudget : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, ∫ omega, principal i omega ∂mu ≤ P * previous)
    (hoscillatoryBudget : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, ∫ omega, oscillatory i omega ∂mu ≤
        O * delta ^ 30 * previous) :
    ((cells.card : Real)⁻¹) * ∑ i ∈ cells,
        |∫ omega, mixed i omega ∂mu| ≤
      Real.sqrt P * Real.sqrt O * delta ^ 15 * previous := by
  apply normalized_finset_sum_mixed_le_delta_fifteen cells hcells
    (fun i => |∫ omega, mixed i omega ∂mu|)
    (fun i => ∫ omega, principal i omega ∂mu)
    (fun i => ∫ omega, oscillatory i omega ∂mu)
  · intro i hi
    exact integral_nonneg_of_ae (hprincipal0 i hi)
  · intro i hi
    exact integral_nonneg_of_ae (hoscillatory0 i hi)
  · intro i hi
    exact abs_integral_mixed_le_sqrt_integral_mul_sqrt_integral
      (hmixedInt i hi) (hprincipalInt i hi) (hoscillatoryInt i hi)
      (hprincipal0 i hi) (hoscillatory0 i hi) (hmixed i hi)
  · exact hP
  · exact hO
  · exact hdelta
  · exact hprevious
  · exact hprincipalBudget
  · exact hoscillatoryBudget

/-- Literal signed mixed component used in the finite-volume energy split.
The absolute value of the normalized signed sum is controlled by the
preceding normalized sum of absolute values. -/
theorem abs_normalized_finset_sum_integral_mixed_le_delta_fifteen
    {iota Omega : Type*} [DecidableEq iota] [MeasurableSpace Omega]
    {mu : Measure Omega}
    (cells : Finset iota) (hcells : cells.Nonempty)
    (mixed principal oscillatory : iota → Omega → Real)
    (hmixedInt : ∀ i, i ∈ cells → Integrable (mixed i) mu)
    (hprincipalInt : ∀ i, i ∈ cells → Integrable (principal i) mu)
    (hoscillatoryInt : ∀ i, i ∈ cells → Integrable (oscillatory i) mu)
    (hprincipal0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] principal i)
    (hoscillatory0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] oscillatory i)
    (hmixed : ∀ i, i ∈ cells → ∀ᵐ omega ∂mu, |mixed i omega| ≤
      Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega))
    {P O delta previous : Real}
    (hP : 0 ≤ P) (hO : 0 ≤ O) (hdelta : 0 ≤ delta)
    (hprevious : 0 ≤ previous)
    (hprincipalBudget : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, ∫ omega, principal i omega ∂mu ≤ P * previous)
    (hoscillatoryBudget : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, ∫ omega, oscillatory i omega ∂mu ≤
        O * delta ^ 30 * previous) :
    |((cells.card : Real)⁻¹) * ∑ i ∈ cells,
        ∫ omega, mixed i omega ∂mu| ≤
      Real.sqrt P * Real.sqrt O * delta ^ 15 * previous := by
  have havgAbs :
      |((cells.card : Real)⁻¹) * ∑ i ∈ cells,
          ∫ omega, mixed i omega ∂mu| ≤
        ((cells.card : Real)⁻¹) * ∑ i ∈ cells,
          |∫ omega, mixed i omega ∂mu| := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg cells.card))]
    exact mul_le_mul_of_nonneg_left
      (Finset.abs_sum_le_sum_abs (f := fun i => ∫ omega, mixed i omega ∂mu) cells)
      (inv_nonneg.mpr (Nat.cast_nonneg cells.card))
  exact havgAbs.trans <|
    normalized_finset_abs_integral_mixed_le_delta_fifteen
      cells hcells mixed principal oscillatory hmixedInt hprincipalInt
        hoscillatoryInt hprincipal0 hoscillatory0 hmixed
        hP hO hdelta hprevious hprincipalBudget hoscillatoryBudget

/-! ## Direct insertion into the penultimate variational inequalities -/

/-- Primal penultimate inequality obtained directly from a finite random-cell
family.  The three component bounds required by
`one_step_upper_penultimate_of_component_bounds` are constructed here from
the principal and oscillatory budgets plus cellwise energy Cauchy. -/
theorem one_step_upper_penultimate_of_finite_cell_budgets
    {iota Omega : Type*} [DecidableEq iota] [MeasurableSpace Omega]
    {mu : Measure Omega}
    (cells : Finset iota) (hcells : cells.Nonempty)
    (mixed principal oscillatory : iota → Omega → Real)
    (hmixedInt : ∀ i, i ∈ cells → Integrable (mixed i) mu)
    (hprincipalInt : ∀ i, i ∈ cells → Integrable (principal i) mu)
    (hoscillatoryInt : ∀ i, i ∈ cells → Integrable (oscillatory i) mu)
    (hprincipal0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] principal i)
    (hoscillatory0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] oscillatory i)
    (hmixed : ∀ i, i ∈ cells → ∀ᵐ omega ∂mu, |mixed i omega| ≤
      Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega))
    {delta tau h d A P O next cell previous : Real}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hO : 0 ≤ O)
    (hcell0 : 0 ≤ cell) (hprevious0 : 0 ≤ previous)
    (hPO : Real.sqrt P * Real.sqrt O ≤ A) (hOLe : O ≤ A)
    (hprincipalBudget : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, ∫ omega, principal i omega ∂mu ≤ P * previous)
    (hprincipalSharp : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, ∫ omega, principal i omega ∂mu ≤
        (1 - 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cell +
          A * delta ^ 15 * previous)
    (hoscillatoryBudget : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, ∫ omega, oscillatory i omega ∂mu ≤
        O * delta ^ 30 * previous)
    (hvariational :
      (1 / 2 : Real) * next ≤
        (1 / 2 : Real) * (((cells.card : Real)⁻¹) *
          ∑ i ∈ cells, ∫ omega, principal i omega ∂mu) +
        (((cells.card : Real)⁻¹) *
          ∑ i ∈ cells, ∫ omega, mixed i omega ∂mu) +
        (1 / 2 : Real) * (((cells.card : Real)⁻¹) *
          ∑ i ∈ cells, ∫ omega, oscillatory i omega ∂mu)) :
    (1 / 2 : Real) * next ≤
      (1 / 2 - tau * h / d + (4 * A) * delta ^ 4 * h ^ 2) * cell +
        (4 * A) * delta ^ 15 * previous := by
  let principalAvg : Real := ((cells.card : Real)⁻¹) *
    ∑ i ∈ cells, ∫ omega, principal i omega ∂mu
  let mixedAvg : Real := ((cells.card : Real)⁻¹) *
    ∑ i ∈ cells, ∫ omega, mixed i omega ∂mu
  let oscillatoryAvg : Real := ((cells.card : Real)⁻¹) *
    ∑ i ∈ cells, ∫ omega, oscillatory i omega ∂mu
  have hmixedRaw : |mixedAvg| ≤
      Real.sqrt P * Real.sqrt O * delta ^ 15 * previous := by
    simpa only [mixedAvg] using
      abs_normalized_finset_sum_integral_mixed_le_delta_fifteen
        cells hcells mixed principal oscillatory hmixedInt hprincipalInt
          hoscillatoryInt hprincipal0 hoscillatory0 hmixed
          hP hO hdelta0 hprevious0 hprincipalBudget hoscillatoryBudget
  have htail0 : 0 ≤ delta ^ 15 * previous := by positivity
  have hmixedFinal : |mixedAvg| ≤ A * delta ^ 15 * previous := by
    exact hmixedRaw.trans <| by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hPO htail0
  have hoscFinal : oscillatoryAvg ≤ A * delta ^ 30 * previous := by
    have htail30 : 0 ≤ delta ^ 30 * previous := by positivity
    exact (show oscillatoryAvg ≤ O * delta ^ 30 * previous by
      simpa only [oscillatoryAvg] using hoscillatoryBudget).trans <| by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hOLe htail30
  apply one_step_upper_penultimate_of_component_bounds
    hdelta0 hdelta1 hA hcell0 hprevious0
    (principal := principalAvg) (mixed := mixedAvg)
    (oscillatory := oscillatoryAvg)
  · simpa only [principalAvg] using hprincipalSharp
  · exact hmixedFinal
  · exact hoscFinal
  · simpa only [principalAvg, mixedAvg, oscillatoryAvg] using hvariational

/-- Dual counterpart of
`one_step_upper_penultimate_of_finite_cell_budgets`; only the sign of the
stationary drift changes. -/
theorem one_step_lower_penultimate_of_finite_cell_budgets
    {iota Omega : Type*} [DecidableEq iota] [MeasurableSpace Omega]
    {mu : Measure Omega}
    (cells : Finset iota) (hcells : cells.Nonempty)
    (mixed principal oscillatory : iota → Omega → Real)
    (hmixedInt : ∀ i, i ∈ cells → Integrable (mixed i) mu)
    (hprincipalInt : ∀ i, i ∈ cells → Integrable (principal i) mu)
    (hoscillatoryInt : ∀ i, i ∈ cells → Integrable (oscillatory i) mu)
    (hprincipal0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] principal i)
    (hoscillatory0 : ∀ i, i ∈ cells → 0 ≤ᵐ[mu] oscillatory i)
    (hmixed : ∀ i, i ∈ cells → ∀ᵐ omega ∂mu, |mixed i omega| ≤
      Real.sqrt (principal i omega) * Real.sqrt (oscillatory i omega))
    {delta tau h d A P O nextStarInv cellStarInv previousInv : Real}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hO : 0 ≤ O)
    (hcell0 : 0 ≤ cellStarInv) (hprevious0 : 0 ≤ previousInv)
    (hPO : Real.sqrt P * Real.sqrt O ≤ A) (hOLe : O ≤ A)
    (hprincipalBudget : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, ∫ omega, principal i omega ∂mu ≤ P * previousInv)
    (hprincipalSharp : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, ∫ omega, principal i omega ∂mu ≤
        (1 + 2 * tau * h / d + A * delta ^ 4 * h ^ 2) * cellStarInv +
          A * delta ^ 15 * previousInv)
    (hoscillatoryBudget : ((cells.card : Real)⁻¹) *
      ∑ i ∈ cells, ∫ omega, oscillatory i omega ∂mu ≤
        O * delta ^ 30 * previousInv)
    (hvariational :
      (1 / 2 : Real) * nextStarInv ≤
        (1 / 2 : Real) * (((cells.card : Real)⁻¹) *
          ∑ i ∈ cells, ∫ omega, principal i omega ∂mu) +
        (((cells.card : Real)⁻¹) *
          ∑ i ∈ cells, ∫ omega, mixed i omega ∂mu) +
        (1 / 2 : Real) * (((cells.card : Real)⁻¹) *
          ∑ i ∈ cells, ∫ omega, oscillatory i omega ∂mu)) :
    (1 / 2 : Real) * nextStarInv ≤
      (1 / 2 + tau * h / d + (4 * A) * delta ^ 4 * h ^ 2) * cellStarInv +
        (4 * A) * delta ^ 15 * previousInv := by
  let principalAvg : Real := ((cells.card : Real)⁻¹) *
    ∑ i ∈ cells, ∫ omega, principal i omega ∂mu
  let mixedAvg : Real := ((cells.card : Real)⁻¹) *
    ∑ i ∈ cells, ∫ omega, mixed i omega ∂mu
  let oscillatoryAvg : Real := ((cells.card : Real)⁻¹) *
    ∑ i ∈ cells, ∫ omega, oscillatory i omega ∂mu
  have hmixedRaw : |mixedAvg| ≤
      Real.sqrt P * Real.sqrt O * delta ^ 15 * previousInv := by
    simpa only [mixedAvg] using
      abs_normalized_finset_sum_integral_mixed_le_delta_fifteen
        cells hcells mixed principal oscillatory hmixedInt hprincipalInt
          hoscillatoryInt hprincipal0 hoscillatory0 hmixed
          hP hO hdelta0 hprevious0 hprincipalBudget hoscillatoryBudget
  have htail0 : 0 ≤ delta ^ 15 * previousInv := by positivity
  have hmixedFinal : |mixedAvg| ≤ A * delta ^ 15 * previousInv := by
    exact hmixedRaw.trans <| by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hPO htail0
  have hoscFinal : oscillatoryAvg ≤ A * delta ^ 30 * previousInv := by
    have htail30 : 0 ≤ delta ^ 30 * previousInv := by positivity
    exact (show oscillatoryAvg ≤ O * delta ^ 30 * previousInv by
      simpa only [oscillatoryAvg] using hoscillatoryBudget).trans <| by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hOLe htail30
  apply one_step_lower_penultimate_of_component_bounds
    hdelta0 hdelta1 hA hcell0 hprevious0
    (principal := principalAvg) (mixed := mixedAvg)
    (oscillatory := oscillatoryAvg)
  · simpa only [principalAvg] using hprincipalSharp
  · exact hmixedFinal
  · exact hoscFinal
  · simpa only [principalAvg, mixedAvg, oscillatoryAvg] using hvariational

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
