import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepRandomCellSpecialization
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepVectorH1Besov
import SubdiffusiveProcess.Providers.Section2.CoarseGrainedPoincare
import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField




open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.Providers.Section5

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section



theorem oneStep_publicFlux_inverseEnergy_eq {d : ℕ}
    (Q : Homogenization.TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (F : Homogenization.Vec d → Homogenization.Vec d) :
    ∫ x, vecDot
          (matVecMul (Ch03.publicCoeffField Q a x) (F x))
          (matVecMul ((a.coeffOn Q).toCoeffField x)⁻¹
            (matVecMul (Ch03.publicCoeffField Q a x) (F x)))
        ∂normalizedCubeMeasure Q =
      ∫ x, vecDot (F x)
          (matVecMul (Ch03.publicCoeffField Q a x) (F x))
        ∂normalizedCubeMeasure Q := by
  apply integral_congr_ae
  have haeCube : Ch03.publicCoeffField Q a =ᵐ[cubeMeasure Q]
      (a.coeffOn Q).toCoeffField := by
    simpa [volumeMeasureOn, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using
      Ch03.publicCoeffField_ae_eq_openCubeSet Q a
  have hae := Gagliardo.ae_normalizedCubeMeasure_iff.2 haeCube
  filter_upwards [hae, ae_openCubeSet_normalizedCubeMeasure Q] with x hax hx
  have hEll :=
    (Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet Q a).2 x hx
  have hdet := isUnit_det_of_isEllipticMatrix hEll
  rw [← hax, matVecMul_mul, Matrix.nonsing_inv_mul _ hdet, matVecMul_one,
    vecDot_comm]

/-- The public `CoeffOn` and its pointwise elliptic representative have the
same normalized gradient energy. -/
theorem oneStep_publicGradient_energy_eq {d : ℕ}
    (Q : Homogenization.TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (F : Homogenization.Vec d → Homogenization.Vec d) :
    ∫ x, vecDot (F x)
          (matVecMul ((a.coeffOn Q).toCoeffField x) (F x))
        ∂normalizedCubeMeasure Q =
      ∫ x, vecDot (F x)
          (matVecMul (Ch03.publicCoeffField Q a x) (F x))
        ∂normalizedCubeMeasure Q := by
  apply integral_congr_ae
  have haeCube : Ch03.publicCoeffField Q a =ᵐ[cubeMeasure Q]
      (a.coeffOn Q).toCoeffField := by
    simpa [volumeMeasureOn, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using
      Ch03.publicCoeffField_ae_eq_openCubeSet Q a
  have hae := Gagliardo.ae_normalizedCubeMeasure_iff.2 haeCube
  filter_upwards [hae] with x hax
  rw [hax]

/-- The one-step primal random-cell energy with both Besov inputs discharged.
The sole field hypothesis is the centered gradient used in the manuscript;
the coefficient is the canonical pointwise representative of the public
triadic family. -/
theorem oneStep_dirichletCell_energy_le_poincare_quarter
    {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (haSymm : ∀ R, (a.coeffOn R).IsSymmetric)
    (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (X : OneStepDirichletCellMinimizer Q
      (Ch03.publicCoeffField Q a) u.grad)
    (hcenter : cubeAverageVec Q u.grad = 0) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.field x)
          (matVecMul (Ch03.publicCoeffField Q a x) (X.field x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          oneStepQuarterCellConst d) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareUpperEllipticityFactor Q a (1 / 4 : ℝ)
            (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) u.grad) (oneStepCellB Q H) := by
  let ell : ℝ :=
    (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
      Ch03.poincareUpperEllipticityFactor Q a (1 / 4 : ℝ) (.finite 1)) ^ 2
  have hEll := Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet Q a
  have hfieldL2 : MemVectorL2 (openCubeSet Q) X.field :=
    u.grad_memVectorL2.add X.correction.toH1Function.grad_memVectorL2
  have hfluxL2 : MemVectorL2 (openCubeSet Q)
      (fun x ↦ matVecMul (Ch03.publicCoeffField Q a x) (X.field x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hfieldL2
  have hflux : MemLp
      (fun x ↦ matVecMul (Ch03.publicCoeffField Q a x) (X.field x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q hfluxL2
  have hfactor0 : 0 ≤
      Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareUpperEllipticityFactor Q a (1 / 4 : ℝ) (.finite 1) := by
    unfold Ch03.poincareDiscountFactor Ch03.poincareUpperEllipticityFactor
    exact mul_nonneg
      (Real.rpow_nonneg
        (geometricDiscount_pos (by norm_num : (0 : ℝ) < (1 / 4) * 1)).le _)
      (Real.rpow_nonneg
        (Ch02.LambdaSq_finite_nonneg Q a
          (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 : ℝ) ≤ 1)) _)
  have hsqrtEll : Real.sqrt ell =
      Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareUpperEllipticityFactor Q a (1 / 4 : ℝ) (.finite 1) := by
    exact Real.sqrt_sq hfactor0
  have henergy :
      (∫ x, vecDot
          (matVecMul (Ch03.publicCoeffField Q a x) (X.field x))
          (matVecMul ((a.coeffOn Q).toCoeffField x)⁻¹
            (matVecMul (Ch03.publicCoeffField Q a x) (X.field x)))
        ∂normalizedCubeMeasure Q) =
      volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.field x)
          (matVecMul (Ch03.publicCoeffField Q a x) (X.field x))) := by
    rw [oneStep_publicFlux_inverseEnergy_eq]
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure,
      oneStep_volumeAverage_openCubeSet_eq_cubeAverage]
  have hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q (1 / 4 : ℝ) N
          (fun x ↦ matVecMul (Ch03.publicCoeffField Q a x) (X.field x)) ≤
        Real.sqrt ell *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.field x)
              (matVecMul (Ch03.publicCoeffField Q a x) (X.field x)))) := by
    intro N
    have hp := SubdiffusiveProcess.Providers.Section2.coarsePoincarePartialOneRaw
      Q a haSymm (1 / 4 : ℝ) (by norm_num)
      X.correction.toH1Function
      (fun x ↦ matVecMul (Ch03.publicCoeffField Q a x) (X.field x))
      hfluxL2 (X.weakDivergenceFree hEll u.grad_memVectorL2) N
    rw [hsqrtEll, ← henergy]
    exact hp.2
  simpa only [ell] using
    X.energy_le_of_gradient_quarter u H hEll (sq_nonneg _) hcenter hflux hneg

/-- Dual random-cell counterpart of
`oneStep_dirichletCell_energy_le_poincare_quarter`.  The selected Neumann
potential receives the lower-ellipticity branch of coarse Poincare, while the
centered datum receives the already proved quarter-Besov interpolation. -/
theorem oneStep_neumannCell_energy_le_poincare_quarter
    {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (haSymm : ∀ R, (a.coeffOn R).IsSymmetric)
    (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u)
    (X : OneStepNeumannCellMinimizer Q
      (Ch03.publicCoeffField Q a) u.grad)
    (hcenter : cubeAverageVec Q u.grad = 0) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          oneStepQuarterCellConst d) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor Q a (1 / 4 : ℝ)
            (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) u.grad) (oneStepCellB Q H) := by
  let ell : ℝ :=
    (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
      Ch03.poincareLowerEllipticityFactor Q a (1 / 4 : ℝ) (.finite 1)) ^ 2
  have hEll := Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet Q a
  have hgrad : MemLp X.potential.toH1Function.grad
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
      X.potential.toH1Function.grad_memVectorL2
  have hfactor0 : 0 ≤
      Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor Q a (1 / 4 : ℝ) (.finite 1) := by
    unfold Ch03.poincareDiscountFactor Ch03.poincareLowerEllipticityFactor
    exact mul_nonneg
      (Real.rpow_nonneg
        (geometricDiscount_pos (by norm_num : (0 : ℝ) < (1 / 4) * 1)).le _)
      (Real.rpow_nonneg
        (Ch02.lambdaSq_finite_nonneg Q a
          (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 : ℝ) ≤ 1)) _)
  have hsqrtEll : Real.sqrt ell =
      Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor Q a (1 / 4 : ℝ) (.finite 1) := by
    exact Real.sqrt_sq hfactor0
  have henergy :
      (∫ x, vecDot (X.potential.toH1Function.grad x)
          (matVecMul ((a.coeffOn Q).toCoeffField x)
            (X.potential.toH1Function.grad x))
        ∂normalizedCubeMeasure Q) =
      volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) := by
    rw [oneStep_publicGradient_energy_eq]
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure,
      oneStep_volumeAverage_openCubeSet_eq_cubeAverage]
    rfl
  have hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q (1 / 4 : ℝ) N
          X.potential.toH1Function.grad ≤
        Real.sqrt ell *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x))) := by
    intro N
    have hp := SubdiffusiveProcess.Providers.Section2.coarsePoincarePartialOneRaw
      Q a haSymm (1 / 4 : ℝ) (by norm_num)
      X.potential.toH1Function (0 : Homogenization.Vec d → Homogenization.Vec d)
      MeasureTheory.MemLp.zero (isSolenoidalOn_zero (U := openCubeSet Q)) N
    rw [hsqrtEll, ← henergy]
    exact hp.1
  simpa only [ell] using
    X.energy_le_of_gradient_quarter u H hEll (sq_nonneg _) hcenter hgrad hneg

/-- Solenoidal vector-`H¹` form of the lower random-cell estimate.  The
coarse-Poincare input is unchanged from the gradient specialization above;
only the positive quarter-Besov datum is supplied by the coordinatewise
vector carrier. -/
theorem oneStep_neumannCell_vectorH1_energy_le_poincare_quarter
    {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (haSymm : ∀ R, (a.coeffOn R).IsSymmetric)
    {F : Homogenization.Vec d → Homogenization.Vec d}
    (G : CubeVectorH1Function Q)
    (X : OneStepNeumannCellMinimizer Q (Ch03.publicCoeffField Q a) F)
    (hF_eq : F = cubeFluctuationVec Q G.toField) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor Q a (1 / 4 : ℝ)
            (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) F)
          (cubeScaleFactor Q * ∑ k : Fin d,
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x))) := by
  let ell : ℝ :=
    (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
      Ch03.poincareLowerEllipticityFactor Q a (1 / 4 : ℝ) (.finite 1)) ^ 2
  have hEll := Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet Q a
  have hgrad : MemLp X.potential.toH1Function.grad
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
      X.potential.toH1Function.grad_memVectorL2
  have hfactor0 : 0 ≤
      Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor Q a (1 / 4 : ℝ) (.finite 1) := by
    unfold Ch03.poincareDiscountFactor Ch03.poincareLowerEllipticityFactor
    exact mul_nonneg
      (Real.rpow_nonneg
        (geometricDiscount_pos (by norm_num : (0 : ℝ) < (1 / 4) * 1)).le _)
      (Real.rpow_nonneg
        (Ch02.lambdaSq_finite_nonneg Q a
          (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 : ℝ) ≤ 1)) _)
  have hsqrtEll : Real.sqrt ell =
      Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor Q a (1 / 4 : ℝ) (.finite 1) := by
    exact Real.sqrt_sq hfactor0
  have henergy :
      (∫ x, vecDot (X.potential.toH1Function.grad x)
          (matVecMul ((a.coeffOn Q).toCoeffField x)
            (X.potential.toH1Function.grad x))
        ∂normalizedCubeMeasure Q) =
      volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) := by
    rw [oneStep_publicGradient_energy_eq]
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure,
      oneStep_volumeAverage_openCubeSet_eq_cubeAverage]
    rfl
  have hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm Q (1 / 4 : ℝ) N
          X.potential.toH1Function.grad ≤
        Real.sqrt ell *
          Real.sqrt (volumeAverage (openCubeSet Q) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x))) := by
    intro N
    have hp := SubdiffusiveProcess.Providers.Section2.coarsePoincarePartialOneRaw
      Q a haSymm (1 / 4 : ℝ) (by norm_num)
      X.potential.toH1Function (0 : Homogenization.Vec d → Homogenization.Vec d)
      MeasureTheory.MemLp.zero (isSolenoidalOn_zero (U := openCubeSet Q)) N
    rw [hsqrtEll, ← henergy]
    exact hp.1
  simpa only [ell] using
    X.energy_le_of_vectorH1_quarter G hF_eq hEll (sq_nonneg _) hgrad hneg

/-- A.e.-representative form of the solenoidal vector-`H¹` estimate. -/
theorem oneStep_neumannCell_vectorH1_energy_le_poincare_quarter_ae
    {d : ℕ} [NeZero d]
    (Q : Homogenization.TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (haSymm : ∀ R, (a.coeffOn R).IsSymmetric)
    {F : Homogenization.Vec d → Homogenization.Vec d}
    (G : CubeVectorH1Function Q)
    (X : OneStepNeumannCellMinimizer Q (Ch03.publicCoeffField Q a) F)
    (hF_ae : F =ᵐ[volumeMeasureOn (openCubeSet Q)]
      cubeFluctuationVec Q G.toField) :
    volumeAverage (openCubeSet Q) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor Q a (1 / 4 : ℝ)
            (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q G.toField))
          (cubeScaleFactor Q * ∑ k : Fin d,
            cubeLpNorm Q (2 : ℝ≥0∞)
              (fun x ↦ euclideanNorm ((G.coord k).grad x))) := by
  let Y : OneStepNeumannCellMinimizer Q (Ch03.publicCoeffField Q a)
      (cubeFluctuationVec Q G.toField) := X.congrDatum hF_ae
  exact oneStep_neumannCell_vectorH1_energy_le_poincare_quarter
    Q a haSymm G Y rfl

end

end SubdiffusiveProcess.Providers.Section5
