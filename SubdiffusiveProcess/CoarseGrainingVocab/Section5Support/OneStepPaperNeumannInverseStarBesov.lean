module

public import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffP4Bounds
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPaperNeumannCellBesov
public import SubdiffusiveProcess.Providers.Section2.CoarseGrainedPoincare
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField

@[expose] public section

/-!
# Paper-sign Neumann cell estimate in the inverse-star metric

This is the dual, paper-sign counterpart of the Dirichlet quarter-Besov cell
estimate used by the primal one-step competitor.  The shell datum is formed
between cutoffs `n` and `n + h`, while the cell energy may be measured at an
independent cutoff `L`.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private theorem integral_coeffOn_gradientEnergy_eq_publicCoeffField
    {d : ℕ} (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d)
    (F : Vec d → Vec d) :
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

/-- The paper-sign Neumann cell energy, measured in the literal inverse-star
metric at cutoff `L`, is controlled by the lower coarse-Poincare factor and
the quarter-Besov size of the shell-flux fluctuation. -/
theorem oneStepPaperNeumannCellFluctuation_inverseStar_energy_le_poincare_quarter
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (hgradEq : uS.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad)
    (X : OneStepNeumannCellMinimizer R
      (Ch03.publicCoeffField R
        (aCutoffEnvelopeTriadicCoeffFamily M L omega))
      (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh)) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.flux x)
          (matVecMul
            ((blockMatrixOfCoeff (scalarCoeffField
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)).lowerRight)
            (X.flux x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm R (2 : ℝ≥0∞)
            (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh))
          (cubeScaleFactor R * ∑ k : Fin d,
            cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
              (((oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf
                ).coord k).grad x))) := by
  let a := aCutoffEnvelopeTriadicCoeffFamily M L omega
  let ell : ℝ :=
    (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
      Ch03.poincareLowerEllipticityFactor R a (1 / 4 : ℝ) (.finite 1)) ^ 2
  have hEll := Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet R a
  have hpot : MemLp X.potential.toH1Function.grad
      (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet R
      X.potential.toH1Function.grad_memVectorL2
  have hfactor0 : 0 ≤
      Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor R a (1 / 4 : ℝ) (.finite 1) := by
    unfold Ch03.poincareDiscountFactor Ch03.poincareLowerEllipticityFactor
    exact mul_nonneg
      (Real.rpow_nonneg
        (geometricDiscount_pos (by norm_num : (0 : ℝ) < (1 / 4) * 1)).le _)
      (Real.rpow_nonneg
        (Ch02.lambdaSq_finite_nonneg R a
          (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 : ℝ) ≤ 1)) _)
  have hsqrtEll : Real.sqrt ell =
      Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor R a (1 / 4 : ℝ) (.finite 1) :=
    Real.sqrt_sq hfactor0
  have henergy :
      (∫ x, vecDot (X.potential.toH1Function.grad x)
          (matVecMul ((a.coeffOn R).toCoeffField x)
            (X.potential.toH1Function.grad x))
        ∂normalizedCubeMeasure R) =
      volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) := by
    rw [integral_coeffOn_gradientEnergy_eq_publicCoeffField]
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure,
      oneStep_volumeAverage_openCubeSet_eq_cubeAverage]
    rfl
  have hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm R (1 / 4 : ℝ) N
          X.potential.toH1Function.grad ≤
        Real.sqrt ell *
          Real.sqrt (volumeAverage (openCubeSet R) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x))) := by
    intro N
    have hp := SubdiffusiveProcess.Providers.Section2.coarsePoincarePartialOneRaw
      R a (fun S ↦
        (aCutoffEnvelopeScalarTriadicCoeffData M L omega).onCube S
          |>.isSymmetric)
      (1 / 4 : ℝ) (by norm_num) X.potential.toH1Function
      (0 : Vec d → Vec d) MemLp.zero
      (isSolenoidalOn_zero (U := openCubeSet R)) N
    rw [hsqrtEll, ← henergy]
    exact hp.1
  have hpair :=
    X.energy_le_of_paperNeumannRawCellH1_quarter
      M n h omega q hh uS H hR hRhalf hgradEq hEll (sq_nonneg _) hpot hneg
  have hae : Ch03.publicCoeffField R a =ᵐ[
      volumeMeasureOn (openCubeSet R)]
      scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) := by
    exact Ch03.publicCoeffField_ae_eq_openCubeSet R a
  have hinverseEnergy :
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.flux x)
            (matVecMul
              ((blockMatrixOfCoeff (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)).lowerRight)
              (X.flux x))) =
        volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.potential.toH1Function.grad x) (X.flux x)) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    have hdet : IsUnit
        (scalarCoeffField
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x).det :=
      isUnit_det_of_isEllipticMatrix
        (isEllipticMatrix_scalarMatrix
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x))
    have hs : symmPart
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x) =
          scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x := by
      simp only [scalarCoeffField,
        Homogenization.Book.Ch02.symmPart_scalarMatrix]
    unfold OneStepNeumannCellMinimizer.flux blockMatrixOfCoeff
    dsimp only
    rw [hx, hs, matVecMul_mul, Matrix.nonsing_inv_mul _ hdet,
      matVecMul_one]
    exact vecDot_comm _ _
  rw [hinverseEnergy]
  simpa only [a, ell] using hpair

/-- The cell-local paper-sign carrier has the derivative-size bound required
by the Besov fold. -/
theorem oneStepPaperNeumannRawCellH1OnCell_euclideanGradientSize_le_cellB
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uR : H1Function (openCubeSet R))
    (HR : HasWeakHessianOn (openCubeSet R) uR)
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    cubeScaleFactor R * ∑ k : Fin d,
        cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
          (((oneStepPaperNeumannRawCellH1OnCell M n h omega q hh uR HR hRQ
            ).coord k).grad x)) ≤
      (d : ℝ) * (oneStepShellForcingCellB (Q := Q) (R := R)
          M n h omega q hh + oneStepCellB R HR) := by
  let G := oneStepPaperNeumannRawCellH1OnCell M n h omega q hh uR HR hRQ
  let S : CubeVectorH1Function R :=
    { coord := fun i ↦
        ((oneStepShellForcingH1 M n h omega q Q hh).coord i).restrict
          (isOpen_openCubeSet R) hRQ }
  have hshell : oneStepShellForcingCellB (Q := Q) (R := R)
      M n h omega q hh =
      cubeScaleFactor R * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        S.gradientCoordL2NormSum := by
    unfold oneStepShellForcingCellB CubeVectorH1Function.gradientCoordL2NormSum
    calc
      cubeScaleFactor R * ∑ i : Fin d, ∑ j : Fin d,
          cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦
            (oneStepShellForcingW14 M n h omega q Q hh).jacobian x i j) =
        cubeScaleFactor R * ∑ i : Fin d, ∑ j : Fin d,
          ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
            ‖(S.coord i).gradCoordToScalarL2 j‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        have hmem : MemLp (fun x ↦ (S.coord i).grad x j)
            (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
          (S.coord i).grad_memL2_normalizedCubeMeasure j
        calc
          cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦
              (oneStepShellForcingW14 M n h omega q Q hh).jacobian x i j) =
            cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ (S.coord i).grad x j) := by
              congr 1
          _ = ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
              ‖(S.coord i).gradCoordToScalarL2 j‖ :=
            cubeLpNorm_two_eq_volume_inv_rpow_half_mul_norm_toScalarL2_openCubeSet
              R hmem
      _ = cubeScaleFactor R * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d,
            ‖(S.coord i).gradCoordToScalarL2 j‖ := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        ring_nf
  have hraw : G.gradientCoordL2NormSum ≤
      S.gradientCoordL2NormSum + HR.hessianCoordL2NormSum := by
    unfold CubeVectorH1Function.gradientCoordL2NormSum
    calc
      ∑ i : Fin d, (G.coord i).gradientCoordL2NormSum ≤
          ∑ i : Fin d, ((S.coord i).gradientCoordL2NormSum +
            (HR.gradCoordH1Function i).gradientCoordL2NormSum) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        unfold H1Function.gradientCoordL2NormSum
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ ↦ ?_
        simpa only [G, S, oneStepPaperNeumannRawCellH1OnCell,
          H1Function.gradCoordToScalarL2_add] using
            norm_add_le ((S.coord i).gradCoordToScalarL2 j)
              ((HR.gradCoordH1Function i).gradCoordToScalarL2 j)
      _ = (∑ i : Fin d, (S.coord i).gradientCoordL2NormSum) +
          ∑ i : Fin d, (HR.gradCoordH1Function i).gradientCoordL2NormSum :=
        Finset.sum_add_distrib
      _ = S.gradientCoordL2NormSum + HR.hessianCoordL2NormSum := by congr 1
  have hscale : 0 ≤ cubeScaleFactor R := cubeScaleFactor_nonneg R
  have hnorm := cubeVectorH1_euclideanGradientSum_le R G
  have hfactor : 0 ≤ cubeScaleFactor R *
      ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ)) := by
    exact mul_nonneg hscale <| mul_nonneg (Nat.cast_nonneg d) <|
      Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R)) _
  calc
    cubeScaleFactor R * ∑ k : Fin d,
        cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm ((G.coord k).grad x)) ≤
      cubeScaleFactor R *
        ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          ∑ k : Fin d, (G.coord k).gradientCoordL2NormSum) :=
      mul_le_mul_of_nonneg_left hnorm hscale
    _ ≤ cubeScaleFactor R *
        ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          (S.gradientCoordL2NormSum + HR.hessianCoordL2NormSum)) := by
      calc
        _ = (cubeScaleFactor R *
            ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ))) *
              ∑ k : Fin d, (G.coord k).gradientCoordL2NormSum := by ring
        _ ≤ (cubeScaleFactor R *
            ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ))) *
              (S.gradientCoordL2NormSum + HR.hessianCoordL2NormSum) :=
          mul_le_mul_of_nonneg_left hraw hfactor
        _ = _ := by ring
    _ = (d : ℝ) *
        (cubeScaleFactor R * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          S.gradientCoordL2NormSum + oneStepCellB R HR) := by
      unfold oneStepCellB oneStepCellNormalizedHessianSize
      ring
    _ = _ := by rw [← hshell]

/-- Cell-local form of the paper-sign inverse-star estimate.  Only a weak
Hessian realization on `R` is required; no interior-half inclusion is part of
this interface. -/
theorem oneStepPaperNeumannCellFluctuation_inverseStar_energy_le_poincare_quarter_onCell
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uR : H1Function (openCubeSet R))
    (HR : HasWeakHessianOn (openCubeSet R) uR)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (hgradEq : uR.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad)
    (X : OneStepNeumannCellMinimizer R
      (Ch03.publicCoeffField R
        (aCutoffEnvelopeTriadicCoeffFamily M L omega))
      (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh)) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.flux x)
          (matVecMul
            ((blockMatrixOfCoeff (scalarCoeffField
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)).lowerRight)
            (X.flux x))) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 *
        (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
          Ch03.poincareLowerEllipticityFactor R
            (aCutoffEnvelopeTriadicCoeffFamily M L omega) (1 / 4 : ℝ)
              (.finite 1)) ^ 2 *
        oneStepCellBesovError
          (cubeLpNorm R (2 : ℝ≥0∞)
            (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh))
          (cubeScaleFactor R * ∑ k : Fin d,
            cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
              (((oneStepPaperNeumannRawCellH1OnCell
                M n h omega q hh uR HR hRQ).coord k).grad x))) := by
  let a := aCutoffEnvelopeTriadicCoeffFamily M L omega
  let ell : ℝ :=
    (Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
      Ch03.poincareLowerEllipticityFactor R a (1 / 4 : ℝ) (.finite 1)) ^ 2
  have hEll := Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet R a
  have hpot : MemLp X.potential.toH1Function.grad
      (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet R
      X.potential.toH1Function.grad_memVectorL2
  have hfactor0 : 0 ≤
      Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor R a (1 / 4 : ℝ) (.finite 1) := by
    unfold Ch03.poincareDiscountFactor Ch03.poincareLowerEllipticityFactor
    exact mul_nonneg
      (Real.rpow_nonneg
        (geometricDiscount_pos (by norm_num : (0 : ℝ) < (1 / 4) * 1)).le _)
      (Real.rpow_nonneg
        (Ch02.lambdaSq_finite_nonneg R a
          (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 : ℝ) ≤ 1)) _)
  have hsqrtEll : Real.sqrt ell =
      Ch03.poincareDiscountFactor (1 / 4 : ℝ) (.finite 1) *
        Ch03.poincareLowerEllipticityFactor R a (1 / 4 : ℝ) (.finite 1) :=
    Real.sqrt_sq hfactor0
  have henergy :
      (∫ x, vecDot (X.potential.toH1Function.grad x)
          (matVecMul ((a.coeffOn R).toCoeffField x)
            (X.potential.toH1Function.grad x))
        ∂normalizedCubeMeasure R) =
      volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) := by
    rw [integral_coeffOn_gradientEnergy_eq_publicCoeffField]
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure,
      oneStep_volumeAverage_openCubeSet_eq_cubeAverage]
    rfl
  have hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm R (1 / 4 : ℝ) N
          X.potential.toH1Function.grad ≤
        Real.sqrt ell *
          Real.sqrt (volumeAverage (openCubeSet R) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x))) := by
    intro N
    have hp := SubdiffusiveProcess.Providers.Section2.coarsePoincarePartialOneRaw
      R a (fun S ↦
        (aCutoffEnvelopeScalarTriadicCoeffData M L omega).onCube S
          |>.isSymmetric)
      (1 / 4 : ℝ) (by norm_num) X.potential.toH1Function
      (0 : Vec d → Vec d) MemLp.zero
      (isSolenoidalOn_zero (U := openCubeSet R)) N
    rw [hsqrtEll, ← henergy]
    exact hp.1
  have hpair :=
    X.energy_le_of_paperNeumannRawCellH1OnCell_quarter
      M n h omega q hh uR HR hR hRQ hgradEq hEll (sq_nonneg _) hpot hneg
  have hae : Ch03.publicCoeffField R a =ᵐ[
      volumeMeasureOn (openCubeSet R)]
      scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) := by
    exact Ch03.publicCoeffField_ae_eq_openCubeSet R a
  have hinverseEnergy :
      volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.flux x)
            (matVecMul
              ((blockMatrixOfCoeff (scalarCoeffField
                (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x)).lowerRight)
              (X.flux x))) =
        volumeAverage (openCubeSet R) (fun x ↦
          vecDot (X.potential.toH1Function.grad x) (X.flux x)) := by
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    have hdet : IsUnit
        (scalarCoeffField
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x).det :=
      isUnit_det_of_isEllipticMatrix
        (isEllipticMatrix_scalarMatrix
          (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x))
    have hs : symmPart
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x) =
          scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) x := by
      simp only [scalarCoeffField,
        Homogenization.Book.Ch02.symmPart_scalarMatrix]
    unfold OneStepNeumannCellMinimizer.flux blockMatrixOfCoeff
    dsimp only
    rw [hx, hs, matVecMul_mul, Matrix.nonsing_inv_mul _ hdet,
      matVecMul_one]
    exact vecDot_comm _ _
  rw [hinverseEnergy]
  simpa only [a, ell] using hpair

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support


