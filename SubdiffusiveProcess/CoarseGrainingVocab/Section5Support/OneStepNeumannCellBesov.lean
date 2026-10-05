module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepConcreteCellCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCenteredVariance
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepMixedNorm
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannInteriorEquation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepVectorH1Besov
public import Homogenization.Sobolev.MatchedPair.Core

@[expose] public section

/-!
# Positive Besov carrier for the literal Neumann cell fluctuation

On an interior source cell, the field `exp(H) q - grad W` is represented
coordinatewise in `H¹` by the restricted smooth shell forcing minus the
gradient-coordinate `H¹` witness supplied by the weak Hessian of `W`.
The constant vector `q` disappears after subtracting the cell average.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The canonical triadic Neumann solution admits the half-parent weak
Hessian supplied by the deterministic interior CZ interface.  This is a
samplewise regularity statement about the already selected measurable
Lax--Milgram solution, not a second solution selection. -/
theorem exists_oneStepTriadicNeumann_innerHalfWeakHessian_reduced
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (Q : TriadicCube d) (hh : 0 < h) :
    ∃ uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)),
      uS.grad =
          (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad ∧
        ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS,
          H.hessianCoordL2NormSum ≤
            ∑ i : Fin d, ∑ _j : Fin d,
              @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestReducedBound
                d Q
                (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function
                (oneStepShellForcingH1 M n h omega q Q hh).divergence i
                (1 / 2 : ℝ) (7 / 12 : ℝ) (3 / 4 : ℝ) (7 / 8 : ℝ)
                (CubeCalderonZygmund.outerThreeQuarterSevenEighthCutoff Q) := by
  let u := oneStepTriadicNeumannSolution M n h q Q omega hh
  have hu : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) u
      (fun x ↦ -(oneStepShellForcingH1 M n h omega q Q hh).toField x) := by
    intro phi
    have hweak := oneStepTriadicNeumannSolution_isWeakSolution
      M n h q Q omega hh phi
    have hfield := oneStepShellForcingH1_toField_ae_eq
      M n h omega q Q hh
    calc
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (identityCoeffField d x) (u.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (-oneStepMultiplierAt M n h x omega • q)
            (phi.toH1Function.grad x) ∂volume := hweak
      _ = ∫ x in openCubeSet Q,
          vecDot (-(oneStepShellForcingH1 M n h omega q Q hh).toField x)
            (phi.toH1Function.grad x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hfield] with x hx
        rw [hx]
        simp only [neg_smul]
  obtain ⟨uS, _huSfun, huSgrad, H, hH⟩ :=
    exists_oneStepShellNeumann_innerHalfWeakHessian_reduced
      M n h omega q Q hh u hu
  exact ⟨uS, huSgrad, H, hH⟩

/-- Any mean-zero solution driven by the shell forcing has the same gradient
as the canonical triadic Neumann solution, modulo Sobolev representatives. -/
theorem oneStepShellNeumann_grad_ae_eq_triadic
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (Q : TriadicCube d) (hh : 0 < h)
    (uN : H1MeanZeroFunction (openCubeSet Q))
    (huN : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) uN
      (fun x ↦ -(oneStepShellForcingH1 M n h omega q Q hh).toField x)) :
    uN.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let uC := oneStepTriadicNeumannSolution M n h q Q omega hh
  have huC : IsMeanZeroNeumannRhsWeakSolution
      (identityCoeffField d) (openCubeSet Q) uC
      (fun x ↦ -(oneStepShellForcingH1 M n h omega q Q hh).toField x) := by
    intro phi
    have hweak := oneStepTriadicNeumannSolution_isWeakSolution
      M n h q Q omega hh phi
    have hfield := oneStepShellForcingH1_toField_ae_eq
      M n h omega q Q hh
    calc
      ∫ x in openCubeSet Q,
          vecDot (matVecMul (identityCoeffField d x) (uC.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (-oneStepMultiplierAt M n h x omega • q)
            (phi.toH1Function.grad x) ∂volume := hweak
      _ = ∫ x in openCubeSet Q,
          vecDot (-(oneStepShellForcingH1 M n h omega q Q hh).toField x)
            (phi.toH1Function.grad x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hfield] with x hx
        rw [hx]
        simp only [neg_smul]
  have hgrad :=
    IsMeanZeroNeumannRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
      (openCubeSet_nonempty_internal Q) huN huC
      (isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q))
  have hN := uN.toH1Function.coeFn_gradToVectorL2
  have hC := uC.toH1Function.coeFn_gradToVectorL2
  change uN.toH1Function.gradToVectorL2 =
    uC.toH1Function.gradToVectorL2 at hgrad
  rw [hgrad] at hN
  filter_upwards [hN, hC] with x hxN hxC
  exact hxN.symm.trans hxC

/-- Coordinatewise `H¹` realization of the nonconstant part
`(exp(H)-1)q - grad W` on an interior Neumann source cell. -/
noncomputable def oneStepNeumannRawCellH1
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ)) :
    CubeVectorH1Function R where
  coord i :=
    ((oneStepShellForcingH1 M n h omega q Q hh).coord i).restrict
        (isOpen_openCubeSet R)
        (hRhalf.trans <|
          (scaledOpenCubeSet_subset_scaledClosedCubeSet Q (1 / 2 : ℝ)).trans <|
            scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q
              (by norm_num) (by norm_num)) -
      (H.restrict (isOpen_openCubeSet R) hRhalf).gradCoordH1Function i

/-- The shell-only part of the Neumann vector-`H¹` datum on a source cell. -/
noncomputable def oneStepShellForcingCellH1
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ)) :
    CubeVectorH1Function R where
  coord i :=
    ((oneStepShellForcingH1 M n h omega q Q hh).coord i).restrict
      (isOpen_openCubeSet R)
      (hRhalf.trans <|
        (scaledOpenCubeSet_subset_scaledClosedCubeSet Q (1 / 2 : ℝ)).trans <|
          scaledClosedCubeSet_subset_openCubeSet_of_nonneg_of_lt_one Q
            (by norm_num) (by norm_num))

/-- Measurable coordinate-sum form of the shell-Jacobian contribution to the
positive cell derivative size. -/
def oneStepShellForcingCellB
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h) : ℝ :=
  cubeScaleFactor R * ∑ i : Fin d, ∑ j : Fin d,
    cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦
      (oneStepShellForcingW14 M n h omega q Q hh).jacobian x i j)

theorem measurable_oneStepShellForcingCellB
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Vec d) (hh : 0 < h) :
    Measurable fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
      oneStepShellForcingCellB (Q := Q) (R := R) M n h omega q hh := by
  unfold oneStepShellForcingCellB cubeLpNorm
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _hi
  apply Finset.measurable_sum
  intro j _hj
  exact ENNReal.measurable_toReal.comp <|
    measurable_eLpNorm_two_prod_right (normalizedCubeMeasure R)
      (fun omega x ↦
        (oneStepShellForcingW14 M n h omega q Q hh).jacobian x i j)
      (measurable_oneStepShellForcingW14_jacobian_uncurry
        M n h q Q hh i j)

/-- The Sobolev and explicit-Jacobian readouts of the shell derivative size
agree exactly. -/
theorem oneStepShellForcingCellB_eq
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ)) :
    oneStepShellForcingCellB (Q := Q) (R := R) M n h omega q hh =
      cubeScaleFactor R * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        (oneStepShellForcingCellH1 M n h omega q hh hRhalf
          ).gradientCoordL2NormSum := by
  let S := oneStepShellForcingCellH1 M n h omega q hh hRhalf
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

/-- Derivative size of the literal Neumann datum is the sum of the shell
Jacobian size and the selected weak-Hessian size. -/
theorem oneStepNeumannRawCellH1_gradientCoordL2NormSum_le
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ)) :
    (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
      ).gradientCoordL2NormSum ≤
      (oneStepShellForcingCellH1 M n h omega q hh hRhalf
        ).gradientCoordL2NormSum +
      (H.restrict (isOpen_openCubeSet R) hRhalf).hessianCoordL2NormSum := by
  let S := oneStepShellForcingCellH1 M n h omega q hh hRhalf
  let HR := H.restrict (isOpen_openCubeSet R) hRhalf
  unfold CubeVectorH1Function.gradientCoordL2NormSum
  calc
    ∑ i : Fin d,
        ((oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf).coord i
          ).gradientCoordL2NormSum ≤
      ∑ i : Fin d, ((S.coord i).gradientCoordL2NormSum +
        (HR.gradCoordH1Function i).gradientCoordL2NormSum) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          simpa only [oneStepNeumannRawCellH1, oneStepShellForcingCellH1, S, HR] using!
            gradientCoordL2NormSum_sub_le (S.coord i)
              (HR.gradCoordH1Function i)
    _ = (∑ i : Fin d, (S.coord i).gradientCoordL2NormSum) +
        ∑ i : Fin d, (HR.gradCoordH1Function i).gradientCoordL2NormSum :=
      Finset.sum_add_distrib
    _ = (∑ i : Fin d, (S.coord i).gradientCoordL2NormSum) +
        HR.hessianCoordL2NormSum := by
          congr 1
    _ = _ := by rfl

/-- Concrete dimension-explicit majorant for the positive derivative size in
the Neumann quarter-Besov estimate. -/
theorem oneStepNeumannRawCellH1_euclideanGradientSize_le
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ)) :
    cubeScaleFactor R * ∑ k : Fin d,
        cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
          (((oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
            ).coord k).grad x)) ≤
      (d : ℝ) *
        (cubeScaleFactor R * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          (oneStepShellForcingCellH1 M n h omega q hh hRhalf
            ).gradientCoordL2NormSum +
          oneStepCellB R
            (H.restrict (isOpen_openCubeSet R) hRhalf)) := by
  let G := oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
  let S := oneStepShellForcingCellH1 M n h omega q hh hRhalf
  let HR := H.restrict (isOpen_openCubeSet R) hRhalf
  have hscale : 0 ≤ cubeScaleFactor R := cubeScaleFactor_nonneg R
  have hnorm := cubeVectorH1_euclideanGradientSum_le R G
  have hraw := oneStepNeumannRawCellH1_gradientCoordL2NormSum_le
    M n h omega q hh uS H hRhalf
  have hraw' : ∑ k : Fin d, (G.coord k).gradientCoordL2NormSum ≤
      S.gradientCoordL2NormSum + HR.hessianCoordL2NormSum := by
    simpa only [G, S, HR, CubeVectorH1Function.gradientCoordL2NormSum] using hraw
  have hfactor : 0 ≤ cubeScaleFactor R *
      ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ)) := by
    exact mul_nonneg hscale <| mul_nonneg (Nat.cast_nonneg d) <|
      Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg R)) _
  calc
    cubeScaleFactor R * ∑ k : Fin d,
        cubeLpNorm R (2 : ℝ≥0∞)
          (fun x ↦ euclideanNorm ((G.coord k).grad x)) ≤
      cubeScaleFactor R *
        ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          ∑ k : Fin d, (G.coord k).gradientCoordL2NormSum) :=
      mul_le_mul_of_nonneg_left hnorm hscale
    _ ≤ cubeScaleFactor R *
        ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          (S.gradientCoordL2NormSum + HR.hessianCoordL2NormSum)) := by
      calc
        cubeScaleFactor R *
            ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
              ∑ k : Fin d, (G.coord k).gradientCoordL2NormSum) =
          (cubeScaleFactor R *
            ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ))) *
              ∑ k : Fin d, (G.coord k).gradientCoordL2NormSum := by ring
        _ ≤ (cubeScaleFactor R *
            ((d : ℝ) * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ))) *
              (S.gradientCoordL2NormSum + HR.hessianCoordL2NormSum) :=
          mul_le_mul_of_nonneg_left hraw' hfactor
        _ = _ := by ring
    _ = (d : ℝ) *
        (cubeScaleFactor R * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          S.gradientCoordL2NormSum + oneStepCellB R HR) := by
      unfold oneStepCellB oneStepCellNormalizedHessianSize
      ring

/-- The same derivative bound in its fully measurable shell/Hessian
majorant form. -/
theorem oneStepNeumannRawCellH1_euclideanGradientSize_le_measurable
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ)) :
    cubeScaleFactor R * ∑ k : Fin d,
        cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
          (((oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
            ).coord k).grad x)) ≤
      (d : ℝ) *
        (oneStepShellForcingCellB (Q := Q) (R := R)
            M n h omega q hh +
          oneStepCellB R
            (H.restrict (isOpen_openCubeSet R) hRhalf)) := by
  rw [oneStepShellForcingCellB_eq M n h omega q hh hRhalf]
  exact oneStepNeumannRawCellH1_euclideanGradientSize_le
    M n h omega q hh uS H hRhalf

/-- Monotonicity of the positive cell error in its derivative argument. -/
theorem oneStepCellBesovError_mono_right {A B C : ℝ}
    (hA : 0 ≤ A) (hBC : B ≤ C) :
    oneStepCellBesovError A B ≤ oneStepCellBesovError A C := by
  unfold oneStepCellBesovError
  have hsqrt := Real.sqrt_le_sqrt hBC
  have hcross : A * Real.sqrt A * Real.sqrt B ≤
      A * Real.sqrt A * Real.sqrt C :=
    mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg hA (Real.sqrt_nonneg A))
  linarith

/-- Joint monotonicity of the positive cell error. -/
theorem oneStepCellBesovError_mono {A B C D : ℝ}
    (hA : 0 ≤ A) (hAC : A ≤ C) (hBD : B ≤ D) :
    oneStepCellBesovError A B ≤ oneStepCellBesovError C D := by
  have hC : 0 ≤ C := hA.trans hAC
  have hsqrtA : Real.sqrt A ≤ Real.sqrt C := Real.sqrt_le_sqrt hAC
  have hsqrtB : Real.sqrt B ≤ Real.sqrt D := Real.sqrt_le_sqrt hBD
  have hAA : A * Real.sqrt A ≤ C * Real.sqrt C :=
    mul_le_mul hAC hsqrtA (Real.sqrt_nonneg _) hC
  have hcross : A * Real.sqrt A * Real.sqrt B ≤
      C * Real.sqrt C * Real.sqrt D :=
    mul_le_mul hAA hsqrtB (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))
  unfold oneStepCellBesovError
  have hsq : A ^ 2 ≤ C ^ 2 := by nlinarith
  linarith

@[simp] theorem oneStepNeumannRawCellH1_toField_apply
    {d : ℕ} {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (x : Vec d) :
    (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField x =
      oneStepMultiplierAt M n h x omega • q - uS.grad x := by
  funext i
  simp [oneStepNeumannRawCellH1, CubeVectorH1Function.toField,
    oneStepShellForcingH1,
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain, H1Function.restrict,
    oneStepShellForcingCoord, HasWeakHessianOn.gradCoordH1Function,
    HasWeakHessianOn.restrict]

/-- The literal centered Neumann cell fluctuation is the cube fluctuation of
the preceding vector `H¹` carrier whenever the weak-Hessian representative
uses the canonical Neumann gradient. -/
theorem oneStepNeumannCellFluctuationField_eq_cubeFluctuationVec_rawCellH1
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (hgrad : uS.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad) :
    oneStepNeumannCellFluctuationField M n h q Q R omega hh =
      cubeFluctuationVec R
        (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField := by
  let G := (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField
  have hraw : G = fun x ↦
      oneStepMultiplierAt M n h x omega • q -
        (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad x := by
    funext x
    simpa only [G, hgrad] using
      oneStepNeumannRawCellH1_toField_apply M n h omega q hh uS H hRhalf x
  change oneStepNeumannCellFluctuationField M n h q Q R omega hh =
    cubeFluctuationVec R G
  rw [hraw]
  unfold oneStepNeumannCellFluctuationField oneStepNeumannSlopeField
  funext x
  unfold cubeFluctuationVec
  have hmem : MemVectorL2 (cubeSet R) (fun y ↦
      oneStepMultiplierAt M n h y omega • q -
        (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad y) := by
    have hopen := (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
      ).memVectorL2_toField_openCubeSet
    have hcube : MemVectorL2 (cubeSet R) G := by
      simpa only [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hopen
    rw [hraw] at hcube
    exact hcube
  have havg := cubeAverageVec_add R (fun _ : Vec d ↦ q)
    (fun y ↦ oneStepMultiplierAt M n h y omega • q -
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad y)
    (memVectorL2_const q) hmem
  rw [cubeAverageVec_const] at havg
  have hslope : oneStepNeumannSlopeField M n h q Q omega hh =
      fun y ↦ q + (oneStepMultiplierAt M n h y omega • q -
        (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad y) := by
    funext y
    unfold oneStepNeumannSlopeField
    abel
  rw [oneStepNeumannCellSlope_eq_cubeAverageVec M n h q Q R hR omega hh,
    hslope, havg]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The literal dual cell fluctuation is the cube fluctuation of the full
measurable large-cube slope. -/
theorem oneStepNeumannCellFluctuationField_eq_cubeFluctuationVec_slope
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hR : R ∈ descendantsAtDepth Q j) :
    oneStepNeumannCellFluctuationField M n h q Q R omega hh =
      cubeFluctuationVec R
        (oneStepNeumannSlopeField M n h q Q omega hh) := by
  unfold oneStepNeumannCellFluctuationField cubeFluctuationVec
  rw [oneStepNeumannCellSlope_eq_cubeAverageVec M n h q Q R hR omega hh]



theorem oneStepNeumannCellFluctuationField_ae_eq_cubeFluctuationVec_rawCellH1
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (hgrad : uS.grad =ᵐ[volumeMeasureOn (openCubeSet R)]
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad) :
    oneStepNeumannCellFluctuationField M n h q Q R omega hh =ᵐ[
        volumeMeasureOn (openCubeSet R)]
      cubeFluctuationVec R
        (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField := by
  let G := (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField
  let V : Vec d → Vec d := fun x ↦
    oneStepMultiplierAt M n h x omega • q -
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad x
  have hraw : G =ᵐ[volumeMeasureOn (openCubeSet R)] V := by
    filter_upwards [hgrad] with x hx
    simpa only [G, V, hx] using
      oneStepNeumannRawCellH1_toField_apply M n h omega q hh uS H hRhalf x
  have hrawCube : G =ᵐ[volume.restrict (cubeSet R)] V := by
    simpa only [volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hraw
  have havg : cubeAverageVec R G = cubeAverageVec R V :=
    cubeAverageVec_eq_of_ae_eq_on_cubeSet hrawCube
  have hmem : MemVectorL2 (cubeSet R) V := by
    have hopen := (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
      ).memVectorL2_toField_openCubeSet
    have hG : MemVectorL2 (cubeSet R) G := by
      simpa only [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hopen
    exact hG.ae_eq hrawCube
  have havgAdd := cubeAverageVec_add R (fun _ : Vec d ↦ q) V
    (memVectorL2_const q) hmem
  rw [cubeAverageVec_const] at havgAdd
  have hslope : oneStepNeumannSlopeField M n h q Q omega hh =
      fun y ↦ q + V y := by
    funext y
    unfold oneStepNeumannSlopeField V
    abel
  unfold oneStepNeumannCellFluctuationField
  rw [oneStepNeumannCellSlope_eq_cubeAverageVec M n h q Q R hR omega hh,
    hslope, havgAdd]
  filter_upwards [hraw] with x hx
  unfold cubeFluctuationVec
  change q + V x - (q + cubeAverageVec R V) =
    G x - cubeAverageVec R G
  rw [hx, havg]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Positive `q = 1` dual-test bound for the literal centered Neumann datum
on an interior source cell. -/
theorem oneStepNeumannCellFluctuation_qOne_dualTest_quarter_le
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (hgrad : uS.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad)
    (i : Fin d) (N : ℕ) :
    cubeBesovDualTestNorm R (1 / 4 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x ↦ oneStepNeumannCellFluctuationField
          M n h q Q R omega hh x i) ≤
      cubeBesovScaleWeight (1 / 4 : ℝ) R *
        ((max 2 (cubeBesovW12EmbeddingConstant d)) *
          oneStepCellBesovSize
            (cubeLpNorm R (2 : ℝ≥0∞)
              (cubeFluctuationVec R
                (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField))
            (cubeScaleFactor R * ∑ k : Fin d,
              cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
                (((oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
                  ).coord k).grad x)))) := by
  rw [oneStepNeumannCellFluctuationField_eq_cubeFluctuationVec_rawCellH1
    M n h omega q hh uS H hR hRhalf hgrad]
  exact oneStep_cubeVectorH1_cubeFluctuation_qOne_dualTest_quarter_le R
    (oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf) i N

/-- Literal Neumann source-cell energy estimate obtained from the vector
`H¹` carrier.  The only analytic input left explicit is the negative
coarse-Poincare estimate for the selected cell potential. -/
theorem OneStepNeumannCellMinimizer.energy_le_of_neumannRawCellH1_quarter
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (hgradEq : uS.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad)
    {a : CoeffField d} {lam Lam : ℝ}
    (X : OneStepNeumannCellMinimizer R a
      (oneStepNeumannCellFluctuationField M n h q Q R omega hh))
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R) a)
    {ellipticity : ℝ} (hell : 0 ≤ ellipticity)
    (hpot : MemLp X.potential.toH1Function.grad
      (2 : ℝ≥0∞) (normalizedCubeMeasure R))
    (hneg : ∀ N : ℕ,
      cubeBesovNegativeVectorPartialSeminorm R (1 / 4 : ℝ) N
          X.potential.toH1Function.grad ≤
        Real.sqrt ellipticity *
          Real.sqrt (volumeAverage (openCubeSet R) (fun x ↦
            vecDot (X.potential.toH1Function.grad x) (X.flux x)))) :
    volumeAverage (openCubeSet R) (fun x ↦
        vecDot (X.potential.toH1Function.grad x) (X.flux x)) ≤
      2 * (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 4 : ℝ))) *
          max 2 (cubeBesovW12EmbeddingConstant d)) ^ 2 * ellipticity *
        oneStepCellBesovError
          (cubeLpNorm R (2 : ℝ≥0∞)
            (oneStepNeumannCellFluctuationField M n h q Q R omega hh))
          (cubeScaleFactor R * ∑ k : Fin d,
            cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
              (((oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
                ).coord k).grad x))) := by
  let G := oneStepNeumannRawCellH1 M n h omega q hh uS H hRhalf
  have hdatum : oneStepNeumannCellFluctuationField M n h q Q R omega hh =
      cubeFluctuationVec R G.toField :=
    oneStepNeumannCellFluctuationField_eq_cubeFluctuationVec_rawCellH1
      M n h omega q hh uS H hR hRhalf hgradEq
  simpa only [G] using
    X.energy_le_of_vectorH1_quarter G hdatum hEll hell hpot hneg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
