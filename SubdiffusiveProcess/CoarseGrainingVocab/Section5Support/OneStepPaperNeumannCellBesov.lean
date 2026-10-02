import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepNeumannCellBesov
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPaperNeumannFlux

/-!
# Positive Besov carrier for the paper-sign Neumann flux

The dependency's selected Neumann solution is the negative of the manuscript's
`W`.  Hence the nonconstant part of `exp(H) q - grad W` is represented by the
shell forcing **plus** the selected solution gradient.  This file mirrors the
existing vector-`H¹` carrier with that sign and connects it to
`oneStepPaperNeumannCellFluctuationField`.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- Cell-local coordinatewise `H¹` realization of the nonconstant manuscript
flux.  Unlike the original interior-cube carrier below, this only asks for the
weak Hessian on the cell where the Besov estimate is evaluated. -/
noncomputable def oneStepPaperNeumannRawCellH1OnCell
    {d : ℕ} {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (uR : H1Function (openCubeSet R))
    (HR : HasWeakHessianOn (openCubeSet R) uR)
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    CubeVectorH1Function R where
  coord i :=
    ((oneStepShellForcingH1 M n h omega q Q hh).coord i).restrict
        (isOpen_openCubeSet R) hRQ +
      HR.gradCoordH1Function i

/-- Coordinatewise `H¹` realization of the nonconstant manuscript flux
`(exp(H)-1)q + grad u`, where the package solution is `u = -W`. -/
noncomputable def oneStepPaperNeumannRawCellH1
    {d : ℕ} {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
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
              (by norm_num) (by norm_num)) +
      (H.restrict (isOpen_openCubeSet R) hRhalf).gradCoordH1Function i

/-- The paper-sign carrier has the same derivative majorant as the legacy
carrier: changing the sign of the Hessian term does not change the triangle
bound. -/
theorem oneStepPaperNeumannRawCellH1_gradientCoordL2NormSum_le
    {d : ℕ} {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ)) :
    (oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf
      ).gradientCoordL2NormSum ≤
      (oneStepShellForcingCellH1 M n h omega q hh hRhalf
        ).gradientCoordL2NormSum +
      (H.restrict (isOpen_openCubeSet R) hRhalf).hessianCoordL2NormSum := by
  let S := oneStepShellForcingCellH1 M n h omega q hh hRhalf
  let HR := H.restrict (isOpen_openCubeSet R) hRhalf
  unfold CubeVectorH1Function.gradientCoordL2NormSum
  calc
    ∑ i : Fin d,
        ((oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf).coord i
          ).gradientCoordL2NormSum ≤
      ∑ i : Fin d, ((S.coord i).gradientCoordL2NormSum +
        (HR.gradCoordH1Function i).gradientCoordL2NormSum) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          unfold H1Function.gradientCoordL2NormSum
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun j _ ↦ ?_
          simpa only [oneStepPaperNeumannRawCellH1, S, HR,
            H1Function.gradCoordToScalarL2_add] using
              norm_add_le ((S.coord i).gradCoordToScalarL2 j)
                ((HR.gradCoordH1Function i).gradCoordToScalarL2 j)
    _ = (∑ i : Fin d, (S.coord i).gradientCoordL2NormSum) +
        ∑ i : Fin d, (HR.gradCoordH1Function i).gradientCoordL2NormSum :=
      Finset.sum_add_distrib
    _ = (∑ i : Fin d, (S.coord i).gradientCoordL2NormSum) +
        HR.hessianCoordL2NormSum := by congr 1
    _ = _ := by rfl

/-- Dimension-explicit derivative majorant for the paper-sign carrier. -/
theorem oneStepPaperNeumannRawCellH1_euclideanGradientSize_le_measurable
    {d : ℕ} {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ)) :
    cubeScaleFactor R * ∑ k : Fin d,
        cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
          (((oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf
            ).coord k).grad x)) ≤
      (d : ℝ) *
        (oneStepShellForcingCellB (Q := Q) (R := R) M n h omega q hh +
          oneStepCellB R (H.restrict (isOpen_openCubeSet R) hRhalf)) := by
  let G := oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf
  let S := oneStepShellForcingCellH1 M n h omega q hh hRhalf
  let HR := H.restrict (isOpen_openCubeSet R) hRhalf
  have hscale : 0 ≤ cubeScaleFactor R := cubeScaleFactor_nonneg R
  have hnorm := cubeVectorH1_euclideanGradientSum_le R G
  have hraw := oneStepPaperNeumannRawCellH1_gradientCoordL2NormSum_le
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
          mul_le_mul_of_nonneg_left hraw' hfactor
        _ = _ := by ring
    _ = (d : ℝ) *
        (cubeScaleFactor R * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
          S.gradientCoordL2NormSum + oneStepCellB R HR) := by
      unfold oneStepCellB oneStepCellNormalizedHessianSize
      ring
    _ = _ := by rw [← oneStepShellForcingCellB_eq M n h omega q hh hRhalf]

@[simp] theorem oneStepPaperNeumannRawCellH1_toField_apply
    {d : ℕ} {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (x : Vec d) :
    (oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField x =
      oneStepMultiplierAt M n h x omega • q + uS.grad x := by
  funext i
  simp [oneStepPaperNeumannRawCellH1, CubeVectorH1Function.toField,
    oneStepShellForcingH1,
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain, H1Function.restrict,
    oneStepShellForcingCoord]

/-- The centered paper flux is exactly the cube fluctuation of the paper-sign
vector-`H¹` carrier. -/
theorem oneStepPaperNeumannCellFluctuationField_eq_cubeFluctuationVec_rawCellH1
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (hgrad : uS.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad) :
    oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh =
      cubeFluctuationVec R
        (oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField := by
  let G := (oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField
  have hraw : G = fun x ↦
      oneStepMultiplierAt M n h x omega • q +
        (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad x := by
    funext x
    simpa only [G, hgrad] using
      oneStepPaperNeumannRawCellH1_toField_apply M n h omega q hh uS H hRhalf x
  change oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh =
    cubeFluctuationVec R G
  rw [hraw]
  unfold oneStepPaperNeumannCellFluctuationField oneStepPaperNeumannFlux
  funext x
  unfold cubeFluctuationVec
  have hmem : MemVectorL2 (cubeSet R) (fun y ↦
      oneStepMultiplierAt M n h y omega • q +
        (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad y) := by
    have hopen := (oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf
      ).memVectorL2_toField_openCubeSet
    have hcube : MemVectorL2 (cubeSet R) G := by
      simpa only [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hopen
    rw [hraw] at hcube
    exact hcube
  have havg := cubeAverageVec_add R (fun _ : Vec d ↦ q)
    (fun y ↦ oneStepMultiplierAt M n h y omega • q +
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad y)
    (memVectorL2_const q) hmem
  rw [cubeAverageVec_const] at havg
  have hflux : oneStepPaperNeumannFlux M n h q Q omega hh =
      fun y ↦ q + (oneStepMultiplierAt M n h y omega • q +
        (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad y) := by
    funext y
    unfold oneStepPaperNeumannFlux
    abel
  rw [oneStepPaperNeumannCellSlope_eq_cubeAverageVec M n h q Q R omega hh hR,
    hflux, havg]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Paper-sign positive `q=1` dual-test estimate on an interior cell. -/
theorem oneStepPaperNeumannCellFluctuation_qOne_dualTest_quarter_le
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (hgrad : uS.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad)
    (i : Fin d) (N : ℕ) :
    cubeBesovDualTestNorm R (1 / 4 : ℝ) (2 : ℝ≥0∞) (1 : ℝ≥0∞) N
        (fun x ↦ oneStepPaperNeumannCellFluctuationField
          M n h q Q R omega hh x i) ≤
      cubeBesovScaleWeight (1 / 4 : ℝ) R *
        ((max 2 (cubeBesovW12EmbeddingConstant d)) *
          oneStepCellBesovSize
            (cubeLpNorm R (2 : ℝ≥0∞)
              (cubeFluctuationVec R
                (oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf).toField))
            (cubeScaleFactor R * ∑ k : Fin d,
              cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
                (((oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf
                  ).coord k).grad x)))) := by
  rw [oneStepPaperNeumannCellFluctuationField_eq_cubeFluctuationVec_rawCellH1
    M n h omega q hh uS H hR hRhalf hgrad]
  exact oneStep_cubeVectorH1_cubeFluctuation_qOne_dualTest_quarter_le R
    (oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf) i N

/-- Energy endpoint for the correctly signed manuscript cell datum. -/
theorem OneStepNeumannCellMinimizer.energy_le_of_paperNeumannRawCellH1_quarter
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (uS : H1Function (scaledOpenCubeSet Q (1 / 2 : ℝ)))
    (H : HasWeakHessianOn (scaledOpenCubeSet Q (1 / 2 : ℝ)) uS)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRhalf : openCubeSet R ⊆ scaledOpenCubeSet Q (1 / 2 : ℝ))
    (hgradEq : uS.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad)
    {a : CoeffField d} {lam Lam : ℝ}
    (X : OneStepNeumannCellMinimizer R a
      (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh))
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
            (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh))
          (cubeScaleFactor R * ∑ k : Fin d,
            cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
              (((oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf
                ).coord k).grad x))) := by
  let G := oneStepPaperNeumannRawCellH1 M n h omega q hh uS H hRhalf
  have hdatum : oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh =
      cubeFluctuationVec R G.toField :=
    oneStepPaperNeumannCellFluctuationField_eq_cubeFluctuationVec_rawCellH1
      M n h omega q hh uS H hR hRhalf hgradEq
  simpa only [G] using
    X.energy_le_of_vectorH1_quarter G hdatum hEll hell hpot hneg

@[simp] theorem oneStepPaperNeumannRawCellH1OnCell_toField_apply
    {d : ℕ} {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (uR : H1Function (openCubeSet R))
    (HR : HasWeakHessianOn (openCubeSet R) uR)
    (hRQ : openCubeSet R ⊆ openCubeSet Q) (x : Vec d) :
    (oneStepPaperNeumannRawCellH1OnCell M n h omega q hh uR HR hRQ).toField x =
      oneStepMultiplierAt M n h x omega • q + uR.grad x := by
  funext i
  simp [oneStepPaperNeumannRawCellH1OnCell, CubeVectorH1Function.toField,
    oneStepShellForcingH1,
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain, H1Function.restrict,
    oneStepShellForcingCoord]

/-- Cell-local form of the paper-sign fluctuation identity. -/
theorem oneStepPaperNeumannCellFluctuationField_eq_cubeFluctuationVec_rawCellH1OnCell
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (uR : H1Function (openCubeSet R))
    (HR : HasWeakHessianOn (openCubeSet R) uR)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (hgrad : uR.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad) :
    oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh =
      cubeFluctuationVec R
        (oneStepPaperNeumannRawCellH1OnCell M n h omega q hh uR HR hRQ
          ).toField := by
  let G :=
    (oneStepPaperNeumannRawCellH1OnCell M n h omega q hh uR HR hRQ).toField
  have hraw : G = fun x ↦
      oneStepMultiplierAt M n h x omega • q +
        (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad x := by
    funext x
    simpa only [G, hgrad] using
      oneStepPaperNeumannRawCellH1OnCell_toField_apply
        M n h omega q hh uR HR hRQ x
  change oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh =
    cubeFluctuationVec R G
  rw [hraw]
  unfold oneStepPaperNeumannCellFluctuationField oneStepPaperNeumannFlux
  funext x
  unfold cubeFluctuationVec
  have hmem : MemVectorL2 (cubeSet R) (fun y ↦
      oneStepMultiplierAt M n h y omega • q +
        (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad y) := by
    have hopen :=
      (oneStepPaperNeumannRawCellH1OnCell M n h omega q hh uR HR hRQ
        ).memVectorL2_toField_openCubeSet
    have hcube : MemVectorL2 (cubeSet R) G := by
      simpa only [MemVectorL2, volumeMeasureOn,
        volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hopen
    rw [hraw] at hcube
    exact hcube
  have havg := cubeAverageVec_add R (fun _ : Vec d ↦ q)
    (fun y ↦ oneStepMultiplierAt M n h y omega • q +
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad y)
    (memVectorL2_const q) hmem
  rw [cubeAverageVec_const] at havg
  have hflux : oneStepPaperNeumannFlux M n h q Q omega hh =
      fun y ↦ q + (oneStepMultiplierAt M n h y omega • q +
        (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad y) := by
    funext y
    unfold oneStepPaperNeumannFlux
    abel
  rw [oneStepPaperNeumannCellSlope_eq_cubeAverageVec M n h q Q R omega hh hR,
    hflux, havg]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Cell-local energy endpoint for the correctly signed manuscript datum. -/
theorem OneStepNeumannCellMinimizer.energy_le_of_paperNeumannRawCellH1OnCell_quarter
    {d j : ℕ} [NeZero d] {Q R : TriadicCube d}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (omega : Sample d) (q : Vec d) (hh : 0 < h)
    (uR : H1Function (openCubeSet R))
    (HR : HasWeakHessianOn (openCubeSet R) uR)
    (hR : R ∈ descendantsAtDepth Q j)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (hgradEq : uR.grad =
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad)
    {a : CoeffField d} {lam Lam : ℝ}
    (X : OneStepNeumannCellMinimizer R a
      (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh))
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
            (oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh))
          (cubeScaleFactor R * ∑ k : Fin d,
            cubeLpNorm R (2 : ℝ≥0∞) (fun x ↦ euclideanNorm
              (((oneStepPaperNeumannRawCellH1OnCell
                M n h omega q hh uR HR hRQ).coord k).grad x))) := by
  let G := oneStepPaperNeumannRawCellH1OnCell M n h omega q hh uR HR hRQ
  have hdatum : oneStepPaperNeumannCellFluctuationField M n h q Q R omega hh =
      cubeFluctuationVec R G.toField :=
    oneStepPaperNeumannCellFluctuationField_eq_cubeFluctuationVec_rawCellH1OnCell
      M n h omega q hh uR HR hR hRQ hgradEq
  simpa only [G] using
    X.energy_le_of_vectorH1_quarter G hdatum hEll hell hpot hneg

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
