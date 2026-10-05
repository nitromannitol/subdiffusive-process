module

public import SubdiffusiveProcess.CoarseRHS.RHSDisplays

@[expose] public section

/-!
# The energy display `e.cg.RHS` of `l.coarse.graining.RHS`, in the paper's normalization

`Ch03.energyConsequencesRHSTheory` (CoarseGraining, the formalization of the energy bound of
[ASD, Lemma 2.11]) bounds the coefficient energies of the Dirichlet solution with datum `h` and of the
mean-zero Neumann solution.  As in `RHSDisplays`, the paper's forcing seminorm and datum full norm are
`s ^ (1 / 2)`-normalized; the library powers `s ^ (-3/2)` (forcing) and `s ^ (-1/2)` (datum, at the
upper ellipticity `Λ_{s,2}`, which is at most `Λ_{s/2,2}`) leave room for the printed
`s ^ (-3), s ^ (-3/2)`.
-/

namespace SubdiffusiveProcess.CoarseRHS

open Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec Mat TriadicCube

theorem forceBesov_of_wsp {d : ℕ} [NeZero d] {Q : Homogenization.TriadicCube d} (s : FractionalOrder)
    (G : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    Ch03.ForceBesovRegularity Q s.1 G.toField :=
  Ch03.Legacy.ForceSobolevRegularity.toForceBesovRegularity
    (cubeEuclideanWspField_forceSobolevRegularity s G) s.2.1 s.2.2.le

/-- The Dirichlet and Neumann energies, uniformly in the cube. -/
theorem energy_general (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : Homogenization.TriadicCube d) (sF : FractionalOrder)
      (a : Ch02.TriadicCoeffFamily d)
      (G : CubeEuclideanWspField Q sF FiniteLpExponent.two)
      (hh : H1Function (openCubeSet Q))
      (Hh : CubeEuclideanWspField Q sF FiniteLpExponent.two),
      Hh.toField = hh.grad →
      ∀ v w : H1Function (openCubeSet Q),
        Ch03.ABK26.IsForcedEquation Q (a.coeffOn Q) v G.toField →
        HasZeroTraceDifferenceOn (openCubeSet Q) v hh →
        (∀ φ : H1Function (openCubeSet Q),
          ∫ x in openCubeSet Q,
              vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (w.grad x)) (φ.grad x) ∂volume =
            -(∫ x in openCubeSet Q,
              vecDot (G.toField x - cubeAverageVec Q G.toField) (φ.grad x) ∂volume)) →
        coefficientEnergyNorm Q a v.grad + coefficientEnergyNorm Q a w.grad ≤
          C * Real.rpow sF.1 (-3 : ℝ) *
              Real.rpow (lambda Q (sF.1 / 2) (.finite 2) a) (-(1 / 2 : ℝ)) *
              (Real.rpow (cubeScaleFactor Q) sF.1 *
                (paperFractionalSeminorm Q sF FiniteLpExponent.two G.toField).toReal) +
            C * Real.rpow sF.1 (-(3 / 2 : ℝ)) *
              Real.rpow (Lambda Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ) *
              (Real.rpow (cubeScaleFactor Q) sF.1 *
                (paperFractionalFullNorm Q sF FiniteLpExponent.two Hh.toField).toReal) := by
  obtain ⟨Ce, hCe, hdir, hneu⟩ := (Ch03.energyConsequencesRHSTheory (d := d)).exists_constant
  let Kd : ℝ := caccioppoliExactDatumConstant d
  have hKd : 0 < Kd := caccioppoliExactDatumConstant_pos d
  refine ⟨(Ce + Ce) * (1 + Kd), by positivity, ?_⟩
  intro Q sF a G hh Hh hHh v w hv hzt hw
  have hs0 : 0 < sF.1 := sF.2.1
  have hs1 : sF.1 < 1 := sF.2.2
  have hs2 : 0 < sF.1 / 2 := by linarith
  -- the Dirichlet solution
  have hzt' : ∃ z : H10Function (openCubeSet Q),
      z.toH1Function.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)]
        fun x => v.toFun x - hh.toFun x := by
    obtain ⟨z, hz, -⟩ := hzt
    exact ⟨z, Filter.Eventually.of_forall fun x => by
      show z.toH1Function.toFun x = v.toFun x - hh.toFun x
      have := hz x
      linarith⟩
  let v' : Ch03.DirichletForcedCubeSolution Q a (fun x => -G.toField x) :=
    ⟨v, hh, isForced_neg hv, hzt'⟩
  -- the Neumann solution
  let w₀ : H1MeanZeroFunction (Ch02.cubeDomain Q).carrier :=
    H1Function.toMeanZero (U := (Ch02.cubeDomain Q).carrier) w
  have hw₀ : Ch03.IsMeanZeroNeumannForcedEquation Q a w₀
      (fun x => (fun x => -G.toField x) x - cubeAverageVec Q (fun x => -G.toField x)) := by
    intro φ
    have h := hw φ.toH1Function
    have hg : ∀ x, w₀.toH1Function.grad x = w.grad x := fun x => H1Function.toMeanZero_grad (U := (Ch02.cubeDomain Q).carrier) w x
    simp only [hg, cubeAverageVec_neg']
    change (∫ x in openCubeSet Q,
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (w.grad x)) (φ.toH1Function.grad x)
          ∂volume) =
      ∫ x in openCubeSet Q,
        vecDot (-G.toField x - -cubeAverageVec Q G.toField) (φ.toH1Function.grad x) ∂volume
    rw [h, ← MeasureTheory.integral_neg]
    congr 1
    funext x
    rw [← vecDot_neg_left']
    congr 1
    funext i
    simp only [Pi.neg_apply, Pi.sub_apply]
    ring
  let w' : Ch03.NeumannForcedCubeSolution Q a (fun x => -G.toField x) := ⟨w₀, hw₀⟩
  have hreg := forceBesov_neg sF G
  have hHreg : Ch03.ForceBesovRegularity Q sF.1 (Ch03.dirichletBoundaryGradientField v') := by
    have := forceBesov_of_wsp sF Hh
    rw [hHh] at this
    exact this
  have hDir := hdir v' hs0 hs1 hreg hHreg
  have hNeu := hneu w' hs0 hs1 hreg
  have hEv : Ch03.dirichletForcedSolutionEnergyNorm Q a v' = coefficientEnergyNorm Q a v.grad :=
    h1Energy_eq Q a v
  have hEw : Ch03.neumannForcedSolutionEnergyNorm Q a w' = coefficientEnergyNorm Q a w.grad := by
    have h := h1Energy_eq Q a w₀.toH1Function
    have hg : ∀ x, w₀.toH1Function.grad x = w.grad x :=
      fun x => H1Function.toMeanZero_grad (U := (Ch02.cubeDomain Q).carrier) w x
    have hgf : w₀.toH1Function.grad = w.grad := funext hg
    rw [hgf] at h
    exact h
  -- data
  have hcf : (0 : ℝ) < cubeScaleFactor Q := by unfold cubeScaleFactor; positivity
  have hW : 0 ≤ Real.rpow (cubeScaleFactor Q) sF.1 := (Real.rpow_pos_of_pos hcf _).le
  have hL := lambdaSq_two_pos Q a hs2
  have hLam := LambdaSq_two_pos Q a hs2
  have hLams : 0 < Ch02.LambdaSq Q sF.1 (.finite 2) a := LambdaSq_two_pos Q a hs0
  have hUsU : Ch03.poincareUpperEllipticityFactor Q a sF.1 (.finite 2) ≤
      Ch03.poincareUpperEllipticityFactor Q a (sF.1 / 2) (.finite 2) := by
    unfold Ch03.poincareUpperEllipticityFactor
    exact Real.rpow_le_rpow hLams.le
      (Ch02.LambdaSq_antitone Q a hs2 (by linarith) (by simp)) (by norm_num)
  have hBg := besovNeg_le sF G
  have hBh := besovPos_le_datum_general d Q sF Hh
  have hPSg := paperSem_toReal Q sF G.toField
  have hPSh := paperSem_toReal Q sF Hh.toField
  have hA0 := avg_le_W_full d Q sF Hh
  have hPShFp := paperSem_le_full Q sF Hh
  have hBgnn : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1
      (fun x => -G.toField x) :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity hreg
  have hBhnn : 0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1 Hh.toField :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      (forceBesov_of_wsp sF Hh)
  have hSg0 : 0 ≤ (cubeEuclideanWspESeminorm Q sF FiniteLpExponent.two G.toField).toReal :=
    ENNReal.toReal_nonneg
  have hFp0 : 0 ≤ (paperFractionalFullNorm Q sF FiniteLpExponent.two Hh.toField).toReal :=
    ENNReal.toReal_nonneg
  have hlf0 : 0 ≤ Ch03.poincareLowerEllipticityFactor Q a (sF.1 / 2) (.finite 2) :=
    Real.rpow_nonneg hL.le _
  have hU0 : 0 ≤ Ch03.poincareUpperEllipticityFactor Q a (sF.1 / 2) (.finite 2) :=
    Real.rpow_nonneg hLam.le _
  have hUs0 : 0 ≤ Ch03.poincareUpperEllipticityFactor Q a sF.1 (.finite 2) :=
    Real.rpow_nonneg hLams.le _
  have hA00 : 0 ≤ Real.sqrt (vecNormSq (cubeAverageVec Q Hh.toField)) := Real.sqrt_nonneg _
  -- the norm of the datum gradient
  have hN2 : Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q sF.1
        (Ch03.dirichletBoundaryGradientField v') =
      Real.sqrt (vecNormSq (cubeAverageVec Q Hh.toField)) +
        Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1 Hh.toField := by
    show Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q sF.1 hh.grad = _
    rw [← hHh]
    rfl
  have hT1 := scalar_energy_T1 (s := sF.1)
    (lf := Ch03.poincareLowerEllipticityFactor Q a (sF.1 / 2) (.finite 2)) hs0 hs1 hKd.le hlf0 hW
    hSg0 hBg hPSg
  have hT2 := scalar_energy_T2 (s := sF.1) (U := Ch03.poincareUpperEllipticityFactor Q a (sF.1 / 2) (.finite 2))
    (Us := Ch03.poincareUpperEllipticityFactor Q a sF.1 (.finite 2))
    (N2 := Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q sF.1
        (Ch03.dirichletBoundaryGradientField v'))
    hs0 hs1 hKd.le hUs0 hUsU hW ENNReal.toReal_nonneg hBhnn hA00 hN2 hA0 hBh hPSh hPShFp
  have hDir' : coefficientEnergyNorm Q a v.grad ≤
      Ce * (Real.rpow sF.1 (-(3 / 2 : ℝ)) *
        Ch03.poincareLowerEllipticityFactor Q a (sF.1 / 2) (.finite 2) *
        Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1 (fun x => -G.toField x)) +
      Ce * (Real.rpow sF.1 (-(1 / 2 : ℝ)) *
        Ch03.poincareUpperEllipticityFactor Q a sF.1 (.finite 2) *
        Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q sF.1
          (Ch03.dirichletBoundaryGradientField v')) := by
    rw [← hEv]
    have h := hDir
    simp only [Ch03.dirichletEnergyWithRHSRHS] at h
    linarith
  have hNeu' : coefficientEnergyNorm Q a w.grad ≤
      Ce * (Real.rpow sF.1 (-(3 / 2 : ℝ)) *
        Ch03.poincareLowerEllipticityFactor Q a (sF.1 / 2) (.finite 2) *
        Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q sF.1 (fun x => -G.toField x)) := by
    rw [← hEw]
    have h := hNeu
    simp only [Ch03.neumannEnergyWithRHSRHS] at h
    linarith
  have hX0 : 0 ≤ Real.rpow sF.1 (-3 : ℝ) *
      Ch03.poincareLowerEllipticityFactor Q a (sF.1 / 2) (.finite 2) *
      (Real.rpow (cubeScaleFactor Q) sF.1 *
        (paperFractionalSeminorm Q sF FiniteLpExponent.two G.toField).toReal) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) hlf0)
      (mul_nonneg hW ENNReal.toReal_nonneg)
  have hY0 : 0 ≤ Real.rpow sF.1 (-(3 / 2 : ℝ)) *
      Ch03.poincareUpperEllipticityFactor Q a (sF.1 / 2) (.finite 2) *
      (Real.rpow (cubeScaleFactor Q) sF.1 *
        (paperFractionalFullNorm Q sF FiniteLpExponent.two Hh.toField).toReal) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) hU0)
      (mul_nonneg hW ENNReal.toReal_nonneg)
  have hfin := scalar_energy_final (Ev := coefficientEnergyNorm Q a v.grad)
    (Ew := coefficientEnergyNorm Q a w.grad)
    (X := Real.rpow sF.1 (-3 : ℝ) *
      Ch03.poincareLowerEllipticityFactor Q a (sF.1 / 2) (.finite 2) *
      (Real.rpow (cubeScaleFactor Q) sF.1 *
        (paperFractionalSeminorm Q sF FiniteLpExponent.two G.toField).toReal))
    (Y := Real.rpow sF.1 (-(3 / 2 : ℝ)) *
      Ch03.poincareUpperEllipticityFactor Q a (sF.1 / 2) (.finite 2) *
      (Real.rpow (cubeScaleFactor Q) sF.1 *
        (paperFractionalFullNorm Q sF FiniteLpExponent.two Hh.toField).toReal))
    hCe.le hCe.le hKd.le hX0 hY0 hDir' hNeu' (by simpa [mul_comm, mul_assoc, mul_left_comm] using hT1)
    (by simpa [mul_comm, mul_assoc, mul_left_comm] using hT2)
  change _ ≤ (Ce + Ce) * (1 + Kd) * Real.rpow sF.1 (-3 : ℝ) *
      Ch03.poincareLowerEllipticityFactor Q a (sF.1 / 2) (.finite 2) *
      (Real.rpow (cubeScaleFactor Q) sF.1 *
        (paperFractionalSeminorm Q sF FiniteLpExponent.two G.toField).toReal) +
    (Ce + Ce) * (1 + Kd) * Real.rpow sF.1 (-(3 / 2 : ℝ)) *
      Ch03.poincareUpperEllipticityFactor Q a (sF.1 / 2) (.finite 2) *
      (Real.rpow (cubeScaleFactor Q) sF.1 *
        (paperFractionalFullNorm Q sF FiniteLpExponent.two Hh.toField).toReal)
  refine hfin.trans (le_of_eq ?_)
  ring

end SubdiffusiveProcess.CoarseRHS
