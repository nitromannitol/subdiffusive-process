import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyFactor
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.DirichletEnergyPrice
import Homogenization.Book.Ch03.Theorems.EnergyRHS.Theory

/-!
# The Dirichlet energy consequence of the coefficient envelope

This file composes the almost-everywhere ellipticity caps supplied by
`EnergyFactor.lean` with the Dirichlet half of
`energyConsequencesRHSTheory`.  The resulting factor is the same
coefficient-only `dirichletEllipticityEnvelope` used by the later common
random factor; it is independent of the forcing and boundary datum.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A simultaneous cap on the two normalized square-root ellipticity factors
prices the Chapter-3 Dirichlet right-hand side by the same envelope. -/
theorem dirichletEnergyWithRHSRHS_le_of_sqrt_caps [NeZero d]
    {Q : TriadicCube d} {A : CoeffFamily d} {C s sigma Y G H : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q A g)
    (hC : 0 ≤ C) (hs : 0 < s) (hsigma : 0 < sigma) (hY : 0 ≤ Y)
    (hcaps : max
        (Real.sqrt (sigma⁻¹ * Ch02.LambdaSq Q s (.finite 2) A))
        (Real.sqrt (sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹)) ≤ Y)
    (hgReg : ForceBesovRegularity Q s g)
    (hG : scaleNormalizedPositiveBesovVectorSeminormTwo Q s g ≤ G)
    (hhReg : ForceBesovRegularity Q s (dirichletBoundaryGradientField v))
    (hH : scaleNormalizedPositiveBesovVectorNormTwo Q s
      (dirichletBoundaryGradientField v) ≤ H) :
    dirichletEnergyWithRHSRHS C Q A s g v ≤
      C * Real.rpow s (-(3 / 2 : ℝ)) * (Y * Real.sqrt sigma⁻¹) * G +
        C * Real.rpow s (-(1 / 2 : ℝ)) * (Y * Real.sqrt sigma) * H := by
  have hupperRoot :
      Real.sqrt (sigma⁻¹ * Ch02.LambdaSq Q s (.finite 2) A) ≤ Y :=
    (le_max_left _ _).trans hcaps
  have hlowerRoot :
      Real.sqrt (sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹) ≤ Y :=
    (le_max_right _ _).trans hcaps
  have hupperArg : 0 ≤ sigma⁻¹ * Ch02.LambdaSq Q s (.finite 2) A :=
    mul_nonneg (inv_nonneg.mpr hsigma.le)
      (Ch02.LambdaSq_finite_nonneg Q A hs (by norm_num))
  have hlowerArg : 0 ≤ sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹ :=
    mul_nonneg hsigma.le (inv_nonneg.mpr
      (Ch02.lambdaSq_finite_nonneg Q A (by linarith only [hs]) (by norm_num)))
  have hupper : sigma⁻¹ * Ch02.LambdaSq Q s (.finite 2) A ≤ Y ^ (2 : ℕ) := by
    nlinarith [Real.sq_sqrt hupperArg, Real.sqrt_nonneg
      (sigma⁻¹ * Ch02.LambdaSq Q s (.finite 2) A)]
  have hlower : sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹ ≤ Y ^ (2 : ℕ) := by
    nlinarith [Real.sq_sqrt hlowerArg, Real.sqrt_nonneg
      (sigma * (Ch02.lambdaSq Q (s / 2) (.finite 2) A)⁻¹)]
  have hprice := dirichletEnergyWithRHSRHS_le_of_datum_caps
    v hC hs hsigma (sq_nonneg Y) hlower hupper hgReg hG hhReg hH
  simpa [Real.sqrt_sq hY, mul_assoc, mul_left_comm] using hprice

/-- The manuscript energy row: almost surely, every admissible Dirichlet
solution is bounded by the coefficient-only envelope times its two positive
Besov datum quantities.  Finiteness of the raw full `q = 2` response is
obtained from its moment estimate before taking the real readout. -/
theorem exists_ae_dirichletForcedSolutionEnergyNorm_le_envelope
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L N : ℕ)
        {s p B : ℝ}, 0 < s → s < 1 → 0 < p →
        paperENNRealLpNorm M.P.toMeasure p
            (fun omega ↦ paperHomogenizationError
              (originCube d (N : ℤ)) (N : ℤ) (s / 2)
              .infinity (.finite 2) (aCutoffFamily M L omega) (ahom M L)) ≤
          ENNReal.ofReal B →
        ∀ᵐ omega ∂M.P.toMeasure,
          ∀ {g : Vec d → Vec d}
            (v : DirichletForcedCubeSolution (originCube d (N : ℤ))
              (aCutoffFamily M L omega) g) {G H : ℝ},
            ForceBesovRegularity (originCube d (N : ℤ)) s g →
            scaleNormalizedPositiveBesovVectorSeminormTwo
                (originCube d (N : ℤ)) s g ≤ G →
            ForceBesovRegularity (originCube d (N : ℤ)) s
              (dirichletBoundaryGradientField v) →
            scaleNormalizedPositiveBesovVectorNormTwo
                (originCube d (N : ℤ)) s
                (dirichletBoundaryGradientField v) ≤ H →
            dirichletForcedSolutionEnergyNorm
                (originCube d (N : ℤ)) (aCutoffFamily M L omega) v ≤
              C * Real.rpow s (-(3 / 2 : ℝ)) *
                  (dirichletEllipticityEnvelope M L N s omega *
                    Real.sqrt (ahom M L)⁻¹) * G +
                C * Real.rpow s (-(1 / 2 : ℝ)) *
                  (dirichletEllipticityEnvelope M L N s omega *
                    Real.sqrt (ahom M L)) * H := by
  obtain ⟨C, hC, hdir, _⟩ := (energyConsequencesRHSTheory (d := d)).exists_constant
  refine ⟨C, hC, ?_⟩
  intro M L N s p B hs hsOne hp hmoment
  have hcaps :=
    ae_max_sqrt_weightedEllipticity_le_dirichletEllipticityEnvelope_of_moment
      M L N hs (show s / 2 ≤ s / 2 by rfl) hp hmoment
  filter_upwards [hcaps] with omega homega
  intro g v G H hgReg hG hhReg hH
  have hLambda :
      Ch02.LambdaSq (originCube d (N : ℤ)) s (.finite 2)
          (aCutoffFamily M L omega) ≤
        Ch02.LambdaSq (originCube d (N : ℤ)) (s / 2) (.finite 2)
          (aCutoffFamily M L omega) :=
    Ch02.LambdaSq_finite_antitone _ _ (by linarith only [hs])
      (by linarith only [hs]) (by norm_num)
  have hupperRoot :
      Real.sqrt ((ahom M L)⁻¹ *
          Ch02.LambdaSq (originCube d (N : ℤ)) s (.finite 2)
            (aCutoffFamily M L omega)) ≤
        Real.sqrt ((ahom M L)⁻¹ *
          Ch02.LambdaSq (originCube d (N : ℤ)) (s / 2) (.finite 2)
            (aCutoffFamily M L omega)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hLambda
      (inv_nonneg.mpr (ahom_pos M L).le)
  have homega' : max
      (Real.sqrt ((ahom M L)⁻¹ *
        Ch02.LambdaSq (originCube d (N : ℤ)) s (.finite 2)
          (aCutoffFamily M L omega)))
      (Real.sqrt (ahom M L *
        (Ch02.lambdaSq (originCube d (N : ℤ)) (s / 2) (.finite 2)
          (aCutoffFamily M L omega))⁻¹)) ≤
        dirichletEllipticityEnvelope M L N s omega := by
    exact max_le
      (hupperRoot.trans ((le_max_left _ _).trans homega))
      ((le_max_right _ _).trans homega)
  have hmain := hdir v hs hsOne hgReg hhReg
  exact hmain.trans (dirichletEnergyWithRHSRHS_le_of_sqrt_caps
    v hC.le hs (ahom_pos M L)
      ((show (0 : ℝ) ≤ 1 by norm_num).trans
        (one_le_dirichletEllipticityEnvelope M L N s omega))
      homega' hgReg hG hhReg hH)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
