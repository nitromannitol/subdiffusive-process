module

public import SubdiffusiveProcess.Frozen.Section2.CoarseGrainedPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.CoarseRHS.RHSEnergy

@[expose] public section

/-!
`l.coarse.graining.RHS` ([ASD, Lemma 2.11], symmetric specialization), proved.

For `a` symmetric uniformly elliptic on `cu_m`, `g ∈ H^s(cu_m; ℝ^d)`: (1) the gradient display, (2) the flux
display, for every `u ∈ H¹(cu_m)` with `-∇·a∇u = ∇·g`; and (3) for every `h ∈ H^{1+s}(cu_m)` the energy
bound `e.cg.RHS` for the Dirichlet solution `v` (`v - h ∈ H¹₀`) and the mean-zero-flux Neumann solution `w`.
`g ∈ H^s` is `CubeEuclideanWspField Q s 2`; `h ∈ H^{1+s}` is `h ∈ H¹` with `∇h = Hh` for some `Hh ∈ H^s`;
`[·]_{H^s}` is the printed seminorm (`paperFractionalSeminorm`, leading factor `s^{1/2}`) and `‖·‖_{H^s}`
the printed full norm (`paperFractionalFullNorm`).  Forced weak equation: `∫ a∇u·∇φ = -∫ g·∇φ` for
`φ ∈ H¹₀` (`-∇·a∇u = ∇·g`); Neumann: the same for all `φ ∈ H¹` with `g - (g)_{cu_m}`.

PROOF.  The three displays are the CoarseGraining library theorems `Ch03.coarsePoincareRHSTheory`,
`Ch03.weakFluxRHSTheory`, `Ch03.energyConsequencesRHSTheory` (the formalization of [ASD, Lemma 2.11] in the
normalization of [ASD]: seminorms without the factor `s^{1/2}`), whose powers of `s` are at or below the
printed ones.  Passing to the paper's normalization costs `s^{1/2}` on the left of (1), (2) and `s^{-1/2}`
on the forcing/datum norms, absorbed by the slack; see `SubdiffusiveProcess.CoarseRHS.RHSDisplays`,
`SubdiffusiveProcess.CoarseRHS.RHSEnergy`.  The library statements hold for every triadic cube and every
(not necessarily symmetric) coefficient family, so the hypotheses on `Q` and the symmetry of `a` are not used.
-/

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization.Book MeasureTheory
open Homogenization hiding Vec Mat TriadicCube
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem l_coarse_graining_RHS {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : SubdiffusiveProcess.CoarseGrainingVocab.TriadicCube d),
      (∃ m : ℕ, 0 < m ∧ Q = Homogenization.originCube d (m : ℤ)) →
      ∀ (sF : Homogenization.FractionalOrder) (a : Ch02.TriadicCoeffFamily d),
        (∀ R, Ch02.CoeffOn.IsSymmetric (a.coeffOn R)) →
        ∀ G : Homogenization.CubeEuclideanWspField Q sF Homogenization.FiniteLpExponent.two,
          (∀ u : Homogenization.H1Function (Homogenization.openCubeSet Q),
            Homogenization.Book.Ch03.ABK26.IsForcedEquation Q (a.coeffOn Q) u G.toField →
              (paperScaleNormalizedNegativeBesovVectorNorm Q sF.1 (.finite 2) u.grad ≤
                C * Real.rpow sF.1 (-(3 / 2 : ℝ)) *
                    Real.rpow (lambda Q (sF.1 / 2) (.finite 2) a) (-(1 / 2 : ℝ)) *
                    coefficientEnergyNorm Q a u.grad +
                  C * Real.rpow sF.1 (-3 : ℝ) * (lambda Q (sF.1 / 2) (.finite 2) a)⁻¹ *
                    (Real.rpow (Homogenization.cubeScaleFactor Q) sF.1 *
                      (paperFractionalSeminorm Q sF Homogenization.FiniteLpExponent.two
                        G.toField).toReal)) ∧
              (paperScaleNormalizedNegativeBesovVectorNorm Q sF.1 (.finite 2)
                  (fun x => Homogenization.matVecMul ((a.coeffOn Q).toCoeffField x)
                    (u.grad x)) ≤
                C * Real.rpow sF.1 (-(3 / 2 : ℝ)) *
                    Real.rpow (Lambda Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ) *
                    coefficientEnergyNorm Q a u.grad +
                  C * Real.rpow sF.1 (-(9 / 2 : ℝ)) *
                    (Real.rpow (Lambda Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ) /
                      Real.rpow (lambda Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ)) *
                    (Real.rpow (Homogenization.cubeScaleFactor Q) sF.1 *
                      (paperFractionalSeminorm Q sF Homogenization.FiniteLpExponent.two
                        G.toField).toReal))) ∧
          (∀ (hh : Homogenization.H1Function (Homogenization.openCubeSet Q))
            (Hh : Homogenization.CubeEuclideanWspField Q sF Homogenization.FiniteLpExponent.two),
            Hh.toField = hh.grad →
            ∀ v w : Homogenization.H1Function (Homogenization.openCubeSet Q),
              Homogenization.Book.Ch03.ABK26.IsForcedEquation Q (a.coeffOn Q) v G.toField →
              SubdiffusiveProcess.CoarseGrainingVocab.HasZeroTraceDifferenceOn (Homogenization.openCubeSet Q) v hh →
              (∀ φ : Homogenization.H1Function (Homogenization.openCubeSet Q),
                ∫ x in Homogenization.openCubeSet Q,
                    Homogenization.vecDot
                      (Homogenization.matVecMul ((a.coeffOn Q).toCoeffField x) (w.grad x))
                      (φ.grad x) ∂volume =
                  -(∫ x in Homogenization.openCubeSet Q,
                    Homogenization.vecDot
                      (G.toField x - Homogenization.cubeAverageVec Q G.toField)
                      (φ.grad x) ∂volume)) →
              coefficientEnergyNorm Q a v.grad + coefficientEnergyNorm Q a w.grad ≤
                C * Real.rpow sF.1 (-3 : ℝ) *
                    Real.rpow (lambda Q (sF.1 / 2) (.finite 2) a) (-(1 / 2 : ℝ)) *
                    (Real.rpow (Homogenization.cubeScaleFactor Q) sF.1 *
                      (paperFractionalSeminorm Q sF Homogenization.FiniteLpExponent.two
                        G.toField).toReal) +
                  C * Real.rpow sF.1 (-(3 / 2 : ℝ)) *
                    Real.rpow (Lambda Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ) *
                    (Real.rpow (Homogenization.cubeScaleFactor Q) sF.1 *
                      (paperFractionalFullNorm Q sF Homogenization.FiniteLpExponent.two
                        Hh.toField).toReal)) := by
  have _hd := hd
  obtain ⟨C1, hC1, h1⟩ := SubdiffusiveProcess.CoarseRHS.coarsePoincare_flux_general d
  obtain ⟨C2, hC2, h2⟩ := SubdiffusiveProcess.CoarseRHS.energy_general d
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro Q _hQ sF a _haSym G
  have hs0 : 0 < sF.1 := sF.2.1
  have hs2 : 0 < sF.1 / 2 := by linarith
  have hL : 0 < Ch02.lambdaSq Q (sF.1 / 2) (.finite 2) a :=
    SubdiffusiveProcess.CoarseRHS.lambdaSq_two_pos Q a hs2
  have hLam : 0 < Ch02.LambdaSq Q (sF.1 / 2) (.finite 2) a :=
    SubdiffusiveProcess.CoarseRHS.LambdaSq_two_pos Q a hs2
  have hcf : (0 : ℝ) < Homogenization.cubeScaleFactor Q := by
    unfold Homogenization.cubeScaleFactor; positivity
  have hW : 0 ≤ Real.rpow (Homogenization.cubeScaleFactor Q) sF.1 :=
    (Real.rpow_pos_of_pos hcf _).le
  have hp32 : 0 ≤ Real.rpow sF.1 (-(3 / 2 : ℝ)) := (Real.rpow_pos_of_pos hs0 _).le
  have hp3 : 0 ≤ Real.rpow sF.1 (-3 : ℝ) := (Real.rpow_pos_of_pos hs0 _).le
  have hp92 : 0 ≤ Real.rpow sF.1 (-(9 / 2 : ℝ)) := (Real.rpow_pos_of_pos hs0 _).le
  have hlp : 0 ≤ Real.rpow (lambda Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ) :=
    Real.rpow_nonneg hL.le _
  have hlm : 0 ≤ Real.rpow (lambda Q (sF.1 / 2) (.finite 2) a) (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg hL.le _
  have hU : 0 ≤ Real.rpow (Lambda Q (sF.1 / 2) (.finite 2) a) (1 / 2 : ℝ) :=
    Real.rpow_nonneg hLam.le _
  have hLi : 0 ≤ (lambda Q (sF.1 / 2) (.finite 2) a)⁻¹ := inv_nonneg.mpr hL.le
  have hPS : 0 ≤ (paperFractionalSeminorm Q sF Homogenization.FiniteLpExponent.two G.toField).toReal :=
    ENNReal.toReal_nonneg
  have hFp : ∀ Hh : Homogenization.CubeEuclideanWspField Q sF Homogenization.FiniteLpExponent.two,
      0 ≤ (paperFractionalFullNorm Q sF Homogenization.FiniteLpExponent.two Hh.toField).toReal :=
    fun _ => ENNReal.toReal_nonneg
  have hC : C1 ≤ C1 + C2 := by linarith
  have hC' : C2 ≤ C1 + C2 := by linarith
  refine ⟨?_, ?_⟩
  · intro u hu
    obtain ⟨hg, hf⟩ := h1 Q sF a G u hu
    exact ⟨hg.trans (SubdiffusiveProcess.CoarseRHS.coeff_mono hC hp32 hlm
        (Real.sqrt_nonneg _) hp3 hLi (mul_nonneg hW hPS)),
      hf.trans (SubdiffusiveProcess.CoarseRHS.coeff_mono hC hp32 hU
        (Real.sqrt_nonneg _) hp92 (div_nonneg hU hlp) (mul_nonneg hW hPS))⟩
  · intro hh Hh hHh v w hv hzt hw
    exact (h2 Q sF a G hh Hh hHh v w hv hzt hw).trans
      (SubdiffusiveProcess.CoarseRHS.coeff_mono hC' hp3 hlm (mul_nonneg hW hPS) hp32 hU
        (mul_nonneg hW (hFp Hh)))

end SubdiffusiveProcess.Paper
