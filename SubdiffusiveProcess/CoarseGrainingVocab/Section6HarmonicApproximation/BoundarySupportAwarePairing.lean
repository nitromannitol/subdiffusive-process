module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryDescendantEllipticity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMultiscaleCutoffPairing

@[expose] public section

/-!
# Support-aware corrected-flux pairing on descendant cells

The annular cutoff is compactly supported in the parent comparison cube, but
not in each descendant meeting its support.  Consequently the local estimate
must not center the cutoff product by invoking the weak equation separately
on every descendant.  This file records the support-free alternative: apply
the corrected-flux/positive-Besov duality directly to the *uncentered* local
product.  The only remaining local input is its positive-Besov norm.

This is the support-aware local-patch split used by
`Homogenization/Deterministic/CoarseCaccioppoli/EnergyBridge/DescendantSummation.lean`,
with the GMC forced-solution corrected flux in place of the harmonic flux.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The public corrected flux of a forced solution with forcing `-g₀` is
the literal scalar GMC corrected flux `a grad u + g₀`, a.e. on the cube.
Unlike the older Dirichlet wrapper, this identity applies to the restricted
`ForcedCubeSolution` used on arbitrary descendants. -/
theorem cubeAverage_correctedFluxPairing_eq_boundaryDensity_forced
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q : TriadicCube d) (g₀ : Vec d → Vec d)
    (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
    (w eta : Vec d → ℝ) :
    cubeAverage Q (fun x ↦
        vecDot
          (forcedSolutionCorrectedFluxField Q (aCutoffFamily M L omega)
            (fun y ↦ -g₀ y) u x)
          (w x • scalarCutoffGradientField (fun y ↦ eta y ^ 2) x)) =
      cubeAverage Q
        (boundaryCorrectedFluxCutoffPairingDensity
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta w u.toH1.grad g₀) := by
  apply cubeAverage_eq_of_ae_eq_on_cubeSet
  filter_upwards [publicCoeffField_ae_eq_cubeSet Q (aCutoffFamily M L omega)]
    with x hx
  unfold forcedSolutionCorrectedFluxField boundaryCorrectedFluxCutoffPairingDensity
    boundaryCorrectedFlux
  change vecDot
      (matVecMul (publicCoeffField Q (aCutoffFamily M L omega) x) (u.toH1.grad x) -
        -g₀ x)
      (w x • scalarCutoffGradientField (fun y ↦ eta y ^ 2) x) = _
  rw [hx]
  simp only [aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
    ScalarCoeffOnData.toCoeffOn, scalarCoeffField, matVecMul_scalarMatrix,
    sub_neg_eq_add]

/-- Support-free descendant pairing endpoint.  No support or centering
hypothesis appears: the uncentered field `H` is paired directly with the
corrected flux.  This is the local analytic interface required by the finite
translated-cell summation. -/
theorem exists_abs_boundaryCorrectedFluxDensity_le_weakFlux_mul_positiveBesov
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        {Q : TriadicCube d} {t : ℝ} {g₀ H : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        {eta w : Vec d → ℝ} {B : ℝ},
        0 < t → t < 1 →
        ForceBesovRegularity Q t (fun x ↦ -g₀ x) →
        ForceBesovRegularity Q t H → 0 ≤ B →
        scaleNormalizedPositiveBesovVectorNormTwo Q t H ≤ B →
        H = (fun x ↦ w x • scalarCutoffGradientField (fun y ↦ eta y ^ 2) x) →
        |cubeAverage Q
            (boundaryCorrectedFluxCutoffPairingDensity
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) eta w u.toH1.grad g₀)| ≤
          C *
              (weakFluxWithRHSRHS C Q (aCutoffFamily M L omega) t
                  (fun x ↦ -g₀ x) u +
                boundaryNegativeToL2Factor (2 * t) *
                  boundaryNormalizedEuclideanL2 Q (fun x ↦ -g₀ x)) * B := by
  obtain ⟨C, hC, hpair⟩ :=
    exists_abs_correctedFlux_pairing_le_weakFlux_mul_positiveBesov d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q t g₀ H u eta w B ht ht1 hg hH hB hHnorm rfl
  have hraw := hpair u ht ht1 hg hH hB hHnorm
  rw [cubeAverage_correctedFluxPairing_eq_boundaryDensity_forced
    M L omega Q g₀ u w eta] at hraw
  exact hraw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
