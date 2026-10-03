module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryLocalizedHalfSteps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryResidualEighth

@[expose] public section

/-!
# Localized residual eighth with physical readout

This module wires the three localized corrected-flux half-steps to the
affine/residual energy transfer.  The shared remainder is kept in its exact
four-component form until after the weights `1`, `1 / 2`, and `1 / 4` have
been applied.

PROVENANCE: this is the three-localization composition implicit in
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryAssemblyEnergy.lean`,
with the GMC residual-eighth constant walk supplied by
`BoundaryResidualEighth.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- Three localized half-steps, with their literal four-component budgets,
followed by the one-eighth residual and one-half physical readouts. -/
theorem exists_boundaryCrossScale_physicalHalfStep_of_threeLocalizedCells
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE : ℝ} {g₀ : Vec d → Vec d}
        (uRes : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (hRes : H1Function (openCubeSet Q)) (center : Vec d)
        (u v : H1Function (openCubeSet Q))
        {rho₀ rho₁ rho₂ rho₃ : ℝ} (Ad Ag : ℝ → ℝ → ℝ),
        (∀ x, u.grad x = uRes.toH1.grad x + v.grad x) →
        (1 / 3 : ℝ) ≤ rho₀ → rho₀ < rho₁ → rho₁ < rho₂ →
        rho₂ < rho₃ → rho₃ < 1 →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K → 0 ≤ BE →
        (∀ a b, 0 ≤ Ad a b) → (∀ a b, 0 ≤ Ag a b) →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g₀ x) →
        MemLp (fun y ↦ (uRes.toH1).toFun y - hRes.toFun y) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g₀ x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (openCubeSet Q) (uRes.toH1) g₀ →
        MemVectorL2 (openCubeSet Q) g₀ →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (coarseCaccioppoliLocalOpenCube Q center 1)
          (fun y ↦ (uRes.toH1).toFun y - hRes.toFun y) →
        (let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad)
          ∀ k : ℕ, descendantsAverage Q (k + 1) Eh ≤ BE) →
        (∀ a b, (1 / 3 : ℝ) ≤ a → a < b → b < 1 →
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveDatumDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center a
                  (coarseCaccioppoliBufferedCutoffRadius a b)) hRes.grad) ≤ Ad a b) →
        (∀ a b, (1 / 3 : ℝ) ≤ a → a < b → b < 1 →
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveForceDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center a
                  (coarseCaccioppoliBufferedCutoffRadius a b)) g₀) ≤ Ag a b) →
        let B : ℝ → ℝ → ℝ := fun a b ↦
          (5 / 2 : ℝ) * Ad a b +
          (boundaryCommonGapPowerBudget Q s sigma K C 0
              (fun y ↦ (uRes.toH1).toFun y - hRes.toFun y) (fun x ↦ -g₀ x) +
            (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE) *
              Real.rpow (b - a) (-8 : ℝ) +
          (5 / 2 : ℝ) * Ag a b
        boundaryCrossScaleEnergyProfile Q Q center rho₀ (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
          (1 / 2 : ℝ) *
              boundaryCrossScaleEnergyProfile Q Q center rho₃ (fun x ↦
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.grad x)) +
            (5 / 2 : ℝ) * localizedCoeffEnergyValue (openCubeSet Q)
              ((aCutoffFamily M L omega).coeffOn Q) v +
            2 * (B rho₀ rho₁ + (1 / 2 : ℝ) * B rho₁ rho₂ +
              (1 / 4 : ℝ) * B rho₂ rho₃) := by
  obtain ⟨C, hC, hsteps⟩ :=
    exists_three_boundaryCrossScale_halfSteps_of_localizedCells d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE g₀ uRes hRes center u v
    rho₀ rho₁ rho₂ rho₃ Ad Ag hgrad hthird h01 h12 h23 h3
    hs hs4 hsigma hK hBE hAd hAg hupper hlower hreg hu hFL2 hweak hg hzero
    hEh hdatum hforce
  dsimp only
  obtain ⟨h₀, h₁, h₂⟩ := hsteps M L omega uRes hRes center Ad Ag
    hthird h01 h12 h23 h3 hs hs4 hsigma hK hBE hAd hAg hupper hlower hreg
      hu hFL2 hweak hg hzero hEh hdatum hforce
  exact boundaryCrossScaleEnergyProfile_physical_half_of_three_residual_half_steps
    M L omega Q Q center u uRes.toH1 v hgrad h₀ h₁ h₂

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
