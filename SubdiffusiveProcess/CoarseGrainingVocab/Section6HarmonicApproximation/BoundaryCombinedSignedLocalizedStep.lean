module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCombinedSignedFiniteHeight
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCombinedSignedHalfStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryResidualEighth

@[expose] public section

/-!
# Localized signed step with the finite-height premise discharged

This module applies the common-height descendant estimate directly to the
combined signed weak-energy row.  The residual, affine lift, and residual
datum remain three separate outer profiles for the subsequent finite-radius
constant walk.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

/-- Scalar collapse of the combined signed row after the residual-to-physical
outer split.  The lift and datum profiles are charged only once. -/
theorem combinedSignedStep_to_physical_threeQuarter
    {Ein Eout Er EvProfile EhProfile Ev BE Ag P : ℝ}
    (hstep : Ein ≤ (1 / 2 : ℝ) * Er + (5 / 2 : ℝ) * EvProfile +
      (29 / 8 : ℝ) * EhProfile + (5 / 2 : ℝ) * Ag + P)
    (hres : Er ≤ (3 / 2 : ℝ) * Eout + 3 * Ev)
    (hev : EvProfile ≤ Ev) (heh : EhProfile ≤ BE) :
    Ein ≤ (3 / 4 : ℝ) * Eout + 4 * Ev +
      (29 / 8 : ℝ) * BE + (5 / 2 : ℝ) * Ag + P := by
  linarith only [hstep, hres, hev, heh]

/-- Three consecutive signed rows recover the one-half contraction expected
by the standard radius iteration (`(3/4)^3 = 27/64`). -/
theorem physical_half_of_three_threeQuarter_steps
    {E₀ E₁ E₂ E₃ B₀ B₁ B₂ : ℝ}
    (h₀ : E₀ ≤ (3 / 4 : ℝ) * E₁ + B₀)
    (h₁ : E₁ ≤ (3 / 4 : ℝ) * E₂ + B₁)
    (h₂ : E₂ ≤ (3 / 4 : ℝ) * E₃ + B₂)
    (hE₃ : 0 ≤ E₃) :
    E₀ ≤ (1 / 2 : ℝ) * E₃ +
      (B₀ + (3 / 4 : ℝ) * B₁ + (9 / 16 : ℝ) * B₂) := by
  linarith only [h₀, h₁, h₂, hE₃]

/-- A localized scalar-cutoff energy profile is bounded by the full public
coefficient energy of the same `H¹` field. -/
theorem boundaryCrossScaleEnergyProfile_aCutoff_le_localizedCoeffEnergyValue
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) (rho : ℝ)
    (u : H1Function (openCubeSet Q)) :
    boundaryCrossScaleEnergyProfile Q R center rho (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      localizedCoeffEnergyValue (openCubeSet Q)
        ((aCutoffFamily M L omega).coeffOn Q) u := by
  let energy : Vec d → ℝ := fun x ↦
    _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)
  have henergy : IntegrableOn energy (openCubeSet Q) := by
    simpa only [energy] using integrableOn_aCutoff_energy M L omega Q u
  have hle : boundaryCrossScaleEnergyProfile Q R center rho energy ≤
      volumeAverage (openCubeSet Q) energy := by
    unfold boundaryCrossScaleEnergyProfile
    apply volumeAverage_le_volumeAverage_of_le_on (measurableSet_openCubeSet Q)
      (henergy.indicator
        (measurableSet_coarseCaccioppoliLocalClosedCube R center rho)) henergy
    intro x _hx
    by_cases hp : x ∈ coarseCaccioppoliLocalClosedCube R center rho
    · simp [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp]
      exact mul_nonneg (_root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x).le
        (vecNormSq_nonneg _)
  rw [volumeAverage_aCutoff_vecNormSq_eq_localizedCoeffEnergyValue
    M L omega Q u] at hle
  simpa only [energy] using hle

/-- Carrier-level three-quarter row obtained from a combined signed step.
The affine lift is charged by its full-cube energy and the residual datum by
the caller's parent budget. -/
theorem boundaryCrossScale_physical_threeQuarter_of_combinedSignedStep
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter BE Ag P : ℝ}
    (u r v hRes : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = r.grad x + v.grad x)
    (hBE : localizedCoeffEnergyValue (openCubeSet Q)
      ((aCutoffFamily M L omega).coeffOn Q) hRes ≤ BE)
    (hstep : boundaryCrossScaleEnergyProfile Q R center rhoInner (fun x ↦
          _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
        (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
            (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
              vecNormSq (r.grad x)) +
          (5 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
            (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
              vecNormSq (v.grad x)) +
          (29 / 8 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
            (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
              vecNormSq (hRes.grad x)) +
          (5 / 2 : ℝ) * Ag + P) :
    boundaryCrossScaleEnergyProfile Q R center rhoInner (fun x ↦
        _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      (3 / 4 : ℝ) * boundaryCrossScaleEnergyProfile Q R center rhoOuter
          (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
            vecNormSq (u.grad x)) +
        4 * localizedCoeffEnergyValue (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v +
        (29 / 8 : ℝ) * BE + (5 / 2 : ℝ) * Ag + P := by
  have hgradReverse : ∀ x, r.grad x = u.grad x - v.grad x := by
    intro x
    rw [hgrad x]
    abel_nf
  have hres :=
    boundaryCrossScaleEnergyProfile_aCutoff_residual_le_threeHalves_physical_add_three_affine
      M L omega Q R center rhoOuter u r v hgradReverse
  have hev := boundaryCrossScaleEnergyProfile_aCutoff_le_localizedCoeffEnergyValue
    M L omega Q R center rhoOuter v
  have heh0 := boundaryCrossScaleEnergyProfile_aCutoff_le_localizedCoeffEnergyValue
    M L omega Q R center rhoOuter hRes
  have heh := heh0.trans hBE
  exact combinedSignedStep_to_physical_threeQuarter hstep hres hev heh

/-- The signed localized radius row with its sole analytic premise supplied
by the finite-height combined-pairing theorem. -/
theorem exists_boundaryCrossScale_combinedSignedLocalizedStep
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
        (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE Ag : ℝ} {g : Vec d → Vec d}
        (u r v hRes : H1Function (openCubeSet Q)) (center : Vec d)
        {rhoInner rhoOuter : ℝ},
        (∀ x, u.grad x = r.grad x + v.grad x) →
        IsDivFormWeakSolutionOn
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) r g →
        IsDivFormWeakSolutionOn
          (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) (openCubeSet Q) v
            (fun _ ↦ 0) →
        MemVectorL2 (openCubeSet Q) g →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (coarseCaccioppoliLocalOpenCube Q center 1)
          (fun x ↦ r.toFun x - hRes.toFun x) →
        (1 / 3 : ℝ) ≤ rhoInner → rhoInner < rhoOuter → rhoOuter < 1 →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K → 0 ≤ BE →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g x) →
        MemLp (r - hRes).toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        (let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) hRes.grad);
          ∀ k : ℕ, descendantsAverage Q (k + 1) Eh ≤ BE) →
        volumeAverage (openCubeSet Q)
            (boundaryCoerciveForceDensity
              (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
              (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g) ≤ Ag →
        boundaryCrossScaleEnergyProfile Q Q center rhoInner (fun x ↦
            _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
          (1 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
              (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
                vecNormSq (r.grad x)) +
            (5 / 2 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
              (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
                vecNormSq (v.grad x)) +
            (29 / 8 : ℝ) * boundaryCrossScaleEnergyProfile Q Q center rhoOuter
              (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
                vecNormSq (hRes.grad x)) +
            (5 / 2 : ℝ) * Ag +
            4 * (boundaryCommonGapPowerBudget Q s sigma K C BE
              (r - hRes).toFun (fun x ↦ -g x) *
                Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) := by
  obtain ⟨C, hC, hcap⟩ := exists_abs_combinedSignedPairing_triadicGap d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE Ag g u r v hRes center rhoInner rhoOuter
    hgrad hweakR hweakV hg hzero hinner hlt houter hs hs4 hsigma hK hBE
    hupper hlower hreg hresL2 hgL2 hEh hforce
  obtain ⟨k, hchoice⟩ :=
    exists_coarseCaccioppoliTriadicGapScaleChoice hinner hlt houter.le
  have hpair := hcap M L omega r v hRes center hweakR hweakV
    (lt_of_lt_of_le (by norm_num) hinner) hlt hchoice hs hs4 hsigma hK.le
      hupper hlower hreg hresL2 hgL2 hg (hEh k)
  have hstep := boundaryCrossScale_physical_le_of_combinedSignedPairing
    M L omega Q u r v hRes g center hgrad hweakR hweakV hg hzero
      (lt_of_lt_of_le (by norm_num) hinner) hlt houter hforce hpair
  obtain ⟨S, hS⟩ := descendantsAtDepth_nonempty Q (k + 1)
  have hrem := boundaryCommonYoungParentBudgetWeighted_le_gapPowerBudget
    (Q := Q) (S := S) (k := k) (rhoInner := rhoInner) (rhoOuter := rhoOuter)
      (s := s) (sigma := sigma) (K := K) (C := C) (BE := BE)
      (u := (r - hRes).toFun) (F := fun x ↦ -g x)
      hS hinner hlt houter.le hchoice hs hs4 hsigma hK hC hBE hreg
  linarith only [hstep, hrem]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
