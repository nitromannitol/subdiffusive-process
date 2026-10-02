import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicSeam.OpenRadiusClosure




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicSeam

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped ENNReal

noncomputable section

/-- **The affine-external boundary radius recurrence.**

Exactly the landed half-step, with its open outer radius closed and its four
prices collected.  The gap-priced datum and force budgets are the same ones
consumed by `exists_boundaryCrossScaleEnergyProfile_oneThird_le_affineExternal`;
no new analytic premise is introduced. -/
theorem exists_budgetedRadiusRecurrence_of_affineExternalHalfSteps
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE Ad Ag : ℝ} {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (h : H1Function (openCubeSet Q)) (center : Vec d),
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K →
        0 ≤ BE → 0 ≤ Ad → 0 ≤ Ag →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g₀ x) →
        MemLp (fun y ↦ u.toH1.toFun y - h.toFun y) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g₀ x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (openCubeSet Q) u.toH1 g₀ →
        MemVectorL2 (openCubeSet Q) g₀ →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (coarseCaccioppoliLocalOpenCube Q center 1)
          (fun y ↦ u.toH1.toFun y - h.toFun y) →
        (let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) h.grad)
          ∀ k : ℕ, descendantsAverage Q (k + 1) Eh ≤ BE) →
        (∀ rhoInner rhoOuter : ℝ, (1 / 3 : ℝ) ≤ rhoInner →
          rhoInner < rhoOuter → rhoOuter < 1 →
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveDatumDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
                h.grad) ≤
            Ad * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) →
        (∀ rhoInner rhoOuter : ℝ, (1 / 3 : ℝ) ≤ rhoInner →
          rhoInner < rhoOuter → rhoOuter < 1 →
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveForceDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
                g₀) ≤
            Ag * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) →
        Section6HarmonicLocalRow.BudgetedRadiusRecurrence
          (fun rho ↦ boundaryCrossScaleEnergyProfile Q Q center rho (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (u.toH1.grad x)))
          (1 / 2 : ℝ)
          (Real.rpow 2 8 *
            (boundaryCommonGapPowerBudget Q s sigma K C 0
                (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) +
              (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE +
              (5 / 2 : ℝ) * Ad + (5 / 2 : ℝ) * Ag))
          0 8 := by
  obtain ⟨C, hC, hhalf⟩ := exists_boundaryCrossScale_halfStep_of_affineExternalCells d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE Ad Ag g₀ u h center hs hs4 hsigma hK hBE
    hAd hAg hupper hlower hreg hu hFL2 hweak hg hzero hEh hdatum hforce
  have henergy0 : ∀ p ∈ openCubeSet Q,
      0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
        vecNormSq (u.toH1.grad p) := by
    intro p _
    exact mul_nonneg
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega p).le (vecNormSq_nonneg _)
  have henergyInt : IntegrableOn (fun p ↦
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega p *
        vecNormSq (u.toH1.grad p)) (openCubeSet Q) :=
    integrableOn_aCutoff_energy M L omega Q u.toH1
  refine budgetedRadiusRecurrence_profile_of_openHalfSteps
    henergy0 henergyInt ?_
  intro r₁ r₂ hr₁ hlt hr₂
  have hgap0 : 0 < r₂ - r₁ := sub_pos.mpr hlt
  have hpow0 : 0 ≤ Real.rpow (r₂ - r₁) (-8 : ℝ) :=
    Real.rpow_nonneg hgap0.le _
  have hAd' : 0 ≤ Ad * Real.rpow (r₂ - r₁) (-8 : ℝ) := mul_nonneg hAd hpow0
  have hAg' : 0 ≤ Ag * Real.rpow (r₂ - r₁) (-8 : ℝ) := mul_nonneg hAg hpow0
  have hstep := hhalf M L omega
    (Ad := Ad * Real.rpow (r₂ - r₁) (-8 : ℝ))
    (Ag := Ag * Real.rpow (r₂ - r₁) (-8 : ℝ))
    u h center hr₁ hlt hr₂ hs hs4 hsigma hK hBE hAd' hAg' hupper hlower
    hreg hu hFL2 hweak hg hzero hEh
    (hdatum r₁ r₂ hr₁ hlt hr₂) (hforce r₁ r₂ hr₁ hlt hr₂)
  calc
    boundaryCrossScaleEnergyProfile Q Q center r₁ (fun x ↦
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          vecNormSq (u.toH1.grad x)) ≤
        (1 / 2 : ℝ) *
            boundaryCrossScaleEnergyProfile Q Q center r₂ (fun x ↦
              SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                vecNormSq (u.toH1.grad x)) +
          (5 / 2 : ℝ) * (Ad * Real.rpow (r₂ - r₁) (-8 : ℝ)) +
          (boundaryCommonGapPowerBudget Q s sigma K C 0
              (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) +
            (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE) *
              Real.rpow (r₂ - r₁) (-8 : ℝ) +
          (5 / 2 : ℝ) * (Ag * Real.rpow (r₂ - r₁) (-8 : ℝ)) := hstep
    _ = (1 / 2 : ℝ) *
          boundaryCrossScaleEnergyProfile Q Q center r₂ (fun x ↦
            SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (u.toH1.grad x)) +
        (boundaryCommonGapPowerBudget Q s sigma K C 0
              (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) +
            (1 / 8 + (64 * C ^ 4 * K)⁻¹) * BE +
            (5 / 2 : ℝ) * Ad + (5 / 2 : ℝ) * Ag) *
          Real.rpow (r₂ - r₁) (-8 : ℝ) + 0 := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicSeam
