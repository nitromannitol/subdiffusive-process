module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveRadiusEnergy
public import Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliScaleZeroCore
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Averages

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The public matrix-valued forced equation for the scalar cutoff family is
the source-sign scalar weak equation. -/
theorem isDivFormWeakSolutionOn_of_isForcedEquation_aCutoff
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q))
    (g₀ : Vec d → Vec d)
    (hu : IsForcedEquation Q (aCutoffFamily M L omega) u (fun x ↦ -g₀ x)) :
    IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (openCubeSet Q) u g₀ := by
  intro phi
  have hforced := hu phi
  have hflux : (fun x ↦
      vecDot (matVecMul
        (((aCutoffFamily M L omega).coeffOn Q).toCoeffField x) (u.grad x))
        (phi.toH1Function.grad x)) =
      fun x ↦ vecDot
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x • u.grad x)
        (phi.toH1Function.grad x) := by
    funext x
    congr 1
    simp [aCutoffFamily, aCutoffTriadicData,
      ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
      ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
      matVecMul_scalarMatrix]
  have hneg : (fun x ↦ vecDot (-g₀ x) (phi.toH1Function.grad x)) =
      fun x ↦ -vecDot (g₀ x) (phi.toH1Function.grad x) := by
    funext x
    exact vecDot_neg_left _ _
  rw [hflux] at hforced
  simpa only [Ch02.cubeDomain_coe, hneg, integral_neg] using hforced

omit [NeZero d] in
/-- Repackage a public forced equation as the solution structure consumed by
the adaptive active-cell construction. -/
noncomputable def forcedCubeSolutionOfIsForcedEquation
    {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    (u : H1Function (openCubeSet Q)) (hu : IsForcedEquation Q a u g) :
    ForcedCubeSolution Q a g where
  toH1 := u
  weakSolution := hu

omit [NeZero d] in
@[simp] theorem forcedCubeSolutionOfIsForcedEquation_toH1
    {Q : TriadicCube d} {a : CoeffFamily d} {g : Vec d → Vec d}
    (u : H1Function (openCubeSet Q)) (hu : IsForcedEquation Q a u g) :
    (forcedCubeSolutionOfIsForcedEquation u hu).toH1 = u :=
  rfl

omit [NeZero d] in
/-- Exact comparison-field energy partition over every descendant depth. -/
theorem descendantsAverage_comparisonEnergy_eq_parent
    (Q : TriadicCube d) (a : CoeffFamily d)
    (h : H1Function (openCubeSet Q)) (j : ℕ) :
    descendantsAverage Q j (fun S ↦ cubeAverage S
        (coefficientEnergyDensity
          (publicCoeffField S a) h.grad)) =
      cubeAverage Q (coefficientEnergyDensity
        (publicCoeffField Q a) h.grad) := by
  let f : Vec d → ℝ := coefficientEnergyDensity
    ((a.coeffOn Q).toCoeffField) h.grad
  have hf : IntegrableOn f (cubeSet Q) := by
    rw [integrableOn_cubeSet_iff_integrableOn_openCubeSet]
    exact integrableOn_coefficientEnergyDensity_coeffOn Q (a.coeffOn Q) h
  have hpart := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    Q j f hf
  calc
    descendantsAverage Q j (fun S ↦ cubeAverage S
        (coefficientEnergyDensity (publicCoeffField S a) h.grad)) =
        descendantsAverage Q j (fun S ↦ cubeAverage S f) := by
      apply Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms.descendantsAverage_congr_of_eq_on_descendants
      intro S hS
      apply cubeAverage_eq_of_ae_eq_on_cubeSet
      have hle : volumeMeasureOn (cubeSet S) ≤
          volumeMeasureOn (cubeSet Q) := by
        simpa [volumeMeasureOn] using Measure.restrict_mono
          (cubeSet_subset_of_mem_descendantsAtDepth hS) le_rfl
      have hparent := (publicCoeffField_ae_eq_cubeSet Q a).filter_mono
        (MeasureTheory.ae_mono hle)
      filter_upwards
        [publicCoeffField_ae_eq_publicCoeffField_descendant_cubeSet Q a hS,
          hparent]
        with x hx hparentx
      simp only [f, coefficientEnergyDensity]
      rw [← hx, hparentx]
    _ = cubeAverage Q f := hpart.symm
    _ = cubeAverage Q (coefficientEnergyDensity
        (publicCoeffField Q a) h.grad) := by
      apply cubeAverage_eq_of_ae_eq_on_cubeSet
      filter_upwards [(publicCoeffField_ae_eq_cubeSet Q a).symm] with x hx
      simp only [f, coefficientEnergyDensity]
      rw [hx]

private theorem memLp_hilbertifyVecField_of_memLp
    {d : ℕ} {μ : Measure (Vec d)} {F : Vec d → Vec d}
    (hF : MemLp F (2 : ℝ≥0∞) μ) :
    MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞) μ := by
  let T : Vec d →L[ℝ] HilbertVec d :=
    ((HilbertVec.continuousLinearEquivVec d).symm).toContinuousLinearMap
  simpa [hilbertifyVecField] using! T.comp_memLp' hF

/-- The shared `gap^(-8)` active-cell estimate, specialized to the public
forced equation and with its comparison energy averaged exactly. -/
theorem exists_boundaryCrossScaleEnergyProfile_oneThird_le_gapPowerBudget_of_forcedEquation
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K Ad Ag : ℝ} {g₀ : Vec d → Vec d}
        (u h : H1Function (openCubeSet Q)) (center : Vec d),
        IsForcedEquation Q (aCutoffFamily M L omega) u (fun x ↦ -g₀ x) →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (coarseCaccioppoliLocalOpenCube Q center 1)
          (fun y ↦ u.toFun y - h.toFun y) →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K →
        0 ≤ Ad → 0 ≤ Ag →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g₀ x) →
        (∀ j : ℕ,
          let rhoInner := coarseCaccioppoliRadiusSequence j
          let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveDatumDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤
            Ad * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) →
        (∀ j : ℕ,
          let rhoInner := coarseCaccioppoliRadiusSequence j
          let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveForceDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g₀) ≤
            Ag * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) →
        boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ)
            (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (u.grad x)) ≤
          ((5 / 2 : ℝ) * Ad +
              boundaryCommonGapPowerBudget Q s sigma K C
                (cubeAverage Q (coefficientEnergyDensity
                  (publicCoeffField Q (aCutoffFamily M L omega)) h.grad))
                (fun y ↦ u.toFun y - h.toFun y) (fun x ↦ -g₀ x) +
              (5 / 2 : ℝ) * Ag) *
            coarseCaccioppoliRadiusIterationConst 8 := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_boundaryCrossScaleEnergyProfile_oneThird_le_gapPowerBudget d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K Ad Ag g₀ u h center heq hzero hs hs4
    hsigma hK hAd hAg hupper hlower hreg hdatum hforce
  let us : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x) :=
    forcedCubeSolutionOfIsForcedEquation u heq
  have hweak := isDivFormWeakSolutionOn_of_isForcedEquation_aCutoff
    M L omega Q u g₀ heq
  have hgneg : MemVectorL2 (openCubeSet Q) (fun x ↦ -g₀ x) := by
    have h := memVectorL2_cubeSet_of_forceBesovRegularity hreg
    rw [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at h
    exact h
  have hg : MemVectorL2 (openCubeSet Q) g₀ := by
    convert hgneg.neg using 1
    funext x
    simp
  have huLp : MemLp (fun y ↦ us.toH1.toFun y - h.toFun y)
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    us.toH1.memL2_normalizedCubeMeasure.sub h.memL2_normalizedCubeMeasure
  have hgLp : MemLp (fun x ↦ HilbertVec.ofVec (-g₀ x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_hilbertifyVecField_of_memLp hreg.memLp
  let BE := cubeAverage Q (coefficientEnergyDensity
    (publicCoeffField Q (aCutoffFamily M L omega)) h.grad)
  have hBE : 0 ≤ BE :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn Q
      (publicCoeffField Q (aCutoffFamily M L omega)) h.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet Q (aCutoffFamily M L omega))
  have hEh : ∀ k : ℕ,
      let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
        (coefficientEnergyDensity
          (publicCoeffField S (aCutoffFamily M L omega)) h.grad)
      descendantsAverage Q (k + 1) Eh ≤ BE := by
    intro k
    dsimp only
    exact (descendantsAverage_comparisonEnergy_eq_parent Q
      (aCutoffFamily M L omega) h (k + 1)).le
  simpa only [us, BE, forcedCubeSolutionOfIsForcedEquation_toH1] using
    hbase M L omega us h center hweak hg hzero hs hs4 hsigma hK hBE hAd hAg
      hupper hlower hreg huLp hgLp hEh hdatum hforce



theorem exists_boundaryCrossScaleEnergyProfile_oneThird_le_gapPowerBudget_of_projectedTrace
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K Ad Ag : ℝ} {g₀ : Vec d → Vec d}
        (u h : H1Function (openCubeSet Q)) (center : Vec d),
        IsForcedEquation Q (aCutoffFamily M L omega) u (fun x ↦ -g₀ x) →
        LocalizedZeroTraceFunctionOn (openCubeSet Q)
          (openCubeAtScale center (Q.scale - 1))
          (fun y ↦ u.toFun y - h.toFun y) →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 < K →
        0 ≤ Ad → 0 ≤ Ag →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g₀ x) →
        (∀ j : ℕ,
          let rhoInner := coarseCaccioppoliRadiusSequence j
          let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveDatumDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) h.grad) ≤
            Ad * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) →
        (∀ j : ℕ,
          let rhoInner := coarseCaccioppoliRadiusSequence j
          let rhoOuter := coarseCaccioppoliRadiusSequence (j + 1)
          volumeAverage (openCubeSet Q)
              (boundaryCoerciveForceDensity
                (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                  (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) g₀) ≤
            Ag * Real.rpow (rhoOuter - rhoInner) (-8 : ℝ)) →
        boundaryCrossScaleEnergyProfile Q Q center (1 / 3 : ℝ)
            (fun x ↦ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
              vecNormSq (u.grad x)) ≤
          ((5 / 2 : ℝ) * Ad +
              boundaryCommonGapPowerBudget Q s sigma K C
                (cubeAverage Q (coefficientEnergyDensity
                  (publicCoeffField Q (aCutoffFamily M L omega)) h.grad))
                (fun y ↦ u.toFun y - h.toFun y) (fun x ↦ -g₀ x) +
              (5 / 2 : ℝ) * Ag) *
            coarseCaccioppoliRadiusIterationConst 8 := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_boundaryCrossScaleEnergyProfile_oneThird_le_gapPowerBudget_of_forcedEquation d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K Ad Ag g₀ u h center heq htrace hs hs4
    hsigma hK hAd hAg hupper hlower hreg hdatum hforce
  apply hbase M L omega u h center heq
  · simpa only [coarseCaccioppoliLocalOpenCube_one_eq_openCubeAtScale]
      using htrace
  · exact hs
  · exact hs4
  · exact hsigma
  · exact hK
  · exact hAd
  · exact hAg
  · exact hupper
  · exact hlower
  · exact hreg
  · exact hdatum
  · exact hforce

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
