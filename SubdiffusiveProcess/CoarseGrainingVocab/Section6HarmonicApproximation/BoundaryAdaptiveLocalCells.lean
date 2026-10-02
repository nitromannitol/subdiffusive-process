import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCenteredForce




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

/-- At a selected annular gap, the canonical active-cell remainder is the
common-height envelope and its finite average is the explicit parent budget.
No childwise norm remains in the conclusion. -/
theorem exists_boundaryCanonicalAdaptiveLocalCells_parentBudget
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
        (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
        {Q : TriadicCube d} {s sigma K BE : ℝ} {k : ℕ}
        {g₀ : Vec d → Vec d}
        (u : ForcedCubeSolution Q (aCutoffFamily M L omega) (fun x ↦ -g₀ x))
        (h : H1Function (openCubeSet Q)) (center : Vec d)
        {rhoInner rhoOuter : ℝ},
        0 < rhoInner → rhoInner < rhoOuter →
        CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter →
        0 < s → s ≤ 1 / 4 → 0 < sigma → 0 ≤ K →
        sigma⁻¹ * Ch02.LambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega) ≤ K →
        sigma * (Ch02.lambdaSq Q (s / 6) (.finite 2)
            (aCutoffFamily M L omega))⁻¹ ≤ K →
        ForceBesovRegularity Q (s / 3) (fun x ↦ -g₀ x) →
        MemLp (fun y ↦ u.toH1.toFun y - h.toFun y) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        MemLp (fun x ↦ HilbertVec.ofVec (-g₀ x)) (2 : ℝ≥0∞)
          (normalizedCubeMeasure Q) →
        let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
          (coefficientEnergyDensity
            (publicCoeffField S (aCutoffFamily M L omega)) h.grad)
        descendantsAverage Q (k + 1) Eh ≤ BE →
        ∃ remainder : TriadicCube d → ℝ,
          (∀ S ∈ descendantsAtDepth Q (k + 1), 0 ≤ remainder S) ∧
          (∀ S ∈ descendantsAtDepth Q (k + 1),
            (∃ y ∈ cubeSet S,
              y ∈ coarseCaccioppoliLocalClosedCube Q center
                (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) →
            |cubeAverage S
                (boundaryCorrectedFluxCutoffPairingDensity
                  (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
                  (coarseCaccioppoliLocalCanonicalFun Q center rhoInner
                    (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter))
                  (fun y ↦ u.toH1.toFun y - h.toFun y) u.toH1.grad g₀)| ≤
              (1 / 4 : ℝ) * cubeAverage S (fun x ↦
                SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
                  vecNormSq (u.toH1.grad x)) + remainder S) ∧
          descendantsAverage Q (k + 1) remainder ≤
            boundaryCommonYoungParentBudgetWeighted Q k rhoInner rhoOuter
              s sigma K C BE (fun y ↦ u.toH1.toFun y - h.toFun y)
                (fun x ↦ -g₀ x) := by
  obtain ⟨C, hC, hactive⟩ :=
    exists_boundaryCanonicalActiveCell_commonHeight_quarter d
  refine ⟨C, hC, ?_⟩
  intro M L omega Q s sigma K BE k g₀ u h center rhoInner rhoOuter hinner hlt
    hchoice hs hs4 hsigma hK hupper hlower hreg hu hFL2
  dsimp only
  let Eh : TriadicCube d → ℝ := fun S ↦ cubeAverage S
    (coefficientEnergyDensity
      (publicCoeffField S (aCutoffFamily M L omega)) h.grad)
  intro hEhavg
  let remainder : TriadicCube d → ℝ :=
    boundaryCommonYoungRemainder Q k rhoInner rhoOuter s sigma K C
      (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) Eh
  refine ⟨remainder, ?_, ?_, ?_⟩
  · intro S hS
    exact boundaryCommonYoungRemainder_nonneg hinner hlt hs hC.le
      (cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn S
        (publicCoeffField S (aCutoffFamily M L omega)) h.grad
        (publicCoeffField_isEllipticFieldOn_cubeSet S (aCutoffFamily M L omega)))
      (forceBesovRegularity_descendant hreg hS)
  · intro S hS _hactiveSupport
    have hraw := hactive M L omega u h center hS hinner hlt hchoice
      hs hs4 hsigma hK hupper hlower hreg
    let t := s / 3
    let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
    let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter t sigma K W C
    let height := Nat.ceil (boundaryFiniteHeightOfPrefactor t P)
    let eta := coarseCaccioppoliLocalCanonicalFun Q center rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    let Gcut := coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    let Hcut := coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
      (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)
    let Bcut := 2 * Hcut + 2 * Gcut ^ 2
    let uH := u.toH1.restrictToOpenSubcube hS
    let hSfun := h.restrictToOpenSubcube hS
    let wS := uH - hSfun
    let X₀ := cubeLpNorm S (2 : ℝ≥0∞) wS.toFun
    let Xc := cubeLpNorm S (2 : ℝ≥0∞) (cubeFluctuation S wS.toFun)
    let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
    let Gsemi := scaleNormalizedPositiveBesovVectorSeminormTwo S t (fun x ↦ -g₀ x)
    let Af := C * Real.rpow t (-(5 / 2 : ℝ)) *
      (Real.sqrt (W * K) * Real.sqrt sigma) *
      (Real.sqrt (W * K) * Real.sqrt sigma⁻¹)
    let Bf := boundaryNegativeToL2Factor (2 * t)
    let Gfac := Af * Gsemi + Bf * boundaryNormalizedEuclideanL2 S (fun x ↦ -g₀ x)
    have ht : 0 < t := by dsimp [t]; positivity
    have hBcut : 0 ≤ Bcut := by
      dsimp [Bcut, Hcut, Gcut]
      exact add_nonneg
        (mul_nonneg (by norm_num) ((norm_nonneg _).trans
          (coarseCaccioppoliLocalCanonicalFun_hessian_bound Q center hinner
            (coarseCaccioppoliBufferedCutoffRadius_between hlt).1 center)))
        (mul_nonneg (by norm_num) (sq_nonneg _))
    have hGsemi : 0 ≤ Gsemi := by
      dsimp [Gsemi, t]
      exact scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (forceBesovRegularity_descendant hreg hS)
    have hGfac : 0 ≤ Gfac := by
      dsimp [Gfac, Af, Bf]
      exact add_nonneg (mul_nonneg (by positivity) hGsemi)
        (mul_nonneg (boundaryNegativeToL2Factor_nonneg _)
          (boundaryNormalizedEuclideanL2_nonneg S (fun x ↦ -g₀ x)))
    have hmono := boundaryActiveCellYoungRemainder_le_common
      (Q := Q) (S := S) (center := center) (k := k) (height := height)
      (rhoInner := rhoInner) (rhoOuter := rhoOuter) (t := t)
      (sigma := sigma) (K := K) (W := W) (C := C)
      (Bcut := Bcut) (Gs := Gs) (X₀ := X₀) (Xc := Xc)
      (Eh := Eh S) (Gfac := Gfac) hS hinner hlt ht hC.le hBcut
      (Real.sqrt_nonneg _) (cubeLpNorm_nonneg S 2 wS.toFun)
      (cubeLpNorm_nonneg S 2 (cubeFluctuation S wS.toFun))
      (cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn S
        (publicCoeffField S (aCutoffFamily M L omega)) h.grad
      (publicCoeffField_isEllipticFieldOn_cubeSet S (aCutoffFamily M L omega)))
      hGfac
    dsimp only at hraw
    have hpairEq : cubeAverage S
        (boundaryCorrectedFluxCutoffPairingDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
          wS.toFun (restrictForcedCubeSolutionToDescendant u hS).toH1.grad g₀) =
        cubeAverage S
          (boundaryCorrectedFluxCutoffPairingDensity
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta
            (fun y ↦ u.toH1.toFun y - h.toFun y) u.toH1.grad g₀) := by
      simp only [wS, uH, hSfun, H1Function.sub_toFun,
        H1Function.restrictToOpenSubcube_toFun,
        restrictForcedCubeSolutionToDescendant_grad]
    rw [hpairEq] at hraw
    have hquarterEq : cubeAverage S
        (coefficientEnergyDensity
          (publicCoeffField S (aCutoffFamily M L omega)) u.toH1.grad) =
        cubeAverage S (fun x ↦
          SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (u.toH1.grad x)) := by
      apply cubeAverage_eq_of_ae_eq_on_cubeSet
      have hae := publicCoeffField_ae_eq_cubeSet S (aCutoffFamily M L omega)
      filter_upwards [hae] with x hx
      rw [coefficientEnergyDensity, hx]
      change vecDot (u.toH1.grad x)
          (matVecMul (symmPart
            (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) x))
            (u.toH1.grad x)) = _
      simp only [scalarCoeffField]
      rw [Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
        vecDot_smul_right]
      rfl
    simp only [H1Function.sub_toFun,
      H1Function.restrictToOpenSubcube_toFun,
      H1Function.restrictToOpenSubcube_grad] at hraw
    dsimp only [X₀, Xc, uH, hSfun, wS, Gfac, Gsemi, Af, Bf, t, W, P,
      height, Gs, Bcut, Gcut, Hcut] at hmono
    simp only [H1Function.sub_toFun,
      H1Function.restrictToOpenSubcube_toFun] at hmono
    change _ ≤ remainder S at hmono
    rw [hquarterEq] at hraw
    exact hraw.trans (by linarith only [hmono])
  · simpa only [remainder] using
      descendantsAverage_boundaryCommonYoungRemainder_le_weighted Q k
      (fun y ↦ u.toH1.toFun y - h.toFun y) (fun x ↦ -g₀ x) Eh
      hinner hlt hs hs4 hsigma hC.le hu hreg hFL2
      (fun S hS ↦ cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn S
        (publicCoeffField S (aCutoffFamily M L omega)) h.grad
        (publicCoeffField_isEllipticFieldOn_cubeSet S (aCutoffFamily M L omega)))
      hEhavg



theorem descendantsAverage_boundaryCanonicalAdaptiveRemainder_le_gapPower
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k r : ℕ}
    {rhoInner rhoOuter s sigma K C B parentBudget : ℝ}
    (remainder : TriadicCube d → ℝ)
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (havg : descendantsAverage Q (k + 1) remainder ≤ parentBudget)
    (hfactor :
      let t := s / 3
      let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
      let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter
        t sigma K W C
      parentBudget ≤ B *
        (boundaryFiniteHeightHeadGlobalCoeff t
          (Nat.ceil (boundaryFiniteHeightOfPrefactor t P)) ^ 2 * W ^ r)) :
    descendantsAverage Q (k + 1) remainder ≤
      (B * (18 * s⁻¹ *
        (16 * boundaryActiveCellGapConstant d (s / 3) K C C
          (fullVectorPoincareCubeConstant (originCube d 0) *
            (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
        (243 : ℝ) ^ (r + 1))) *
          Real.rpow (rhoOuter - rhoInner) (-(r + 1 : ℕ) : ℝ) := by
  apply descendantsAverage_boundaryCommonHeadRemainder_le_gapPower
    remainder hS hinner hlt hchoice hs hs4 hsigma hK hC hB
  exact havg.trans hfactor



theorem descendantsAverage_boundaryCanonicalAdaptiveRemainder_mul_cutoffLoss_le_gapPower
    {d : ℕ} [NeZero d] {Q S : TriadicCube d} {k r : ℕ}
    {rhoInner rhoOuter s sigma K C B parentBudget : ℝ}
    (remainder : TriadicCube d → ℝ)
    (hS : S ∈ descendantsAtDepth Q (k + 1))
    (hinner : 0 < rhoInner) (hlt : rhoInner < rhoOuter)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k rhoInner rhoOuter)
    (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (havg : descendantsAverage Q (k + 1) remainder ≤ parentBudget)
    (hfactor :
      let t := s / 3
      let W := Real.rpow (3 : ℝ) (2 * (s / 6) * ((k + 1 : ℕ) : ℝ))
      let P := boundaryCommonTailPrefactor Q k rhoInner rhoOuter
        t sigma K W C
      let Bcut :=
        2 * coarseCaccioppoliLocalPatchCutoffHessianBound Q rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter) +
          2 * (coarseCaccioppoliLocalPatchCutoffGradientBound Q rhoInner
            (coarseCaccioppoliBufferedCutoffRadius rhoInner rhoOuter)) ^ 2
      parentBudget ≤ B *
        ((boundaryFiniteHeightHeadGlobalCoeff t
            (Nat.ceil (boundaryFiniteHeightOfPrefactor t P)) ^ 2 * W ^ r) *
          (cubeScaleFactor Q ^ 2 * Bcut))) :
    descendantsAverage Q (k + 1) remainder ≤
      (B * ((288 * (quantitativeCubeCutoffHessianConst d +
          quantitativeCubeCutoffGradientConst d ^ 2)) *
        (18 * s⁻¹ *
          (16 * boundaryActiveCellGapConstant d (s / 3) K C C
            (fullVectorPoincareCubeConstant (originCube d 0) *
              (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
          (243 : ℝ) ^ (r + 1)))) *
        Real.rpow (rhoOuter - rhoInner) (-((r + 1 : ℕ) : ℝ) - 2) := by
  have hgap :=
    boundaryCommonFiniteHeightHead_mul_weight_pow_mul_cutoffLoss_le_gapPower
      (Q := Q) (S := S) (r := r) hS hinner hlt hchoice
        hs hs4 hsigma hK hC
  have hscaled := mul_le_mul_of_nonneg_left hgap hB
  dsimp only at hfactor hscaled
  exact havg.trans (hfactor.trans (by
    simpa only [mul_assoc] using hscaled))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
