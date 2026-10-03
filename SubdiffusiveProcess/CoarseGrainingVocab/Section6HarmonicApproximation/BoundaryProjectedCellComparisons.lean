module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCommonGapBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ProjectedDirichletEnergy

@[expose] public section

/-!
# Projected-cell comparison budgets

This module prices the same-boundary Dirichlet comparison datum before the
physical-carrier radius recurrence is aggregated.  The datum is the same-
boundary Dirichlet comparison constructed on the projected cube, so its
coefficient energy is controlled by the Chapter 3 energy consequence rather
than by a pointwise upper bound for the coefficient.

PROVENANCE: this is the same-boundary comparison-energy step in
`Algsuperdiff/Section4/Provider/ExcessDecay/CoarseDirichletEnergy.lean` and
`CoarseDatumPricing.lean`, specialized to the GMC projected-window prices.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The projected same-boundary comparison energy is bounded by the square of
the two transported Chapter 3 datum prices.  In particular the affine mean
enters through the normalized upper multiscale ellipticity cap, not through a
pointwise coefficient envelope. -/
theorem exists_projectedComparisonEnergy_le_windowPrices_sq
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (c : Vec d) (U : Set (Vec d))
        (sOrder : FractionalOrder) (D : ℝ)
        (A : CoeffFamily d) (sigma K : ℝ)
        (g g0 hgrad : Vec d → Vec d)
        (h0 : H1Function (openCubeSet Q))
        (v : DirichletForcedCubeSolution Q A (fun x ↦ -g0 x)),
        0 < sigma → 0 ≤ K →
        sigma⁻¹ * Ch02.LambdaSq Q (sOrder.1 / 6) (.finite 2) A ≤ K →
        sigma * (Ch02.lambdaSq Q (sOrder.1 / 6) (.finite 2) A)⁻¹ ≤ K →
        ForceBesovRegularity Q sOrder.1 (fun x ↦ -g0 x) →
        ForceBesovRegularity Q sOrder.1
          (dirichletBoundaryGradientField v) →
        Ch03.ABK26.MemCubeEuclideanFullWsp
          Q sOrder FiniteLpExponent.two (fun x ↦ g (x + c)) →
        (∀ x, g0 x = g (x + c)) →
        v.boundaryData = h0 →
        (∀ x, h0.grad x = hgrad (x + c)) →
        Ch03.ABK26.MemCubeEuclideanFullWsp
          Q sOrder FiniteLpExponent.two (fun x ↦ hgrad (x + c)) →
        translateSet c (openCubeSet Q) ⊆ U →
        MeasurableSet U → 0 < volume U → volume U ≠ ⊤ →
        0 < (volume (translateSet c (openCubeSet Q))).toReal →
        (∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ D) →
        MemLp (fun x ↦ HilbertVec.ofVec (hgrad x)) 2
          (volume.restrict U) →
        fractionalSeminormOn U sOrder.1 g ≠ ⊤ →
        fractionalSeminormOn U sOrder.1 hgrad ≠ ⊤ →
        cubeAverage Q (coefficientEnergyDensity (publicCoeffField Q A)
            v.toH1.grad) ≤
          (C * Real.rpow sOrder.1 (-(3 / 2 : ℝ)) *
                (Real.sqrt K * Real.sqrt sigma⁻¹) *
                  projectedForcePrice Q c U sOrder.1 g +
            C * Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
                (Real.sqrt K * Real.sqrt sigma) *
                  projectedBoundaryPrice Q c U sOrder.1 D hgrad) ^ 2 := by
  obtain ⟨C, hC, henergy⟩ :=
    exists_localizedCoeffEnergyValue_openCubeSet_le_dirichletEnergyWithRHSRHS_sq d
  refine ⟨C, hC, ?_⟩
  intro Q c U sOrder D A sigma K g g0 hgrad h0 v hsigma hK hupper hlower
    hgReg hhReg hgLocal hg0 hv hh0 hhLocal hsub hUmeas hU0 hUtop hPpos
    hdiam hhU hgUfin hhUfin
  have hparent := henergy v sOrder.2.1 sOrder.2.2 hgReg hhReg
  have hprice := dirichletEnergyWithRHSRHS_projected_le_windowPrices
    Q c U sOrder D A sigma K C g g0 hgrad h0 v hC.le hsigma hK hupper
      hlower hgReg hhReg hgLocal hg0 hv hh0 hhLocal hsub hUmeas hU0 hUtop
      hPpos hdiam hhU hgUfin hhUfin
  have hD0 : 0 ≤ dirichletEnergyWithRHSRHS C Q A sOrder.1
      (fun x ↦ -g0 x) v := by
    have hg0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q
        sOrder.1 (fun x ↦ -g0 x) :=
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        hgReg
    have hh0 : 0 ≤ scaleNormalizedPositiveBesovVectorNormTwo Q sOrder.1
        (dirichletBoundaryGradientField v) := by
      rw [scaleNormalizedPositiveBesovVectorNormTwo]
      exact add_nonneg (Real.sqrt_nonneg _)
        (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
          hhReg)
    rw [dirichletEnergyWithRHSRHS, poincareLowerEllipticityFactor,
      poincareUpperEllipticityFactor]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hC.le (Real.rpow_nonneg sOrder.2.1.le _))
          (Real.rpow_nonneg
            (Ch02.lambdaSq_finite_nonneg Q A (by linarith [sOrder.2.1])
              (by norm_num)) _))
        hg0)
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hC.le (Real.rpow_nonneg sOrder.2.1.le _))
          (Real.rpow_nonneg
            (Ch02.LambdaSq_finite_nonneg Q A sOrder.2.1 (by norm_num)) _))
        hh0)
  have hsq := pow_le_pow_left₀ hD0 hprice 2
  rw [cubeAverage_coefficientEnergyDensity_publicCoeffField_eq_localizedCoeffEnergyValue]
  exact hparent.trans hsq

/-- Collapse the projected comparison-energy square into separately priced
force and boundary budgets.  This is the scalar `BE ≤ H` interface consumed
by the four-budget profile; no sign assumption on the two prices is needed. -/
theorem projectedComparisonEnergy_le_two_mul_add_of_price_sq_caps
    {BE forcePrice boundaryPrice forceBudget boundaryBudget : ℝ}
    (hBE : BE ≤ (forcePrice + boundaryPrice) ^ 2)
    (hforce : forcePrice ^ 2 ≤ forceBudget)
    (hboundary : boundaryPrice ^ 2 ≤ boundaryBudget) :
    BE ≤ 2 * (forceBudget + boundaryBudget) := by
  calc
    BE ≤ (forcePrice + boundaryPrice) ^ 2 := hBE
    _ ≤ 2 * (forcePrice ^ 2 + boundaryPrice ^ 2) := by
      nlinarith [sq_nonneg (forcePrice - boundaryPrice)]
    _ ≤ 2 * (forceBudget + boundaryBudget) := by
      linarith



noncomputable def projectedPhysicalGapBudgetCap
    (d : ℕ) [NeZero d] (Q : TriadicCube d)
    (s sigma K C U G L : ℝ) : ℝ :=
  let t := s / 3
  let Gs := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (t - 1)))⁻¹)
  let Hdim := fullVectorPoincareCubeConstant (originCube d 0) *
    (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)
  let Dactive := boundaryActiveCellGapConstant d t K C C Hdim
  let a2 := C ^ 2 * t⁻¹ ^ 2 * K * sigma
  let af2 := C ^ 2 * Real.rpow t (-(5 / 2 : ℝ)) ^ 2 * K ^ 2
  let mm2 := 2 * Dactive ^ 2 / (C ^ 2 * a2)
  let au2 := (4 * (d : ℝ) ^ 2 + 8 * Gs ^ 2) *
    (cubeScaleFactor Q)⁻¹ ^ 2
  let bu2 := 8 * (cubeScaleFactor Q)⁻¹ ^ 2
  let bf2 := boundaryNegativeToL2Factor (2 * t) ^ 2
  (((4 * C ^ 2 * a2 + sigma / 2) *
        ((4 * au2 + 16 * bu2) * U ^ 2) +
      (8 * C ^ 2 * mm2 + C ^ 2 / (2 * sigma)) *
        (2 * af2 * G ^ 2 + 2 * bf2 * L ^ 2)) *
    (((243 : ℝ) ^ 3 +
        18 * s⁻¹ *
          (16 * boundaryActiveCellGapConstant d (s / 3) K C C
            (fullVectorPoincareCubeConstant (originCube d 0) *
              (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
          (243 : ℝ) ^ 4) *
      (1 + 288 * (quantitativeCubeCutoffHessianConst d +
        quantitativeCubeCutoffGradientConst d ^ 2)) ^ 2))

/-- Componentwise projected-cell comparison for the physical common-gap
carrier.  This is the literal `X ≤ P` seam: its only analytic inputs are the
local `L²`, positive-Besov, and Euclidean-`L²` prices. -/
theorem boundaryCommonGapPowerBudget_zero_le_projectedPhysicalGapBudgetCap
    (d : ℕ) [NeZero d] (Q : TriadicCube d)
    {s sigma K C U G L : ℝ} (u : Vec d → ℝ) (F : Vec d → Vec d)
    (hs : 0 < s) (hsigma : 0 < sigma) (hK : 0 < K) (hC : 0 < C)
    (hFreg : ForceBesovRegularity Q (s / 3) F)
    (hU : cubeLpNorm Q 2 u ≤ U)
    (hG : scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) F ≤ G)
    (hL : boundaryNormalizedEuclideanL2 Q F ≤ L) :
    boundaryCommonGapPowerBudget Q s sigma K C 0 u F ≤
      projectedPhysicalGapBudgetCap d Q s sigma K C U G L := by
  have hu0 : 0 ≤ cubeLpNorm Q 2 u := cubeLpNorm_nonneg Q 2 u
  have hsemi0 : 0 ≤ scaleNormalizedPositiveBesovVectorSeminormTwo Q (s / 3) F :=
    scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      hFreg
  have hL0 : 0 ≤ boundaryNormalizedEuclideanL2 Q F :=
    boundaryNormalizedEuclideanL2_nonneg Q F
  have hUsq := pow_le_pow_left₀ hu0 hU 2
  have hGsq := pow_le_pow_left₀ hsemi0 hG 2
  have hLsq := pow_le_pow_left₀ hL0 hL 2
  have ht : 0 < s / 3 := by positivity
  have hactive : 0 ≤ boundaryActiveCellGapConstant d (s / 3) K C C
      (fullVectorPoincareCubeConstant (originCube d 0) *
        (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ)) :=
    zero_le_one.trans (boundaryActiveCellGapConstant_one_le d (s / 3) K C C _)
  have hglobal : 0 ≤
      (((243 : ℝ) ^ 3 +
          18 * s⁻¹ *
            (16 * boundaryActiveCellGapConstant d (s / 3) K C C
              (fullVectorPoincareCubeConstant (originCube d 0) *
                (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) *
            (243 : ℝ) ^ 4) *
        (1 + 288 * (quantitativeCubeCutoffHessianConst d +
          quantitativeCubeCutoffGradientConst d ^ 2)) ^ 2) := by
    have hhess := quantitativeCubeCutoffHessianConst_nonneg d
    have hgrad := quantitativeCubeCutoffGradientConst_nonneg d
    positivity
  unfold boundaryCommonGapPowerBudget projectedPhysicalGapBudgetCap
  dsimp only [boundaryCommonRadiusIndependentBudget]
  apply mul_le_mul_of_nonneg_right _ hglobal
  have hGs : 0 ≤ Real.sqrt
      ((1 - Real.rpow (3 : ℝ) (2 * (s / 3 - 1)))⁻¹) := Real.sqrt_nonneg _
  have ha2 : 0 < C ^ 2 * (s / 3)⁻¹ ^ 2 * K * sigma := by positivity
  have haf2 : 0 ≤ C ^ 2 * Real.rpow (s / 3) (-(5 / 2 : ℝ)) ^ 2 * K ^ 2 := by
    positivity
  have hmm2 : 0 ≤ 2 *
      (boundaryActiveCellGapConstant d (s / 3) K C C
        (fullVectorPoincareCubeConstant (originCube d 0) *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) ^ 2 /
      (C ^ 2 * (C ^ 2 * (s / 3)⁻¹ ^ 2 * K * sigma)) := by positivity
  have hau2 : 0 ≤
      (4 * (d : ℝ) ^ 2 + 8 *
        (Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s / 3 - 1)))⁻¹)) ^ 2) *
          (cubeScaleFactor Q)⁻¹ ^ 2 := by
    positivity
  have hbu2 : 0 ≤ 8 * (cubeScaleFactor Q)⁻¹ ^ 2 := by positivity
  have hbf2 : 0 ≤ boundaryNegativeToL2Factor (2 * (s / 3)) ^ 2 := sq_nonneg _
  have hfirst : 0 ≤ 4 * C ^ 2 *
        (C ^ 2 * (s / 3)⁻¹ ^ 2 * K * sigma) + sigma / 2 := by positivity
  have hsecond : 0 ≤ 8 * C ^ 2 *
        (2 * (boundaryActiveCellGapConstant d (s / 3) K C C
          (fullVectorPoincareCubeConstant (originCube d 0) *
            (3 : ℝ) ^ ((d : ℝ) + 1) * (Fintype.card (Fin d) : ℝ))) ^ 2 /
          (C ^ 2 * (C ^ 2 * (s / 3)⁻¹ ^ 2 * K * sigma))) +
      C ^ 2 / (2 * sigma) := by positivity
  simp only [mul_zero, zero_add]
  gcongr

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
