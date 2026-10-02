import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.DirichletEnergyPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ProjectedDatumPrice

/-!
# Dirichlet-energy price for a projected boundary cell

This is the exact composition seam between the transported datum readouts and
the Chapter-3 scalar Dirichlet-energy estimate.  Geometry remains explicit so
the subsequent fixed-cover module can instantiate it cell by cell.

PROVENANCE: mirrors `Algsuperdiff/Section4/Provider/ExcessDecay/
CoarseDirichletEnergy.lean` followed by `CoarseDatumPricing.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- The unsigned source price on one projected cube. -/
noncomputable def projectedForcePrice (Q : TriadicCube d) (c : Vec d)
    (U : Set (Vec d)) (s : ℝ) (g : Vec d → Vec d) : ℝ :=
  caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s) Q *
    (Real.rpow s (-(1 / 2 : ℝ)) *
      (Real.sqrt ((volume U).toReal /
          (volume (translateSet c (openCubeSet Q))).toReal) *
        (fractionalSeminormOn U s g).toReal))

/-- The full boundary-gradient price on one projected cube. -/
noncomputable def projectedBoundaryPrice (Q : TriadicCube d) (c : Vec d)
    (U : Set (Vec d)) (s D : ℝ) (hgrad : Vec d → Vec d) : ℝ :=
  Real.sqrt ((volume U).toReal /
      (volume (translateSet c (openCubeSet Q))).toReal) *
    (D ^ (s + (d : ℝ) / 2) * s ^ (-(1 / 2 : ℝ)) *
      (volume U).toReal ^ (-(1 / 2 : ℝ)) *
        (fractionalSeminormOn U s hgrad).toReal) +
  euclideanNorm (averageVecOn U hgrad) +
  caccioppoliExactDatumConstant d * cubeBesovScaleWeight (-s) Q *
    (Real.rpow s (-(1 / 2 : ℝ)) *
      (Real.sqrt ((volume U).toReal /
          (volume (translateSet c (openCubeSet Q))).toReal) *
        (fractionalSeminormOn U s hgrad).toReal))

/-- The rough Dirichlet lift on a projected cell is bounded entirely by the
ambient source and boundary-gradient prices.  The local-control hypothesis is
needed only at the single `s/6` finite-`2` slot. -/
theorem dirichletEnergyWithRHSRHS_projected_le_windowPrices
    (Q : TriadicCube d) (c : Vec d) (U : Set (Vec d))
    (sOrder : FractionalOrder) (D : ℝ)
    (A : CoeffFamily d) (sigma K C : ℝ)
    (g g0 hgrad : Vec d → Vec d)
    (h0 : H1Function (openCubeSet Q))
    (v : DirichletForcedCubeSolution Q A (fun x => -g0 x))
    (hC : 0 ≤ C) (hsigma : 0 < sigma) (hK : 0 ≤ K)
    (hupper6 : sigma⁻¹ * Ch02.LambdaSq Q (sOrder.1 / 6) (.finite 2) A ≤ K)
    (hlower6 : sigma * (Ch02.lambdaSq Q (sOrder.1 / 6) (.finite 2) A)⁻¹ ≤ K)
    (hgReg : ForceBesovRegularity Q sOrder.1 (fun x => -g0 x))
    (hhReg : ForceBesovRegularity Q sOrder.1
      (dirichletBoundaryGradientField v))
    (hgLocal : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q sOrder FiniteLpExponent.two (fun x => g (x + c)))
    (hg0 : ∀ x, g0 x = g (x + c))
    (hv : v.boundaryData = h0)
    (hh0 : ∀ x, h0.grad x = hgrad (x + c))
    (hhLocal : Ch03.ABK26.MemCubeEuclideanFullWsp
      Q sOrder FiniteLpExponent.two (fun x => hgrad (x + c)))
    (hsub : translateSet c (openCubeSet Q) ⊆ U)
    (hUmeas : MeasurableSet U)
    (hU0 : 0 < volume U) (hUtop : volume U ≠ ∞)
    (hPpos : 0 < (volume (translateSet c (openCubeSet Q))).toReal)
    (hdiam : ∀ x ∈ U, ∀ y ∈ U, euclideanNorm (x - y) ≤ D)
    (hhU : MemLp (fun x => HilbertVec.ofVec (hgrad x)) 2
      (volume.restrict U))
    (hgUfin : fractionalSeminormOn U sOrder.1 g ≠ ∞)
    (hhUfin : fractionalSeminormOn U sOrder.1 hgrad ≠ ∞) :
    dirichletEnergyWithRHSRHS C Q A sOrder.1 (fun x => -g0 x) v ≤
      C * Real.rpow sOrder.1 (-(3 / 2 : ℝ)) *
          (Real.sqrt K * Real.sqrt sigma⁻¹) *
            projectedForcePrice Q c U sOrder.1 g +
        C * Real.rpow sOrder.1 (-(1 / 2 : ℝ)) *
          (Real.sqrt K * Real.sqrt sigma) *
            projectedBoundaryPrice Q c U sOrder.1 D hgrad := by
  have hcaps := datumEllipticityCaps_of_sixth Q A sOrder.2.1 hsigma hupper6 hlower6
  have hPpair := ENNReal.toReal_ne_zero.mp hPpos.ne'
  have hG := projectedForceSeminorm_le_window Q c U sOrder g g0 hgLocal hg0
    hsub hPpair.1 hPpair.2 hU0.ne' hUtop hgUfin
  have hH := projectedBoundaryNorm_le_window Q c U sOrder D hgrad h0 A
    (fun x => -g0 x) v hv hh0 hhLocal hsub hUmeas hU0 hUtop hPpos hdiam
    hhU hhUfin
  exact dirichletEnergyWithRHSRHS_le_of_datum_caps v hC sOrder.2.1 hsigma hK
    hcaps.1 hcaps.2 hgReg hG hhReg hH

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
