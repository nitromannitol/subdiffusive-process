module

public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ExponentComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryResidualEighth
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryLocalizedHalfSteps
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryLocalizedEighth
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryLocalizedSignedEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCombinedSignedFiniteHeight
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCombinedSignedRadiusEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryComparatorParentPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalCarrierAggregation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalCarrierForceBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProjectedCellComparisons
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProjectedCellProfile
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationRestriction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ForcedReplacement
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FullWspTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.GoodEventErrorCap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalComparisonDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.LocalPDEEnergyAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoverAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDNormalization
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDSeparateDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDProjected
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDGoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryASDParentMean
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryPhysicalResidualMean
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryResidualWindowEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryResidualWindowCore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.NegativeNormToL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.OffGridFrame
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorGoodEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorErrorLoop
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorBudgetReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryComparatorErrorReplacement
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorSharpErrorLoop
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryComparatorSharpErrorReplacement
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProjectedComponentAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SummedCoverReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.AdjustableRadiusReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SlabRecurrenceAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.PhysicalRadiusRecurrence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.SignedSlabPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.ComparisonDatumRetained
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySharpLoopApplication
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryWeightedEnergySlot
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryProjectedFeedbackRecurrence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowBoundaryCellPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.StepRowWindowStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.ConclusionAssembly

@[expose] public section

/-!
# Harmonic approximation on good scales

This provider exposes the completed well-posedness block of the
author-stated v5 statement, the local source-sign comparison datum, and the
translated-error, good-event-cap, exponent-comparison, and negative-norm
layers.  The quantitative estimate is not declared under the frozen export
name until the projected-cover Caccioppoli assembly is complete.

The harmonic replacement is constructed before applying the coarse-graining and energy estimates.
-/

namespace SubdiffusiveProcess.Providers.Section6

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

/-- Exact algebraic seam which places the gap-weighted projected feedback in
the contraction slot of the proved eighth-power half-step recurrence. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedFeedbackRecurrence :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.budgetedRadiusRecurrence_of_projectedHalfStepFeedback

/-- Exact conversion of an admissible physical four-budget radius recurrence
to the weighted-energy slot consumed by the boundary sharp loop. -/
noncomputable abbrev harmonicApproximationGoodScales_boundaryWeightedEnergySlot :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_boundaryWeightedEnergySlot_of_physicalRecurrence

/-- Datum-retaining sharp-loop application, factored at the single weighted
energy input supplied by the boundary ASD/radius argument. -/
noncomputable abbrev harmonicApproximationGoodScales_boundarySharpLoop :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_boundaryHarmonicComparison_le_sharpLoopBound_of_weightedEnergy



noncomputable abbrev harmonicApproximationGoodScales_boundaryPowerHandoff :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.indicator_innerComparison_le_of_sharpLoopPower_two

/-- The localized forced/scalar-forced comparison package with the physical
value and gradient identities retained for clause (C). -/
noncomputable abbrev harmonicApproximationGoodScales_localComparisonDataRetained :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_localSourceComparisonDatum_of_dirichlet_retained

/-- The frozen pointwise boundary relation converted to the physical `H¹₀`
carrier required by the sharp coarse-graining comparison. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalTraceCarrier :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.memH10_sub_physical_of_hasZeroTraceDifferenceOn

/-- Restriction of the physical comparison norm from the translated parent
cube to the frozen inner truncated window. -/
noncomputable abbrev harmonicApproximationGoodScales_innerComparisonRestriction :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.normalizedL2On_sub_physical_le_of_subset

/-- Final event split for the comparison clause. -/
noncomputable abbrev harmonicApproximationGoodScales_indicatorComparison :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.indicatorValue_le_of_mem_imp

/-- The source-exact separate-datum ASD row, including its boundary-mean
normalization. -/
noncomputable abbrev harmonicApproximationGoodScales_boundaryASDSeparateDatum
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_boundary_caccioppoli_quarter_with_datum
    d

/-- The separate-datum ASD row after transport to the well-placed projected
boundary cube. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedBoundaryASD
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_projectedBoundaryCellASD
    d

/-- The projected separate-datum ASD row at the manuscript's boundary
pricing slot `(1/2,s/3)`. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedBoundaryASDThird
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_projectedBoundaryCellASD_third
    d

/-- The projected separate-datum ASD row after the amplitude-one good event
prices its Caccioppoli prefactor and all local ellipticity coefficients. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedBoundaryASDGoodEventPrices
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_projectedBoundaryCellASD_goodEventPrices
    d

/-- Exact parent-mean reconciliation for the source-normalized ASD row.  It
identifies the remaining scalar as the physical mean of `u - h`; no
error-dependent comparison is inserted. -/
noncomputable abbrev harmonicApproximationGoodScales_boundaryASDParentMean :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.normalizedL2SqOnSet_sub_datumAverage_eq_centered_add_residualMean

/-- The physical residual mean reduced, by the ambient zero trace, to the
residual-gradient norm on the next boundary window. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalResidualMean :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.physicalResidualMean_weighted_le_boundaryWindowGradient

/-- The physical residual mean after inserting the literal scalar coefficient
energy.  The pointwise inverse-ratio hypothesis is kept visible: the remaining
printed-route input is a boundary-window energy estimate, not another scalar
mean comparison. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalResidualMeanCoeffEnergy :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.physicalResidualMean_weighted_le_boundaryWindowCoeffEnergy

/-- The preceding coefficient-energy reduction with its inverse-ratio premise
discharged by the actual Section 6 good event. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalResidualMeanCoeffEnergyGoodEvent :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.physicalResidualMean_weighted_le_boundaryWindowCoeffEnergy_of_goodEvent

/-- The good-event reduction after the residual coefficient energy is split
into its physical solution and datum components. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalResidualMeanSolutionDatumEnergy :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.physicalResidualMean_weighted_le_boundaryWindowSolutionDatumEnergy_of_goodEvent

/-- Source-exact scalar normalization for the separate-datum ASD boundary
row.  This discharges the mean defect when the datum average is the scalar
subtracted from the parent solution, as required. -/
noncomputable abbrev harmonicApproximationGoodScales_boundaryASDNormalization :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_of_boundaryMean_eq

private noncomputable def forcingWspFieldOfFullMembership {d : ℕ}
    {Q : Homogenization.TriadicCube d} {s : FractionalOrder} {g : Vec d → Vec d}
    (hg : Book.Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two g) :
    CubeEuclideanWspField Q s FiniteLpExponent.two where
  toField := g
  euclideanMemLp := hg.1
  euclideanMemWsp := hg.2

@[simp] private theorem forcingWspFieldOfFullMembership_toField {d : ℕ}
    {Q : Homogenization.TriadicCube d} {s : FractionalOrder} {g : Vec d → Vec d}
    (hg : Book.Ch03.ABK26.MemCubeEuclideanFullWsp
      Q s FiniteLpExponent.two g) :
    (forcingWspFieldOfFullMembership hg).toField = g :=
  rfl

/-- Clause (A) of `l.harmonic.approximation.good.scales.GMC`: existence of the
constant-coefficient harmonic replacement and a.e. uniqueness of both its
value and weak gradient. -/
theorem harmonicApproximationGoodScales_wellPosed
    (d : ℕ) [NeZero d] (n : ℕ) (y : Vec d)
    (uD : H1Function (translatedCube d (n - 2) y)) :
    (∃ v : H1Function (translatedCube d (n - 2) y),
      IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
        HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
    ∀ v v' : H1Function (translatedCube d (n - 2) y),
      (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
          HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
      (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
          HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
      v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
        v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad := by
  refine ⟨exists_isWeaklyHarmonicOn_one_translatedCube (n - 2) y uD, ?_⟩
  intro v v' hv hv'
  exact ae_eq_of_isWeaklyHarmonicOn_one_translatedCube (n - 2) y
    hv.1 hv.2 hv'.1 hv'.2

/-- The v5 inhomogeneous force hypothesis and the anchor's local geometry
discharge every PDE-side premise of finite-`p` coarse graining on
`y + cube_(n-2)`.  The scalar comparator is the manuscript's literal
`(b_(L,n+2))_(z+cube_(n+2))`. -/
theorem harmonicApproximationGoodScales_localComparisonData
    (d : ℕ) [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m n : ℕ)
    (z y x : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (sOrder : FractionalOrder)
    (u h : H1Function (openCubeSet (originCube d (m : ℤ))))
    (g : Vec d → Vec d)
    (hdir : IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
      (originCube d (m : ℤ)) u h g)
    (hg : Book.Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g)
    (hlocal : translatedCube d ((n : ℤ) - 2) y ⊆
      truncatedCube d (m : ℤ) ((n : ℤ) - 1) x) :
    ∃ g0 : Vec d → Vec d,
      Book.Ch03.ABK26.MemCubeEuclideanFullWsp
        (originCube d ((n : ℤ) - 2)) sOrder FiniteLpExponent.two g0 ∧
      ∃ u0 v0 : H1Function (openCubeSet (originCube d ((n : ℤ) - 2))),
        Book.Ch03.ABK26.IsForcedEquation (originCube d ((n : ℤ) - 2))
          ((aCutoffFamily M L (translatePotentialSample y omega)).coeffOn
            (originCube d ((n : ℤ) - 2))) u0 g0 ∧
        Book.Ch03.ABK26.IsScalarForcedEquation (originCube d ((n : ℤ) - 2))
          (tailAverage M L (n + 2) omega (translatedCube d ((n : ℤ) + 2) z)) v0 g0 ∧
        Book.Ch03.ABK26.HasH10Difference (originCube d ((n : ℤ) - 2)) u0 v0 := by
  have hsub : translatedCube d ((n : ℤ) - 2) y ⊆
      openCubeSet (originCube d (m : ℤ)) := by
    intro q hq
    exact (hlocal hq).2
  have hsigma : 0 < tailAverage M L (n + 2) omega
      (translatedCube d ((n : ℤ) + 2) z) := by
    rw [show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega]
    rw [← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z omega)
  exact Section6HarmonicApproximation.exists_localSourceComparisonDatum_of_dirichlet
    M L omega m ((n : ℤ) - 2) y sOrder u h g hdir hg hsub _ hsigma



theorem harmonicApproximationGoodScales_boundaryResidualEighth
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (Q R : Homogenization.TriadicCube d) (center : Vec d)
    {rho₀ rho₁ rho₂ rho₃ B₀ B₁ B₂ : ℝ}
    (u uRes v : H1Function (openCubeSet Q))
    (hgrad : ∀ x, u.grad x = uRes.grad x + v.grad x)
    (h₀ :
      Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile Q R center rho₀
          (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 2 : ℝ) *
          Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile Q R center rho₁
            (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) + B₀)
    (h₁ :
      Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile Q R center rho₁
          (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 2 : ℝ) *
          Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile Q R center rho₂
            (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) + B₁)
    (h₂ :
      Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile Q R center rho₂
          (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
            vecNormSq (uRes.grad x)) ≤
        (1 / 2 : ℝ) *
          Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile Q R center rho₃
            (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
              vecNormSq (uRes.grad x)) + B₂) :
    Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile Q R center rho₀
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) ≤
      (1 / 2 : ℝ) *
          Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile Q R center rho₃
            (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * vecNormSq (u.grad x)) +
        (5 / 2 : ℝ) * Homogenization.Book.Ch03.localizedCoeffEnergyValue
          (openCubeSet Q)
          ((aCutoffFamily M L omega).coeffOn Q) v +
        2 * (B₀ + (1 / 2 : ℝ) * B₁ + (1 / 4 : ℝ) * B₂) := by
  exact
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.boundaryCrossScaleEnergyProfile_physical_half_of_three_residual_half_steps
      M L omega Q R center u uRes v hgrad h₀ h₁ h₂

/-- Provider-side constructor for the three consecutive localized half-step
premises consumed by `harmonicApproximationGoodScales_boundaryResidualEighth`.
The shared budget is already split into low-frequency, descendant datum,
coercive datum, and forcing components. -/
noncomputable abbrev harmonicApproximationGoodScales_threeLocalizedHalfSteps
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_three_boundaryCrossScale_halfSteps_of_localizedCells
    d

/-- The three localized four-budget rows after their residual-eighth and
physical one-half composition.  This is the boundary-radius payload consumed
by the final projected-cell aggregation. -/
noncomputable abbrev harmonicApproximationGoodScales_localizedPhysicalHalfStep
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_boundaryCrossScale_physicalHalfStep_of_threeLocalizedCells
    d

/-- The localized signed weak-energy seam.  Its residual pairing has the sign
fixed by the physical weak formulation before the finite-height bound is
applied. -/
noncomputable abbrev harmonicApproximationGoodScales_signedLocalizedHalfStep :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.boundaryCrossScale_physicalHalfAbsorbable_of_signedResidualPair

/-- Exact localized affine/residual energy cancellation obtained by testing
the coefficient-harmonic lift against the localized residual competitor. -/
noncomputable abbrev harmonicApproximationGoodScales_localizedAffineEnergySplit :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.volumeAverage_localizedAffineEnergySplit_identity

/-- Young-priced form of the preceding exact cancellation. -/
noncomputable abbrev harmonicApproximationGoodScales_localizedAffineEnergySplitLe :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.volumeAverage_localizedAffineEnergySplit_le

/-- Combined signed residual/lift weak-energy premise for the localized
finite-height step. -/
noncomputable abbrev harmonicApproximationGoodScales_localizedSignedAffineResidualEnergy :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.volumeAverage_localizedSignedAffineResidualEnergy_le

/-- The combined residual/lift cutoff pairing after the common finite-height
descendant sum and weighted four-budget collapse. -/
noncomputable abbrev harmonicApproximationGoodScales_combinedSignedFiniteHeight
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_abs_combinedSignedPairing_triadicGap
    d

/-- The finite-height cap composed with the signed weak-energy identity.  It
is the coefficient-exact radius row used before the final finite-radius
iteration. -/
noncomputable abbrev harmonicApproximationGoodScales_combinedSignedRadiusStep :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.boundaryCrossScale_physical_le_of_combinedSignedPairing

/-- The preceding radius row with the finite-height premise and selected
triadic gap fully discharged. -/
noncomputable abbrev harmonicApproximationGoodScales_combinedSignedLocalizedStep
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_boundaryCrossScale_combinedSignedLocalizedStep
    d

/-- Hypothesis-free-in-radius endpoint of the combined signed boundary argument.
All canonical radii and finite-height gap choices are internal. -/
noncomputable abbrev harmonicApproximationGoodScales_combinedSignedRadiusEnergy
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_boundaryCrossScaleEnergyProfile_oneThird_le_combinedSigned
    d

/-- The affine-residual cutoff product after replacement by the physical
`u-h` finite-height carrier.  The canonical lift correction is weakly priced
before the gap power is introduced. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalCarrierReplacement
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_abs_affineResidualCombinedPairing_physicalCarrier_triadicGap
    d



noncomputable abbrev harmonicApproximationGoodScales_physicalCarrierSignedBudget :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.boundaryCrossScale_physical_le_of_combinedSignedPairingBudget

/-- The explicit physical-carrier consecutive-radius row.  Its common
finite-height contribution has already been split into a zero-datum inverse-
gap budget and one external fine-datum energy. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalCarrierLocalizedStep
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_boundaryCrossScale_physicalCarrierLocalizedStep
    d

/-- Canonical-radius iteration of the preceding literal three-quarter row. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalCarrierRadiusEnergy
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_boundaryCrossScaleEnergyProfile_oneThird_le_physicalCarrier
    d

/-- Translated-good-event specialization of the complete physical-carrier
radius endpoint. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalCarrierGoodEventPrices
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_boundaryCrossScaleEnergyProfile_oneThird_le_goodEventAt_physicalCarrier
    d

/-- Literal four-budget collection of the physical-carrier coefficients. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalCarrierAggregation :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.boundaryPhysicalCarrier_profile_le_fourBudgets



noncomputable abbrev harmonicApproximationGoodScales_physicalCarrierFourBudgetProfile :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.boundaryPhysicalCarrier_profile_le_fourBudgets_of_raw

/-- The translated positive-Besov force carrier collapsed to the printed
`s⁻¹² sigma⁻¹ 3^(2sn) [g]²` square budget. -/
noncomputable abbrev harmonicApproximationGoodScales_forceBudget :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.boundaryPhysicalCarrier_forceBudget_le

/-- Complete explicit three-quarter profile after inserting that force
budget; the affine and datum prices remain external to inverse gap powers. -/
noncomputable abbrev harmonicApproximationGoodScales_threeQuarterForceProfile :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.boundaryPhysicalCarrier_profile_le_forceBudget_of_raw

/-- The same-boundary projected comparison energy priced by the transported
source and boundary windows. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedComparisonEnergy
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_projectedComparisonEnergy_le_windowPrices_sq
    d

/-- Scalar `BE ≤ H` collection after separate projected force and boundary
prices have been squared. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedComparisonBudget :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.projectedComparisonEnergy_le_two_mul_add_of_price_sq_caps

/-- Componentwise `X ≤ P` comparison for the physical common-gap carrier. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedPhysicalGapBudget :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.boundaryCommonGapPowerBudget_zero_le_projectedPhysicalGapBudgetCap

/-- The field-changing projected profile, physical child readout, and literal
four-budget coefficient collection.  The remaining analytic inputs are only
the three displayed `BE`, force, and physical-gap caps. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedPhysicalEnergy
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_projectedBoundaryCellPhysicalEnergy_of_budgetCaps
    d

/-- Superdiffusion-style face-oddness and flat-comparator control of the
projected physical parent carrier.  Unlike the boundary-window Poincare
shortcut, this interface does not assume a local energy estimate for the
ambient zero-trace witness. -/
noncomputable abbrev harmonicApproximationGoodScales_boundaryComparatorParentPrice
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_cubeLpNorm_projected_sub_dirichletSolution_le_comparatorPrices
    d

/-- The committed flat-comparator residue run through the exact one-level
finite-`p` homogenization loop and the amplitude-one good-event response
representative.  Its only open slots are the projected weighted energy and
positive forcing budgets owned by the final Caccioppoli aggregation. -/
noncomputable abbrev harmonicApproximationGoodScales_flatComparatorGoodEvent
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_cubeLpNorm_sub_le_flatComparatorGoodEventBound
    d

/-- The physical coefficient-to-flat comparator error after the finite-`p`
homogenization readout and direct scalar-forcing comparison. -/
noncomputable abbrev harmonicApproximationGoodScales_flatComparatorErrorLoop
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop_of_forced
    d

/-- The boundary mean-control parent decomposition with its only physical
flat-comparator residue replaced by the preceding good-event error loop. -/
noncomputable abbrev harmonicApproximationGoodScales_boundaryComparatorErrorReplacement
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_cubeLpNorm_projected_sub_dirichletSolution_le_goodEventComparatorPrices
    d

/-- Finite real readout of the local finite-`p` comparator budget. -/
noncomputable abbrev harmonicApproximationGoodScales_flatComparatorBudgetReadout :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.flatComparatorLocalCoarseBound_toReal_le

/-- Complete real-valued error-loop readout, including the direct forcing
comparison. -/
noncomputable abbrev harmonicApproximationGoodScales_flatComparatorLoopReadout :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.flatComparatorGoodEventLoopBound_le_realReadout

/-- Sharp additive-dual flat-comparator loop on the manuscript corridor. -/
noncomputable abbrev harmonicApproximationGoodScales_flatComparatorSharpErrorLoop
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop_of_forced_sharp
    d



noncomputable abbrev harmonicApproximationGoodScales_translatedSharpErrorLoop
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_normalizedL2On_sub_flatComparator_le_goodEventLoop_of_forced_sharp
    d

/-- Model-facing sharp endpoint at the frozen `[NeZero d]` signature.  The
model's shell prefix supplies the library's `2 ≤ d` witness uniformly before
the model quantifier is consumed. -/
noncomputable abbrev harmonicApproximationGoodScales_flatComparatorSharpErrorLoopNeZero
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_normalizedL2On_sub_wellPlacedFlatComparator_le_goodEventLoop_of_forced_sharp_neZero
    d

/-- Its real readout, with no extra fractional-order loss in the spectral
factor. -/
noncomputable abbrev harmonicApproximationGoodScales_flatComparatorSharpLoopReadout :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.flatComparatorSharpGoodEventLoopBound_le_realReadout

/-- Boundary parent carrier after insertion of the sharp comparator loop. -/
noncomputable abbrev harmonicApproximationGoodScales_boundaryComparatorSharpErrorReplacement
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_cubeLpNorm_projected_sub_dirichletSolution_le_goodEventComparatorPrices_sharp
    d

/-- Projected physical-cell readout after assembling the three component
caps of the common-gap budget. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedComponentAssembly
    (d : ℕ) [NeZero d] :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_projectedBoundaryCellPhysicalEnergy_of_componentCaps
    d

/-- The sharp comparator parent inserted into the literal common-gap cap.
The remaining weighted-energy feedback is exposed in the `Usharp` argument,
without an implicit smallness assumption. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedSharpParentCap
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :=
  SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_boundaryCommonGapPowerBudget_le_projectedSharpParentCap
    d hd

/-- Exact `p=2` partition readout which replaces the sharp loop's abstract
weighted-energy slot by the root normalized coefficient energy. -/
noncomputable abbrev harmonicApproximationGoodScales_weightedRootEnergyReadout :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.weightedLocalSymmetricEnergyLp_two_le_rootEnergyReadout



noncomputable abbrev harmonicApproximationGoodScales_localPDEEnergyAssembly :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_translatedCube_energy_le_of_boundaryCellManuscriptBound

/-- The printed order of operations for the projected boundary cover: first
assemble the fixed `9^d` cover, then absorb the common half-energy term. -/
noncomputable abbrev harmonicApproximationGoodScales_coverFirstHalfAbsorption :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.normalizedCutoffEnergy_projectedCover_le_two_mul_of_half_absorb



noncomputable abbrev harmonicApproximationGoodScales_coverAverageHalfAbsorption :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.normalizedCutoffEnergy_projectedCover_le_two_mul_of_remainderAverage

/-- The literal four-budget constant collection after the projected cover is
summed and its boundary remainder is absorbed. -/
noncomputable abbrev harmonicApproximationGoodScales_summedCoverFourBudget :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.normalizedCutoffEnergy_projectedCover_le_two_max_mul_of_half_absorb

/-- Consumer-side endpoint for the local row: the interior branch,
fixed cover, half absorption, and exact four-budget square-root readout are
all discharged. -/
noncomputable abbrev harmonicApproximationGoodScales_summedCoverEnergyReadout :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_invSqrt_mul_translatedCubeEnergy_le_of_boundaryCellHalfAbsorb

/-- Corrected consumer for the result: an adjustable radius-pair row
is collapsed first, and only its closed energy estimate is square-rooted. -/
noncomputable abbrev harmonicApproximationGoodScales_adjustableRadiusEnergyReadout :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.invSqrt_mul_vectorNormalizedL2On_le_of_radiusPairFourBudgets

/-- Direct term-level specialization of `BudgetedRadiusRecurrence`/`budgetedRadius_iteration` interface.  This is the
live replacement for the refuted fixed-cover `hremainder` route. -/
noncomputable abbrev harmonicApproximationGoodScales_budgetedRadiusCollapse :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.radiusProfile_oneThird_le_of_budgetedQuarterStep

/-- Free-parameter consumer: collapse an arbitrary admissible
budgeted radius row, collect its constants, and perform the exact manuscript
four-budget square-root readout. -/
noncomputable abbrev harmonicApproximationGoodScales_budgetedRadiusEnergyReadout :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.invSqrt_mul_vectorNormalizedL2On_le_of_budgetedRadiusFourBudgets

/-- The slab-Poincare/mean-split algebra which turns a concrete adjustable
boundary row into budgeted recurrence. -/
noncomputable abbrev harmonicApproximationGoodScales_slabRecurrenceAssembly :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.budgetedRadiusRecurrence_of_slabMeanRows

/-- Physical zero-extension variant of the slab recurrence assembly.  The
datum-gradient energy produced by `grad (u - h)` remains an additive budget. -/
noncomputable abbrev harmonicApproximationGoodScales_slabRecurrenceAssemblyWithDatum :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.budgetedRadiusRecurrence_of_slabMeanRows_additive

/-- Honest recurrence assembler for a concrete slab row whose parent/slab
volume ratio has been retained in the inverse-gap exponent. -/
noncomputable abbrev harmonicApproximationGoodScales_scaledMeanRecurrenceAssembly :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.budgetedRadiusRecurrence_of_scaledMeanRows

/-- The missing upper-face sign of the concrete slab endpoint. -/
noncomputable abbrev harmonicApproximationGoodScales_upperFaceSlabPoincare :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.sq_averageOn_le_upperSlabPoincare

/-- A physical radius recurrence, once instantiated on every projected
boundary cell, supplies the complete translated-cube first-order energy
display used by harmonic approximation. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalRecurrenceEnergyReadout :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_translatedCubeEnergyReadout_of_physicalRecurrence

/-- Fixed-quarter specialization with the literal good-event indicator of
the frozen harmonic-approximation statement. -/
noncomputable abbrev harmonicApproximationGoodScales_physicalQuarterRecurrenceEnergyReadout :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_indicator_translatedCubeEnergyReadout_of_physicalQuarterRecurrence

/-- The negated interior gate always gives a genuine flush face; edge and
corner cells therefore introduce no exceptional geometry class. -/
noncomputable abbrev harmonicApproximationGoodScales_projectedFlushFace :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.exists_projectedBoundaryCell_flushFace

/-- The direct zero-trace residual window is contained in the literal
manuscript parent window, with no boundary-cell exception. -/
noncomputable abbrev harmonicApproximationGoodScales_residualWindowSubsetParent :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.boundaryResidualWindow_subset_nextWindow

/-- Exact identification of the direct Poincare residual window with the
projected Caccioppoli core two scales above it. -/
noncomputable abbrev harmonicApproximationGoodScales_residualWindowCore :=
  @SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.truncatedCube_eq_translate_projectedCaccioppoliCore

section

attribute [local instance] Classical.propDecidable

/-- **The frozen v6 harmonic-approximation statement.**

The bare application of
`Section6HarmonicBoundary.ConclusionAssembly.harmonic_approximation_good_scales_of_cellRow`
to the boundary-cell manuscript row produced by
`Section6HarmonicBoundary.exists_boundaryStepCellParentRow`. -/
theorem harmonic_approximation_good_scales
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, m ≤ L → n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemFractionalOn (cube d m) s h.grad →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          (∃ v : H1Function (translatedCube d (n - 2) y),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
          (∀ v v' : H1Function (translatedCube d (n - 2) y),
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
            v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
              v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            indicatorValue (goodEvent M none (n + 2) z 1 (s / 8))
                  (fun _ => normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q)) ω ≤
                C * s ^ (-2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    (normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
                        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                    else 0)) +
                  C * s ^ (-8 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    C * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal else 0) := by
  obtain ⟨Cbd, hCbd, hbrow⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.exists_boundaryStepCellParentRow d
  obtain ⟨Cb, hCb, hrow⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.exists_boundaryCellManuscriptRow_of_boundaryStepCellParentRow
      d hCbd hbrow
  exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.harmonic_approximation_good_scales_of_cellRow
    d hCb hrow

end

end

end SubdiffusiveProcess.Providers.Section6
