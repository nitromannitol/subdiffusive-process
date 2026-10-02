import SubdiffusiveProcess.Geometry.RationalTriadicCatalogue
import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
import SubdiffusiveProcess.Sobolev.VolumeResponseOperator
import SubdiffusiveProcess.Lane2.LimitForm

/-! Private statement-review carriers for the three Section 9 repairs.
These definitions contain no catalogue, boundedness, comparison or uniqueness premise.
The determining family and killed response spaces are fixed canonically.
-/

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section9

/-- The paper's countable determining family: every rational-centred triadic cube. -/
abbrev determiningCube (d i : ℕ) : Opens (SpatialCoordinates d) :=
  centeredCube (rationalTriadicCenter d i) (rationalTriadicSide d i)
    (rationalTriadicSide_pos d i)

/-- The actual killed H1_0 response space on a determining cube. -/
def determiningResponseSpace (d i : ℕ) [NeZero d] : ResponseSpace (determiningCube d i) :=
  killedResponseSpace (centeredCube_killedPoincare
    (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))

/-- Choose the proved measurable continuous version of the model's infrared sum. -/
def comparisonInfrared (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) : BilateralField d → C(SpatialCoordinates d, ℝ) :=
  Classical.choose (exists_infraredCharacterization hd M)

/-- One killed inverse on each determining cube, indexed by the sample. -/
abbrev KilledInverseFamily (d : ℕ) (Ω : Type) :=
  (i : ℕ) → Ω → DomainL2 (determiningCube d i) →L[ℝ] DomainL2 (determiningCube d i)

/-- The two actual finite-cutoff operators use the same environment at each representation index. -/
def representedCutoffInverse (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Ω : Type)
    (env : ℕ → Ω → BilateralField d) (N : ℕ → ℕ) (i n : ℕ) (ω : Ω) :
    DomainL2 (determiningCube d i) →L[ℝ] DomainL2 (determiningCube d i) :=
  volumeResponseOperator (determiningResponseSpace d i)
    (Lane4.cutoffPositiveCoefficient M (comparisonInfrared d hd M) (env n ω) (N n)
      (rationalTriadicCenter d i) (rationalTriadicSide_pos d i))

/-- Source context for a jointly represented pair of subsequential limits.
The environment at each index has the actual chaos law, converges to one field,
and is shared by both cutoff sequences. The inverse operators converge in norm
on one full event. Both limits are functions of the same limiting layers, as
specified at the start of the paper's comparison subsection. There are no
analytic estimates or conclusions of Section 9 in this predicate.
-/
def JointCutoffLimits (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
    (GE GF : KilledInverseFamily d Ω) (NE NF : ℕ → ℕ) : Prop :=
  IsProbabilityMeasure P ∧
  MeasurePreserving field P (chaosSampleLaw M).toMeasure ∧
  StrictMono NE ∧ StrictMono NF ∧
  (∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure) ∧
  (∀ᵐ ω ∂P, Tendsto (fun n => env n ω) atTop (𝓝 (field ω))) ∧
  (∀ᵐ ω ∂P, ∀ i,
    Tendsto (fun n => representedCutoffInverse d hd M Ω env NE i n ω) atTop (𝓝 (GE i ω)) ∧
    Tendsto (fun n => representedCutoffInverse d hd M Ω env NF i n ω) atTop (𝓝 (GF i ω))) ∧
  (∃ GEfield GFfield : KilledInverseFamily d (BilateralField d),
    (∀ i, Measurable (GEfield i)) ∧ (∀ i, Measurable (GFfield i)) ∧
    ∀ᵐ ω ∂P, ∀ i, GE i ω = GEfield i (field ω) ∧ GF i ω = GFfield i (field ω))

/-- Existence of actual joint limits after a common refinement of any two cutoff subsequences.
All probability spaces, environments and operators are conclusions of this predicate.
-/
def HasJointCutoffLimits (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (NE NF : ℕ → ℕ) : Prop :=
  ∃ seq : ℕ → ℕ, StrictMono seq ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
      (GE GF : KilledInverseFamily d Ω),
      JointCutoffLimits d hd M Ω P field env GE GF (NE ∘ seq) (NF ∘ seq)

/-- Form equality up to a positive scalar, including infinite energies outside the domain. -/
def ProportionalLimitForms (d : ℕ) (Ω : Type) (GE GF : KilledInverseFamily d Ω)
    (c : ℝ) (ω : Ω) : Prop :=
  ∀ i, limitFormDomain (GE i ω) = limitFormDomain (GF i ω) ∧
    ∀ u : DomainL2 (determiningCube d i),
      limitFormEnergy (GF i ω) u = ENNReal.ofReal c * limitFormEnergy (GE i ω) u

/-- Lower endpoint, optimized over the entire determining family for each realization. -/
def lowerEndpoint (d : ℕ) (Ω : Type) (GE GF : KilledInverseFamily d Ω) (ω : Ω) : ℝ :=
  sSup {a : ℝ | 0 < a ∧ ∀ i, ∀ u : DomainL2 (determiningCube d i),
    (a : EReal) * limitFormEnergy (GE i ω) u ≤ limitFormEnergy (GF i ω) u}

/-- Upper endpoint, optimized over the entire determining family for each realization. -/
def upperEndpoint (d : ℕ) (Ω : Type) (GE GF : KilledInverseFamily d Ω) (ω : Ω) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ ∀ i, ∀ u : DomainL2 (determiningCube d i),
    limitFormEnergy (GF i ω) u ≤ (a : EReal) * limitFormEnergy (GE i ω) u}

end SubdiffusiveProcess.Section9
