module

public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.conv_represented_estimates_transfer
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_represented_bounds_seq
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The catalogue-free part of the represented joint package: literally the first eleven
conjuncts of `aux_thm_C0_JointHypU` (probability space, limit field `field` of the chaos law,
strictly increasing cutoffs, cutoff-dependent environments `envE n`, `envF n` of the chaos law that
converge almost surely to `field`, the pinned killed spaces, the actual cutoff killed inverses
`GNE i n`, `GNF i n` evaluated at `(envE n ω, NE n)`, `(envF n ω, NF n)`, and their almost-sure
operator-norm limits `GE i`, `GF i`). -/
def aux_conv_represented_env_interface_joint
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) : Prop :=
  IsProbabilityMeasure P ∧ Measurable field ∧
    Measure.map field P = (chaosSampleLaw model).toMeasure ∧
    InfraredCharacterization model H ∧ StrictMono NE ∧ StrictMono NF ∧
    (∀ n, MeasurePreserving (envE n) P (chaosSampleLaw model).toMeasure ∧
      MeasurePreserving (envF n) P (chaosSampleLaw model).toMeasure) ∧
    (∀ᵐ omega ∂P,
      Tendsto (fun n => envE n omega) atTop (𝓝 (field omega)) ∧
      Tendsto (fun n => envF n omega) atTop (𝓝 (field omega))) ∧
    (∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i))) ∧
    (∀ᵐ omega ∂P, ∀ i n f,
      GNE i n omega f =
        (responseSolution (S i)
          (Lane4.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
          ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1 ∧
      GNF i n omega f =
        (responseSolution (S i)
          (Lane4.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
          ((sobolevVolumeLoad f).comp (S i).space.subtypeL)).val.1) ∧
    (∀ᵐ omega ∂P, ∀ i,
      Tendsto (fun n => GNE i n omega) atTop (𝓝 (GE i omega)) ∧
      Tendsto (fun n => GNF i n omega) atTop (𝓝 (GF i omega)))

/-- Environment form of `aux_thm_prop_catalogue`: the represented catalogue of a bounded family
of cubes, along `NE` with the environments `envE n` and along `NF` with `envF n`.  The fixed-field
original replaces `envE`, `envF` by `fun _ ω => field ω`. -/
def aux_conv_represented_env_interface_catalogue (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) : Prop :=
  ∃ (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (root : ℕ)
    (hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
    (Dcat : ∀ i, Submodule ℚ
      (DomainL2 (centeredCube (z i) (r i) (hr i))))
    (hDcat : ∀ i, Countable (Dcat i))
    (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
    (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (traceH1 : ∀ i, ℕ → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
    (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (Cext beta t : ℝ) (I : Paper.in_J d)
    (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
    (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
    (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
    letI : ∀ i, Countable (Dcat i) := hDcat
    conv_represented_estimates d hd model H Ω P NE envE
      ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I
      ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
      (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
    conv_represented_estimates d hd model H Ω P NF envF
      ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I
      ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
      (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey

/-- The finite-cutoff catalogue of a bounded family of cubes on the ORIGINAL (chaos-law) space,
along `NE` and `NF`: the data of `aux_conv_represented_env_interface_catalogue` evaluated at the
environment itself, the clauses of `conv_represented_estimates` except the pathwise boundedness of
the constants (`aux_conv_represented_estimates_transfer_core`), and measurable, tight responses. -/
def aux_conv_represented_env_interface_orig (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) : Prop :=
  ∃ (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (root : ℕ)
    (hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
    (Dcat : ∀ i, Submodule ℚ
      (DomainL2 (centeredCube (z i) (r i) (hr i))))
    (hDcat : ∀ i, Countable (Dcat i))
    (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
    (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (traceH1 : ∀ i, ℕ → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (usrcE usrcF : ∀ i, Dcat i → ℕ → BilateralField d → (Sspace i).space)
    (srcRepE srcRepF : ∀ i, Dcat i → ℕ → BilateralField d → SpatialCoordinates d → ℝ)
    (ucellE ucellF : ∀ i, ℕ → ℕ → BilateralField d → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (Cext beta t : ℝ) (I : Paper.in_J d)
    (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
    (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
    (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ)
    (G0E G0F : Set (BilateralField d)),
    (∀ i n, Measurable (catalogResponse i (NE n)) ∧ Measurable (catalogResponse i (NF n))) ∧
    (∀ i, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      (chaosSampleLaw model).toMeasure {β | Mb < |catalogResponse i (NE n) β|} ≤
        ENNReal.ofReal rho ∧
      (chaosSampleLaw model).toMeasure {β | Mb < |catalogResponse i (NF n) β|} ≤
        ENNReal.ofReal rho) ∧
    letI : ∀ i, Countable (Dcat i) := hDcat
    aux_conv_represented_estimates_transfer_core d hd model H NE ℕ root z r hr Sspace Dcat fcat
      (fun _ => ℕ) trace traceH1 usrcE srcRepE ucellE Cext beta alpha eta t {1} I ℕ
      (fun i n β => catalogResponse i (NE n) β) (fun i n β => catalogConstant i (NE n) β) G0E
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
    aux_conv_represented_estimates_transfer_core d hd model H NF ℕ root z r hr Sspace Dcat fcat
      (fun _ => ℕ) trace traceH1 usrcF srcRepF ucellF Cext beta alpha eta t {1} I ℕ
      (fun i n β => catalogResponse i (NF n) β) (fun i n β => catalogConstant i (NF n) β) G0F
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey

/-- **The environment-form represented package (exact hypothesis of the repaired `thm_c1`).**
On a probability space carrying cutoff-dependent environments `envE`, `envF` and a limit field,
the catalogue-free joint package for the global family of cubes together with, for every `k`, a
bounded catalogue (enumeration `e` of the cubes with index at most `k`, sharing the response
spaces, operators and both cutoff sequences) in environment form.  This is the environment-form
replacement of `in_joint_extracted_candidates` (`hJoint`), `aux_thm_prop_bounds_pointwise`
(`hBounds`), `in_represented_enum` (`hEnum`) and `aux_thm_c1_catalogues` (`hCat`). -/
def conv_represented_env_interface (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GNE GNF : (i : ℕ) → ℕ → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ) : Prop :=
  aux_conv_represented_env_interface_joint d model H Ω P field envE envF z r hr Sspace
      GNE GNF GE GF NE NF ∧
    ∀ k : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ k, ∃ j, e j = i) ∧
      aux_conv_represented_env_interface_catalogue d hd model H Ω P envE envF
        (z ∘ e) (r ∘ e) (fun j => hr (e j)) (fun j => Sspace (e j)) NE NF alpha eta

/-- Environment form of the represented-bounds hypothesis `in_represented_bounds`
(`aux_thm_prop_bounds_pointwise` / `hBounds` of the frozen fixed-field theorems): for almost every
sample and every cube, the bundle `in_represented_bounds_seq` holds for the *varying-environment*
coefficient sequence `n ↦ cutoffPositiveCoefficient model H (env n ω) (N n) (z i) (hr i)` with the
represented limit operator. The fixed-field bundle is the special case `env n = field`
(`aux_in_represented_bounds_seq_iff`). It is a separate hypothesis: the collar, plateau-cutoff and
finite-mesh fields of the bundle are supplied by other packets, not by the coordinate construction. -/
def aux_conv_represented_env_interface_bounds (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (GE GF : (i : ℕ) → Ω →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) : Prop :=
  ∀ᵐ omega ∂P, ∀ i : ℕ,
    in_represented_bounds_seq d hd (z i) (r i) (hr i) (Sspace i)
      (fun n => Lane4.cutoffPositiveCoefficient model H (envE n omega) (NE n) (z i) (hr i))
      (GE i omega) ∧
    in_represented_bounds_seq d hd (z i) (r i) (hr i) (Sspace i)
      (fun n => Lane4.cutoffPositiveCoefficient model H (envF n omega) (NF n) (z i) (hr i))
      (GF i omega)

end Paper
