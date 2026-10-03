module

public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.conv_represented_env_interface_grids

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The represented catalogue retaining full rational grid coverage and buffered collar profiles. -/
def conv_represented_catalogue_grids (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (E : Paper.in_J d) (beta0 t0 : ℝ) : Prop :=
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
    (I = E ∧ beta = beta0 ∧ t = t0) ∧
    (∀ (j : ℕ) (o : SpatialCoordinates d), (∀ i : Fin d, ∃ q : ℚ, o i = (q : ℝ)) →
      ∃ g : ℕ, gridRoot g = j ∧ origin g = o) ∧
    (∀ (j' : ℕ) (k : ℕ) (j : ℕ), ∃ h : ℕ,
      trace j h = bufferedCollarProfile d (z j') (r j') (r j' / (10 * (3 : ℝ) ^ k))) ∧
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

end Paper
