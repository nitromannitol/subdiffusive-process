module

public import Mathlib
public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.Foundations.CollarBufferedProfile

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **The original-space finite-cutoff catalogue with the buffered collar profiles as traces.**  Exactly
`aux_conv_represented_env_interface_orig`, with the additional requirement that for every catalogue cube `j'`,
every level `k` and every cube `j` the buffered collar profile
`bufferedCollarProfile d (z j') (r j') (r j' / (10 * 3 ^ k))` is a trace of the catalogue on `j` (the trace
family is one function family for all cubes, so the restrictions to subcubes are traces too). -/
def conv_represented_env_interface_buffered (d : ℕ) (hd : 2 ≤ d)
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
    (∀ (j' : ℕ) (k : ℕ) (j : ℕ), ∃ h : ℕ,
      trace j h = bufferedCollarProfile d (z j') (r j') (r j' / (10 * (3 : ℝ) ^ k))) ∧
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

end Paper
