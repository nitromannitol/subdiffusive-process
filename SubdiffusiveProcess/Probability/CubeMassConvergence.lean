module

public import SubdiffusiveProcess.Probability.CubeMassMartingale
public import Mathlib.Probability.Martingale.Convergence

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

theorem chaosCutoff_centeredCube_ae_tendsto
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ Xinfty : BilateralField d → ℝ,
      Measurable Xinfty ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        Tendsto (fun N ↦ ((chaosCutoff M N omega)
          (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
          atTop (nhds (Xinfty omega))) ∧
      0 ≤ᵐ[(chaosSampleLaw M).toMeasure] Xinfty := by
  let X : ℕ → BilateralField d → ℝ := fun N omega ↦
    ((chaosCutoff M N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  have hbase := chaosCutoff_centeredCube_martingale_nonnegative M z r hr
  have hmart : Martingale X
      (conditionalFineFiltration (fun _ ↦ 0) measurable_const)
      (chaosSampleLaw M).toMeasure := by
    simpa [X] using hbase.1
  have hnonneg : ∀ N omega, 0 ≤ X N omega := by
    simp [X]
  have hI0 : 0 ≤ ∫ omega, X 0 omega ∂(chaosSampleLaw M).toMeasure :=
    integral_nonneg (fun omega ↦ hnonneg 0 omega)
  let R : ℝ≥0 := ⟨∫ omega, X 0 omega ∂(chaosSampleLaw M).toMeasure, hI0⟩
  have hInt (N : ℕ) :
      (∫ omega, X 0 omega ∂(chaosSampleLaw M).toMeasure) =
        ∫ omega, X N omega ∂(chaosSampleLaw M).toMeasure := by
    have h := hmart.setIntegral_eq (i := 0) (j := N) (Nat.zero_le N)
      (s := Set.univ) MeasurableSet.univ
    simpa only [setIntegral_univ] using h
  have hbdd : ∀ N, eLpNorm (X N) 1 (chaosSampleLaw M).toMeasure ≤ (R : ℝ≥0∞) := by
    intro N
    rw [eLpNorm_one_eq_lintegral_enorm (hmart.integrable N).aestronglyMeasurable]
    rw [lintegral_enorm_of_ae_nonneg (Eventually.of_forall (hnonneg N))]
    rw [← ofReal_integral_eq_lintegral_ofReal (hmart.integrable N)
      (Eventually.of_forall (hnonneg N))]
    rw [← hInt N]
    change ENNReal.ofReal (R : ℝ) ≤ (R : ℝ≥0∞)
    rw [ENNReal.ofReal_coe_nnreal]
  let Xinfty : BilateralField d → ℝ :=
    Filtration.limitProcess X
      (conditionalFineFiltration (fun _ ↦ 0) measurable_const)
      (chaosSampleLaw M).toMeasure
  have hmeas : Measurable Xinfty := by
    dsimp [Xinfty]
    exact Filtration.stronglyMeasurable_limit_process'.measurable
  have hlim := hmart.submartingale.ae_tendsto_limitProcess hbdd
  refine ⟨Xinfty, hmeas, ?_, ?_⟩
  · simpa [Xinfty, X] using hlim
  · filter_upwards [hlim] with omega hω
    exact ge_of_tendsto' hω (fun N ↦ hnonneg N omega)


end SubdiffusiveProcess
