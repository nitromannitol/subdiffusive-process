module

public import SubdiffusiveProcess.Lane1.ZeroOne

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem chaos_tail_law
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (mu : BilateralField d → Measure (SpatialCoordinates d))
    (hmeas : Measurable mu)
    (hlocfin : ∀ omega, IsLocallyFiniteMeasure (mu omega))
    (hconv : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      MeasuresConvergeLocally
        (fun N => weightedChaosCutoff M H N omega) (mu omega)) :
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (chaosSampleLaw M).toMeasure
          {omega | mu omega (centeredCube z r hr :
            Set (SpatialCoordinates d)) = 0} = 0 ∨
        (chaosSampleLaw M).toMeasure
          {omega | mu omega (centeredCube z r hr :
            Set (SpatialCoordinates d)) = 0} = 1 := by
  intro z r hr
  have hopen : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [centeredCube_coe_eq_ball]
    exact Metric.isOpen_ball
  exact chaos_zero_one_open M H mu hmeas hlocfin hconv hopen

end Paper
