module

public import SubdiffusiveProcess.MultiplicativeChaos.ZeroOne

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The second input of the full-support argument (`mfd:prop-chaos-growth`): the
event that a cube carries no mass has probability zero or one.  (The first is
positivity of the mean.)

This is Kolmogorov's zero-one law over the independent layers.  Its content is
that `mu(Q) = 0` is, up to null sets, an event of the TAIL of the layer
sequence.  The first `k+1` layers enter the cutoff densities only through the
factor `exp(sum_{j <= k} g_j - (k+1) tau^2)`, which is continuous and strictly
positive, hence bounded between two positive constants on the compact support
of a test function; removing it leaves the test integrals of the cutoff
densities of the layers beyond `k` alone, whose upper limits therefore decide
`mu(Q) = 0` and read only those layers.  Being independent of every head
block, the indicator has `E[1_A | F_k] = E[1_A]` for every `k`, and Levy's
upward theorem -- `ae_eq_const_of_condExp_eq_const` together with
`condExp_eq_integral_of_ae_condExp_of_indep` -- makes it almost surely
constant. -/
theorem chaos_tail_law
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (_hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
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

end SubdiffusiveProcess.Paper
