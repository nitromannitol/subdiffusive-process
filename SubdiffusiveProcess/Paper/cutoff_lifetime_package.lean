module

public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Main.DiffusionPath
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CutoffSpeedDensity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The finite-cutoff **lifetime kernel**: the section of `KN N` at `omega`, pushed forward along
`LifetimePath.ofContinuousPath`.

This is the `L` demanded by `finite_cutoff_local_path_bounds`,
`prop_limit_properties_cutoff_symmetry` and their consumers.  It is not a choice: the transport identity
`hL` determines it uniquely (see `aux_cutoff_lifetime_package_unique`). -/
def aux_cutoff_lifetime_package_kernel {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) :
    Kernel (SpatialCoordinates d) (Path d) :=
  ((KN N).comap (fun x : SpatialCoordinates d => (omega, x))
      (measurable_const.prodMk measurable_id)).map
    LifetimePath.ofContinuousPath

/-- `hL`: the transport identity, by construction. -/
theorem aux_cutoff_lifetime_package_spec {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (N : ℕ) (omega : BilateralField d) (x : SpatialCoordinates d) :
    Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) =
      aux_cutoff_lifetime_package_kernel KN N omega x := by
  rw [aux_cutoff_lifetime_package_kernel,
    Kernel.map_apply _ LifetimePath.measurable_ofContinuousPath, Kernel.comap_apply]

/-- The transport identity pins `L` uniquely, so no selection is involved. -/
theorem aux_cutoff_lifetime_package_unique {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d))
    (hL : ∀ N omega x,
      Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x) :
    L = fun N omega => aux_cutoff_lifetime_package_kernel KN N omega := by
  funext N omega
  apply Kernel.ext
  intro x
  rw [← hL N omega x, aux_cutoff_lifetime_package_spec]

/-- `hLstrong` is redundant: `LocalDiffusion` already carries `StrongMarkov`. -/
theorem aux_cutoff_lifetime_package_strong_markov {d : ℕ}
    {c rho : SpatialCoordinates d → ℝ} {law : Kernel (SpatialCoordinates d) (Path d)}
    (h : LocalDiffusionData c rho law) : StrongMarkov law :=
  h.1.1

/-- **Published input: continuous killed density for the finite-cutoff operator.**

De Giorgi–Nash–Moser / Aronson.  For a uniformly elliptic divergence-form operator on a bounded open
set, with coefficients that are continuous and bounded above and below by positive constants there, the
killed (Dirichlet) transition density exists and is jointly continuous in `(t, x, y)` on
`Ioi 0 ×ˢ U ×ˢ U`.

The finite-cutoff coefficients satisfy those hypotheses outright, with no smallness or randomness
condition: writing `V = cutoffPotential H omega N` and `b = (N+1) * tauSq M.P`,
`cutoffSpeedDensity M H omega N = exp (V - b) > 0` is continuous everywhere, and
`cutoffCoefficient M H omega N = (ahom M N)⁻¹ • cutoffSpeedDensity M H omega N`; on any bounded open set
both are continuous and two-sided bounded by positive constants, since a continuous positive function
attains positive min and finite max on the compact closure.

This is the ONLY non-formal content of the `L` package.  Everything else is proved:
`aux_cutoff_lifetime_package_kernel` supplies `L`, `aux_cutoff_lifetime_package_spec` supplies `hL` by construction,
`aux_cutoff_lifetime_package_unique` shows the transport identity pins `L` uniquely, and
`aux_cutoff_lifetime_package_strong_markov` shows `hLstrong` is redundant because `LocalDiffusion` already
contains `StrongMarkov`.

Deferred external input.
No Lean witness. -/
structure aux_cutoff_lifetime_package_Input {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)) : Prop where
  /-- The cutoff lifetime law is a local diffusion with a continuous killed density, for a.e. sample
  and every cutoff. -/
  localDiffusionData : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
    LocalDiffusionData (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
      (aux_cutoff_lifetime_package_kernel KN N omega)

/-- The assembled `L` package: `L`, `hL`, `hLlocal`, `hLstrong` — exactly the four arguments that
`finite_cutoff_local_path_bounds` and `prop_limit_properties_cutoff_symmetry` now demand.

Only `hLlocal` comes from the published input; the other three are proved here. -/
theorem cutoff_lifetime_package {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hinput : aux_cutoff_lifetime_package_Input M H KN) :
    ∃ L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d),
      (∀ N omega x,
        Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        LocalDiffusionData (cutoffCoefficient M H omega N)
          (cutoffSpeedDensity M H omega N) (L N omega)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N, StrongMarkov (L N omega)) := by
  refine ⟨fun N omega => aux_cutoff_lifetime_package_kernel KN N omega,
    fun N omega x => aux_cutoff_lifetime_package_spec KN N omega x,
    hinput.localDiffusionData, ?_⟩
  filter_upwards [hinput.localDiffusionData] with omega homega
  intro N
  exact aux_cutoff_lifetime_package_strong_markov (homega N)



/-- **Heat-kernel-free finite-cutoff input**.

The paper's finite-cutoff SDE facts used by the elliptic route (the stopped Itô
formula of the elliptic tightness section): for a.e. sample and every cutoff, the lifetime law is a
`LocalDiffusion` — strong Markov, coefficients bounded above and below on compacts, and killed resolvents on
bounded open sets equal to `H¹₀` massive weak solutions.  It omits the continuous killed density (heat kernel)
of `aux_cutoff_lifetime_package_Input`, which it is implied by (`aux_cutoff_lifetime_package_Input.toLocalInput`).
-/
structure aux_cutoff_lifetime_package_LocalInput {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)) : Prop where
  /-- The cutoff lifetime law is a local diffusion, for a.e. sample and every cutoff. -/
  localDiffusion : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
    LocalDiffusion (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N)
      (aux_cutoff_lifetime_package_kernel KN N omega)

/-- The heat-kernel input implies the heat-kernel-free one. -/
theorem aux_cutoff_lifetime_package_Input.toLocalInput {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d}
    {H : BilateralField d → C(SpatialCoordinates d, ℝ)}
    {KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d)}
    (h : aux_cutoff_lifetime_package_Input M H KN) :
    aux_cutoff_lifetime_package_LocalInput M H KN :=
  ⟨h.localDiffusionData.mono fun _ hω N => (hω N).1⟩

/-- The heat-kernel-free `L` package: `L`, `hL`, `hLlocal : LocalDiffusion`, `hLstrong`. -/
theorem aux_cutoff_lifetime_package_local {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hinput : aux_cutoff_lifetime_package_LocalInput M H KN) :
    ∃ L : ℕ → BilateralField d → Kernel (SpatialCoordinates d) (Path d),
      (∀ N omega x,
        Measure.map LifetimePath.ofContinuousPath (KN N (omega, x)) = L N omega x) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        LocalDiffusion (cutoffCoefficient M H omega N)
          (cutoffSpeedDensity M H omega N) (L N omega)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N, StrongMarkov (L N omega)) := by
  refine ⟨fun N omega => aux_cutoff_lifetime_package_kernel KN N omega,
    fun N omega x => aux_cutoff_lifetime_package_spec KN N omega x,
    hinput.localDiffusion, ?_⟩
  filter_upwards [hinput.localDiffusion] with omega homega
  intro N
  exact (homega N).1


end SubdiffusiveProcess.Paper
