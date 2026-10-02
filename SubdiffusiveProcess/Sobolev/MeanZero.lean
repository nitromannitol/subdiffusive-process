import SubdiffusiveProcess.Sobolev.GradientRange

/-!
# Mean-zero Sobolev data and the affine Neumann load

The domain has finite Lebesgue volume. Mean zero means its actual volume
integral vanishes. The affine Neumann load is the sum of the coordinate
volume integrals of the weak gradient; identifying its boundary-flux formula
is a separate trace/divergence theorem.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- A constant scalar function as an actual domain L2 equivalence class. -/
def domainConstantL2 (c : ℝ) : DomainL2 Ω :=
  (memLp_const (μ := volume.restrict (Ω : Set (SpatialCoordinates d))) (p := 2) c).toLp
    (fun _ => c)

/-- Almost-everywhere identity for the constant L2 function. -/
theorem domainConstantL2_coeFn (c : ℝ) :
    (domainConstantL2 (Ω := Ω) c : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] fun _ => c := MemLp.coeFn_toLp _

/-- A constant L2 vector pairs as the ordinary volume integral. -/
theorem inner_domainConstantL2 (c : ℝ) (u : DomainL2 Ω) :
    inner ℝ (domainConstantL2 c) u =
      ∫ x in (Ω : Set (SpatialCoordinates d)), c * u x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [domainConstantL2_coeFn (Ω := Ω) c] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]

/-- The actual mean-zero H1 graph; the zero integral uses Lebesgue measure. -/
def meanZeroSobolevGraph (Ω : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))] :
    Submodule ℝ (SobolevData Ω) :=
  weakSobolevGraph Ω ⊓ LinearMap.ker (sobolevVolumeLoad (domainConstantL2 1))

/-- Membership specifies both the distributional gradient and zero mean. -/
theorem mem_meanZeroSobolevGraph_iff (z : SobolevData Ω) :
    z ∈ meanZeroSobolevGraph Ω ↔ z ∈ weakSobolevGraph Ω ∧
      (∫ x in (Ω : Set (SpatialCoordinates d)), z.1 x) = 0 := by
  simp only [meanZeroSobolevGraph, Submodule.mem_inf, LinearMap.mem_ker]
  change (z ∈ weakSobolevGraph Ω ∧ inner ℝ (domainConstantL2 1) z.1 = 0) ↔ _
  simp only [inner_domainConstantL2, one_mul]

/-- Mean-zero Sobolev data form a closed subspace of the actual graph space. -/
theorem isClosed_meanZeroSobolevGraph :
    IsClosed (meanZeroSobolevGraph Ω : Set (SobolevData Ω)) :=
  isClosed_weakSobolevGraph.inter (isClosed_eq
    (sobolevVolumeLoad (domainConstantL2 (Ω := Ω) 1)).continuous continuous_const)

/-- The affine Neumann load on an actual gradient vector. -/
def affineNeumannLoad (p : Fin d → ℝ) : HilbertGradient Ω →L[ℝ] ℝ :=
  ∑ i : Fin d, (innerSL ℝ (domainConstantL2 (p i))).comp (PiLp.proj 2 _ i)

/-- This is exactly the volume formula for the affine Neumann load. -/
theorem affineNeumannLoad_apply (p : Fin d → ℝ) (g : HilbertGradient Ω) :
    affineNeumannLoad p g = ∑ i : Fin d,
      ∫ x in (Ω : Set (SpatialCoordinates d)), p i * g i x := by
  simp only [affineNeumannLoad, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, innerSL_apply_apply, inner_domainConstantL2]

end SubdiffusiveProcess
