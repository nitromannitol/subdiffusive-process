module

public import SubdiffusiveProcess.Sobolev.KilledGraph
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Banach

@[expose] public section

/-!
# Closed gradient ranges and volume loads

Only the finite tuple of scalar L2 spaces receives a Hilbert norm. Spatial
coordinates retain their ordinary product norm; no vector-valued Lp coercion
through a Euclidean-space wrapper occurs. The Poincare estimate below is an
explicit foundational input on a concrete closed subspace of the weak graph.
It is not a model convergence or regularity assumption.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal ContDiff Distributions
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Coordinatewise square-integrable gradients, with the sum-of-squares Hilbert norm. -/
abbrev HilbertGradient (Ω : Opens (SpatialCoordinates d)) :=
  PiLp 2 (fun _ : Fin d => DomainL2 Ω)

/-- The actual coordinate gradient projection from function/gradient data. -/
def sobolevGradient : SobolevData Ω →L[ℝ] HilbertGradient Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => DomainL2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.snd ℝ _ _)

/-- The Hilbert gradient norm is exactly the sum of the coordinate L2 energies. -/
theorem sobolevGradient_norm_sq (z : SobolevData Ω) :
    ‖sobolevGradient z‖ ^ 2 = ∑ i : Fin d, ‖z.2 i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

/-- Restrict the actual gradient projection to any concrete Sobolev subspace. -/
def subspaceGradient (V : Submodule ℝ (SobolevData Ω)) : V →L[ℝ] HilbertGradient Ω :=
  sobolevGradient.comp V.subtypeL

/-- Poincare bounds the whole graph norm by the gradient norm. -/
theorem sobolevData_norm_le_gradient {K : ℝ≥0} (z : SobolevData Ω)
    (hP : ‖z.1‖ ≤ K * ‖sobolevGradient z‖) :
    ‖z‖ ≤ (max K 1 : ℝ≥0) * ‖sobolevGradient z‖ := by
  rw [Prod.norm_def]
  apply max_le
  · exact hP.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K 1)
      (norm_nonneg _))
  · have hgrad : ‖z.2‖ ≤ ‖sobolevGradient z‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      exact PiLp.norm_apply_le (sobolevGradient z) i
    exact hgrad.trans (le_mul_of_one_le_left (norm_nonneg _)
      (by exact_mod_cast le_max_right K 1))

/-- Poincare gives an injective gradient projection with a quantitative inverse bound. -/
theorem subspaceGradient_antilipschitz (V : Submodule ℝ (SobolevData Ω)) (K : ℝ≥0)
    (hP : ∀ z : V, ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient V z‖) :
    AntilipschitzWith (max K 1) (subspaceGradient V) :=
  (subspaceGradient V).antilipschitz_of_bound fun z => sobolevData_norm_le_gradient (z : SobolevData Ω) (hP z)

/-- Closedness of the actual graph and Poincare prove closedness of its gradient image. -/
theorem isClosed_subspaceGradient_range (V : Submodule ℝ (SobolevData Ω))
    (hV : IsClosed (V : Set (SobolevData Ω))) (K : ℝ≥0)
    (hP : ∀ z : V, ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient V z‖) :
    IsClosed (Set.range (subspaceGradient V)) := by
  have : IsClosed (V : Set (SobolevData Ω)) := hV
  have : CompleteSpace V := IsClosed.completeSpace_coe
  exact (subspaceGradient_antilipschitz V K hP).isClosed_range (subspaceGradient V).uniformContinuous

/-- The actual lift from the gradient range is determined uniquely by Poincare. -/
def sobolevGradientEquiv (V : Submodule ℝ (SobolevData Ω))
    (hV : IsClosed (V : Set (SobolevData Ω))) (K : ℝ≥0)
    (hP : ∀ z : V, ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient V z‖) :
    V ≃L[ℝ] LinearMap.range (subspaceGradient V).toLinearMap := by
  haveI : IsClosed (V : Set (SobolevData Ω)) := hV
  haveI : CompleteSpace V := IsClosed.completeSpace_coe
  exact ContinuousLinearMap.equivRange
    (subspaceGradient_antilipschitz V K hP).injective (isClosed_subspaceGradient_range V hV K hP)

/-- The range equivalence is precisely the original coordinate gradient map. -/
theorem sobolevGradientEquiv_coe (V : Submodule ℝ (SobolevData Ω))
    (hV : IsClosed (V : Set (SobolevData Ω))) (K : ℝ≥0)
    (hP : ∀ z : V, ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient V z‖) (z : V) :
    (sobolevGradientEquiv V hV K hP z : HilbertGradient Ω) = subspaceGradient V z := rfl

/-- L2 volume pairing on actual function/gradient data. -/
def sobolevVolumeLoad (f : DomainL2 Ω) : SobolevData Ω →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (ContinuousLinearMap.fst ℝ _ _)

/-- The load uses Lebesgue volume on the domain, rather than the later singular speed measure. -/
theorem sobolevVolumeLoad_apply (f : DomainL2 Ω) (z : SobolevData Ω) :
    sobolevVolumeLoad f z = ∫ x in (Ω : Set (SpatialCoordinates d)), f x * z.1 x := by
  change inner ℝ f z.1 = _
  rw [L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- The induced load on gradients uses the unique Sobolev lift. -/
def gradientVolumeLoad (V : Submodule ℝ (SobolevData Ω))
    (hV : IsClosed (V : Set (SobolevData Ω))) (K : ℝ≥0)
    (hP : ∀ z : V, ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient V z‖)
    (f : DomainL2 Ω) : LinearMap.range (subspaceGradient V).toLinearMap →L[ℝ] ℝ :=
  ((sobolevVolumeLoad f).comp V.subtypeL).comp (sobolevGradientEquiv V hV K hP).symm.toContinuousLinearMap

/-- Transport to the gradient space preserves the actual volume load. -/
theorem gradientVolumeLoad_on_graph (V : Submodule ℝ (SobolevData Ω))
    (hV : IsClosed (V : Set (SobolevData Ω))) (K : ℝ≥0)
    (hP : ∀ z : V, ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient V z‖)
    (f : DomainL2 Ω) (z : V) :
    gradientVolumeLoad V hV K hP f (sobolevGradientEquiv V hV K hP z) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), f x * (z : SobolevData Ω).1 x := by
  change sobolevVolumeLoad f ((sobolevGradientEquiv V hV K hP).symm
    (sobolevGradientEquiv V hV K hP z) : V) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, sobolevVolumeLoad_apply]

end SubdiffusiveProcess
