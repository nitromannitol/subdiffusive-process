module

public import SubdiffusiveProcess.Compactness.PointwiseExtraction
public import SubdiffusiveProcess.Sobolev.UniformCubeLimit
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace UniformConvergence
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Compactness

/-- Equicontinuous bounded representatives on a closed cube give an actual
uniform and L2 cluster, without assuming an L2 limit in advance. -/
theorem exists_cube_uniform_l2_cluster
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (F : ℕ → SpatialCoordinates d → ℝ)
    (W : ℕ → DomainL2 (centeredCube z r hr))
    (hW : ∀ n, (W n : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] F n)
    (M : ℝ)
    (hequi : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ ε > 0, ∃ δ > 0,
        ∀ y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          dist y x < δ → ∀ n, |F n y - F n x| < ε)
    (hbd : ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ n, |F n x| ≤ M)
    (ns : ℕ → ℕ) :
    ∃ (ms : ℕ → ℕ) (u : DomainL2 (centeredCube z r hr))
      (g : SpatialCoordinates d → ℝ),
      StrictMono ms ∧
      ContinuousOn g (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      (u : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g ∧
      TendstoUniformlyOn (fun n => F (ns (ms n))) g atTop
        (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      Tendsto (fun n => W (ns (ms n))) atTop (𝓝 u) := by
  classical
  let K := closure (centeredCube z r hr : Set (SpatialCoordinates d))
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (lane2_isCompact_closure_centeredCube z hr)
  haveI : Nonempty K := ⟨⟨z, subset_closure (by
    show z ∈ Metric.ball z (r / 2)
    exact Metric.mem_ball_self (by linarith))⟩⟩
  let f : ℕ → K → ℝ := fun n x => F (ns n) x
  have heq : Equicontinuous f := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hequi x.1 x.2 ε hε
    refine ⟨δ, hδ, fun y hy n => ?_⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact h y.1 y.2 (by simpa only [Subtype.dist_eq] using hy) (ns n)
  have hbd' : ∀ x : K, ∃ C : ℝ, ∀ n, ‖f n x‖ ≤ C :=
    fun x => ⟨M, fun n => by rw [Real.norm_eq_abs]; exact hbd x.1 x.2 (ns n)⟩
  obtain ⟨gc, ms, hms, hgc, hpt⟩ := exists_pointwise_subseq_of_equicontinuous heq hbd'
  have hunif : TendstoUniformly (fun n => f (ms n)) gc atTop :=
    UniformFun.tendsto_iff_tendstoUniformly.mp
      (((heq.comp ms).tendsto_uniformFun_iff_pi atTop gc).mpr (tendsto_pi_nhds.mpr hpt))
  obtain ⟨u, g, hg, hug, hgg⟩ := exists_cubeL2_of_continuous_closedCube z hr ⟨gc, hgc⟩
  have hunif' : TendstoUniformly
      (fun n (x : K) => F (ns (ms n)) x.1) (fun x : K => g x.1) atTop := by
    convert hunif using 1
    funext x
    exact hgg x.1 x.2
  exact ⟨ms, u, g, hms, hg, hug,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hunif',
    cube_tendsto_of_uniformly_on z hr (fun n => F (ns (ms n)))
      (fun n => W (ns (ms n))) (fun n => hW (ns (ms n))) g u hug hunif'⟩

end SubdiffusiveProcess.Compactness
