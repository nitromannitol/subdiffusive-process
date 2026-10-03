module

public import SubdiffusiveProcess.Lane2.NativeBridge
public import SubdiffusiveProcess.Lane2.CellDirichlet
public import Mathlib.Geometry.Manifold.SmoothApprox

@[expose] public section

/-! Smooth uniform approximation and native weak Sobolev data on a bounded cube.
The approximations carry no uniform derivative or energy bound. -/

open Filter MeasureTheory Set TopologicalSpace
open Homogenization
open scoped Topology ContDiff
noncomputable section
namespace SubdiffusiveProcess

/-- Every continuous scalar function is a uniform limit of globally smooth functions. -/
theorem exists_smooth_uniform_approximation {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (f : X → ℝ) (hf : Continuous f) :
    ∃ phi : ℕ → X → ℝ, (∀ n, ContDiff ℝ ∞ (phi n)) ∧
      TendstoUniformly phi f atTop := by
  have happrox (n : ℕ) : ∃ g : X → ℝ, ContDiff ℝ ∞ g ∧
      ∀ x, dist (g x) (f x) < 1 / ((n : ℝ) + 1) := by
    obtain ⟨g, hg, hgf, _⟩ := hf.exists_contDiff_approx (⊤ : ℕ∞)
      (ε := fun _ => 1 / ((n : ℝ) + 1)) continuous_const
      (fun _ => by positivity)
    exact ⟨g, hg, hgf⟩
  choose phi hphi hbound using happrox
  refine ⟨phi, hphi, Metric.tendstoUniformly_iff.mpr ?_⟩
  intro eps heps
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [hlim.eventually (gt_mem_nhds heps)] with n hn
  intro x
  simpa only [dist_comm (f x) (phi n x)] using (hbound n x).trans hn

/-- A smooth scalar function gives actual weak Sobolev data on a bounded cube. -/
theorem exists_weak_datum_of_smooth {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f) :
    ∃ b : weakSobolevGraph (centeredCube z r hr),
      ((b.val.1 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f := by
  let u : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain
      (lane2_isOpenBoundedConvexDomain_centeredCube z hr) (hf.of_le (by norm_num))
  exact ⟨⟨sobolevDataOfH1 u, sobolevDataOfH1_mem_weak u⟩,
    sobolevDataOfH1_fst_coeFn u⟩

end SubdiffusiveProcess
