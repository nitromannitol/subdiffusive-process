import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Sobolev.SmoothFractionalClass

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper

/-- Smooth fractional representative construction, paper 1918–1921.
Carried-input tick list:
- SOURCE: d, the positive-side centered cube z,r and an ambient smooth f.
- CONCLUDED HERE: a scalar half-fractional cube class whose volume-restricted
  representative agrees almost everywhere with f.
The class is constructed by the original-grid averages and their pointwise
identification for continuous data; fractional membership is not a premise. -/
theorem lem_19_smooth_fractional_representative
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (f : SpatialCoordinates d → ℝ) (hf : ContDiff ℝ ∞ f) :
    ∃ v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
      (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] f := by
  let O : Opens (SpatialCoordinates d) := ⊤
  have hO : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (O : Set (SpatialCoordinates d)) := by
    intro x hx
    trivial
  have hf' : ContDiffOn ℝ ∞
      (fun x : SpatialCoordinates d => fun _ : Fin 1 => f x)
      (O : Set (SpatialCoordinates d)) := by
    rw [contDiffOn_pi]
    intro i
    simpa only [O, Set.mem_univ, forall_true_left] using hf.contDiffOn
  obtain ⟨hmem, hfinite⟩ := contDiffOn_cube_fractional_L2
    hd z r hr O hO (fun x : SpatialCoordinates d => fun _ : Fin 1 => f x)
      hf' (1 / 2 : ℝ) (by norm_num) (by norm_num)
  let u : Fin 1 → DomainL2 (centeredCube z r hr) :=
    fun i => (hmem i).toLp (fun x : SpatialCoordinates d => f x)
  have hu : ∀ i : Fin 1,
      (u i : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x : SpatialCoordinates d => f x) := by
    intro i
    exact MemLp.coeFn_toLp (hmem i)
  have hprop : cubeFractionalL2Seminorm hd z r hr halfFractionalOrder u < ⊤ := by
    simpa only [cubeFractionalL2Seminorm, u, halfFractionalOrder] using hfinite
  let v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder :=
    ⟨u, hprop⟩
  refine ⟨v, ?_⟩
  simpa only [v, u] using hu 0

end Paper
