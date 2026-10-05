module

public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Paper.lem_19_smooth_density_one_step_dilation
public import SubdiffusiveProcess.Paper.lem_19_smooth_density_one_step_mollification
public import SubdiffusiveProcess.Paper.lem_19_smooth_density_one_step_error_assembly

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- One positive-error step in the smooth-density construction of Lemma 19,
`mfd:lem-19`.
Carried-input tick list:
- SOURCE: dimension `d ≥ 2`, arbitrary centre `z`, positive side `r`, a
  half-fractional class `v`, and a positive tolerance `ε`.
- CONCLUDED HERE: an ambient globally smooth representative `f`, its actual
  half-fractional restriction `a`, an admissible difference `diff` representing
  `v - a`, and the strict error bound below `ε`.
The inward dilation and enlarged-cube mollification are constructions in the
paper proof, not hypotheses. The following fine children expose those
construction steps without changing the parent conclusion:
- DEPENDENCY `lem_19_smooth_density_one_step_dilation` supplies the inward
  factor, transported fractional class, and first error.
- DEPENDENCY `lem_19_smooth_density_one_step_mollification` supplies the
  smooth representative, its fractional class, and the second error.
- DEPENDENCY `lem_19_smooth_density_one_step_error_assembly` supplies the
  admissible total difference and final strict error bound.
The existing triadic smooth-density theorem is not a paper hypothesis for
this arbitrary-cube statement. -/
theorem lem_19_smooth_density_one_step
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
      (f : SpatialCoordinates d → ℝ)
      (diff : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
      ContDiff ℝ ∞ f ∧
      ((a.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f) ∧
      diff.val 0 = v.val 0 - a.val 0 ∧
      cubeFractionalL2Norm hd z r hr halfFractionalOrder diff < ε := by
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨lam, u, dilErr, hu, hdil, hdilErr⟩ :=
    lem_19_smooth_density_one_step_dilation d hd z r hr v
      (η := ε / 2) hε2
  obtain ⟨a, f, mollErr, hf, ha, hmoll, hmollErr⟩ :=
    lem_19_smooth_density_one_step_mollification d hd z r hr v lam u hu
      (η := ε / 2) hε2
  obtain ⟨diff, hdiff, hdiffErr⟩ :=
    lem_19_smooth_density_one_step_error_assembly d hd z r hr v u a
      dilErr mollErr hdil hmoll hε hdilErr hmollErr
  exact ⟨a, f, diff, hf, ha, hdiff, hdiffErr⟩

end SubdiffusiveProcess.Paper
