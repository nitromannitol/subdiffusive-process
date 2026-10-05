module

public import SubdiffusiveProcess.Paper.lem_19_arbitrary_cube_frostman_trace
public import SubdiffusiveProcess.Paper.lem_19_smooth_fractional_representative
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Smooth-data part of Lemma 19.
Carried-input Scope and inputs:
- SOURCE: arbitrary center z and positive side r specify the paper's cube Q.
- SOURCE: t > d - 1, finite nu, support in the closed cube, K >= 0 and
  the ball-growth hypothesis are precisely.
- DEPENDENCY lem_19_arbitrary_cube_frostman_trace supplies the
  arbitrary-centered-cube trace estimate and smooth-data L2(nu) integrability
  from the null-face, Jensen and summation argument.
- DEPENDENCY lem_19_smooth_fractional_representative constructs a
  half-fractional class for every ambient smooth f, pinned by volume-a.e.
  equality on Q.
- CONCLUDED HERE: the two supplied construction steps are combined into the
  smooth trace bound on every centered cube.
The constant is chosen before nu, K, f and v. No trace estimate, null-face
property or cell-average convergence is carried as a hypothesis. -/
theorem lem_19_smooth_trace_bound
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : (d : ℝ) - 1 < t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (nu : Measure (SpatialCoordinates d)) (K : ℝ),
        nu Set.univ < (⊤ : ℝ≥0∞) →
        nu (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0 →
        0 ≤ K →
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            nu (Metric.ball x rr) ≤ ENNReal.ofReal (K * rr ^ t)) →
        ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
          MemLp f 2 nu ∧
            (∃ v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
              (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict
                  (centeredCube z r hr : Set (SpatialCoordinates d))] f) ∧
            ∀ (v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
              (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict
                  (centeredCube z r hr : Set (SpatialCoordinates d))] f →
              ∀ hf : MemLp f 2 nu,
                ‖hf.toLp f‖ ^ 2 ≤
                  C * (K + (nu (closure
                    (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) *
                    (cubeFractionalL2Norm hd z r hr halfFractionalOrder v) ^ 2 := by
  obtain ⟨C, hC, htrace⟩ :=
    lem_19_arbitrary_cube_frostman_trace d hd z r hr t ht
  refine ⟨C, hC, ?_⟩
  intro nu K hnu hsupp hK hgrowth f hf
  have hmem : MemLp f 2 nu :=
    (htrace nu K hnu hsupp hK hgrowth f hf).1
  have hv := lem_19_smooth_fractional_representative d hd z r hr f hf
  refine ⟨hmem, hv, ?_⟩
  intro v hvrep hfnu
  exact (htrace nu K hnu hsupp hK hgrowth f hf).2 v hvrep hfnu

end SubdiffusiveProcess.Paper
