module

public import SubdiffusiveProcess.Paper.lem_19_smooth_trace_bound
public import SubdiffusiveProcess.Paper.lem_19_smooth_density
public import SubdiffusiveProcess.Paper.lem_19_trace_completion
public import SubdiffusiveProcess.Paper.lem_19_limit_membership
public import SubdiffusiveProcess.Paper.lem_19_interpolation_upgrade
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshError
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Lemma 19, unchanged theorem type.
Carried-input tick list:
- SOURCE: arbitrary cube z,r; t > d - 1; finite supported nu and its growth
  bound K. The constant precedes nu and K.
- PUBLISHED INPUT: hInterp is the existing deferred fractional interpolation
  input, with its stated normalization.
- DEPENDENCIES lem_19_smooth_trace_bound and lem_19_smooth_density conclude
  the cell-average trace bound  and smooth approximation.
- DEPENDENCY lem_19_trace_completion concludes the unique completion and
  bounded-density identification.
- DEPENDENCY lem_19_limit_membership concludes the missing fractional
  membership of the L2 limit; lem_19_interpolation_upgrade concludes the
  full-sequence upgrade.
No construction is added as a hypothesis. These proof-step refinements
make the paper's proof steps explicit. The completed trace and the full convergence assertion remain
conclusions over arbitrary cubes. -/
theorem lem_19
    (d : ℕ) (hd : 2 ≤ d) (hInterp : CubeFractionalInterpolationInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ)
    (ht : (d : ℝ) - 1 < t) :
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ (nu : Measure (SpatialCoordinates d)) (K : ℝ),
        nu Set.univ < (⊤ : ℝ≥0∞) →
        nu (closure (centeredCube z r hr : Set (SpatialCoordinates d)))ᶜ = 0 →
        0 ≤ K →
        (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            nu (Metric.ball x rr) ≤ ENNReal.ofReal (K * rr ^ t)) →
        ∃! T : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder →
            Lp ℝ 2 nu,
          (∀ u v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
            ∃ w : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
              w.val 0 = u.val 0 - v.val 0) ∧
          (∀ (u v w : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
            w.val 0 = u.val 0 - v.val 0 →
            ‖T u - T v‖ ^ 2 ≤
              C * (K + (nu (closure
                    (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) *
                (cubeFractionalL2Norm hd z r hr halfFractionalOrder w) ^ 2) ∧
          (∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
            ∀ (v : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder),
              (v.val 0 : SpatialCoordinates d → ℝ) =ᵐ[
                  volume.restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d))] f →
              ∀ hf : MemLp f 2 nu, T v = hf.toLp f) ∧
          (∀ u : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
            ‖T u‖ ^ 2 ≤
              C * (K + (nu (closure
                    (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) *
                (cubeFractionalL2Norm hd z r hr halfFractionalOrder u) ^ 2) ∧
          (∀ D : ℝ, 0 ≤ D →
            nu ≤ ENNReal.ofReal D •
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) →
            ∀ u : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
              MemLp (u.val 0) 2 nu ∧
                ∀ hu : MemLp (u.val 0) 2 nu, T u = hu.toLp (u.val 0))) ∧
    (∀ (threeQuarters : Set.Ioo (0 : ℝ) 1), (threeQuarters : ℝ) = 3 / 4 →
      ∀ (w : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters)
        (vlim : DomainL2 (centeredCube z r hr)) (M : ℝ),
        (∀ n : ℕ, cubeFractionalL2Norm hd z r hr threeQuarters (w n) ≤ M) →
        Tendsto (fun n : ℕ => (w n).val 0) atTop (𝓝 vlim) →
        ∃ vhalf : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
          vhalf.val 0 = vlim ∧
          ∃ diff : ℕ → CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder,
            (∀ n : ℕ, (diff n).val 0 = (w n).val 0 - vlim) ∧
            Tendsto (fun n : ℕ =>
              cubeFractionalL2Norm hd z r hr halfFractionalOrder (diff n))
              atTop (𝓝 0)) := by
  exact ⟨lem_19_trace_completion d hd z r hr t ht,
    lem_19_interpolation_upgrade d hd hInterp z r hr⟩


end SubdiffusiveProcess.Paper
