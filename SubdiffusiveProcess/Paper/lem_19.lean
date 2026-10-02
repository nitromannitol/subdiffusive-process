import SubdiffusiveProcess.Paper.lem_19_smooth_trace_bound
import SubdiffusiveProcess.Paper.lem_19_smooth_density
import SubdiffusiveProcess.Paper.lem_19_trace_completion
import SubdiffusiveProcess.Paper.lem_19_limit_membership
import SubdiffusiveProcess.Paper.lem_19_interpolation_upgrade
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane2.BoundaryPackaging
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.ResponseMarkov
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.MeshError
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Main.MeasureTrace
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

/-- Lemma 19 (paper 1881–1946), unchanged theorem type.
Carried-input tick list:
- SOURCE: arbitrary cube z,r; t > d - 1; finite supported nu and its growth
  bound K (1883–1885). The constant precedes nu and K.
- PUBLISHED INPUT: hInterp is the existing deferred fractional interpolation
  input, invoked at 1943–1945 and normalized as recorded in
  DEV-028-G4-fractional-interpolation-normalization.
- DEPENDENCIES lem_19_smooth_trace_bound and lem_19_smooth_density conclude
  the cell-average trace bound (1897–1921) and smooth approximation (1923–1940).
- DEPENDENCY lem_19_trace_completion concludes the unique completion and
  bounded-density identification (1940–1942).
- DEPENDENCY lem_19_limit_membership concludes the missing fractional
  membership of the L2 limit; lem_19_interpolation_upgrade concludes the
  full-sequence upgrade (1943–1945).
No construction is added as a hypothesis. These statement-only refinements
make the paper's proof steps explicit; DEV-hand-lem19-construction-split records
the split, and DEV-032-G4-trace-limit-membership records the original carrier
correction. The completed trace and the full convergence assertion remain
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


end Paper
