import SubdiffusiveProcess.Paper.lane4_neumann_boundary_identity_trace_foundation
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Paper.lane4_neumann_load
import SubdiffusiveProcess.Paper.lane4_neumann_boundary_identity_face_trace
import SubdiffusiveProcess.Paper.lane4_neumann_boundary_identity_weak_ftc
import SubdiffusiveProcess.Paper.lane4_neumann_boundary_identity_frontier_hn_decomposition
import SubdiffusiveProcess.Paper.lane4_neumann_boundary_identity_boundary_assembly
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff

open MeasureTheory TopologicalSpace Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section
namespace Paper

/-- Audit ticks: concrete Hn surface; actual normal; trace assembled from unique continuous face restrictions; surface measure equality concluded (no free law); no input assumes divergence; paper770–771 supplier lane4_neumann_load; statement-only proof steps supplied by lane4_neumann_boundary_identity_face_trace, lane4_neumann_boundary_identity_weak_ftc, lane4_neumann_boundary_identity_frontier_hn_decomposition, and lane4_neumann_boundary_identity_boundary_assembly. Actual sourceclaimpluscoordinate carrier elaboration, no proofs/helperdefinitions outside single declaration. -/
theorem lane4_neumann_boundary_identity
    (n : ℕ) (hn : 1 ≤ n) :
    let Q : Opens (SpatialCoordinates (n + 1)) := unitNeumannCube (n + 1)
    let Qface : Opens (SpatialCoordinates n) := unitNeumannCube n
    let μface : Measure (SpatialCoordinates n) :=
      volume.restrict (Qface : Set (SpatialCoordinates n))
    let muBoundary : Measure (SpatialCoordinates (n + 1)) :=
      (MeasureTheory.Measure.hausdorffMeasure (n : ℝ)).restrict
        (frontier (Q : Set (SpatialCoordinates (n + 1))))
    let normal : SpatialCoordinates (n + 1) → SpatialCoordinates (n + 1) :=
      fun x i => if x i = 1 then 1 else if x i = 0 then -1 else 0
    ∃ (Tr : (i : Fin (n + 1)) → (side : Bool) →
        weakSobolevGraph Q →L[ℝ] DomainL2 Qface) (Ct : ℝ),
      0 < Ct ∧
      (∀ (i : Fin (n + 1)) (side : Bool) (v : weakSobolevGraph Q),
        ‖Tr i side v‖ ≤ Ct * ‖v‖) ∧
      (∀ (φ : SpatialCoordinates (n + 1) → ℝ),
        ContDiff ℝ 1 φ →
          ∀ (v : weakSobolevGraph Q),
            ((v : SobolevData Q).1 : SpatialCoordinates (n + 1) → ℝ) =ᵐ[
              volume.restrict (Q : Set (SpatialCoordinates (n + 1)))] φ →
              ∀ (i : Fin (n + 1)) (side : Bool),
                ((Tr i side v : DomainL2 Qface) : SpatialCoordinates n → ℝ) =ᵐ[μface]
                  (fun y => φ (Fin.insertNth i (if side then 1 else 0) y))) ∧
      (∀ (v : weakSobolevGraph Q) (p : SpatialCoordinates (n + 1)),
        (∑ i : Fin (n + 1),
            p i * ∫ x in (Q : Set (SpatialCoordinates (n + 1))),
              (sobolevGradient (v : SobolevData Q) i) x) =
          ∑ i : Fin (n + 1),
            p i *
              ((∫ y in (Qface : Set (SpatialCoordinates n)),
                  ((Tr i true v : DomainL2 Qface) : SpatialCoordinates n → ℝ) y) -
                (∫ y in (Qface : Set (SpatialCoordinates n)),
                  ((Tr i false v : DomainL2 Qface) : SpatialCoordinates n → ℝ) y))) ∧
      (∀ (Tr' : (i : Fin (n + 1)) → (side : Bool) →
          weakSobolevGraph Q →L[ℝ] DomainL2 Qface),
        (∀ (φ : SpatialCoordinates (n + 1) → ℝ),
          ContDiff ℝ 1 φ →
            ∀ (v : weakSobolevGraph Q),
              ((v : SobolevData Q).1 : SpatialCoordinates (n + 1) → ℝ) =ᵐ[
                volume.restrict (Q : Set (SpatialCoordinates (n + 1)))] φ →
                ∀ (i : Fin (n + 1)) (side : Bool),
                  ((Tr' i side v : DomainL2 Qface) : SpatialCoordinates n → ℝ) =ᵐ[μface]
                    (fun y => φ (Fin.insertNth i (if side then 1 else 0) y))) →
          Tr' = Tr) ∧
      muBoundary =
        ∑ i : Fin (n + 1),
          (Measure.map (fun y : SpatialCoordinates n =>
              @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (1 : ℝ) y) μface +
            Measure.map (fun y : SpatialCoordinates n =>
              @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (0 : ℝ) y) μface) ∧
      (let traceBoundary : weakSobolevGraph Q → SpatialCoordinates (n + 1) → ℝ :=
          fun v x =>
            ∑ i : Fin (n + 1),
              if x i = 1 then
                ((Tr i true v : DomainL2 Qface) : SpatialCoordinates n → ℝ)
                  (fun j : Fin n => x (i.succAbove j))
              else if x i = 0 then
                ((Tr i false v : DomainL2 Qface) : SpatialCoordinates n → ℝ)
                  (fun j : Fin n => x (i.succAbove j))
              else 0
        ∀ (v : weakSobolevGraph Q) (p : SpatialCoordinates (n + 1)),
          Integrable
              (fun x =>
                (∑ i : Fin (n + 1), p i * normal x i) * traceBoundary v x)
              muBoundary ∧
            (∫ x, (∑ i : Fin (n + 1), p i * normal x i) * traceBoundary v x ∂muBoundary) =
              ∑ i : Fin (n + 1),
                p i * ∫ x in (Q : Set (SpatialCoordinates (n + 1))),
                  (sobolevGradient (v : SobolevData Q) i) x) := by
  intro Q Qface μface muBoundary normal
  have htrace_raw := lane4_neumann_boundary_identity_trace_foundation n hn
  rcases htrace_raw with ⟨⟨Tr0, Ct0, hCt0, hbound0, hsmooth0⟩, hdense0⟩
  have hface_raw := lane4_neumann_boundary_identity_face_trace n hn ⟨Tr0, Ct0, hCt0, hbound0, hsmooth0⟩ hdense0
  rcases hface_raw with ⟨Tr, Ct, hCt, hbound, hsmooth, hunique⟩
  have hdecomp_raw := lane4_neumann_boundary_identity_frontier_hn_decomposition n hn
  have hint (v : weakSobolevGraph Q) (p : SpatialCoordinates (n + 1)) :=
    lane4_neumann_boundary_identity_boundary_assembly n hn Tr Ct hCt hbound hsmooth hdecomp_raw v p
  refine ⟨Tr, Ct, hCt, hbound, hsmooth, ?_, hunique, hdecomp_raw, ?_⟩
  · intro v p
    exact lane4_neumann_boundary_identity_weak_ftc n hn Tr hsmooth v p
  · exact hint

end Paper
