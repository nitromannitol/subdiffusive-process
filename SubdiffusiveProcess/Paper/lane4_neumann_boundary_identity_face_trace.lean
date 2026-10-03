module

public import SubdiffusiveProcess.Lane4.Carriers
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

open MeasureTheory TopologicalSpace Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section
namespace Paper



theorem lane4_neumann_boundary_identity_face_trace
    (n : ℕ) (hn : 1 ≤ n) :
    let Q : Opens (SpatialCoordinates (n + 1)) := unitNeumannCube (n + 1)
    let Qface : Opens (SpatialCoordinates n) := unitNeumannCube n
    let μface : Measure (SpatialCoordinates n) :=
      volume.restrict (Qface : Set (SpatialCoordinates n))
    (htrace :
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
                ((Tr i side v : DomainL2 Qface) : SpatialCoordinates n → ℝ) =ᵐ[
                  volume.restrict (Qface : Set (SpatialCoordinates n))]
                  (fun y => φ (Fin.insertNth i (if side then 1 else 0) y)))) →
    (hdense : Dense ({v : weakSobolevGraph Q |
      ∃ (φ : SpatialCoordinates (n + 1) → ℝ),
        ContDiff ℝ 1 φ ∧
          ((v : SobolevData Q).1 : SpatialCoordinates (n + 1) → ℝ) =ᵐ[
            volume.restrict (Q : Set (SpatialCoordinates (n + 1)))] φ} :
        Set (weakSobolevGraph Q))) →
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
          Tr' = Tr) := by
  dsimp
  intro htrace hdense
  rcases htrace with ⟨Tr, Ct, hCt, hbound, hsmooth⟩
  refine ⟨Tr, Ct, hCt, hbound, ?_, ?_⟩
  · intro φ hφ v hv i side
    exact hsmooth φ hφ v hv i side
  · intro Tr' hTr'
    funext i
    funext side
    apply ContinuousLinearMap.ext
    intro v
    apply congrFun
    apply hdense.denseRange_val.equalizer
      (Tr' i side).continuous (Tr i side).continuous
    funext v
    rcases v with ⟨v, ⟨φ, hφ, hv⟩⟩
    apply MeasureTheory.Lp.ext
    exact (hTr' φ hφ v hv i side).trans (hsmooth φ hφ v hv i side).symm

end Paper
