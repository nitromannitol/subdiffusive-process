import SubdiffusiveProcess.Sobolev.HolderBoundaryExtension
import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Geometry.TriadicResidual

/-!
# Central trace from a concentric grid

This file turns a supplied compatible grid witness into the trace witness on its
middle triadic cell. It makes no additional existence or energy claim.
-/

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- The middle triadic child of a triple cube is exactly its concentric inner cube. -/
theorem centralTriadicCell_eq_centeredCube {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    oddGridCell z (3 * r) (mul_pos (by norm_num) hr) (triadicHalf 1) (fun _ => 1) =
      centeredCube z r hr := by
  have hhalf : triadicHalf 1 = 1 := rfl
  rw [hhalf]
  have hcenter : oddGridCenter z (3 * r) 1 (fun _ => (1 : Fin 3)) = z := by
    funext i
    simp only [oddGridCenter, Fin.val_one, Nat.cast_one, sub_self, zero_mul, add_zero]
  have hside : (3 * r) / (2 * ((1 : ℕ) : ℝ) + 1) = r := by
    norm_num
  ext x
  simp only [oddGridCell, centeredCube]
  rw [hcenter, hside]

/-- A compatible concentric grid witness gives a local trace witness with the central cell's exact seminorm cost. -/
theorem exists_local_trace_of_concentric_grid
    {d : ℕ} [NeZero d]
    (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : DirichletForm.EnergyMeasure E)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta : ℝ) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (C : ℝ) (Lam : OddGridIndex d (triadicHalf 1) → ℝ)
    (hGrid : ∀ g : SpatialCoordinates d → ℝ,
      ContinuousOn g (closure (centeredCube z (3 * r) (mul_pos (by norm_num) hr) : Set (SpatialCoordinates d))) →
      IsHolderOn beta (closure (centeredCube z (3 * r) (mul_pos (by norm_num) hr) : Set (SpatialCoordinates d))) g →
      (∀ x ∈ frontier (centeredCube z (3 * r) (mul_pos (by norm_num) hr) : Set (SpatialCoordinates d)), g x = 0) →
      ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
        (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
        ∀ k : OddGridIndex d (triadicHalf 1),
          (∀ x ∈ frontier (oddGridCell z (3 * r) (mul_pos (by norm_num) hr) (triadicHalf 1) k :
            Set (SpatialCoordinates d)), V x = g x) ∧
          (Gamma.measure v (oddGridCell z (3 * r) (mul_pos (by norm_num) hr) (triadicHalf 1) k :
            Set (SpatialCoordinates d))).toReal ≤
            C * Lam k * r ^ ((d : ℝ) - 2) *
              (r ^ beta * holderSeminorm beta
                (frontier (oddGridCell z (3 * r) (mul_pos (by norm_num) hr) (triadicHalf 1) k :
                  Set (SpatialCoordinates d))) g) ^ 2)
    (b : SpatialCoordinates d → ℝ)
    (hbc : ContinuousOn b (frontier (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hbh : IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b) :
    ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
      v ∈ E.domain ∧ ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
      (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = b x) ∧
      (Gamma.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        C * Lam (fun _ => 1) * r ^ ((d : ℝ) - 2) *
          (r ^ beta * holderSeminorm beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b) ^ 2 := by
  have hR : r < 3 * r := by
    linarith only [hr]
  obtain ⟨g, hgcont, hgholder, hgb, hgzero⟩ :=
    exists_holder_concentric_extension z r (3 * r) hR b hbc beta hb hb1 hbh
  have hgcontOn :
      ContinuousOn g (closure (centeredCube z (3 * r) (mul_pos (by norm_num) hr) :
        Set (SpatialCoordinates d))) := hgcont.continuousOn
  have hgholderOn :
      Lane4.IsHolderOn beta
        (closure (centeredCube z (3 * r) (mul_pos (by norm_num) hr) :
          Set (SpatialCoordinates d))) g := by
    unfold Lane4.IsHolderOn at hgholder ⊢
    apply hgholder.mono
    intro q hq
    rcases hq with ⟨x, hx, y, hy, hxy, hq⟩
    exact ⟨x, Set.mem_univ x, y, Set.mem_univ y, hxy, hq⟩
  obtain ⟨v, V, hv, hVcont, hVae, hVcell⟩ := hGrid g hgcontOn hgholderOn hgzero
  have hVmid := hVcell (fun _ => 1)
  have htrace :
      ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), V x = b x := by
    intro x hx
    have hxmid :
        x ∈ frontier (oddGridCell z (3 * r) (mul_pos (by norm_num) hr) (triadicHalf 1)
          (fun _ => 1) : Set (SpatialCoordinates d)) := by
      rw [centralTriadicCell_eq_centeredCube z r hr]
      exact hx
    calc
      V x = g x := hVmid.1 x hxmid
      _ = b x := hgb hx
  have hgbCube : EqOn g b
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) := hgb
  have hseminorm :
      Lane4.holderSeminorm beta
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g =
        Lane4.holderSeminorm beta
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b := by
    unfold Lane4.holderSeminorm
    rw [holderRatioSet_congr hgbCube]
  have hcost := hVmid.2
  have hcost' :
      (Gamma.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        C * Lam (fun _ => 1) * r ^ ((d : ℝ) - 2) *
          (r ^ beta * Lane4.holderSeminorm beta
            (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b) ^ 2 := by
    simpa only [centralTriadicCell_eq_centeredCube z r hr, hseminorm] using hcost
  exact ⟨v, V, hv, hVcont, hVae, htrace, hcost'⟩
end SubdiffusiveProcess
