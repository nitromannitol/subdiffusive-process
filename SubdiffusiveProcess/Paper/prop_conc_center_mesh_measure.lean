module

public import SubdiffusiveProcess.Paper.prop_conc_boundary_mesh
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Sobolev.NativeAffineEnergyMeasure

@[expose] public section

/-! The central observation cell of a harmonic mesh has the actual affine energy measure.
The identity restricts the padded-cube measure to the cell and makes no claim about its total mass. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff BigOperators
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- The central mesh energy measure equals the actual affine graph energy measure on the cell. -/
theorem prop_conc_center_mesh_measure
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (a : ℕ → SpatialCoordinates d → ℝ)
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (hAC : ∀ n, (aC n).val =ᵐ[volume.restrict
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] a n)
    (beta : SpatialCoordinates d → ℝ)
    (betaH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hbetaH : betaH.toFun = beta) (t alpha : ℝ)
    (Mesh : aux_prop_conc_boundary_mesh_Data z (3 * r) h3r S a aC beta betaH 1 t alpha)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube z r hr),
      ‖v.val.1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) v‖)
    (aq : ℕ → PositiveCoefficient (centeredCube z r hr))
    (haq : ∀ n, (aq n).val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] a n)
    (p : Fin d → ℝ)
    (hbeta : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), beta x = ∑ i, p i * x i)
    (n : ℕ) :
    ((volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal ((aC n).val x * ∑ i : Fin d, ((Mesh.uS n).val.2 i x) ^ 2))).restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)) =
    (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
      (fun x => ENNReal.ofReal ((aq n).val x * ∑ i : Fin d,
        ((dirichletMinimizer (killedResponseSpace hP) (aq n)
          (affineSobolev (centeredCube_isBounded z hr) p 0)).val.2 i x) ^ 2)) := by
  let k0 : OddGridIndex d (triadicHalf 1) := fun _ => ⟨triadicHalf 1, by norm_num [triadicHalf]⟩
  have hcell : (oddGridCell z (3 * r) h3r (triadicHalf 1) k0 : Set (SpatialCoordinates d)) =
      centeredCube z r hr := aux_prop_boundary_center_cell z r hr h3r
  have hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith only [hr])
  have hharm := aux_prop_boundary_harm_transport (a n) _ _ _ (Mesh.u n) _
    (oddGridCell_subset z h3r (triadicHalf 1) k0) (centeredCube z r hr).isOpen hqQ hcell
    (Mesh.harmonic n k0)
  have htrace := aux_prop_boundary_trace_transport _ _ _ (Mesh.u n) betaH _
    (oddGridCell_subset z h3r (triadicHalf 1) k0) (centeredCube z r hr).isOpen hqQ hcell
    (Mesh.trace n k0)
  apply padded_native_affine_energyMeasure_restrict hqQ (centeredCube_isBounded z hr) hP
    (aC n) (aq n) (a n) (hAC n) (haq n) (Mesh.u n) (Mesh.uS n).val (Mesh.rep n)
    (betaH.restrict (centeredCube z r hr).isOpen hqQ) p ?_ htrace hharm
  filter_upwards [ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx
  change betaH.toFun x = _
  rw [hbetaH]
  exact hbeta x hx

end
end SubdiffusiveProcess.Paper
