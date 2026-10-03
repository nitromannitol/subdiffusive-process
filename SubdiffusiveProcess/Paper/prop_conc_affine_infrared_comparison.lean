module

public import SubdiffusiveProcess.Paper.lem_prefix_limit_atom_extraction
public import SubdiffusiveProcess.Main.CutoffInfraredFactor

@[expose] public section

/-! # Infrared comparison for affine cell responses

Bounded infrared potentials compare the actual affine response with the native
unit-cell response. This supplies the total-energy part of a growth bound only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology BigOperators

namespace Paper
noncomputable section

/-- A bounded infrared field gives two-sided pointwise coefficient comparison on a cube. -/
theorem aux_prop_conc_affine_infrared_comparison_coefficients
    {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (S : ℝ)
    (hS : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), |H om x| ≤ S) :
    (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      Real.exp (-S) * (cutoffPositiveCoefficient M (fun _ => 0) om N z hr).val x ≤
        (cutoffPositiveCoefficient M H om N z hr).val x) ∧
    (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N z hr).val x ≤
        Real.exp S * (cutoffPositiveCoefficient M (fun _ => 0) om N z hr).val x) := by
  have hpair : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      Real.exp (-S) * (cutoffPositiveCoefficient M (fun _ => 0) om N z hr).val x ≤
        (cutoffPositiveCoefficient M H om N z hr).val x ∧
      (cutoffPositiveCoefficient M H om N z hr).val x ≤
        Real.exp S * (cutoffPositiveCoefficient M (fun _ => 0) om N z hr).val x := by
    filter_upwards [aux_aux_macro_energy_recurrence_coeff_ae M H om N z hr,
      aux_aux_macro_energy_recurrence_coeff_ae M (fun _ => 0) om N z hr,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hxH hx0 hx
    rw [hxH, hx0, cutoffCoefficient_infrared_factor M H om N x]
    have habs := abs_le.mp (hS x (centeredCube_subset_closedCube z hr hx))
    have ha0 := (cutoffCoefficient_pos M (fun _ => 0) om N x).le
    exact ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr habs.1) ha0,
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr habs.2) ha0⟩
  exact ⟨hpair.mono fun _ h => h.1, hpair.mono fun _ h => h.2⟩

/-- The affine energy with infrared field is controlled by the native unit-cell response. -/
theorem prop_conc_affine_infrared_comparison
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (u : Fin d → ℝ) (S : ℝ)
    (hS : ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      |H om x| ≤ S)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖) :
    affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP
      (cutoffPositiveCoefficient M H om N 0 one_pos) u ≤
      Real.exp S * (2 * volume.real
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) *
          ∑ i : Fin d, (u i) ^ 2) * aux_lem_prefix_limit_atom_extraction_Rf M N om := by
  obtain ⟨hlo, hhi⟩ := aux_prop_conc_affine_infrared_comparison_coefficients M H om N 0 one_pos S hS
  have hresp := (dirichletResponse_exp_comparison (killedResponseSpace hP)
    (cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos)
    (cutoffPositiveCoefficient M H om N 0 one_pos)
    (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0) S hlo hhi).2
  change affineDirichletResponse _ hP _ u ≤ Real.exp S * affineDirichletResponse _ hP _ u at hresp
  have heq : affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
      hP (cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos) u =
      aux_lem_prefix_limit_atom_extraction_Dz M u N om := by
    unfold aux_lem_prefix_limit_atom_extraction_Dz aux_lem_prefix_limit_atom_extraction_D
    rw [aux_lem_prefix_limit_atom_extraction_coef_eq]
  rw [heq] at hresp
  exact (hresp.trans (mul_le_mul_of_nonneg_left
    (aux_lem_prefix_limit_atom_extraction_Dz_le M u N om) (Real.exp_pos S).le)).trans_eq
      (by ring)

end
end Paper
