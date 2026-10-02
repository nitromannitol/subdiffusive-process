import SubdiffusiveProcess.Paper.prop_conc_affine_infrared_comparison
import SubdiffusiveProcess.Paper.prop_conc_affine_cutoff_growth

/-! # Affine growth above the cutoff scale

The pathwise Campanato estimate controls actual affine minimizers in terms of
one regularity prefix, the infrared supremum, and the native response. No
microscopic estimate or concentration conclusion is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology BigOperators

namespace Paper
noncomputable section

/-- The native response and infrared multiplier give the two Campanato input bounds. -/
theorem aux_prop_conc_affine_macro_bound_inputs
    {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N P0 : ℕ) (t : ℝ) (u : Fin d → ℝ)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖) :
    let S := ‖(H om).restrict (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖
    let cu := 2 * volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) *
        ∑ i : Fin d, (u i) ^ 2
    let Cphi := max 1 (c2Norm
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => affineSlope u x + 0))
    let K := (3 : ℝ) ^ (t * (P0 : ℝ)) * Real.exp S *
      (1 + cu * aux_lem_prefix_limit_atom_extraction_Rf M N om)
    (∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      (3 : ℝ) ^ (t * (P0 : ℝ)) * Real.exp (|H om x|) ≤ K) ∧
    (3 : ℝ) ^ (t * (P0 : ℝ)) * affineDirichletResponse
      (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP
      (cutoffPositiveCoefficient M H om N 0 one_pos) u ≤ K * (0 + Cphi) ^ 2 := by
  dsimp only
  let S := ‖(H om).restrict (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖
  let cu := 2 * volume.real
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) *
      ∑ i : Fin d, (u i) ^ 2
  let Cphi := max 1 (c2Norm
    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
    (fun x => affineSlope u x + 0))
  let X := (3 : ℝ) ^ (t * (P0 : ℝ))
  have hX : 0 ≤ X := Real.rpow_nonneg (by norm_num) _
  have hcu : 0 ≤ cu := mul_nonneg (mul_nonneg (by norm_num) measureReal_nonneg)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hR : 0 ≤ aux_lem_prefix_limit_atom_extraction_Rf M N om :=
    aux_lem_prefix_limit_atom_extraction_eval_nonneg _
  have hB : 0 ≤ cu * aux_lem_prefix_limit_atom_extraction_Rf M N om := mul_nonneg hcu hR
  have hphi : 1 ≤ (0 + Cphi) ^ 2 := by
    have hc : 1 ≤ Cphi := le_max_left _ _
    nlinarith only [hc]
  have hS : ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      |H om x| ≤ S := aux_lem_prefix_limit_atom_extraction_restrict_bound _ _
  constructor
  · intro x hx
    calc
      X * Real.exp (|H om x|) ≤ X * Real.exp S :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hS x hx)) hX
      _ ≤ X * Real.exp S * (1 + cu * aux_lem_prefix_limit_atom_extraction_Rf M N om) :=
        le_mul_of_one_le_right (mul_nonneg hX (Real.exp_pos _).le) (by linarith only [hB])
  · have hresponse := prop_conc_affine_infrared_comparison M H om N u S hS hP
    calc
      X * affineDirichletResponse _ hP _ u ≤
          X * (Real.exp S * cu * aux_lem_prefix_limit_atom_extraction_Rf M N om) :=
        mul_le_mul_of_nonneg_left hresponse hX
      _ ≤ X * Real.exp S * (1 + cu * aux_lem_prefix_limit_atom_extraction_Rf M N om) := by
        nlinarith only [mul_nonneg hX (Real.exp_pos S).le]
      _ ≤ (X * Real.exp S * (1 + cu * aux_lem_prefix_limit_atom_extraction_Rf M N om)) *
          (0 + Cphi) ^ 2 :=
        le_mul_of_one_le_right
          (mul_nonneg (mul_nonneg hX (Real.exp_pos _).le) (by linarith only [hB])) hphi

/-- Campanato controls the actual affine minimizer at every radius above the cutoff wavelength. -/
theorem prop_conc_affine_macro_bound
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (hdelta : M.delta ≤ Sreg.C⁻¹) (halpha : 1 - ((d : ℝ) - t) / 4 ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (hom : Tendsto (infraredPartialSum om) atTop (𝓝 (H om)))
    (N P0 : ℕ)
    (hpre : ∀ L0 : ℕ, ∃ L' : ℕ, L0 ≤ L' ∧
      Sreg.prefixLen (N + L') (1 - ((d : ℝ) - t) / 4) N ((3 : ℝ) ^ N • (0 : SpatialCoordinates d))
        (aux_aux_macro_energy_recurrence_relabel N om) ≤ P0)
    (u : Fin d → ℝ)
    (hP : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖)
    (x : SpatialCoordinates d) (rho : ℝ) (hx : x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hcutoff : (3 : ℝ) ^ (-(N : ℤ)) ≤ rho) :
    let a := cutoffPositiveCoefficient M H om N 0 one_pos
    let b := affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0
    let S := ‖(H om).restrict (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖
    let cu := 2 * volume.real
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) *
        ∑ i : Fin d, (u i) ^ 2
    let Cphi := max 1 (c2Norm
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => affineSlope u x + 0))
    let K := (3 : ℝ) ^ (t * (P0 : ℝ)) * Real.exp S *
      (1 + cu * aux_lem_prefix_limit_atom_extraction_Rf M N om)
    localGradientEnergy a
      (s := Metric.ball x rho ∩ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
      (Metric.isOpen_ball.measurableSet.inter (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet)
      (sobolevGradient (dirichletMinimizer (killedResponseSpace hP) a b).val) ≤
        2 * aux_aux_macro_energy_recurrence_Z Sreg.C Cp t d * rho ^ t * K * (0 + Cphi) ^ 2 := by
  obtain ⟨hKref, hKsrc⟩ := aux_prop_conc_affine_macro_bound_inputs M H om N P0 t u hP
  apply aux_prop_growth_macro_energy_unit_bound hd Cp hFE M Sreg t ht htd hdelta halpha
    H om hom 0 N P0 hpre _ hKref 0 0 le_rfl aemeasurable_const
    (Eventually.of_forall fun _ => by rw [Pi.zero_apply, abs_zero])
    (fun x => affineSlope u x + 0) _ ((affineSlope u).contDiff.add contDiff_const)
    (le_max_right _ _) _ _
    (affineL2_coeFn (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0)
    (aux_prop_conc_affine_cutoff_growth_solves _ hP _ u) hKsrc x rho hx hrho hrho1 hcutoff

end
end Paper
