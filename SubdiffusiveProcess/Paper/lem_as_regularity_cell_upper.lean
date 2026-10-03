module

public import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative
public import SubdiffusiveProcess.Paper.cor_neumann_source
public import SubdiffusiveProcess.Paper.aux_macro_moment_bank

@[expose] public section

/-! Every admissible triadic cell inherits upper coarse ellipticity from the unit root.
This is a deterministic ancestor comparison and asserts no probabilistic estimate. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess SubdiffusiveProcess.Lane4
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch02
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- Cell upper ellipticity is controlled by a weaker root multiscale norm. -/
theorem lem_as_regularity_cell_upper {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d,ℝ)) (omega : BilateralField d) (N : ℕ)
    (s e : ℝ) (he : 0 < e) (hes : e < s) (hs1 : s ≤ 1)
    (j : ℕ) (k : Fin d → ℤ) (hk : aux_prop_growth_holder_macro_campanato_Adm j k) :
    let z := aux_prop_growth_holder_macro_campanato_center (fun _ => (1/2:ℝ)) j k
    let r := aux_prop_growth_holder_macro_campanato_side j
    E.Lam z r (aux_prop_growth_holder_macro_campanato_side_pos j)
      (cutoffPositiveCoefficient M H omega N z (aux_prop_growth_holder_macro_campanato_side_pos j)) z r s 2 ≤
      (Ch02.geometricDiscount s 2/Ch02.geometricDiscount e 2)*
        (1-(3:ℝ)^(-2*(s-e)))⁻¹*(3:ℝ)^(2*e*j)*
        E.Lam (fun _ => (1/2:ℝ)) 1 one_pos
          (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos)
          (fun _ => (1/2:ℝ)) 1 e 2 := by
  intro z r
  have hr : 0 < r := aux_prop_growth_holder_macro_campanato_side_pos j
  have hsub : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ (unitNeumannCube d : Set (SpatialCoordinates d)) :=
    aux_prop_growth_holder_macro_campanato_cell_subset (fun _ => (1/2:ℝ)) hk
  have hrepV := (cutoffPositiveCoefficient_representative M H omega N z hr).2.2.2
  have hrepQ := (cutoffPositiveCoefficient_representative M H omega N (fun _ => (1/2:ℝ)) one_pos).2.2.2
  have heq : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H omega N z hr).val x =
        (cutoffPositiveCoefficient M H omega N (fun _ => (1/2:ℝ)) one_pos).val x := by
    filter_upwards [hrepV,ae_restrict_of_ae_restrict_of_subset hsub hrepQ] with x hx hy
    exact hx.trans hy.symm
  have hdesc : dilateCube (-(j:ℤ)) (translateCube k (originCube d 0)) ∈
      descendantsAtScale (originCube d 0) ((originCube d 0).scale-(j:ℤ)) := by
    have hzero : originCube d 0 ∈ descendantsAtScale (originCube d 0) (-(0:ℤ)) := by
      change originCube d 0 ∈ descendantsAtScale (originCube d 0) (originCube d 0).scale
      rw [descendantsAtScale_self]
      exact Finset.mem_singleton_self _
    have hh := aux_cor_neumann_source_desc_compose hk hzero
    simpa only [Nat.add_zero,pow_zero,one_mul,originCube,translateCube,dilateCube,
      Pi.zero_apply,add_zero,zero_add] using hh
  exact aux_aux_macro_moment_bank_Lam_ancestor E z r hr _ (fun _ => (1/2:ℝ)) 1 one_pos _
    z r hr (fun _ => (1/2:ℝ)) 1 one_pos subset_rfl subset_rfl j k
    (by dsimp only [r,aux_prop_growth_holder_macro_campanato_side]; rw [mul_inv_cancel₀ (by positivity)])
    (fun i => rfl) hdesc heq s e he hes hs1

end Paper
