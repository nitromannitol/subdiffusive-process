module

public import SubdiffusiveProcess.Paper.lem_as_regularity_cell_coercivity

@[expose] public section

/-! Uniform energy decay and root coarse coercivity imply all-depth cell variance decay.
This deterministic step uses the actual coefficient on each cell. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Metric SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal BigOperators
noncomputable section
namespace Paper

/-- All-depth cell Campanato bounds follow from the two uniform scalar controls. -/
theorem lem_as_regularity_neumann_cells {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E) (alpha t : ℝ) (ht0 : 0 ≤ t)
    (he : 0 < 2 + t - 2 * alpha - d) :
    ∀ KE Kell : ℝ, 0 ≤ KE → 0 ≤ Kell → ∃ X : ℝ, 0 < X ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ),
      (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
        (fun _ => (1 / 2 : ℝ)) 1 (min (2 + t - 2 * alpha - d) 1 / 2) 2)⁻¹ ≤ Kell →
    ∀ (v : meanZeroSobolevGraph (unitNeumannCube d)) (Kf : ℝ),
      (∀ c ∈ unitNeumannCube d, ∀ r : ℝ, 0 < r → r ≤ 1 →
        localGradientEnergy
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          (s := Metric.ball c r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤ KE * Kf ^ 2 * r ^ t) →
    ∀ j : ℕ, ∀ kk : Fin d → ℤ, aux_prop_growth_holder_macro_campanato_Adm j kk →
      aux_prop_growth_holder_macro_campanato_var
        (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk)
        ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
        (aux_prop_growth_holder_macro_campanato_side j ^ alpha * (X * Kf)) ^ 2 *
          volume.real (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk) := by
  intro KE Kell hKE hKell
  let e := 2 + t - 2 * alpha - d
  let e' := min e 1
  have he' : 0 < e' := lt_min he zero_lt_one
  have he'e : e' ≤ e := min_le_left _ _
  have he'1 : e' ≤ 1 := min_le_right _ _
  let Cg := (1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))
  have hCg0 : 0 ≤ Cg := by
    have hh : (3 : ℝ) ^ (-e') < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos he')
    dsimp only [Cg]
    exact div_nonneg (by norm_num) (sub_nonneg.mpr hh.le)
  let A := max 1 (P.C ^ 2 * Cg)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAC : P.C ^ 2 * Cg ≤ A := le_max_right _ _
  have hexp : 2 + t = e + 2 * alpha + d := by dsimp only [e]; ring
  refine ⟨1 + A * (KE + Kell), add_pos_of_pos_of_nonneg zero_lt_one (by positivity), ?_⟩
  intro M H om N hroot v Kf hen j kk hkk
  have hseries := aux_lem_as_regularity_cell_coercivity_series E
    (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
    e' he' (he'1.trans (by norm_num))
  set c := aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j kk with hc
  set s := aux_prop_growth_holder_macro_campanato_side j with hsdef
  have hs0 : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos j
  have hs1 : s ≤ 1 := aux_prop_growth_holder_macro_campanato_side_le_one j
  have hcellT : aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk =
      (centeredCube c s hs0 : Set (SpatialCoordinates d)) :=
    (centeredCube_coe_eq_ball c s hs0).symm
  have hQball : (unitNeumannCube d : Set (SpatialCoordinates d)) =
      ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
    rw [unitNeumannCube, centeredCube_coe_eq_ball]
  have hTQ : (centeredCube c s hs0 : Set (SpatialCoordinates d)) ⊆
      (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    rw [← hcellT, hQball]
    exact aux_prop_growth_holder_macro_campanato_cell_subset _ hkk
  have hle : centeredCube c s hs0 ≤ unitNeumannCube d := hTQ
  have hcQ : c ∈ unitNeumannCube d := by
    apply hTQ
    rw [centeredCube_coe_eq_ball]
    exact mem_ball_self (half_pos hs0)
  have hcoef : ∀ᵐ y ∂volume.restrict (centeredCube c s hs0 : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N c hs0).val y =
        (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos).val y := by
    filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M H om N c hs0,
      ae_restrict_of_ae_restrict_of_subset hTQ
        (aux_prop_growth_holder_micro_campanato_coeff_ae M H om N (fun _ => (1 / 2 : ℝ))
          one_pos)] with y h1 h2
    rw [h1, h2]
  have hPc := aux_cor_neumann_source_cell_poincare hd E P c s hs0 hle
    (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (cutoffPositiveCoefficient M H om N c hs0) hcoef
    ⟨(v : SobolevData (unitNeumannCube d)),
      (inf_le_left : meanZeroSobolevGraph (unitNeumannCube d) ≤
        weakSobolevGraph (unitNeumannCube d)) v.property⟩
  have hE1 := hen c hcQ (s / 2) (half_pos hs0) (by linarith only [hs1])
  have hset : Metric.ball c (s / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)) =
      (centeredCube c s hs0 : Set (SpatialCoordinates d)) := by
    rw [← centeredCube_coe_eq_ball c s hs0]; exact Set.inter_eq_left.2 hTQ
  have hE2 : localGradientEnergy
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (s := (centeredCube c s hs0 : Set (SpatialCoordinates d)))
      (centeredCube c s hs0).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤ KE * Kf ^ 2 * (s / 2) ^ t := by
    rw [← aux_cor_neumann_source_energy_congr _ hset
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)]
    exact hE1
  have hlam := aux_cor_neumann_source_lam_cell E M H om N j kk hkk e e' he' he'e he'1 hseries.1
  have hV := aux_prop_growth_holder_macro_campanato_cell_volume (fun _ : Fin d => (1 / 2 : ℝ)) j kk
  rw [hV, hcellT]
  have hfin := aux_cor_neumann_source_cell_alg d _ P.C s _ _ (KE) Kf t e alpha (Kell) Cg A
    hs0 (inv_nonneg.2 (E.lam_pos _ _ _ _ _ _ _ _).le) hKE hKell ht0 hA1 hAC hexp
    hPc hE2 (by
      rw [hseries.2] at hlam
      exact hlam.trans (mul_le_mul_of_nonneg_left hroot hCg0))
  exact hfin
end Paper
