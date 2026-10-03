module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib3_energy_core
public import SubdiffusiveProcess.Paper.prop_growth_holder_macro_campanato
public import SubdiffusiveProcess.Paper.prop_growth_trunc_holder_macro
public import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
public import SubdiffusiveProcess.Paper.in_6_16

@[expose] public section

/-! Stage 3 (calibration): unit-cube macro Campanato (variance) decay for a coefficient with Section-6 frame data at FE level `Lc`
(arbitrary relation of `Lc` to the frame `n`).  Generalises `aux_prop_growth_holder_macro_campanato_core_step`,
`aux_prop_growth_trunc_holder_macro_core_osc` and `..._unit_H1`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section HolderUnit

variable {d : ℕ}

/-- One prefix-good frame, arbitrary FE level `Lc` and reference bounds `hkref`. -/
theorem aux_calib3_holder_unit_core_step (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (alpha : ℝ)
    (hδ : M.delta ≤ Sreg.C⁻¹) (hα : alpha ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (lam Kr : ℝ) (hlam : 0 < lam)
    (hlamA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ cutoffCoefficient M H om N x)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 h1))
    (hb : ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om N z h1) F b u)
    (KP : ℝ≥0) (hKP : ∀ w : killedSobolevGraph (centeredCube z 1 h1),
      ‖(w : SobolevData (centeredCube z 1 h1)).1‖ ≤
        KP * ‖subspaceGradient (killedSobolevGraph (centeredCube z 1 h1)) w‖)
    (Lc : ℕ) (aFin : PositiveCoefficient (centeredCube z 1 h1)) (cFin : ℝ) (hcF : 0 < cFin)
    (hcoef : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      aFin.val y = cFin * (Sreg.cutoffOn Lc (aux_aux_macro_energy_recurrence_relabel N om)
        ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y))
    (hkref : cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) ≤ 2 * Kr ∧
      (cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om))⁻¹ ≤ 2 * Kr)
    (η : ℝ) (hη0 : 0 ≤ η) (hηl : η ≤ lam / 2)
    (hη : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      |aFin.val y - cutoffCoefficient M H om N y| < η)
    (j : ℕ) (hjN : j ≤ N)
    (hjP : (Sreg.prefixLen Lc alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) : ℤ) ≤ j)
    (k : Fin d → ℤ) (hk : aux_prop_growth_holder_macro_campanato_Adm j k) :
    aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k)
        ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ) ≤
      2 * ((Sreg.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha *
        (Real.sqrt 2 * (Real.sqrt (aux_prop_growth_holder_macro_campanato_var
            (centeredCube z 1 h1 : Set (SpatialCoordinates d))
            ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)) +
          KP * (2 * η / lam) * Real.sqrt (aux_aux_macro_energy_recurrence_gradSq
            (u : SobolevData (centeredCube z 1 h1)))) +
          (2 * Cp * Kr * Kf + d * Cφ))) ^ 2 *
        volume.real (aux_prop_growth_holder_macro_campanato_cell z j k)) +
      2 * (KP * (2 * η / lam) * Real.sqrt (aux_aux_macro_energy_recurrence_gradSq
        (u : SobolevData (centeredCube z 1 h1)))) ^ 2 := by
  have hAae := aux_aux_macro_energy_recurrence_coeff_ae M H om N z h1
  have hmem := ae_restrict_mem (μ := volume) (centeredCube z 1 h1).isOpen.measurableSet
  have hAl : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ (cutoffPositiveCoefficient M H om N z h1).val y := by
    filter_upwards [hAae, hmem] with y h1' h2'
    rw [h1']; exact hlamA y (centeredCube_subset_closedCube z h1 h2')
  have hη' : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      |aFin.val y - (cutoffPositiveCoefficient M H om N z h1).val y| ≤ η := by
    filter_upwards [hAae, hη] with y h1' h2'
    rw [h1']; exact h2'.le
  obtain ⟨u', hu'⟩ := aux_aux_macro_energy_recurrence_exists_solution ⟨KP, hKP⟩ aFin F Kf hFm hFb b
  have hL2 := aux_prop_growth_holder_macro_campanato_trunc_l2 _ aFin lam η hlam hη0 hAl hη' hηl KP
    hKP F b u u' hu hu'
  have hδ0 : 0 ≤ (KP : ℝ) * (2 * η / lam) * Real.sqrt (aux_aux_macro_energy_recurrence_gradSq
      (u : SobolevData (centeredCube z 1 h1))) := by positivity
  have hQfin : volume (centeredCube z 1 h1 : Set (SpatialCoordinates d)) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hQpos : 0 < volume.real (centeredCube z 1 h1 : Set (SpatialCoordinates d)) :=
    centeredCube_volume_pos z h1
  have hRo := aux_prop_growth_holder_macro_campanato_root_near hQfin hQpos (Lp.memLp _)
    (Lp.memLp _) hδ0 hL2
  have hFOi := hFO M Sreg Lc (aux_aux_macro_energy_recurrence_relabel N om) alpha hδ hα N z
    h1 hR aFin cFin hcF hcoef F Kf hKf hFm hFb φ Cφ hφ hCφ b u' hb hu' _ hRo j hjN hjP k hk
  have href := hkref
  have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
  have hsa : 0 ≤ aux_prop_growth_holder_macro_campanato_side j ^ alpha :=
    Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos j).le _
  have hcr := mul_pos hcF (Sreg.refAvg_pos Lc N ((3 : ℝ) ^ N • z)
    (aux_aux_macro_energy_recurrence_relabel N om))
  have hB := aux_prop_growth_holder_macro_campanato_src_bound Sreg.C_pos.le hsa
    (aux_prop_growth_holder_macro_campanato_cell_volume_pos z j k).le hCp hKf hcr
    (by positivity) (by positivity) href.2 hFOi
  exact aux_prop_growth_holder_macro_campanato_cell_near
    (aux_prop_growth_holder_macro_campanato_cell_subset z hk) hQfin
    (aux_prop_growth_holder_macro_campanato_cell_volume_ne_top z j k)
    (aux_prop_growth_holder_macro_campanato_cell_volume_pos z j k) (Lp.memLp _) (Lp.memLp _) hL2 hB

/-- Root oscillation at frame `N`, FE level `Lc`. -/
theorem aux_calib3_holder_unit_core_osc (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (alpha : ℝ)
    (hδ : M.delta ≤ Sreg.C⁻¹) (hα : alpha ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (lam Kr : ℝ) (hlam : 0 < lam)
    (hlamA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ cutoffCoefficient M H om N x)
    (Lc : ℕ)
    (hFEd : ∃ cFin : ℝ, 0 < cFin ∧
      (∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M H om N z h1).val y =
          cFin * (Sreg.cutoffOn Lc (aux_aux_macro_energy_recurrence_relabel N om)
            ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y)) ∧
      cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) ≤ 2 * Kr ∧
      (cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om))⁻¹ ≤ 2 * Kr)
    (P0 : ℕ) (hpre0 : Sreg.prefixLen Lc alpha N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) ≤ P0)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 h1))
    (hb : ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om N z h1) F b u)
    (j : ℕ) (hjN : j ≤ N) (hjP : P0 ≤ j)
    (k : Fin d → ℤ) (hk : aux_prop_growth_holder_macro_campanato_Adm j k) :
    aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z j k)
        ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ) ≤
      (2 * Sreg.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha *
        (Real.sqrt (aux_prop_growth_holder_macro_campanato_var
            (centeredCube z 1 h1 : Set (SpatialCoordinates d))
            ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)) +
          (2 * Cp * Kr * Kf + d * Cφ))) ^ 2 *
        volume.real (aux_prop_growth_holder_macro_campanato_cell z j k) := by
  obtain ⟨KP, hKP⟩ := aux_aux_macro_moment_bank_killed_poincare hd z 1 h1
  have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
  have hKr0 : 0 ≤ Kr := by
    obtain ⟨cF, hcF, -, hk1, -⟩ := hFEd
    have := mul_pos hcF (Sreg.refAvg_pos Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om))
    linarith
  have hr0 : 0 ≤ 2 * Cp * Kr * Kf + d * Cφ := by positivity
  have hsa : 0 ≤ aux_prop_growth_holder_macro_campanato_side j ^ alpha :=
    Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos j).le _
  have hV0 := (aux_prop_growth_holder_macro_campanato_cell_volume_pos z j k).le
  have ho0 : 0 ≤ Real.sqrt (aux_prop_growth_holder_macro_campanato_var
      (centeredCube z 1 h1 : Set (SpatialCoordinates d))
      ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)) := Real.sqrt_nonneg _
  have hG0 : 0 ≤ Real.sqrt (aux_aux_macro_energy_recurrence_gradSq
      (u : SobolevData (centeredCube z 1 h1))) := Real.sqrt_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 4 * Sreg.C ^ 2 * (aux_prop_growth_holder_macro_campanato_side j ^ alpha) ^ 2 *
      (2 * (Real.sqrt (aux_prop_growth_holder_macro_campanato_var
            (centeredCube z 1 h1 : Set (SpatialCoordinates d))
            ((u : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)) +
          (2 * Cp * Kr * Kf + d * Cφ)) + 1) *
        volume.real (aux_prop_growth_holder_macro_campanato_cell z j k) + 3 := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  obtain ⟨hη0, hηl, hδle⟩ := aux_prop_growth_holder_macro_campanato_eta_choice KP.2 hG0 hlam
    (lt_min one_pos (div_pos hε hE0) : 0 < min 1 (ε / E))
  obtain ⟨cFin, hcF, hcoef, hkref⟩ := hFEd
  have hηae : ∀ η : ℝ, 0 < η →
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        |(cutoffPositiveCoefficient M H om N z h1).val y - cutoffCoefficient M H om N y| < η := by
    intro η hη
    filter_upwards [aux_aux_macro_energy_recurrence_coeff_ae M H om N z h1] with y hy
    rw [hy, sub_self, abs_zero]
    exact hη
  have hjP' : (Sreg.prefixLen Lc alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) : ℤ) ≤ j := by
    have : Sreg.prefixLen Lc alpha N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) ≤ j := hpre0.trans hjP
    exact_mod_cast this
  have hstep := aux_calib3_holder_unit_core_step hd Cp hCp hFO M Sreg alpha hδ hα H
    om N z h1 hR lam Kr hlam hlamA F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu KP hKP Lc
    (cutoffPositiveCoefficient M H om N z h1) cFin hcF hcoef hkref _ hη0.le hηl (hηae _ hη0) j hjN hjP'
    k hk
  have hδ0 : 0 ≤ (KP : ℝ) * (2 * min (lam / 2) (min 1 (ε / E) * lam / (2 * (KP * Real.sqrt
      (aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) + 1))) / lam) *
      Real.sqrt (aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) := by
    have := hη0.le
    positivity
  have hfin := aux_prop_growth_holder_macro_campanato_core_arith Sreg.C_pos.le hsa ho0 hr0 hV0 hδ0
    (hδle.trans (min_le_left _ _)) hε (by rw [← hE]; exact hδle.trans (min_le_right _ _)) hr0 le_rfl
    hstep
  calc _ ≤ _ := hfin
    _ = _ := by ring

/-- Variance decay at all admissible scales `P0 ≤ j ≤ n` (unit cube). -/
theorem calib3_holder_unit (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg' : in_6_16 d M') (alphaM alpha : ℝ)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hα : alphaM ∈ Sreg'.alphaRange) (hαα : alpha ≤ alphaM)
    (H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (om' : BilateralField d)
    (z' : SpatialCoordinates d) (n P0 : ℕ) (hR : (0 : ℝ) < 3 ^ n)
    (Rs : ℝ)
    (Lc : ℕ)
    (hFEd : ∃ cFin : ℝ, 0 < cFin ∧
      (∀ᵐ y ∂volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M' H' om' n z' one_pos).val y =
          cFin * (Sreg'.cutoffOn Lc (aux_aux_macro_energy_recurrence_relabel n om')
            ((3 : ℝ) ^ n • z') (3 ^ n) hR).val ((3 : ℝ) ^ n • y)) ∧
      cFin * Sreg'.refAvg Lc n ((3 : ℝ) ^ n • z') (aux_aux_macro_energy_recurrence_relabel n om') ≤ 2 * Rs ∧
      (cFin * Sreg'.refAvg Lc n ((3 : ℝ) ^ n • z') (aux_aux_macro_energy_recurrence_relabel n om'))⁻¹ ≤ 2 * Rs)
    (hpre0 : Sreg'.prefixLen Lc alphaM n ((3 : ℝ) ^ n • z')
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F
      (volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
      |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z' 1 one_pos : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b v : weakSobolevGraph (centeredCube z' 1 one_pos))
    (hb : ((b : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))] φ)
    (hv : SolvesDirichlet (cutoffPositiveCoefficient M' H' om' n z' one_pos) F b v) :
    ∀ j : ℕ, P0 ≤ j → j ≤ n → ∀ k : Fin d → ℤ,
      aux_prop_growth_holder_macro_campanato_Adm j k →
      aux_prop_growth_holder_macro_campanato_var (aux_prop_growth_holder_macro_campanato_cell z' j k)
          ((v : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ) ≤
        (2 * Sreg'.C * aux_prop_growth_holder_macro_campanato_side j ^ alpha *
          (Real.sqrt (aux_prop_growth_holder_macro_campanato_var
              (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))
              ((v : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ)) +
            (2 * Cp * Rs * Kf + d * Cφ))) ^ 2 *
          volume.real (aux_prop_growth_holder_macro_campanato_cell z' j k) := by
  intro j hjP hjn k hk
  obtain ⟨lam, Λ, hlam, hlamA, -⟩ :=
    aux_aux_macro_energy_recurrence_cutoffCoefficient_bounds M' H' om' n z' one_pos
  have hcore := aux_calib3_holder_unit_core_osc hd Cp hCp hFO M' Sreg' alphaM hδC
    hα H' om' n z' one_pos hR lam Rs hlam hlamA Lc hFEd P0 hpre0
    F Kf hKf hFm hFb φ Cφ hφ hCφ b v hb hv j hjn hjP k hk
  refine hcore.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ?_ ?_ 2)
    (aux_prop_growth_holder_macro_campanato_cell_volume_pos z' j k).le)
  · have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
    have hRs0 : 0 ≤ Rs := by
      obtain ⟨cF, hcF, -, hk1, -⟩ := hFEd
      have := mul_pos hcF (Sreg'.refAvg_pos Lc n ((3 : ℝ) ^ n • z') (aux_aux_macro_energy_recurrence_relabel n om'))
      linarith
    have := Sreg'.C_pos
    have := Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos j).le alphaM
    positivity
  · have hsle : aux_prop_growth_holder_macro_campanato_side j ^ alphaM ≤
        aux_prop_growth_holder_macro_campanato_side j ^ alpha :=
      Real.rpow_le_rpow_of_exponent_ge (aux_prop_growth_holder_macro_campanato_side_pos j)
        (aux_prop_growth_holder_macro_campanato_side_le_one j) hαα
    have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
    have hRs0 : 0 ≤ Rs := by
      obtain ⟨cF, hcF, -, hk1, -⟩ := hFEd
      have := mul_pos hcF (Sreg'.refAvg_pos Lc n ((3 : ℝ) ^ n • z') (aux_aux_macro_energy_recurrence_relabel n om'))
      linarith
    have hX : 0 ≤ Real.sqrt (aux_prop_growth_holder_macro_campanato_var
        (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))
        ((v : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ)) +
          (2 * Cp * Rs * Kf + d * Cφ) := by positivity
    have := Sreg'.C_pos
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsle (by positivity)) hX

end HolderUnit

end Paper
