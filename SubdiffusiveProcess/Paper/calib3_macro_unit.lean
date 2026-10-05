module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib3_energy_core
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
public import SubdiffusiveProcess.Paper.in_6_16

@[expose] public section

/-! Stage 3 (calibration): unit-cube macro-energy growth `ρ^{t1}` for a coefficient with Section-6 frame data at FE level `Lc`
(arbitrary relation of `Lc` to the frame `n`).  Generalises `aux_prop_growth_trunc_macro_energy_recurrence_om` and `..._unit_bound`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise Distributions
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Recurrence in the radius from the one-centre estimate (`eq:mfd-macro`), FE level `Lc`. -/
theorem aux_calib3_macro_unit_recurrence {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg : in_6_16 d M)
    (hchild : aux_aux_macro_energy_recurrence_DensityChild Sreg) (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδ : M.delta ≤ Sreg.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (N : ℕ) (hR : (0 : ℝ) < 3 ^ N)
    (Kr : ℝ) (Lc : ℕ)
    (hFEd : ∃ cFin : ℝ, 0 < cFin ∧
      (∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M H om N z h1).val y =
          cFin * (Sreg.cutoffOn Lc (aux_aux_macro_energy_recurrence_relabel N om)
            ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y)) ∧
      cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) ≤ 2 * Kr ∧
      (cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om))⁻¹ ≤ 2 * Kr)
    (P0 : ℕ) (hpre0 : Sreg.prefixLen Lc (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) ≤ P0)
    (Kmac : ℝ)
    (hKref : (3 : ℝ) ^ (t1 * (P0 : ℝ)) * Kr ≤ Kmac)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 h1))
    (hb : ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om N z h1) F b u)
    (hKsrc : (3 : ℝ) ^ (t1 * (P0 : ℝ)) *
      sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z h1)
        (u : SobolevData (centeredCube z 1 h1)) (u : SobolevData (centeredCube z 1 h1)) ≤
      Kmac * (Kf + Cφ) ^ 2)
    (x : SpatialCoordinates d) (ρ R : ℝ)
    (hx : x ∈ (centeredCube z 1 h1 : Set (SpatialCoordinates d))) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hR1 : R ≤ 1) (hρN : (3 : ℝ) ^ (-(N : ℤ)) ≤ ρ) :
    localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
        (s := Metric.ball x ρ ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) ≤
      aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d * ((ρ / R) ^ t1 *
        localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
          (s := Metric.ball x R ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) +
        ρ ^ t1 * Kmac * (Kf + Cφ) ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 < t1 := lt_of_le_of_lt (by linarith only [hdR] : (0 : ℝ) ≤ (d : ℝ) - 1) ht1
  have h3P : 1 ≤ (3 : ℝ) ^ (t1 * (P0 : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg ht10.le (Nat.cast_nonneg _))
  have hfA0 := sobolevCoefficientForm_nonneg (cutoffPositiveCoefficient M H om N z h1)
    (u : SobolevData (centeredCube z 1 h1))
  have hfA : sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z h1)
      (u : SobolevData (centeredCube z 1 h1)) (u : SobolevData (centeredCube z 1 h1)) ≤
      Kmac * (Kf + Cφ) ^ 2 := (le_mul_of_one_le_left hfA0 h3P).trans hKsrc
  have hKr0 : 0 < Kr := by
    obtain ⟨cF, hcF, -, hk1, -⟩ := hFEd
    have := mul_pos hcF (Sreg.refAvg_pos Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om))
    linarith
  have hKrK : Kr ≤ Kmac := (le_mul_of_one_le_left hKr0.le h3P).trans hKref
  have hFEd' : ∃ cFin : ℝ, 0 < cFin ∧
      (∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M H om N z h1).val y =
          cFin * (Sreg.cutoffOn Lc (aux_aux_macro_energy_recurrence_relabel N om)
            ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y)) ∧
      cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) ≤ 2 * Kmac ∧
      (cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om))⁻¹ ≤ 2 * Kmac := by
    obtain ⟨cF, hcF, hid, hk1, hk2⟩ := hFEd
    exact ⟨cF, hcF, hid, hk1.trans (by linarith), hk2.trans (by linarith)⟩
  have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
  have hX0 : 0 ≤ Kmac * (Kf + Cφ) ^ 2 := hfA0.trans hfA
  have hZ0 := aux_aux_macro_energy_recurrence_Z_nonneg Sreg.C Cp t1 d
  have hBR0 : 0 ≤ localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
      (s := Metric.ball x R ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet)
      (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) :=
    localGradientEnergy_nonneg _ _ _
  have hρR0 : 0 ≤ (ρ / R) ^ t1 := Real.rpow_nonneg (div_nonneg hρ.le (hρ.le.trans hρR)) _
  -- it suffices to bound by `Z ρ^{t₁} K (K_f + C_φ)²`
  suffices hmain : localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
      (s := Metric.ball x ρ ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet)
      (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) ≤
      aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d * (ρ ^ t1 * (Kmac * (Kf + Cφ) ^ 2)) by
    refine hmain.trans (mul_le_mul_of_nonneg_left ?_ hZ0)
    rw [mul_assoc (ρ ^ t1) Kmac]
    exact le_add_of_nonneg_left (mul_nonneg hρR0 hBR0)
  have hρ1 : ρ ≤ 1 := hρR.trans hR1
  have hρt : 0 ≤ ρ ^ t1 := Real.rpow_nonneg hρ.le _
  by_cases hcase : ((3 : ℝ) ^ P0)⁻¹ / 2 ≤ ρ
  · -- initial scales: the global energy bound
    refine aux_aux_macro_energy_recurrence_initial_close d Sreg.C Cp t1 ρ (Kmac * (Kf + Cφ) ^ 2) _ _ P0 ht10 hρ hcase hX0
      ?_ hKsrc
    exact localGradientEnergy_le _ _ _
  · -- scales between the wavelength and the prefix: the one-centre estimate
    push Not at hcase
    obtain ⟨n, hnP, hρn, h6⟩ := aux_aux_macro_energy_recurrence_select_n N P0 ρ hρN hcase
    obtain ⟨lam, Λ, hlam, hlamA, hΛA⟩ := aux_aux_macro_energy_recurrence_cutoffCoefficient_bounds M H om N z h1
    have hcore := calib3_energy_core hd Cp hFE M Sreg hchild (1 - ((d : ℝ) - t1) / 4) hδ hα H om N z h1
      hR lam Λ Kmac hlam hlamA hΛA Lc hFEd' P0 hpre0 F Kf hKf hFm hFb φ Cφ hφ hCφ b u
      hb hu x hx n hnP
    have hmono := aux_aux_macro_energy_recurrence_localEnergy_mono (cutoffPositiveCoefficient M H om N z h1)
      (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
        MeasurableSet (Metric.ball x ρ ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
      (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
        MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
          (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
      (Set.inter_subset_inter_left _ (Metric.ball_subset_ball hρn))
      (sobolevGradient (u : SobolevData (centeredCube z 1 h1)))
    have hK0 : 0 ≤ Kmac := hKr0.le.trans hKrK
    exact aux_aux_macro_energy_recurrence_onecentre_close d Sreg.C Cp t1 ρ Kf Cφ Kmac _ _ _
      (aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C (1 - ((d : ℝ) - t1) / 4) N n)
      (aux_aux_macro_energy_recurrence_P_le (d := d) Sreg.C t1 ρ N n hdR ht1 ht1' hρ hρ1 h6)
      hKf hCφ0 hK0 hρt hfA (hmono.trans hcore)

/-- **Unit-cube energy growth** for a coefficient with FE data at level `Lc` (Stage 3; generalises
`aux_prop_growth_trunc_macro_energy_unit_bound`). -/
theorem calib3_macro_unit {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M' : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg' : in_6_16 d M')
    (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg'.alphaRange)
    (H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (om' : BilateralField d)
    (z' : SpatialCoordinates d) (n P0 : ℕ) (hR : (0 : ℝ) < 3 ^ n)
    (Kr : ℝ) (Lc : ℕ)
    (hFEd : ∃ cFin : ℝ, 0 < cFin ∧
      (∀ᵐ y ∂volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M' H' om' n z' one_pos).val y =
          cFin * (Sreg'.cutoffOn Lc (aux_aux_macro_energy_recurrence_relabel n om')
            ((3 : ℝ) ^ n • z') (3 ^ n) hR).val ((3 : ℝ) ^ n • y)) ∧
      cFin * Sreg'.refAvg Lc n ((3 : ℝ) ^ n • z') (aux_aux_macro_energy_recurrence_relabel n om') ≤ 2 * Kr ∧
      (cFin * Sreg'.refAvg Lc n ((3 : ℝ) ^ n • z') (aux_aux_macro_energy_recurrence_relabel n om'))⁻¹ ≤ 2 * Kr)
    (hpre0 : Sreg'.prefixLen Lc (1 - ((d : ℝ) - t1) / 4) n ((3 : ℝ) ^ n • z')
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
    (K' : ℝ)
    (hKref : (3 : ℝ) ^ (t1 * (P0 : ℝ)) * Kr ≤ K')
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F
      (volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
      |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z' 1 one_pos : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z' 1 one_pos))
    (hb : ((b : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M' H' om' n z' one_pos) F b u)
    (hKsrc : (3 : ℝ) ^ (t1 * (P0 : ℝ)) *
      sobolevCoefficientForm (cutoffPositiveCoefficient M' H' om' n z' one_pos)
        (u : SobolevData (centeredCube z' 1 one_pos))
        (u : SobolevData (centeredCube z' 1 one_pos)) ≤ K' * (Kf + Cφ) ^ 2)
    (x : SpatialCoordinates d) (ρ : ℝ)
    (hx : x ∈ (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hρN : (3 : ℝ) ^ (-(n : ℤ)) ≤ ρ) :
    localGradientEnergy (cutoffPositiveCoefficient M' H' om' n z' one_pos)
        (s := Metric.ball x ρ ∩ (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z' 1 one_pos).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z' 1 one_pos))) ≤
      2 * aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d * ρ ^ t1 * K' * (Kf + Cφ) ^ 2 := by
  have hrec := aux_calib3_macro_unit_recurrence hd Cp hFE M' Sreg' Sreg'.energy_density t1 ht1 ht1'
    hδC hα H' om' z' one_pos n hR Kr Lc hFEd P0 hpre0 K' hKref F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu
    hKsrc x ρ 1 hx hρ hρ1 le_rfl hρN
  set Z := aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d with hZ
  have hZ0 : 0 ≤ Z := aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 < t1 := by linarith
  have h3P : 1 ≤ (3 : ℝ) ^ (t1 * (P0 : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg ht10.le (Nat.cast_nonneg _))
  set a := cutoffPositiveCoefficient M' H' om' n z' one_pos
  have hform0 := sobolevCoefficientForm_nonneg a (u : SobolevData (centeredCube z' 1 one_pos))
  have hform : sobolevCoefficientForm a (u : SobolevData (centeredCube z' 1 one_pos))
      (u : SobolevData (centeredCube z' 1 one_pos)) ≤ K' * (Kf + Cφ) ^ 2 :=
    (le_mul_of_one_le_left hform0 h3P).trans hKsrc
  have hB1 : localGradientEnergy a
      (s := Metric.ball x 1 ∩ (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (centeredCube z' 1 one_pos).isOpen.measurableSet)
      (sobolevGradient (u : SobolevData (centeredCube z' 1 one_pos))) ≤ K' * (Kf + Cφ) ^ 2 :=
    (localGradientEnergy_le _ _ _).trans hform
  have hρt : 0 ≤ ρ ^ t1 := Real.rpow_nonneg hρ.le _
  rw [div_one] at hrec
  calc _ ≤ _ := hrec
    _ ≤ Z * (ρ ^ t1 * (K' * (Kf + Cφ) ^ 2) + ρ ^ t1 * K' * (Kf + Cφ) ^ 2) := by
        gcongr
    _ = 2 * Z * ρ ^ t1 * K' * (Kf + Cφ) ^ 2 := by ring

end SubdiffusiveProcess.Paper
