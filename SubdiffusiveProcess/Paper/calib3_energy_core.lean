module

public import Mathlib
public import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Paper.in_6_16

@[expose] public section

/-! Stage 3 (calibration): the one-centre energy estimate at a frame level `N` for an arbitrary coefficient that is, on the unit
cube, a positive multiple of the stationary coefficient `a_{Lc}` of the `N`-relabelled field, with the FE level `Lc` independent of
the frame `N` (in particular `Lc < N`: the H = 0 coefficient on cubes of side `3^j`, `Lc = N - j`).  Generalises
`aux_prop_growth_trunc_macro_energy_core` (`Lc = N + L0`, `H = H_{L0}`) and `aux_aux_macro_energy_recurrence_core_step`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise Distributions
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- One prefix-good frame, arbitrary FE level `Lc` and reference bounds `hkref`. -/
theorem aux_calib3_energy_core_step {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg : in_6_16 d M)
    (hchild : aux_aux_macro_energy_recurrence_DensityChild Sreg) (alpha : ℝ) (hδ : M.delta ≤ Sreg.C⁻¹)
    (hα : alpha ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (lam Λ Kr : ℝ) (hlam : 0 < lam)
    (hlamA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ cutoffCoefficient M H om N x)
    (hΛA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      cutoffCoefficient M H om N x ≤ Λ)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 h1 : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 h1))
    (hb : ((b : SobolevData (centeredCube z 1 h1)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om N z h1) F b u)
    (x : SpatialCoordinates d) (hx : x ∈ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
    (n : ℕ) (Lc : ℕ) (aFin : PositiveCoefficient (centeredCube z 1 h1)) (cFin : ℝ)
    (hcF : 0 < cFin)
    (hcoef : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      aFin.val y = cFin * (Sreg.cutoffOn Lc (aux_aux_macro_energy_recurrence_relabel N om) ((3 : ℝ) ^ N • z)
        (3 ^ N) hR).val ((3 : ℝ) ^ N • y))
    (hkref : cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) ≤ 2 * Kr ∧
      (cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om))⁻¹ ≤ 2 * Kr)
    (η : ℝ) (hηl : η ≤ lam / 2)
    (hη : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      |aFin.val y - cutoffCoefficient M H om N y| < η)
    (hn : (n : ℤ) ≤ (N : ℤ) - Sreg.prefixLen Lc alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om)) :
    localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
        (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
          MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
            (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
        (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) ≤
      16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n *
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z h1)
            (u : SobolevData _) (u : SobolevData _) +
        8 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n * Kr *
          (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2) +
        (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ *
          (4 * η ^ 2 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) := by
  obtain ⟨A, hAdef⟩ : ∃ A : PositiveCoefficient (centeredCube z 1 h1),
      A = cutoffPositiveCoefficient M H om N z h1 := ⟨_, rfl⟩
  rw [← hAdef] at hu ⊢
  have hAae : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      A.val y = cutoffCoefficient M H om N y := by
    rw [hAdef]; exact aux_aux_macro_energy_recurrence_coeff_ae M H om N z h1
  have hmem := ae_restrict_mem (μ := volume) (centeredCube z 1 h1).isOpen.measurableSet
  have hAl : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ A.val y := by
    filter_upwards [hAae, hmem] with y h1' h2'
    rw [h1']; exact hlamA y (centeredCube_subset_closedCube z h1 h2')
  have hAL : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      A.val y ≤ Λ := by
    filter_upwards [hAae, hmem] with y h1' h2'
    rw [h1']; exact hΛA y (centeredCube_subset_closedCube z h1 h2')
  have hη' : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      |aFin.val y - A.val y| ≤ η := by
    filter_upwards [hAae, hη] with y h1' h2'
    rw [h1']; exact h2'.le
  have hA2 : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      A.val y ≤ 2 * aFin.val y := by
    filter_upwards [hAl, hη'] with y h1' h2'
    have := (abs_le.1 h2').1
    linarith
  have ha2 : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      aFin.val y ≤ 2 * A.val y := by
    filter_upwards [hAl, hη'] with y h1' h2'
    have := (abs_le.1 h2').2
    linarith
  have hP := aux_aux_macro_moment_bank_killed_poincare hd z 1 h1
  obtain ⟨u', hu'⟩ := aux_aux_macro_energy_recurrence_exists_solution hP aFin F Kf hFm hFb b
  have hfin := hFE M Sreg hchild Lc (aux_aux_macro_energy_recurrence_relabel N om) alpha hδ hα N z h1 hR aFin cFin
    hcF hcoef F Kf hKf hFm hFb φ Cφ hφ hCφ b u' hb hu' x hx n hn
  have href := hkref
  have hstab := aux_aux_macro_energy_recurrence_stability A aFin lam η hlam hAl hη' hηl F b u u' hu hu'
  have hB : MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
      (centeredCube z 1 h1 : Set (SpatialCoordinates d))) :=
    isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet
  have hΓ1 := aux_aux_macro_energy_recurrence_localEnergy_sub_le A hB (u : SobolevData _) (u' : SobolevData _)
  have hΓ2 := localGradientEnergy_le_mul A aFin 2 hA2 hB
    (sobolevGradient (u' : SobolevData (centeredCube z 1 h1)))
  have hΓ3 := aux_aux_macro_energy_recurrence_localEnergy_le_gradSq A Λ hAL hB
    ((u : SobolevData (centeredCube z 1 h1)) - (u' : SobolevData _))
  have hf1 : sobolevCoefficientForm aFin (u' : SobolevData _) (u' : SobolevData _) ≤
      2 * sobolevCoefficientForm A (u' : SobolevData _) (u' : SobolevData _) :=
    weightedGradientForm_le_mul aFin A 2 ha2 _
  have hf2 := bilinear_quadratic_sub_le (sobolevCoefficientForm A)
    (sobolevCoefficientForm_symm A) (sobolevCoefficientForm_nonneg A)
    (u' : SobolevData (centeredCube z 1 h1)) (u : SobolevData _)
  have hf3 : sobolevCoefficientForm A ((u' : SobolevData (centeredCube z 1 h1)) -
        (u : SobolevData (centeredCube z 1 h1)))
      ((u' : SobolevData (centeredCube z 1 h1)) - (u : SobolevData (centeredCube z 1 h1))) ≤
      Λ * aux_aux_macro_energy_recurrence_gradSq ((u : SobolevData (centeredCube z 1 h1)) -
        (u' : SobolevData (centeredCube z 1 h1))) := by
    rw [aux_aux_macro_energy_recurrence_gradSq_sub_comm]
    exact aux_aux_macro_energy_recurrence_form_le_gradSq A Λ hAL _
  have hρ0 : 0 < cFin * Sreg.refAvg Lc N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om) :=
    mul_pos hcF (Sreg.refAvg_pos _ _ _ _)
  have hchain := aux_aux_macro_energy_recurrence_energy_chain _ _ _ _ _ _ _ _ _ _ _ Kr Cp Kf Cφ (d : ℝ) Λ hΓ1 hΓ2 hΓ3
    hfin (aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C alpha N n) href.1 href.2 hρ0 hf1 hf2 hf3
  have hΛ0 : 0 ≤ Λ := by
    have := (hlamA z (Metric.mem_closedBall_self (by norm_num))).trans
      (hΛA z (Metric.mem_closedBall_self (by norm_num)))
    linarith
  have hcoefP : 0 ≤ (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ :=
    mul_nonneg (by linarith [aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C alpha N n]) hΛ0
  unfold aux_aux_macro_energy_recurrence_P at hchain ⊢
  calc _ ≤ _ := hchain
    _ ≤ _ := by
      gcongr

/-- **One-centre estimate** at frame `N` with FE level `Lc` (paper Step 1 of `mfd:prop-growth`, `eq:mfd-macro`). -/
theorem calib3_energy_core {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg : in_6_16 d M)
    (hchild : aux_aux_macro_energy_recurrence_DensityChild Sreg) (alpha : ℝ) (hδ : M.delta ≤ Sreg.C⁻¹)
    (hα : alpha ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (lam Λ Kr : ℝ) (hlam : 0 < lam)
    (hlamA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ cutoffCoefficient M H om N x)
    (hΛA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      cutoffCoefficient M H om N x ≤ Λ)
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
    (x : SpatialCoordinates d) (hx : x ∈ (centeredCube z 1 h1 : Set (SpatialCoordinates d)))
    (n : ℕ) (hn : (n : ℤ) ≤ (N : ℤ) - P0) :
    localGradientEnergy (cutoffPositiveCoefficient M H om N z h1)
        (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
          MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
            (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
        (sobolevGradient (u : SobolevData (centeredCube z 1 h1))) ≤
      16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n *
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z h1)
            (u : SobolevData _) (u : SobolevData _) +
        8 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n * Kr *
          (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2) := by
  have hΛ0 : 0 ≤ Λ := by
    have := (hlamA z (Metric.mem_closedBall_self (by norm_num))).trans
      (hΛA z (Metric.mem_closedBall_self (by norm_num)))
    linarith
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ *
      (4 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    have := aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C alpha N n
    have := aux_aux_macro_energy_recurrence_gradSq_nonneg (u : SobolevData (centeredCube z 1 h1))
    positivity
  obtain ⟨cFin, hcF, hcoef, hkref⟩ := hFEd
  have hn' : (n : ℤ) ≤ (N : ℤ) - Sreg.prefixLen Lc alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) := by
    have : (Sreg.prefixLen Lc alpha N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) : ℤ) ≤ (P0 : ℤ) := by exact_mod_cast hpre0
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (lam / 2) (Real.sqrt (ε / (Kc + 1))) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hηdef]
    exact lt_min (half_pos hlam) (Real.sqrt_pos.2 (div_pos hε (by linarith)))
  have hηl : η ≤ lam / 2 := by rw [hηdef]; exact min_le_left _ _
  have hηsq : Kc * η ^ 2 ≤ ε := by
    have h1' : η ^ 2 ≤ ε / (Kc + 1) := by
      have : η ≤ Real.sqrt (ε / (Kc + 1)) := by rw [hηdef]; exact min_le_right _ _
      calc η ^ 2 ≤ (Real.sqrt (ε / (Kc + 1))) ^ 2 := pow_le_pow_left₀ hη0.le this 2
        _ = ε / (Kc + 1) := Real.sq_sqrt (div_nonneg hε.le (by linarith))
    calc Kc * η ^ 2 ≤ Kc * (ε / (Kc + 1)) := mul_le_mul_of_nonneg_left h1' hKc0
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
  have hηae : ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      |(cutoffPositiveCoefficient M H om N z h1).val y -
        cutoffCoefficient M H om N y| < η := by
    filter_upwards [aux_aux_macro_energy_recurrence_coeff_ae M
      H om N z h1] with y hy
    rw [hy, sub_self, abs_zero]
    exact hη0
  have hstep := aux_calib3_energy_core_step hd Cp hFE M Sreg hchild alpha hδ hα
    H om N z h1 hR lam Λ Kr hlam
    hlamA hΛA F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu x hx n Lc
    (cutoffPositiveCoefficient M H om N z h1) cFin hcF hcoef hkref
    η hηl hηae hn'
  have heq : (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ *
      (4 * η ^ 2 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) =
      Kc * η ^ 2 := by
    rw [hKc]; ring
  rw [heq] at hstep
  linarith

end SubdiffusiveProcess.Paper
