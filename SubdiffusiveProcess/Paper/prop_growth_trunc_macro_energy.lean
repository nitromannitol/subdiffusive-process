module

public import SubdiffusiveProcess.Paper.prop_growth_trunc_bank
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
public import SubdiffusiveProcess.Paper.aux_macro_moment_bank

@[expose] public section

/-!
# Macro-scale energy at a finite infrared truncation (Step 1 of `mfd:prop-growth`)

For every truncation `H_{L'}` the all-cube macro energy bound of `prop_growth_macro_energy`
holds.  At a finite truncation the finite-level identity is exact, so the per-level recurrence
applies at level `N + L'` with no truncation limit; the residual shift maps level `L'` to
`k + L'`.  Not claimed: constants uniform in the model.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise Distributions
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **One-centre estimate at a finite infrared truncation** (paper Step 1 of
`mfd:prop-growth`): for `H = H_{L0}`, a single prefix-good level suffices. -/
theorem aux_prop_growth_trunc_macro_energy_core {d : ℕ} (hd : 2 ≤ d)
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
    (hKr : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)), Real.exp |H om x| ≤ Kr)
    (L0 : ℕ) (hHT : H = fun om' => infraredPartialSum om' L0)
    (P0 : ℕ) (hpre0 : Sreg.prefixLen (N + L0) alpha N ((3 : ℝ) ^ N • z)
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
  subst hHT
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
  obtain ⟨cFin, hcF, hcoef⟩ : ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M (fun om' => infraredPartialSum om' L0) om N z h1).val y =
          cFin * (Sreg.cutoffOn (N + L0) (aux_aux_macro_energy_recurrence_relabel N om)
            ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y) := by
    obtain ⟨cFin, hcF, hae⟩ := aux_prop_growth_macro_energy_finite_identity Sreg om N L0 z h1
      (by positivity)
    refine ⟨cFin, hcF, ?_⟩
    filter_upwards [hae] with y hy
    rw [hy]
    congr 1
    exact aux_aux_macro_energy_recurrence_cutoffOn_congr Sreg (N + L0) rfl
      (by rw [zpow_natCast]) (by rw [zpow_natCast, mul_one]) _ _ (by rw [zpow_natCast])
  have hn' : (n : ℤ) ≤ (N : ℤ) - Sreg.prefixLen (N + L0) alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) := by
    have : (Sreg.prefixLen (N + L0) alpha N ((3 : ℝ) ^ N • z)
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
      |(cutoffPositiveCoefficient M (fun om' => infraredPartialSum om' L0) om N z h1).val y -
        cutoffCoefficient M (fun om' => infraredPartialSum om' L0) om N y| < η := by
    filter_upwards [aux_aux_macro_energy_recurrence_coeff_ae M
      (fun om' => infraredPartialSum om' L0) om N z h1] with y hy
    rw [hy, sub_self, abs_zero]
    exact hη0
  have hstep := aux_aux_macro_energy_recurrence_core_step hd Cp hFE M Sreg hchild alpha hδ hα
    (fun om' => infraredPartialSum om' L0) om N z h1 hR lam Λ Kr hlam
    hlamA hΛA hKr F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu x hx n L0
    (cutoffPositiveCoefficient M (fun om' => infraredPartialSum om' L0) om N z h1) cFin hcF hcoef
    η hηl hηae hn'
  have heq : (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ *
      (4 * η ^ 2 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq (u : SobolevData (centeredCube z 1 h1))) =
      Kc * η ^ 2 := by
    rw [hKc]; ring
  rw [heq] at hstep
  linarith

/-- **Unit-cube recurrence at a finite infrared truncation.** -/
theorem aux_prop_growth_trunc_macro_energy_recurrence_om {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg : in_6_16 d M)
    (hchild : aux_aux_macro_energy_recurrence_DensityChild Sreg) (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδ : M.delta ≤ Sreg.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (N : ℕ) (hR : (0 : ℝ) < 3 ^ N)
    (L0 : ℕ) (hHT : H = fun om' => infraredPartialSum om' L0)
    (P0 : ℕ) (hpre0 : Sreg.prefixLen (N + L0) (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) ≤ P0)
    (Kmac : ℝ)
    (hKref : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      (3 : ℝ) ^ (t1 * (P0 : ℝ)) * Real.exp (|H om x|) ≤ Kmac)
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
  have hKr : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      Real.exp |H om x| ≤ Kmac := fun x hx =>
    (le_mul_of_one_le_left (Real.exp_pos _).le h3P).trans (hKref x hx)
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
    have hcore := aux_prop_growth_trunc_macro_energy_core hd Cp hFE M Sreg hchild (1 - ((d : ℝ) - t1) / 4) hδ hα H om N z h1
      hR lam Λ Kmac hlam hlamA hΛA hKr L0 hHT P0 hpre0 F Kf hKf hFm hFb φ Cφ hφ hCφ b u
      hb hu x hx n hnP
    have hmono := aux_aux_macro_energy_recurrence_localEnergy_mono (cutoffPositiveCoefficient M H om N z h1)
      (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
        MeasurableSet (Metric.ball x ρ ∩ (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
      (isOpen_ball.measurableSet.inter (centeredCube z 1 h1).isOpen.measurableSet :
        MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
          (centeredCube z 1 h1 : Set (SpatialCoordinates d))))
      (Set.inter_subset_inter_left _ (Metric.ball_subset_ball hρn))
      (sobolevGradient (u : SobolevData (centeredCube z 1 h1)))
    have hK0 : 0 ≤ Kmac := (Real.exp_pos _).le.trans (hKr z (Metric.mem_closedBall_self
      (by norm_num)))
    exact aux_aux_macro_energy_recurrence_onecentre_close d Sreg.C Cp t1 ρ Kf Cφ Kmac _ _ _
      (aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C (1 - ((d : ℝ) - t1) / 4) N n)
      (aux_aux_macro_energy_recurrence_P_le (d := d) Sreg.C t1 ρ N n hdR ht1 ht1' hρ hρ1 h6)
      hKf hCφ0 hK0 hρt hfA (hmono.trans hcore)


/-- **Unit-cube energy growth at a finite infrared truncation.** -/
theorem aux_prop_growth_trunc_macro_energy_unit_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M' : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg' : in_6_16 d M')
    (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg'.alphaRange)
    (H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (om' : BilateralField d)
    (z' : SpatialCoordinates d) (n P0 : ℕ)
    (L0 : ℕ) (hHT : H' = fun om'' => infraredPartialSum om'' L0)
    (hpre0 : Sreg'.prefixLen (n + L0) (1 - ((d : ℝ) - t1) / 4) n ((3 : ℝ) ^ n • z')
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
    (K' : ℝ)
    (hKref : ∀ x ∈ (closedCube z' 1 one_pos : Set (SpatialCoordinates d)),
      (3 : ℝ) ^ (t1 * (P0 : ℝ)) * Real.exp (|H' om' x|) ≤ K')
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
  have hR : (0 : ℝ) < 3 ^ n := by positivity
  have hrec := aux_prop_growth_trunc_macro_energy_recurrence_om hd Cp hFE M' Sreg' Sreg'.energy_density t1 ht1 ht1'
    hδC hα H' om' z' one_pos n hR L0 hHT P0 hpre0 K' hKref F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu
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


open _root_.SubdiffusiveProcess.Model in
/-- **The residual-shift coefficient identity at a finite infrared truncation**, for every
sample (no infrared limit): level `L0` on `Q(z,r)` becomes level `k + L0` on the unit cube. -/
theorem aux_prop_growth_trunc_macro_energy_coeff_identity {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M M' : GMCModel d)
    (htau : tauSq M'.P = tauSq M.P) (L0 : ℕ) (r : ℝ) (k : ℕ) (om : BilateralField d)
    (n : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M (fun om' => infraredPartialSum om' L0) om (n + k) (r • x) =
      aux_prop_growth_macro_energy_shiftC M M' k n om *
        cutoffCoefficient M' (fun om' => infraredPartialSum om' (k + L0))
          (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r k om) n x := by
  have hIR : ∀ y : SpatialCoordinates d,
      (fun om' => infraredPartialSum om' (k + L0)) (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r k om) y =
        (fun om' => infraredPartialSum om' L0) om (r • y) +
          (∑ i ∈ Finset.range k, om (-(Int.ofNat i)) (r • y)) - _root_.SubdiffusiveProcess.MacroAllCube.lowAnchor k om := by
    intro y
    have h := congrArg (fun f : C(SpatialCoordinates d, ℝ) => f y)
      (aux_prop_growth_macro_energy_infraredPartialSum_residualShift_cm r k L0 om)
    simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.coe_sum,
      Finset.sum_apply, ContinuousMap.const_apply] at h
    exact h
  have hpot := _root_.SubdiffusiveProcess.MacroAllCube.cutoffPotential_residualShift
    (fun om' => infraredPartialSum om' L0) (fun om' => infraredPartialSum om' (k + L0))
    r k n om hIR x
  unfold cutoffCoefficient aux_prop_growth_macro_energy_shiftC
  rw [hpot, htau]
  have h := _root_.SubdiffusiveProcess.MacroAllCube.normalized_coefficient_shift (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (n + k))
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M' n)
    (cutoffPotential (fun om' => infraredPartialSum om' (k + L0))
      (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r k om) n x) (_root_.SubdiffusiveProcess.MacroAllCube.lowAnchor k om)
    (tauSq M.P) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M' n).ne' k n
  rw [show ((n + k : ℕ) + 1 : ℝ) = ((n + k : ℕ) : ℝ) + 1 by push_cast; ring] at h
  convert h using 2

/-- **Middle scales of an arbitrary-side cube at a finite infrared truncation.** -/
theorem aux_prop_growth_trunc_macro_energy_middle {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M M' : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg' : in_6_16 d M')
    (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg'.alphaRange)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (om om' : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (k n : ℕ)
    (hrk3 : r * (3 : ℝ) ^ k ≤ 3)
    (c E : ℝ) (hc : 0 < c) (hcE : c ≤ E) (hcE' : c⁻¹ ≤ E) (hE1 : 1 ≤ E)
    (hcoefid : ∀ x : SpatialCoordinates d,
      cutoffCoefficient M H om (n + k) (r • x) = c * cutoffCoefficient M' H' om' n x)
    (P0 : ℕ)
    (L1 : ℕ) (hHT' : H' = fun om'' => infraredPartialSum om'' L1)
    (hpre0 : Sreg'.prefixLen (n + L1) (1 - ((d : ℝ) - t1) / 4) n ((3 : ℝ) ^ n • (r⁻¹ • z))
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
    (Rs : ℝ) (hRs : ∀ x ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp (|H' om' x|) ≤ Rs)
    (Kg : ℝ) (hKg0 : 0 ≤ Kg)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om (n + k) z hr) F b u)
    (hglob : sobolevCoefficientForm (cutoffPositiveCoefficient M H om (n + k) z hr)
        (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) ≤
      Kg * (Kf + Cphi) ^ 2)
    (x : SpatialCoordinates d) (rad : ℝ) (hx : x ∈ centeredCube z r hr) (hrad0 : 0 < rad)
    (hradr : rad ≤ r) (hradN : (3 : ℝ) ^ (-((n + k : ℕ) : ℤ)) ≤ rad) :
    localGradientEnergy (cutoffPositiveCoefficient M H om (n + k) z hr)
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
      aux_prop_growth_macro_energy_Kmid d (aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d)
          t1 r E P0 Rs Kg * (Kf + Cphi) ^ 2 * rad ^ t1 := by
  have hri : 0 < r⁻¹ := inv_pos.2 hr
  have hQT := aux_prop_growth_macro_energy_cube_eq_smul z hr one_pos
  have hTQ := aux_prop_growth_macro_energy_cube_eq_inv_smul z hr one_pos
  have hcoef := aux_prop_growth_macro_energy_coef_rel M M' H H' om om' z hr k n c hcoefid
  obtain ⟨F', b', v, hF'm, hF'b, hb', hsol', hloc, hform⟩ :=
    aux_prop_growth_macro_energy_dirichlet_transfer hr hc hQT hTQ _ _ hcoef F Kf hFm hFb phi b u
      hb hu
  have hphi' : ContDiff ℝ 2 (fun y : SpatialCoordinates d => phi (r • y)) :=
    hphi.comp (contDiff_id.const_smul r)
  have hCphi' := aux_prop_growth_macro_energy_c2Norm_dilate z hr hr1 one_pos phi hphi Cphi hCphi
  have hCphi0 : 0 ≤ Cphi := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ phi).trans hCphi
  have hKf' : 0 ≤ c⁻¹ * r ^ 2 * Kf := by positivity
  have hZ0 := aux_aux_macro_energy_recurrence_Z_nonneg Sreg'.C Cp t1 d
  have hE0 : 0 ≤ E := le_trans zero_le_one hE1
  have h3P0 : 0 ≤ (3 : ℝ) ^ (t1 * (P0 : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hRs0 : 0 ≤ Rs := (Real.exp_pos _).le.trans (hRs (r⁻¹ • z)
    (Metric.mem_closedBall_self (by norm_num)))
  have hW0 : 0 ≤ E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg := by positivity
  have hK'0 : 0 ≤ (3 : ℝ) ^ (t1 * (P0 : ℝ)) * (Rs + E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg) := by
    positivity
  have hKref : ∀ y ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      (3 : ℝ) ^ (t1 * (P0 : ℝ)) * Real.exp (|H' om' y|) ≤
        (3 : ℝ) ^ (t1 * (P0 : ℝ)) * (Rs + E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg) := by
    intro y hy
    exact mul_le_mul_of_nonneg_left ((hRs y hy).trans (le_add_of_nonneg_right hW0)) h3P0
  obtain ⟨hsq1, hsq2⟩ := aux_prop_growth_macro_energy_sum_sq hc hr hr1 hcE hcE' hE1 hKf hCphi0
  have hKsrc := aux_prop_growth_macro_energy_ksrc_arith d hr hcE' hE1 hKg0 hRs0 h3P0
    (sobolevCoefficientForm_nonneg _ _) hform hglob hsq1 (sq_nonneg _)
  have hx' : r⁻¹ • x ∈ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)) := by
    rw [hTQ]; exact Set.smul_mem_smul_set hx
  have ht10 : 0 < t1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hρ'0, hρ'1, hρpow⟩ := aux_prop_growth_macro_energy_radius hr hrad0 hradr hrk3 hradN
    ht10.le (t1 := t1)
  have hunit := aux_prop_growth_trunc_macro_energy_unit_bound hd Cp hFE M' Sreg' t1 ht1 ht1' hδC hα H'
    om' (r⁻¹ • z) n P0 L1 hHT' hpre0 _ hKref F' (c⁻¹ * r ^ 2 * Kf) hKf' hF'm hF'b
    (fun y => phi (r • y)) (3 * Cphi) hphi' hCphi' b' v hb' hsol' hKsrc (r⁻¹ • x)
    (max (rad / r) ((3 : ℝ) ^ (-(n : ℤ)))) hx' hρ'0 hρ'1 (le_max_right _ _)
  have hS : MeasurableSet (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet
  have hball : r⁻¹ • (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) =
      Metric.ball (r⁻¹ • x) (rad / r) ∩
        (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)) := by
    rw [aux_aux_macro_energy_recurrence_ball_inter_smul x rad _ hri, ← hTQ, inv_mul_eq_div]
  have hrS : MeasurableSet
      (r⁻¹ • (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))) := by
    rw [hball]
    exact isOpen_ball.measurableSet.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet
  have hl := hloc _ hS hrS
  rw [aux_aux_macro_energy_recurrence_localEnergy_congr _ hball hrS
    (isOpen_ball.measurableSet.inter
      (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet)] at hl
  have hmono := aux_aux_macro_energy_recurrence_localEnergy_mono
    (cutoffPositiveCoefficient M' H' om' n (r⁻¹ • z) one_pos)
    (isOpen_ball.measurableSet.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet :
      MeasurableSet (Metric.ball (r⁻¹ • x) (rad / r) ∩
        (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))))
    (isOpen_ball.measurableSet.inter (centeredCube (r⁻¹ • z) 1 one_pos).isOpen.measurableSet :
      MeasurableSet (Metric.ball (r⁻¹ • x) (max (rad / r) ((3 : ℝ) ^ (-(n : ℤ)))) ∩
        (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))))
    (Set.inter_subset_inter_left _ (Metric.ball_subset_ball (le_max_left _ _)))
    (sobolevGradient (v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)))
  have hkey : c⁻¹ * (r⁻¹) ^ d * r ^ 2 *
      localGradientEnergy (cutoffPositiveCoefficient M H om (n + k) z hr) hS
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
      2 * aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d *
        ((3 : ℝ) ^ t1 * rad ^ t1 * r ^ (-t1)) *
        ((3 : ℝ) ^ (t1 * (P0 : ℝ)) * (Rs + E ^ 3 * ((r⁻¹) ^ d * (r⁻¹) ^ 2) * Kg)) *
        (9 * E ^ 2 * (Kf + Cphi) ^ 2) := by
    rw [← hl]
    refine hmono.trans (hunit.trans ?_)
    gcongr
  have hfin := aux_prop_growth_macro_energy_middle_arith d hc hr hcE hZ0 hK'0 hrad0 hkey
  refine hfin.trans (le_of_eq ?_)
  unfold aux_prop_growth_macro_energy_Kmid
  ring


/-- **The pathwise all-cutoff bound at a finite infrared truncation.** -/
theorem aux_prop_growth_trunc_macro_energy_ae_bound {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M M' : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg' : in_6_16 d M')
    (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg'.alphaRange)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ))
    (L0 : ℕ) (hHT : H = fun om' => infraredPartialSum om' L0)
    (htau : _root_.SubdiffusiveProcess.Model.tauSq M'.P = _root_.SubdiffusiveProcess.Model.tauSq M.P)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (kk : ℕ)
    (hk3 : r * (3 : ℝ) ^ kk ≤ 3)
    (hT : MeasurePreserving (_root_.SubdiffusiveProcess.MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure)
    (hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤ aux_prop_growth_macro_energy_env M kk om)
    (Lm : ℕ → BilateralField d → ℕ)
    (hHT' : H' = fun om' => infraredPartialSum om' (kk + L0))
    (hLpre0 : ∀ᵐ om' ∂(chaosSampleLaw M').toMeasure, ∀ N : ℕ,
        Sreg'.prefixLen (N + (kk + L0)) (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • (r⁻¹ • z))
          (aux_aux_macro_energy_recurrence_relabel N om') ≤ Lm N om')
    (Kg : ℕ → BilateralField d → ℝ) (hKg0 : ∀ N om, 0 ≤ Kg N om)
    (hKgsrc : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
        ContDiff ℝ 2 phi →
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
        ∀ (x : SpatialCoordinates d) (rad : ℝ),
          x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
          (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
          localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
              (s := Metric.ball x rad ∩
                (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter
                (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
            aux_prop_growth_macro_energy_Kfinal M kk r t1
                (aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d) Lm
                (aux_prop_growth_macro_energy_Rs H' z r) Kg N om * (Kf + Cphi) ^ 2 * rad ^ t1 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 < t1 := by linarith
  filter_upwards [hKgsrc, hT.quasiMeasurePreserving.ae hLpre0] with om hsrc hpre
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve x rad hx hrad0 hrad1 hradN
  have hglob := hsrc N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
  have hZ0 := aux_aux_macro_energy_recurrence_Z_nonneg Sreg'.C Cp t1 d
  have hcg0 : 0 ≤ (3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) * Kg N om := by
    have := hKg0 N om
    positivity
  have hsq0 : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
  have hradt : 0 ≤ rad ^ t1 := Real.rpow_nonneg hrad0.le _
  unfold aux_prop_growth_macro_energy_Kfinal
  by_cases hcase : kk ≤ N ∧ rad < r
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + kk := ⟨N - kk, by omega⟩
    rw [ite_eq_left hcase.1, Nat.add_sub_cancel]
    have hRdom : ∀ y ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
        Real.exp (|H' (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r kk om) y|) ≤
          aux_prop_growth_macro_energy_Rs H' z r (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r kk om) := by
      intro y hy
      refine Real.exp_le_exp.2 ?_
      have h := ContinuousMap.norm_coe_le_norm
        ((H' (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r kk om)).restrict
          ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))) ⟨y, hy⟩
      rwa [Real.norm_eq_abs] at h
    have hmid := aux_prop_growth_trunc_macro_energy_middle hd Cp hFE M M' Sreg' t1 ht1 ht1' hδC hα H H'
      om (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r kk om) z r hr hr1 kk n hk3
      (aux_prop_growth_macro_energy_shiftC M M' kk n om) (aux_prop_growth_macro_energy_env M kk om)
      (aux_prop_growth_macro_energy_shiftC_pos M M' kk n om) (hshift n om).1 (hshift n om).2
      (aux_prop_growth_macro_energy_one_le_env M kk om)
      (fun x => by rw [hHT, hHT']; exact aux_prop_growth_trunc_macro_energy_coeff_identity M M' htau L0 r kk om n x)
      (Lm n (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r kk om)) (kk + L0) hHT' (hpre n)
      (aux_prop_growth_macro_energy_Rs H' z r (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r kk om)) hRdom
      (Kg (n + kk) om) (hKg0 _ _) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve hglob x rad
      hx hrad0 hcase.2.le hradN
    refine hmid.trans ?_
    have hmul := mul_le_mul_of_nonneg_right hcg0 (mul_nonneg hsq0 hradt)
    nlinarith
  · have hif0 : 0 ≤ (if kk ≤ N then
        aux_prop_growth_macro_energy_Kmid d (aux_aux_macro_energy_recurrence_Z Sreg'.C Cp t1 d) t1 r
          (aux_prop_growth_macro_energy_env M kk om)
          (Lm (N - kk) (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r kk om))
          (aux_prop_growth_macro_energy_Rs H' z r (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r kk om)) (Kg N om)
        else 0) := by
      split_ifs
      · exact aux_prop_growth_macro_energy_Kmid_nonneg d hZ0 hr
          (aux_prop_growth_macro_energy_one_le_env M kk om) (Real.exp_pos _).le (hKg0 N om)
      · exact le_refl 0
    have hfac := aux_prop_growth_macro_energy_global_factor hr hr1 hrad0 ht10.le hradN hcase
    have hloc : localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
        (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        sobolevCoefficientForm (cutoffPositiveCoefficient M H om N z hr)
          (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) :=
      localGradientEnergy_le _ _ _
    have hK0 : 0 ≤ Kg N om * (Kf + Cphi) ^ 2 := mul_nonneg (hKg0 N om) hsq0
    calc _ ≤ Kg N om * (Kf + Cphi) ^ 2 := hloc.trans hglob
      _ ≤ Kg N om * (Kf + Cphi) ^ 2 * ((3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) * rad ^ t1) :=
          le_mul_of_one_le_right hK0 hfac
      _ = (3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) * Kg N om * (Kf + Cphi) ^ 2 * rad ^ t1 := by ring
      _ ≤ _ := by
          have := mul_nonneg hif0 (mul_nonneg hsq0 hradt)
          nlinarith


/-- The prefix length at one fixed level has the geometric tail of `in_6_16`. -/
theorem aux_prop_growth_trunc_macro_energy_prefix_fixed {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg : in_6_16 d M) (alpha κ : ℝ)
    (hδC : M.delta ≤ Sreg.C⁻¹) (hα : alpha ∈ Sreg.alphaRange)
    (hκ : κ = (1 - alpha) ^ 2 / (Sreg.C * M.delta ^ 2 * |Real.log M.delta|))
    (hκ0 : 0 < κ) (z : SpatialCoordinates d) (L1 : ℕ) :
    ∃ Lmac : ℕ → BilateralField d → ℕ,
      (∀ N, Measurable (Lmac N)) ∧
      (∀ N k : ℕ, (chaosSampleLaw M).toMeasure {om | k < Lmac N om} ≤
        ENNReal.ofReal (Sreg.C * Real.exp (κ * Sreg.C) * Real.exp (-κ * k))) ∧
      (∀ om, ∀ N : ℕ, Sreg.prefixLen (N + L1) alpha N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) ≤ Lmac N om) := by
  refine ⟨fun N om => Sreg.prefixLen (N + L1) alpha N ((3 : ℝ) ^ N • z)
    (aux_aux_macro_energy_recurrence_relabel N om), fun N => (Sreg.prefix_measurable _ _ _ _).comp
    (aux_aux_macro_moment_bank_relabel_measurePreserving M N).measurable, ?_,
    fun om N => le_rfl⟩
  intro N k
  have hpres := aux_aux_macro_moment_bank_relabel_measurePreserving M N
  have hset : {om | k < Sreg.prefixLen (N + L1) alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om)} = aux_aux_macro_moment_bank_relabel N ⁻¹'
      {om | k < Sreg.prefixLen (N + L1) alpha N ((3 : ℝ) ^ N • z) om} := rfl
  rw [hset, hpres.measure_preimage
    (measurableSet_lt measurable_const (Sreg.prefix_measurable _ _ _ _)).nullMeasurableSet]
  exact aux_aux_macro_moment_bank_tail_geometric M Sreg alpha κ hδC hα hκ hκ0.le _ _ _ k

theorem prop_growth_trunc_macro_energy :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (t1 : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t1 → t1 < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (L0 : ℕ),
      H = (fun om' => infraredPartialSum om' L0) → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (Kmac : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
            (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              Kmac N om * (Kf + Cphi) ^ 2 * rad ^ t1 := by
  intro d hd _ _ E P X S t1 k ps ht1 ht2 hps
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 < t1 := by linarith
  -- one exponent for all listed orders
  obtain ⟨Pexp, hPdef⟩ : ∃ Pexp : ℝ, Pexp = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => by linarith [hps i]
  have hP1 : 1 ≤ Pexp := by rw [hPdef]; linarith
  have hpsP : ∀ i, ps i ≤ Pexp := by
    intro i
    rw [hPdef]
    have := Finset.single_le_sum (f := ps) (fun j _ => by linarith [hps j]) (Finset.mem_univ i)
    linarith
  -- the truncated global-energy bank at the quadrupled order (threshold before the model)
  obtain ⟨dB, hdB, hbank⟩ := prop_growth_trunc_bank d hd E P X S (2 * (2 * Pexp)) (by linarith)
  obtain ⟨dA, hdA, hthr⟩ := aux_aux_macro_moment_bank_threshold (d := d) t1 (2 * Pexp) ht1 ht2
    ht10.le (by linarith)
  obtain ⟨Cp, -, hFE⟩ := aux_aux_macro_energy_recurrence_finite_estimate (d := d) hd
  have hD0 := _root_.SubdiffusiveProcess.ResidualModel.residualDisorderFactor_pos d
  refine ⟨min dB (min (dA / _root_.SubdiffusiveProcess.ResidualModel.residualDisorderFactor d)
    (2 * _root_.SubdiffusiveProcess.ResidualModel.residualDisorderFactor d)⁻¹), lt_min hdB (lt_min (div_pos hdA hD0)
      (by positivity)), ?_⟩
  intro M Rm H L0 hHT hδ z r hr hr1
  subst hHT
  have hδB : M.delta ≤ dB := hδ.trans (min_le_left _ _)
  have hδA : M.delta ≤ dA / _root_.SubdiffusiveProcess.ResidualModel.residualDisorderFactor d :=
    hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδD : M.delta ≤ (2 * _root_.SubdiffusiveProcess.ResidualModel.residualDisorderFactor d)⁻¹ :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the residual scale and the bounded-dilation model `M_s`
  obtain ⟨kk, hk1, hk3⟩ := _root_.SubdiffusiveProcess.MacroAllCube.exists_residual_scale hr hr1
  obtain ⟨M', hM'⟩ : ∃ M' : _root_.SubdiffusiveProcess.Model.GMCModel d,
      M' = _root_.SubdiffusiveProcess.ResidualModel.residualModel M hk1.le hk3 hδD := ⟨_, rfl⟩
  have hT : MeasurePreserving (_root_.SubdiffusiveProcess.MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure := by
    rw [hM']; exact _root_.SubdiffusiveProcess.ResidualModel.measurePreserving_residualModel M r kk hk1.le hk3 hδD
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M'.P = _root_.SubdiffusiveProcess.Model.tauSq M.P := by
    rw [hM']; exact _root_.SubdiffusiveProcess.ResidualModel.residualModel_tauSq M hk1.le hk3 hδD
  have hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤
        aux_prop_growth_macro_energy_env M kk om := by
    intro n om; rw [hM']; exact aux_prop_growth_macro_energy_shiftC_bounds M hk1.le hk3 hδD kk n om
  have hδ' : M'.delta ≤ dA := by
    rw [hM', _root_.SubdiffusiveProcess.ResidualModel.residualModel_delta]
    rw [le_div_iff₀ hD0] at hδA
    linarith
  -- the native regularity input of `M_s` and its thresholds
  obtain ⟨hδC', hα', hκ'⟩ := hthr M' (aux_prop_growth_macro_energy_nativeSreg M') hδ'
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      ((aux_prop_growth_macro_energy_nativeSreg M').C * M'.delta ^ 2 * |Real.log M'.delta|) :=
    ⟨_, rfl⟩
  rw [← hκ] at hκ'
  have hlam : 0 ≤ 2 * (2 * Pexp) * t1 * Real.log 3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    have : (0 : ℝ) ≤ Pexp := by linarith
    positivity
  have hκ0 : 0 < κ := lt_of_le_of_lt hlam hκ'
  obtain ⟨Lm, hLmeas, hLtail, hLpre⟩ := aux_prop_growth_trunc_macro_energy_prefix_fixed M'
    (aux_prop_growth_macro_energy_nativeSreg M') (1 - ((d : ℝ) - t1) / 4) κ hδC' hα' hκ hκ0
    (r⁻¹ • z) (kk + L0)
  have hA1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M').C *
      Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) := by
    have h1 : 1 ≤ (aux_prop_growth_macro_energy_nativeSreg M').C :=
      (aux_prop_growth_macro_energy_nativeSreg M').C_ge_one
    have h2 : 1 ≤ Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) :=
      Real.one_le_exp (by positivity)
    nlinarith
  have hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M').toMeasure ≤
      ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))) := by
    intro n
    have hXm : AEStronglyMeasurable (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
        (chaosSampleLaw M').toMeasure := by
      simpa only [Function.comp_def] using!
        ((measurable_from_nat (f := fun j : ℕ => (3 : ℝ) ^ (t1 * (j : ℝ)))).comp (hLmeas n)).aestronglyMeasurable
    rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hXm]
    exact aux_aux_macro_moment_bank_eLpNorm_rpow_three_le _ (Lm n) t1 (2 * (2 * Pexp))
      (by linarith) _ (aux_aux_macro_moment_bank_lintegral_exp_le
        (chaosSampleLaw M').toMeasure (Lm n) (hLmeas n) _ κ _ hA1 hlam hκ' (hLtail n))
  -- the truncated global energy on `Q(z,r)`
  obtain ⟨Kg, Cg, hKg0, hKgmem, hKgnorm, hKgsrc'⟩ := hbank M Rm hδB L0 z r hr hr1
  -- the residual reference factor
  obtain ⟨hRmeas, -, hRmem⟩ := aux_prop_growth_trunc_bank_reference hd M' (kk + L0)
    (closedCube (r⁻¹ • z) 1 one_pos) (2 * (2 * Pexp)) (by linarith)
  have hmom := aux_prop_growth_macro_energy_Kfinal_moment M M' kk r t1
    (aux_aux_macro_energy_recurrence_Z (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d)
    Pexp hr (aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _) hP1 hT Lm hLmeas _ hX
    (aux_prop_growth_macro_energy_Rs (fun om' => infraredPartialSum om' (kk + L0)) z r) hRmeas _ le_rfl Kg (ENNReal.ofReal Cg)
    (fun N => (hKgmem N).aestronglyMeasurable) hKgnorm
  -- the common finite bound
  obtain ⟨Btot, hBtot⟩ : ∃ Btot : ℝ≥0∞, Btot =
      ENNReal.ofReal ((3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1)) * ENNReal.ofReal Cg +
        (ENNReal.ofReal (18 * aux_aux_macro_energy_recurrence_Z
              (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d * (3 : ℝ) ^ t1 *
              (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1))) *
            (eLpNorm (fun om => aux_prop_growth_macro_energy_env M kk om ^ 3)
                (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure *
              (ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
                  Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
                (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^
                  (1 / (2 * (2 * Pexp))) *
                eLpNorm (aux_prop_growth_macro_energy_Rs (fun om' => infraredPartialSum om' (kk + L0)) z r)
                  (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M').toMeasure)) +
          ENNReal.ofReal (18 * aux_aux_macro_energy_recurrence_Z
              (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d * (3 : ℝ) ^ t1 *
              (r ^ d * (r⁻¹) ^ 2 * r ^ (-t1)) * ((r⁻¹) ^ d * (r⁻¹) ^ 2)) *
            (eLpNorm (fun om => aux_prop_growth_macro_energy_env M kk om ^ 6)
                (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure *
              (ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
                  Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
                (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^
                  (1 / (2 * (2 * Pexp))) * ENNReal.ofReal Cg))) := ⟨_, rfl⟩
  have hfin : Btot ≠ ⊤ := by
    have hE3 := (aux_prop_growth_macro_energy_memLp_env_pow M kk 3 (2 * Pexp) (by linarith)).eLpNorm_lt_top.ne
    have hE6 := (aux_prop_growth_macro_energy_memLp_env_pow M kk 6 (2 * Pexp) (by linarith)).eLpNorm_lt_top.ne
    have hBX : ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^
          (1 / (2 * (2 * Pexp))) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    have hR := hRmem.eLpNorm_lt_top.ne
    rw [hBtot]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hE3 (ENNReal.mul_ne_top hBX hR)),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top hE6 (ENNReal.mul_ne_top hBX ENNReal.ofReal_ne_top))⟩⟩
  refine ⟨aux_prop_growth_macro_energy_Kfinal M kk r t1
      (aux_aux_macro_energy_recurrence_Z (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d)
      Lm (aux_prop_growth_macro_energy_Rs (fun om' => infraredPartialSum om' (kk + L0)) z r) Kg, fun _ => Btot.toReal, ?_, ?_, ?_, ?_⟩
  · intro N om
    unfold aux_prop_growth_macro_energy_Kfinal
    have h1 : 0 ≤ (3 : ℝ) ^ ((kk : ℝ) * t1) * r ^ (-t1) * Kg N om := by
      have := hKg0 N om
      positivity
    have h2 : 0 ≤ (if kk ≤ N then
        aux_prop_growth_macro_energy_Kmid d
          (aux_aux_macro_energy_recurrence_Z (aux_prop_growth_macro_energy_nativeSreg M').C Cp t1 d)
          t1 r (aux_prop_growth_macro_energy_env M kk om)
          (Lm (N - kk) (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r kk om))
          (aux_prop_growth_macro_energy_Rs (fun om' => infraredPartialSum om' (kk + L0)) z r (_root_.SubdiffusiveProcess.MacroAllCube.residualShift r kk om)) (Kg N om)
        else 0) := by
      split_ifs
      · exact aux_prop_growth_macro_energy_Kmid_nonneg d
          (aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _) hr
          (aux_prop_growth_macro_energy_one_le_env M kk om) (Real.exp_pos _).le (hKg0 N om)
      · exact le_refl 0
    exact add_nonneg h1 h2
  · intro i N
    obtain ⟨hm, hb⟩ := hmom N
    exact lt_of_le_of_lt ((eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal (hpsP i))).trans (hb.trans (le_of_eq hBtot.symm)))
      (lt_top_iff_ne_top.2 hfin)
  · intro i N
    obtain ⟨hm, hb⟩ := hmom N
    rw [ENNReal.ofReal_toReal hfin]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hpsP i))).trans
      (hb.trans (le_of_eq hBtot.symm))
  · exact aux_prop_growth_trunc_macro_energy_ae_bound hd Cp hFE M M'
      (aux_prop_growth_macro_energy_nativeSreg M') t1 ht1 ht2 hδC' hα'
      (fun om' => infraredPartialSum om' L0) (fun om' => infraredPartialSum om' (kk + L0)) L0 rfl
      htau z r hr hr1 kk hk3 hT hshift Lm rfl (Filter.Eventually.of_forall hLpre) Kg hKg0
      hKgsrc'

end SubdiffusiveProcess.Paper
