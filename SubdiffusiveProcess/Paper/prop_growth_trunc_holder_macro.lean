module

public import SubdiffusiveProcess.Paper.prop_growth_holder_macro_campanato
public import SubdiffusiveProcess.Paper.prop_growth_trunc_macro_energy
public import SubdiffusiveProcess.Paper.prop_growth_trunc_bank
public import SubdiffusiveProcess.Paper.prop_growth_trunc_energy_assembly
public import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments
public import SubdiffusiveProcess.Paper.aux_macro_moment_bank
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence

@[expose] public section

/-!
# Campanato decay above the wavelength at a finite infrared truncation

The macro Campanato child of `mfd:prop-growth` for every `H_{L'}`.  The root oscillation uses
the Poincaré inequality of the characterized coefficient and the cross bank.  Not claimed:
constants uniform in the model.
-/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section HolderTrunc

variable {d : ℕ}

theorem aux_prop_growth_trunc_holder_macro_core_osc (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg : in_6_16 d M) (alpha : ℝ)
    (hδ : M.delta ≤ Sreg.C⁻¹) (hα : alpha ∈ Sreg.alphaRange)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (hR : (0 : ℝ) < 3 ^ N)
    (lam Kr : ℝ) (hlam : 0 < lam)
    (hlamA : ∀ x ∈ (closedCube z 1 h1 : Set (SpatialCoordinates d)),
      lam ≤ cutoffCoefficient M H om N x)
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
  have hKr0 : 0 ≤ Kr := (Real.exp_pos _).le.trans (hKr z (Metric.mem_closedBall_self (by norm_num)))
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
  obtain ⟨cFin, hcF, hcoef⟩ : ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M H om N z h1).val y =
          cFin * (Sreg.cutoffOn (N + L0) (aux_aux_macro_energy_recurrence_relabel N om)
            ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y) := by
    subst hHT
    obtain ⟨cFin, hcF, hae⟩ := aux_prop_growth_macro_energy_finite_identity Sreg om N L0 z h1
      (by positivity)
    refine ⟨cFin, hcF, ?_⟩
    filter_upwards [hae] with y hy
    rw [hy]
    congr 1
    exact aux_aux_macro_energy_recurrence_cutoffOn_congr Sreg (N + L0) rfl
      (by rw [zpow_natCast]) (by rw [zpow_natCast, mul_one]) _ _ (by rw [zpow_natCast])
  have hηae : ∀ η : ℝ, 0 < η →
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        |(cutoffPositiveCoefficient M H om N z h1).val y - cutoffCoefficient M H om N y| < η := by
    intro η hη
    filter_upwards [aux_aux_macro_energy_recurrence_coeff_ae M H om N z h1] with y hy
    rw [hy, sub_self, abs_zero]
    exact hη
  have hjP' : (Sreg.prefixLen (N + L0) alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) : ℤ) ≤ j := by
    have : Sreg.prefixLen (N + L0) alpha N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) ≤ j := hpre0.trans hjP
    exact_mod_cast this
  have hstep := aux_prop_growth_holder_macro_campanato_core_step hd Cp hCp hFO M Sreg alpha hδ hα H
    om N z h1 hR lam Kr hlam hlamA hKr F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu KP hKP L0
    (cutoffPositiveCoefficient M H om N z h1) cFin hcF hcoef _ hη0.le hηl (hηae _ hη0) j hjN hjP'
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


theorem aux_prop_growth_trunc_holder_macro_unit_H1 (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (M' : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg' : in_6_16 d M') (alphaM alpha : ℝ)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hα : alphaM ∈ Sreg'.alphaRange) (hαα : alpha ≤ alphaM)
    (H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (om' : BilateralField d)
    (z' : SpatialCoordinates d) (n P0 : ℕ)
    (L0 : ℕ) (hHT : H' = fun om'' => infraredPartialSum om'' L0)
    (hpre0 : Sreg'.prefixLen (n + L0) alphaM n ((3 : ℝ) ^ n • z')
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
    (Rs : ℝ) (hRs : ∀ x ∈ (closedCube z' 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp |H' om' x| ≤ Rs)
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
  have hR : (0 : ℝ) < 3 ^ n := by positivity
  obtain ⟨lam, Λ, hlam, hlamA, -⟩ :=
    aux_aux_macro_energy_recurrence_cutoffCoefficient_bounds M' H' om' n z' one_pos
  have hcore := aux_prop_growth_trunc_holder_macro_core_osc hd Cp hCp hFO M' Sreg' alphaM hδC
    hα H' om' n z' one_pos hR lam Rs hlam hlamA hRs L0 hHT P0 hpre0
    F Kf hKf hFm hFb φ Cφ hφ hCφ b v hb hv j hjn hjP k hk
  refine hcore.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ?_ ?_ 2)
    (aux_prop_growth_holder_macro_campanato_cell_volume_pos z' j k).le)
  · have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
    have hRs0 : 0 ≤ Rs := (Real.exp_pos _).le.trans (hRs z' (Metric.mem_closedBall_self (by norm_num)))
    have := Sreg'.C_pos
    have := Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos j).le alphaM
    positivity
  · have hsle : aux_prop_growth_holder_macro_campanato_side j ^ alphaM ≤
        aux_prop_growth_holder_macro_campanato_side j ^ alpha :=
      Real.rpow_le_rpow_of_exponent_ge (aux_prop_growth_holder_macro_campanato_side_pos j)
        (aux_prop_growth_holder_macro_campanato_side_le_one j) hαα
    have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
    have hRs0 : 0 ≤ Rs := (Real.exp_pos _).le.trans (hRs z' (Metric.mem_closedBall_self (by norm_num)))
    have hX : 0 ≤ Real.sqrt (aux_prop_growth_holder_macro_campanato_var
        (centeredCube z' 1 one_pos : Set (SpatialCoordinates d))
        ((v : SobolevData (centeredCube z' 1 one_pos)).1 : SpatialCoordinates d → ℝ)) +
          (2 * Cp * Rs * Kf + d * Cφ) := by positivity
    have := Sreg'.C_pos
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsle (by positivity)) hX

theorem aux_prop_growth_trunc_holder_macro_middle (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {E : in_J d} (P : in_poincare d hd E)
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (CPw : ℝ) (hCPw : 0 ≤ CPw)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (v : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        CPw * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (alpha : ℝ) (hα0 : 0 < alpha) (Kd : ℝ) (hKd0 : 0 ≤ Kd)
    (hKd : aux_prop_growth_holder_macro_campanato_UnitProp d alpha Kd)
    (M M' : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg' : in_6_16 d M') (alphaM : ℝ)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hαM : alphaM ∈ Sreg'.alphaRange) (hαα : alpha ≤ alphaM)
    (t1 e : ℝ) (he : 0 < e) (hexp : 2 + t1 = 2 * alpha + d + e)
    (ht1Y : alpha + (d : ℝ) / 2 ≤ t1)
    (H H' H0 : BilateralField d → C(SpatialCoordinates d, ℝ)) (om om' : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (kk n : ℕ)
    (hrk1 : 1 ≤ r * (3 : ℝ) ^ kk)
    (c Ec : ℝ) (hc : 0 < c) (hcE' : c⁻¹ ≤ Ec)
    (hcoefid : ∀ x : SpatialCoordinates d,
      cutoffCoefficient M H om (n + kk) (r • x) = c * cutoffCoefficient M' H' om' n x)
    (P0 : ℕ)
    (L1 : ℕ) (hHT' : H' = fun om'' => infraredPartialSum om'' L1)
    (hpre0 : Sreg'.prefixLen (n + L1) alphaM n ((3 : ℝ) ^ n • (r⁻¹ • z))
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
    (Rs : ℝ) (hRs : ∀ x ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp (|H' om' x|) ≤ Rs)
    (Λ Kg Mx Kmac : ℝ) (hΛ0 : 0 ≤ Λ) (hKg0 : 0 ≤ Kg) (hKmac0 : 0 ≤ Kmac)
    (hΛ : (E.lam z r hr (cutoffPositiveCoefficient M H0 om (n + kk) z hr) z r 1 1)⁻¹ ≤ Λ)
    (hMx : 0 < Mx)
    (hfl : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mx⁻¹ ≤ cutoffCoefficient M H om (n + kk) x)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M H om (n + kk) z hr) F b u)
    (hglob : sobolevCoefficientForm (cutoffPositiveCoefficient M H0 om (n + kk) z hr)
        (u : SobolevData (centeredCube z r hr)) (u : SobolevData (centeredCube z r hr)) ≤
      Kg * (Kf + Cphi) ^ 2)
    (hmac : ∀ (x : SpatialCoordinates d) (rad : ℝ),
      x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 → (3 : ℝ) ^ (-((n + kk : ℕ) : ℤ)) ≤ rad →
      localGradientEnergy (cutoffPositiveCoefficient M H om (n + kk) z hr)
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        Kmac * (Kf + Cphi) ^ 2 * rad ^ t1)
    (x : SpatialCoordinates d) (hx : x ∈ centeredCube z r hr) (rad : ℝ)
    (hradN : (3 : ℝ) ^ (-((n + kk : ℕ) : ℤ)) ≤ rad) (hradr : rad ≤ r) :
    ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
          (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (u : SobolevData (centeredCube z r hr)).1) ^ 2
        ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
      (aux_prop_growth_holder_macro_campanato_Kmid d Kd Sreg'.C Cp alpha t1 r e
          (Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2)) CPw n P0 Λ Kg Rs Ec Mx Kmac * (Kf + Cphi)) ^ 2 *
        rad ^ (2 * alpha) *
        volume.real (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hQT := aux_prop_growth_macro_energy_cube_eq_smul z hr one_pos
  have hTQ := aux_prop_growth_macro_energy_cube_eq_inv_smul z hr one_pos
  have hcoef := aux_prop_growth_macro_energy_coef_rel M M' H H' om om' z hr kk n c hcoefid
  obtain ⟨F', b', v, hF'm, hF'b, hb', hsol', hloc, hvrel⟩ :=
    aux_prop_growth_holder_macro_campanato_transfer hr hc hQT hTQ _ _ hcoef F Kf hFm hFb phi b u
      hb hu
  have hphi' : ContDiff ℝ 2 (fun y : SpatialCoordinates d => phi (r • y)) :=
    hphi.comp (contDiff_id.const_smul r)
  have hCphi' := aux_prop_growth_macro_energy_c2Norm_dilate z hr hr1 one_pos phi hphi Cphi hCphi
  have hCphi0 : 0 ≤ Cphi := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ phi).trans hCphi
  have hKf' : 0 ≤ c⁻¹ * r ^ 2 * Kf := by positivity
  have hK : 0 ≤ Kf + Cphi := by positivity
  have H1 := aux_prop_growth_trunc_holder_macro_unit_H1 hd Cp hCp hFO M' Sreg' alphaM alpha hδC
    hαM hαα H' om' (r⁻¹ • z) n P0 L1 hHT' hpre0 Rs hRs F' (c⁻¹ * r ^ 2 * Kf) hKf' hF'm hF'b
    (fun y => phi (r • y)) (3 * Cphi) hphi' hCphi' b' v hb' hsol'
  have hfloor : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx * (cutoffPositiveCoefficient M H om (n + kk) z hr).val y := by
    filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M H om (n + kk) z hr,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy hyQ
    rw [hy]
    have hlo := hfl y (centeredCube_subset_closedCube z hr hyQ)
    calc (1 : ℝ) = Mx * Mx⁻¹ := (mul_inv_cancel₀ hMx.ne').symm
      _ ≤ Mx * cutoffCoefficient M H om (n + kk) y := mul_le_mul_of_nonneg_left hlo hMx.le
  have H2 := aux_prop_growth_holder_macro_campanato_middle_H2 CPw hCPw hPoinc alpha t1 e he hexp z
    hr hr1 (n + kk) n _ (cutoffPositiveCoefficient M' H' om' n (r⁻¹ • z) one_pos) c Mx Kmac
    (Kf + Cphi) hc hMx.le hKmac0 hcoef hfloor u v hloc hmac
  have hvarQ := aux_prop_growth_holder_macro_campanato_root_var P z hr
    (cutoffPositiveCoefficient M H0 om (n + kk) z hr) u Λ (Kg * (Kf + Cphi) ^ 2) hΛ hglob
  have hroot := aux_prop_growth_holder_macro_campanato_transport_root z hr _ _ hvrel
  have hO := aux_prop_growth_holder_macro_campanato_root_arith hr hΛ0 hKg0 hK hvarQ hroot
  have hO0 := Real.sqrt_nonneg (aux_prop_growth_holder_macro_campanato_var
    (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))
    ((v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1 : SpatialCoordinates d → ℝ))
  have H3 : aux_prop_growth_holder_macro_campanato_var (ball (r⁻¹ • z) (1 / 2))
      ((v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1 : SpatialCoordinates d → ℝ) ≤
      (Real.sqrt (aux_prop_growth_holder_macro_campanato_var
        (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))
        ((v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1 : SpatialCoordinates d → ℝ))) ^ 2 :=
    le_of_eq (Real.sq_sqrt (aux_prop_growth_holder_macro_campanato_var_nonneg _ _)).symm
  have hRs0 : 0 ≤ Rs :=
    (Real.exp_pos _).le.trans (hRs (r⁻¹ • z) (Metric.mem_closedBall_self (by norm_num)))
  have hx' : r⁻¹ • x ∈ ball (r⁻¹ • z) (1 / 2) := by
    change r⁻¹ • x ∈ (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))
    rw [hTQ]; exact Set.smul_mem_smul_set hx
  have hrad0 : 0 < rad := lt_of_lt_of_le (by positivity) hradN
  have hCS : 0 ≤ 2 * Sreg'.C := by have := Sreg'.C_pos; linarith
  have hXnn : 0 ≤ Real.sqrt (aux_prop_growth_holder_macro_campanato_var
      (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d))
      ((v : SobolevData (centeredCube (r⁻¹ • z) 1 one_pos)).1 : SpatialCoordinates d → ℝ)) +
      (2 * Cp * Rs * (c⁻¹ * r ^ 2 * Kf) + d * (3 * Cphi)) := by positivity
  have hWnn : 0 ≤ (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1 * aux_prop_growth_holder_macro_campanato_side n ^ e *
      Mx + Kmac) * (Kf + Cphi) := by
    have := (aux_prop_growth_holder_macro_campanato_side_pos n).le
    have := hMx.le
    positivity
  have hunit := hKd (r⁻¹ • z) _ (Lp.memLp _) n P0 (2 * Sreg'.C) _ _ _
    ((3 : ℝ) ^ (-((n + kk : ℕ) : ℤ)) / r) hCS hXnn hWnn hO0 (by positivity)
    (aux_prop_growth_holder_macro_campanato_rho_min_le hr kk n hrk1) H1 H2 H3 (r⁻¹ • x) hx'
    (rad / r) (div_le_div_of_nonneg_right hradN hr.le) ((div_le_one hr).2 hradr)
  obtain ⟨hvarT, hvolT⟩ := aux_prop_growth_holder_macro_campanato_transport z hr _ _ hvrel x rad
  rw [aux_prop_growth_holder_macro_campanato_target_eq
    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
    Set.inter_subset_right]
  unfold aux_prop_growth_holder_macro_campanato_Kmid
  have hY := aux_prop_growth_holder_macro_campanato_Y_le (d := d) alpha t1 P0 (by positivity) ht1Y
  have hX := aux_prop_growth_holder_macro_campanato_middle_X d hr hr1 hc hCp hRs0 hKf hCphi0 hcE' hO
  have hYO := mul_le_mul hY hO hO0 (by positivity)
  have hY0 : 0 ≤ ((2 : ℝ) * 3 ^ P0) ^ (alpha + (d : ℝ) / 2) := by positivity
  exact aux_prop_growth_holder_macro_campanato_middle_arith hr hrad0 hKd0
    Sreg'.C_pos.le hXnn hWnn hY0 hO0 hK hX
    le_rfl (le_of_le_of_eq hYO (by ring)) hunit hvarT hvolT measureReal_nonneg


theorem aux_prop_growth_trunc_holder_macro_ae_bound (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {E : in_J d} (P : in_poincare d hd E)
    (Cp : ℝ) (hCp : 0 ≤ Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (CPw : ℝ) (hCPw : 0 ≤ CPw)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (v : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        CPw * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (alpha : ℝ) (hα0 : 0 < alpha) (Kd : ℝ) (hKd0 : 0 ≤ Kd)
    (hKd : aux_prop_growth_holder_macro_campanato_UnitProp d alpha Kd)
    (M M' : _root_.SubdiffusiveProcess.Model.GMCModel d) (Sreg' : in_6_16 d M') (t1 e : ℝ)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hαM : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg'.alphaRange)
    (hαα : alpha ≤ 1 - ((d : ℝ) - t1) / 4)
    (he : 0 < e) (hexp : 2 + t1 = 2 * alpha + d + e) (ht1Y : alpha + (d : ℝ) / 2 ≤ t1)
    (H H' H0 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (L0 : ℕ) (hHT : H = fun om' => infraredPartialSum om' L0)
    (htau : _root_.SubdiffusiveProcess.Model.tauSq M'.P = _root_.SubdiffusiveProcess.Model.tauSq M.P)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (kk : ℕ)
    (hk1 : 1 < r * (3 : ℝ) ^ kk) (hk3 : r * (3 : ℝ) ^ kk ≤ 3)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure)
    (hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤ aux_prop_growth_macro_energy_env M kk om)
    (Lm : ℕ → BilateralField d → ℕ)
    (hHT' : H' = fun om' => infraredPartialSum om' (kk + L0))
    (hLpre0 : ∀ᵐ om' ∂(chaosSampleLaw M').toMeasure, ∀ N : ℕ,
        Sreg'.prefixLen (N + (kk + L0)) (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • (r⁻¹ • z))
          (aux_aux_macro_energy_recurrence_relabel N om') ≤ Lm N om')
    (Rs : BilateralField d → ℝ)
    (hRs : ∀ om', ∀ x ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp (|H' om' x|) ≤ Rs om')
    (Λ Kg Mx Kmac : ℕ → BilateralField d → ℝ)
    (hΛ0 : ∀ N om, 0 ≤ Λ N om) (hKg0 : ∀ N om, 0 ≤ Kg N om) (hKmac0 : ∀ N om, 0 ≤ Kmac N om)
    (hΛ : ∀ N om, (E.lam z r hr (cutoffPositiveCoefficient M H0 om N z hr) z r 1 1)⁻¹ ≤ Λ N om)
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
          sobolevCoefficientForm (cutoffPositiveCoefficient M H0 om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2)
    (hext : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, 0 < Mx N om ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        (Mx N om)⁻¹ ≤ cutoffCoefficient M H om N x)
    (hmacE : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
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
            Kmac N om * (Kf + Cphi) ^ 2 * rad ^ t1) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
        0 ≤ Kf →
        AEMeasurable F
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
          |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
        ContDiff ℝ 2 phi →
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
      ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
        ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ rad → rad ≤ r →
          ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
                (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (u : SobolevData (centeredCube z r hr)).1) ^ 2
              ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
            (aux_prop_growth_holder_macro_campanato_Kosc M kk r t1 e alpha Kd Sreg'.C Cp
                (Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2)) CPw P.C Lm Rs Λ Kg Mx Kmac N om *
              (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
              volume.real (Metric.ball x rad ∩
                (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  filter_upwards [hKgsrc, hmacE, hext, hT.quasiMeasurePreserving.ae hLpre0]
    with om hsrc hmac hex hpre
  intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve x hx rad hradN hradr
  have hglob := hsrc N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
  have hmacN := hmac N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
  obtain ⟨hMx, hfl⟩ := hex N
  have hCphi0 : 0 ≤ Cphi := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ phi).trans hCphi
  unfold aux_prop_growth_holder_macro_campanato_Kosc
  by_cases hN : kk ≤ N
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + kk := ⟨N - kk, by omega⟩
    rw [ite_eq_left hN, Nat.add_sub_cancel]
    exact aux_prop_growth_trunc_holder_macro_middle hd P Cp hCp hFO CPw hCPw hPoinc alpha hα0
      Kd hKd0 hKd M M' Sreg' _ hδC hαM hαα t1 e he hexp ht1Y H H' H0 om
      (MacroAllCube.residualShift r kk om) z r hr hr1 kk n hk1.le
      (aux_prop_growth_macro_energy_shiftC M M' kk n om) (aux_prop_growth_macro_energy_env M kk om)
      (aux_prop_growth_macro_energy_shiftC_pos M M' kk n om) (hshift n om).2
      (fun x => by rw [hHT, hHT']; exact aux_prop_growth_trunc_macro_energy_coeff_identity M M' htau L0 r kk om n x)
      (Lm n (MacroAllCube.residualShift r kk om)) (kk + L0) hHT' (hpre n) (Rs (MacroAllCube.residualShift r kk om))
      (hRs _) (Λ (n + kk) om) (Kg (n + kk) om) (Mx (n + kk) om) (Kmac (n + kk) om) (hΛ0 _ _)
      (hKg0 _ _) (hKmac0 _ _) (hΛ _ _) hMx hfl F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
      hglob hmacN x hx rad hradN hradr
  · rw [ite_eq_right hN]
    have hrad := aux_prop_growth_holder_macro_campanato_early hr hk3 hN hradN hradr
    rw [hrad]
    exact aux_prop_growth_holder_macro_campanato_global P z hr _ u (Λ N om) (Kg N om) (Kf + Cphi)
      (hΛ0 _ _) (hKg0 _ _) (by positivity) (hΛ N om) hglob x hx alpha hα0.le

theorem aux_prop_growth_trunc_holder_macro_assemble {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {E : in_J d} (P : in_poincare d hd E)
    (Cp : ℝ) (hCp : 0 < Cp) (hFO : aux_prop_growth_holder_macro_campanato_FO (d := d) Cp)
    (CPw : ℝ) (hCPw : 0 ≤ CPw)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (v : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        CPw * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (alpha : ℝ) (ha0 : 0 < alpha) (Kd : ℝ) (hKd1 : 1 ≤ Kd)
    (hKd : aux_prop_growth_holder_macro_campanato_UnitProp d alpha Kd)
    {k : ℕ} (ps : Fin k → ℝ) (Pexp : ℝ) (hP1 : 1 ≤ Pexp) (hpsP : ∀ i, ps i ≤ Pexp)
    (M M' : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H H' H0 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (L0 : ℕ) (hHT : H = fun om' => infraredPartialSum om' L0)
    (htau : _root_.SubdiffusiveProcess.Model.tauSq M'.P = _root_.SubdiffusiveProcess.Model.tauSq M.P)
    (t1 e : ℝ) (_ht10 : 0 ≤ t1)
    (hδC : M'.delta ≤ (aux_prop_growth_macro_energy_nativeSreg M').C⁻¹)
    (hα' : 1 - ((d : ℝ) - t1) / 4 ∈ (aux_prop_growth_macro_energy_nativeSreg M').alphaRange)
    (hαM : alpha ≤ 1 - ((d : ℝ) - t1) / 4)
    (he : 0 < e) (hexp : 2 + t1 = 2 * alpha + d + e) (ht1Y : alpha + (d : ℝ) / 2 ≤ t1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (kk : ℕ)
    (hk1 : 1 < r * (3 : ℝ) ^ kk) (hk3 : r * (3 : ℝ) ^ kk ≤ 3)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure)
    (hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤ aux_prop_growth_macro_energy_env M kk om)
    (Lm : ℕ → BilateralField d → ℕ) (hLmeas : ∀ n, Measurable (Lm n))
    (hHT' : H' = fun om' => infraredPartialSum om' (kk + L0))
    (hLpre0 : ∀ᵐ om' ∂(chaosSampleLaw M').toMeasure, ∀ N : ℕ,
        (aux_prop_growth_macro_energy_nativeSreg M').prefixLen (N + (kk + L0))
          (1 - ((d : ℝ) - t1) / 4) N
          ((3 : ℝ) ^ N • (r⁻¹ • z)) (aux_aux_macro_energy_recurrence_relabel N om') ≤ Lm N om')
    (BX : ℝ≥0∞) (hBX : BX ≠ ⊤)
    (hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure ≤ BX)
    (hRmeas : Measurable fun om' => Real.exp ‖(H' om').restrict
      ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))‖)
    (hRdom : ∀ om', ∀ x ∈ (closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp |H' om' x| ≤ Real.exp ‖(H' om').restrict
        ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))‖)
    (hRmem : MemLp (fun om' => Real.exp ‖(H' om').restrict
      ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))‖)
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure)
    (Kmac : ℕ → BilateralField d → ℝ) (BK : ℝ) (hKmac0 : ∀ N om, 0 ≤ Kmac N om)
    (hKmacmem : ∀ N, AEStronglyMeasurable (Kmac N) (chaosSampleLaw M).toMeasure)
    (hKmacnorm : ∀ N, eLpNorm (Kmac N) (ENNReal.ofReal Pexp) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal BK)
    (hmacE : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
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
            Kmac N om * (Kf + Cphi) ^ 2 * rad ^ t1)
    (Kg : ℕ → BilateralField d → ℝ) (BG : ℝ)
    (hKg0 : ∀ N om, 0 ≤ Kg N om)
    (hKgmem : ∀ N, AEStronglyMeasurable (Kg N) (chaosSampleLaw M).toMeasure)
    (hKgnorm : ∀ N, eLpNorm (Kg N) (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal BG)
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
          sobolevCoefficientForm (cutoffPositiveCoefficient M H0 om N z hr)
              (u : SobolevData (centeredCube z r hr))
              (u : SobolevData (centeredCube z r hr)) ≤
            Kg N om * (Kf + Cphi) ^ 2)
    (BL : ℝ)
    (hLmem : ∀ N, AEStronglyMeasurable (fun om : BilateralField d =>
      (E.lam z r hr (cutoffPositiveCoefficient M H0 om N z hr) z r (1 / 8) 1)⁻¹)
      (chaosSampleLaw M).toMeasure)
    (hLnorm : ∀ N, eLpNorm (fun om : BilateralField d =>
      (E.lam z r hr (cutoffPositiveCoefficient M H0 om N z hr) z r (1 / 8) 1)⁻¹)
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal BL)
    (Mx : ℕ → BilateralField d → ℝ) (BM : ℝ) (hMx0 : ∀ N om, 0 ≤ Mx N om)
    (hMxm : ∀ N, AEStronglyMeasurable (Mx N) (chaosSampleLaw M).toMeasure)
    (hMb : ∀ N, eLpNorm (fun om => aux_prop_growth_holder_macro_campanato_side (N - kk) ^ e * Mx N om)
      (ENNReal.ofReal Pexp) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal BM)
    (hext : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, 0 < Mx N om ∧
      ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
        (Mx N om)⁻¹ ≤ cutoffCoefficient M H om N x) :
    ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ rad → rad ≤ r →
            ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
                ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
                  (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z r hr)).1) ^ 2
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hΛle : ∀ N om, (E.lam z r hr (cutoffPositiveCoefficient M H0 om N z hr) z r 1 1)⁻¹ ≤
      (E.lam z r hr (cutoffPositiveCoefficient M H0 om N z hr) z r (1 / 8) 1)⁻¹ := fun N om =>
    inv_anti₀ (E.lam_pos _ _ _ _ _ _ _ _) (E.lam_mono _ _ _ _ _ _ _ _ _ (by norm_num))
  have hΛ0 : ∀ N om,
      0 ≤ (E.lam z r hr (cutoffPositiveCoefficient M H0 om N z hr) z r (1 / 8) 1)⁻¹ :=
    fun N om => (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _)).le
  have hEmem := aux_prop_growth_macro_energy_memLp_env_pow M kk 1 (2 * Pexp) (by linarith)
  have henv1 : (fun om => aux_prop_growth_macro_energy_env M kk om ^ 1) =
      aux_prop_growth_macro_energy_env M kk := by funext om; rw [pow_one]
  rw [henv1] at hEmem
  have hmom := fun N => aux_prop_growth_holder_macro_campanato_Kosc_moment M M' kk r t1 e alpha Kd
    (aux_prop_growth_macro_energy_nativeSreg M').C Cp (Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2)) CPw P.C
    hr (le_trans zero_le_one hKd1) (aux_prop_growth_macro_energy_nativeSreg M').C_pos.le hCp.le
    (Real.sqrt_nonneg _) hCPw P.C_pos.le Pexp hP1 hT Lm hLmeas BX hX _ hRmeas _ le_rfl _ le_rfl
    (fun N om => (E.lam z r hr (cutoffPositiveCoefficient M H0 om N z hr) z r (1 / 8) 1)⁻¹) Kg Mx
    Kmac (ENNReal.ofReal BL) (ENNReal.ofReal BG) (ENNReal.ofReal BM) (ENNReal.ofReal BK)
    hLmem hLnorm hKgmem hKgnorm hMxm hMb hKmacmem hKmacnorm N
  set Btot := (ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * (aux_prop_growth_macro_energy_nativeSreg M').C *
            (3 * d))) +
          ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * (aux_prop_growth_macro_energy_nativeSreg M').C *
            Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2))) * (ENNReal.ofReal BL + ENNReal.ofReal BG) +
          ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * (aux_prop_growth_macro_energy_nativeSreg M').C *
            (2 * Cp))) *
            (eLpNorm (fun om' => Real.exp ‖(H' om').restrict
                ((closedCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)))‖)
                (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure *
              eLpNorm (aux_prop_growth_macro_energy_env M kk) (ENNReal.ofReal (2 * Pexp))
                (chaosSampleLaw M).toMeasure) +
          ENNReal.ofReal (r ^ (-alpha) * Kd * (CPw * (r⁻¹) ^ d * r ^ 2 * r ^ t1)) *
            ENNReal.ofReal BM +
          ENNReal.ofReal (r ^ (-alpha) * Kd) * ENNReal.ofReal BK +
          ENNReal.ofReal (r ^ (-alpha) * Kd * ((2 : ℝ) ^ (alpha + (d : ℝ) / 2) *
            Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2))) *
            (BX * (ENNReal.ofReal BL + ENNReal.ofReal BG))) +
        ENNReal.ofReal (P.C * r * (r ^ (alpha + (d : ℝ) / 2))⁻¹) *
          (ENNReal.ofReal BL + ENNReal.ofReal BG) with hBtot
  have hfin : Btot ≠ ⊤ := by
    have hR := hRmem.eLpNorm_lt_top.ne
    have hE := hEmem.eLpNorm_lt_top.ne
    rw [hBtot]
    simp only [ne_eq, ENNReal.add_eq_top, ENNReal.mul_eq_top, ENNReal.ofReal_ne_top, hR, hE, hBX,
      false_and, and_false, or_self, not_false_eq_true]
  obtain ⟨hmem1, hmem2⟩ := aux_prop_growth_holder_macro_campanato_moment_conj
    (chaosSampleLaw M).toMeasure ps Pexp hpsP _ Btot hfin hmom
  exact ⟨_, _, aux_prop_growth_holder_macro_campanato_Kosc_nonneg M kk r t1 e alpha Kd _ Cp _ CPw
      P.C Lm _ _ Kg Mx Kmac hr (le_trans zero_le_one hKd1)
      (aux_prop_growth_macro_energy_nativeSreg M').C_pos.le hCp.le (Real.sqrt_nonneg _) hCPw
      P.C_pos.le (fun _ => (Real.exp_pos _).le) hΛ0 hKg0 hMx0 hKmac0, hmem1, hmem2,
    aux_prop_growth_trunc_holder_macro_ae_bound hd P Cp hCp.le hFO CPw hCPw hPoinc alpha
      ha0 Kd (le_trans zero_le_one hKd1) hKd M M' (aux_prop_growth_macro_energy_nativeSreg M') t1 e
      hδC hα' hαM he hexp ht1Y H H' H0 L0 hHT htau z r hr hr1 kk hk1 hk3 hT hshift Lm hHT' hLpre0 _
      hRdom _ Kg Mx Kmac hΛ0 hKg0 hKmac0 hΛle hKgsrc hext hmacE⟩

end HolderTrunc


theorem prop_growth_trunc_holder_macro :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E) (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (L0 : ℕ),
      H = (fun om' => infraredPartialSum om' L0) → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ rad → rad ≤ r →
            ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
                ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
                  (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z r hr)).1) ^ 2
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X S alpha k ps ha0 ha1 hps
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- one exponent for all listed orders
  obtain ⟨Pexp, hPdef⟩ : ∃ Pexp : ℝ, Pexp = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => by linarith [hps i]
  have hP1 : 1 ≤ Pexp := by rw [hPdef]; linarith
  have hpsP : ∀ i, ps i ≤ Pexp := by
    intro i
    rw [hPdef]
    have := Finset.single_le_sum (f := ps) (fun j _ => by linarith [hps j]) (Finset.mem_univ i)
    linarith
  -- the energy exponent and the excess
  obtain ⟨t1, ht1, ht2, ht10, hαM, he0, ht1Y⟩ :=
    aux_prop_growth_holder_macro_campanato_params d hd alpha ha0 ha1
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 2 + t1 - 2 * alpha - d := ⟨_, rfl⟩
  have he : 0 < e := by rw [hedef]; exact he0
  have hexp : 2 + t1 = 2 * alpha + d + e := by rw [hedef]; ring
  -- suppliers, all fixed before the model
  obtain ⟨dMac, hdMac, hmacro⟩ := prop_growth_trunc_macro_energy d hd E P X S t1 1 (fun _ => Pexp)
    ht1 ht2 (fun _ => hP1)
  obtain ⟨dB, hdB, hbank⟩ := aux_prop_growth_trunc_bank_cross d hd E P X S (2 * Pexp) (by linarith)
  obtain ⟨dA, hdA, hthr⟩ := aux_aux_macro_moment_bank_threshold (d := d) t1 (2 * Pexp) ht1 ht2
    ht10 (by linarith)
  obtain ⟨dLf, hdLf, hlamM⟩ := lane4_lambda_inv_moments d hd E (1 / 8)
    ⟨by norm_num, by norm_num⟩
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ :=
    aux_prop_growth_trunc_energy_assembly_root_extremes d hd Pexp hP1
  obtain ⟨CPw, hCPw0, hPoinc⟩ := aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  obtain ⟨Cp, hCp, hFO⟩ := aux_prop_growth_holder_macro_campanato_FO_exists (d := d) hd
  obtain ⟨Kd, hKd1, hKd⟩ := aux_prop_growth_holder_macro_campanato_unit' (d := d) alpha ha0 ha1.le
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hD0 := ResidualModel.residualDisorderFactor_pos d
  have hdL := hdLf (2 * Pexp) (by linarith)
  obtain ⟨dabs, hdabs⟩ : ∃ s : ℝ, s = min 1 ((e / 2) * Real.log 3 / (Cd + Cpe)) := ⟨_, rfl⟩
  have hdabs0 : 0 < dabs := by
    rw [hdabs]
    exact lt_min one_pos (div_pos (mul_pos (half_pos he) hlog3) (add_pos hCd hCpe))
  refine ⟨min dMac (min dB (min (dA / ResidualModel.residualDisorderFactor d)
    (min (2 * ResidualModel.residualDisorderFactor d)⁻¹ (min (dLf (2 * Pexp))
      (min (cd / (2 * Pexp)) dabs))))),
    lt_min hdMac (lt_min hdB (lt_min (div_pos hdA hD0) (lt_min (by positivity)
      (lt_min hdL (lt_min (div_pos hcd (by linarith)) hdabs0))))), ?_⟩
  intro M Rm H L0 hHT hδ z r hr hr1
  subst hHT
  have hδMac : M.delta ≤ dMac := hδ.trans (min_le_left _ _)
  have hδB : M.delta ≤ dB := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδA : M.delta ≤ dA / ResidualModel.residualDisorderFactor d :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδD : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹ :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))
  have hδL : M.delta ≤ dLf (2 * Pexp) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδc : M.delta ≤ cd / (2 * Pexp) :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
  have hδabs : M.delta ≤ dabs :=
    hδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ (e / 2) * Real.log 3 :=
    aux_prop_growth_holder_micro_campanato_rate Cd Cpe e M.delta hCd hCpe hdpos (hδabs.trans_eq hdabs)
  -- the residual scale and the bounded-dilation model `M_s`
  obtain ⟨kk, hk1, hk3⟩ := MacroAllCube.exists_residual_scale hr hr1
  obtain ⟨M', hM'⟩ : ∃ M' : _root_.SubdiffusiveProcess.Model.GMCModel d,
      M' = ResidualModel.residualModel M hk1.le hk3 hδD := ⟨_, rfl⟩
  have hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure := by
    rw [hM']; exact ResidualModel.measurePreserving_residualModel M r kk hk1.le hk3 hδD
  have htau : _root_.SubdiffusiveProcess.Model.tauSq M'.P = _root_.SubdiffusiveProcess.Model.tauSq M.P := by
    rw [hM']; exact ResidualModel.residualModel_tauSq M hk1.le hk3 hδD
  have hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤
        aux_prop_growth_macro_energy_env M kk om := by
    intro n om; rw [hM']; exact aux_prop_growth_macro_energy_shiftC_bounds M hk1.le hk3 hδD kk n om
  have hδ' : M'.delta ≤ dA := by
    rw [hM', ResidualModel.residualModel_delta]
    rw [le_div_iff₀ hD0] at hδA
    linarith
  obtain ⟨hδC', hα', hκ'⟩ := hthr M' (aux_prop_growth_macro_energy_nativeSreg M') hδ'
  obtain ⟨H0, hH0⟩ := exists_infraredCharacterization hd M
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      ((aux_prop_growth_macro_energy_nativeSreg M').C * M'.delta ^ 2 * |Real.log M'.delta|) :=
    ⟨_, rfl⟩
  rw [← hκ] at hκ'
  have hlam : 0 ≤ 2 * (2 * Pexp) * t1 * Real.log 3 := by
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
      Real.one_le_exp (mul_nonneg hκ0.le (by linarith))
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hX4 : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * (2 * Pexp))) (chaosSampleLaw M').toMeasure ≤
      ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))) := by
    intro n
    have hXmeas : Measurable (fun om : BilateralField d => (3 : ℝ) ^ (t1 * (Lm n om : ℝ))) :=
      measurable_const.pow (measurable_const.mul
        ((measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp (hLmeas n)))
    rw [← SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hXmeas.aestronglyMeasurable]
    exact aux_aux_macro_moment_bank_eLpNorm_rpow_three_le _ (Lm n) t1 (2 * (2 * Pexp))
      (by linarith) _ (aux_aux_macro_moment_bank_lintegral_exp_le (chaosSampleLaw M').toMeasure
        (Lm n) (hLmeas n) _ κ _ hA1 hlam hκ' (hLtail n))
  have hle24 : ENNReal.ofReal (2 * Pexp) ≤ ENNReal.ofReal (2 * (2 * Pexp)) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure ≤
      ENNReal.ofReal ((aux_prop_growth_macro_energy_nativeSreg M').C *
          Real.exp (κ * (aux_prop_growth_macro_energy_nativeSreg M').C) * Real.exp κ *
        (1 - Real.exp (-(κ - 2 * (2 * Pexp) * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * (2 * Pexp))) := by
    intro n
    have hXmeas : Measurable (fun om : BilateralField d => (3 : ℝ) ^ (t1 * (Lm n om : ℝ))) :=
      measurable_const.pow (measurable_const.mul
        ((measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp (hLmeas n)))
    exact (eLpNorm_le_eLpNorm_of_exponent_le hle24).trans (hX4 n)
  -- the macro energy of the actual problem
  obtain ⟨Kmac, CbK, hKmac0, hKmacmem, hKmacnorm, hmacE⟩ :=
    hmacro M Rm _ L0 rfl hδMac z r hr hr1
  -- the global energy
  obtain ⟨Kg, Cg, hKg0, hKgmem, hKgnorm, hKgsrc⟩ :=
    hbank M Rm hδB H0 hH0 L0 z r hr hr1
  -- the coarse ellipticity of the root
  obtain ⟨CbL, hLmem, hLnorm⟩ := hlamM M Rm H0 hH0 z r hr hr1 (2 * Pexp) (by linarith) hδL
  -- the coefficient floor
  obtain ⟨D, Mx, CD, CE, hCD, hCE, hDMx0, hext, hmem, -, hMxmom⟩ := hroot M L0 hδc z r hr hr1
  -- the residual reference factor
  obtain ⟨hRmeas, hRdom, hRmem⟩ := aux_prop_growth_trunc_bank_reference hd M' (kk + L0)
    (closedCube (r⁻¹ • z) 1 one_pos) (2 * Pexp) (by linarith)
  exact aux_prop_growth_trunc_holder_macro_assemble hd P Cp hCp hFO CPw hCPw0 hPoinc alpha ha0 Kd
    hKd1 hKd ps Pexp hP1 hpsP M M' (fun om' => infraredPartialSum om' L0)
    (fun om' => infraredPartialSum om' (kk + L0)) H0 L0 rfl htau t1 e ht10 hδC' hα' hαM he hexp
    ht1Y z r hr hr1 kk hk1 hk3 hT hshift Lm hLmeas rfl (Filter.Eventually.of_forall hLpre) _
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) hX hRmeas hRdom hRmem
    Kmac (CbK 0) hKmac0 (fun N => (hKmacmem 0 N).aestronglyMeasurable) (fun N => hKmacnorm 0 N) hmacE Kg Cg hKg0
    (fun N => (hKgmem N).aestronglyMeasurable) hKgnorm hKgsrc
    CbL (fun N => (hLmem N).aestronglyMeasurable) hLnorm Mx _ (fun N om => (hDMx0 N om).2) (fun N => (hmem N).2.aestronglyMeasurable)
    (fun N => aux_prop_growth_holder_macro_campanato_mx_moment _ _ (Mx N) e _ CE he hrate hCE N kk
      (hMxmom N))
    (by
      filter_upwards [hext] with om h
      intro N
      exact ⟨(h N).1, fun x hx => ((h N).2.1 x hx).1⟩)

end SubdiffusiveProcess.Paper
