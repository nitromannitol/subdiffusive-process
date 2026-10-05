module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib3_holder_unit
public import SubdiffusiveProcess.Paper.prop_growth_holder_macro_campanato
public import SubdiffusiveProcess.Paper.prop_growth_trunc_holder_macro
public import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
public import SubdiffusiveProcess.Paper.in_6_16

@[expose] public section

/-! Stage 3 (calibration): the "middle" Campanato step (variance decay from the wavelength to the root cube), with the unit-cube
variance decay input `calib3_holder_unit` (FE level `Lc` arbitrary).  Copy of `aux_prop_growth_trunc_holder_macro_middle`
whose only change is the supplier of `H1`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section HolderMiddle

variable {d : ℕ}

theorem calib3_holder_middle (hd : 2 ≤ d)
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
    (P0 : ℕ) (hR : (0 : ℝ) < 3 ^ n)
    (Rs : ℝ) (Lc : ℕ)
    (hFEd : ∃ cFin : ℝ, 0 < cFin ∧
      (∀ᵐ y ∂volume.restrict (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M' H' om' n (r⁻¹ • z) one_pos).val y =
          cFin * (Sreg'.cutoffOn Lc (aux_aux_macro_energy_recurrence_relabel n om')
            ((3 : ℝ) ^ n • (r⁻¹ • z)) (3 ^ n) hR).val ((3 : ℝ) ^ n • y)) ∧
      cFin * Sreg'.refAvg Lc n ((3 : ℝ) ^ n • (r⁻¹ • z)) (aux_aux_macro_energy_recurrence_relabel n om') ≤ 2 * Rs ∧
      (cFin * Sreg'.refAvg Lc n ((3 : ℝ) ^ n • (r⁻¹ • z)) (aux_aux_macro_energy_recurrence_relabel n om'))⁻¹ ≤ 2 * Rs)
    (hpre0 : Sreg'.prefixLen Lc alphaM n ((3 : ℝ) ^ n • (r⁻¹ • z))
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ P0)
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
  have H1 := calib3_holder_unit hd Cp hCp hFO M' Sreg' alphaM alpha hδC
    hαM hαα H' om' (r⁻¹ • z) n P0 hR Rs Lc hFEd hpre0 F' (c⁻¹ * r ^ 2 * Kf) hKf' hF'm hF'b
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
  have hRs0 : 0 ≤ Rs := by
    obtain ⟨cF, hcF, -, hk1, -⟩ := hFEd
    have := mul_pos hcF (Sreg'.refAvg_pos Lc n ((3 : ℝ) ^ n • (r⁻¹ • z)) (aux_aux_macro_energy_recurrence_relabel n om'))
    linarith
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

end HolderMiddle

end SubdiffusiveProcess.Paper
