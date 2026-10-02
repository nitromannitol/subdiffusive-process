import Mathlib
import SubdiffusiveProcess.Paper.calib3_holder_middle
import SubdiffusiveProcess.Paper.prop_growth_holder_macro_campanato
import SubdiffusiveProcess.Paper.prop_growth_trunc_holder_macro
import SubdiffusiveProcess.Paper.prop_growth_trunc_macro_energy
import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
import SubdiffusiveProcess.Paper.in_6_16

/-! Stage 3 (calibration): the almost-sure macro Campanato bound at levels `N ≥ j + kk` (guarded: the Section-6 frame identity of
the top-block-removed coefficient needs the frame `n ≥ j`).  Copy of `aux_prop_growth_trunc_holder_macro_ae_bound` with the
frame data as hypotheses. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section HolderAeBound

variable {d : ℕ}

/-- The Section-6 frame data (`hFEd` of `calib3_holder_middle`) at every frame `n ≥ j`, with its prefix bound. -/
def aux_calib3_holder_ae_bound_FEData {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] {M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg' : in_6_16 d M')
    (H' : BilateralField d → C(SpatialCoordinates d, ℝ)) (t1 : ℝ) (z : SpatialCoordinates d) (r : ℝ)
    (Lm : ℕ → BilateralField d → ℕ) (Rs : BilateralField d → ℝ) (j : ℕ) : Prop :=
  ∀ n : ℕ, j ≤ n → ∀ om' : BilateralField d, ∃ Lc : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
      (∀ᵐ y ∂volume.restrict (centeredCube (r⁻¹ • z) 1 one_pos : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M' H' om' n (r⁻¹ • z) one_pos).val y =
          cFin * (Sreg'.cutoffOn Lc (aux_aux_macro_energy_recurrence_relabel n om')
            ((3 : ℝ) ^ n • (r⁻¹ • z)) (3 ^ n) (pow_pos (by norm_num) n)).val ((3 : ℝ) ^ n • y)) ∧
      cFin * Sreg'.refAvg Lc n ((3 : ℝ) ^ n • (r⁻¹ • z)) (aux_aux_macro_energy_recurrence_relabel n om') ≤ 2 * Rs om' ∧
      (cFin * Sreg'.refAvg Lc n ((3 : ℝ) ^ n • (r⁻¹ • z)) (aux_aux_macro_energy_recurrence_relabel n om'))⁻¹ ≤ 2 * Rs om' ∧
      Sreg'.prefixLen Lc (1 - ((d : ℝ) - t1) / 4) n ((3 : ℝ) ^ n • (r⁻¹ • z))
        (aux_aux_macro_energy_recurrence_relabel n om') ≤ Lm n om'

theorem calib3_holder_ae_bound (hd : 2 ≤ d)
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
    (M M' : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg' : in_6_16 d M') (t1 e : ℝ)
    (hδC : M'.delta ≤ Sreg'.C⁻¹) (hαM : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg'.alphaRange)
    (hαα : alpha ≤ 1 - ((d : ℝ) - t1) / 4)
    (he : 0 < e) (hexp : 2 + t1 = 2 * alpha + d + e) (ht1Y : alpha + (d : ℝ) / 2 ≤ t1)
    (H H' H0 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (j : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (kk : ℕ)
    (hk1 : 1 ≤ r * (3 : ℝ) ^ kk) (hk3 : r * (3 : ℝ) ^ kk ≤ 3)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure)
    (hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤ aux_prop_growth_macro_energy_env M kk om)
    (Lm : ℕ → BilateralField d → ℕ)
    (hcid : ∀ (n : ℕ) (om : BilateralField d) (x : SpatialCoordinates d),
      cutoffCoefficient M H om (n + kk) (r • x) =
        aux_prop_growth_macro_energy_shiftC M M' kk n om *
          cutoffCoefficient M' H' (MacroAllCube.residualShift r kk om) n x)
    (Rs : BilateralField d → ℝ)
    (hFEd : aux_calib3_holder_ae_bound_FEData Sreg' H' t1 z r Lm Rs j)
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
      ∀ (N : ℕ), j ≤ N → ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
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
      ∀ (N : ℕ), j + kk ≤ N → ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
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
  filter_upwards [hKgsrc, hmacE, hext]
    with om hsrc hmac hex
  intro N hjN F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve x hx rad hradN hradr
  have hglob := hsrc N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
  have hmacN := hmac N (by omega) F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
  obtain ⟨hMx, hfl⟩ := hex N
  have hCphi0 : 0 ≤ Cphi := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ phi).trans hCphi
  unfold aux_prop_growth_holder_macro_campanato_Kosc
  have hN : kk ≤ N := by omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + kk := ⟨N - kk, by omega⟩
  rw [if_pos hN, Nat.add_sub_cancel]
  obtain ⟨Lc, cF, hcF, hid, hk1', hk2', hpre⟩ := hFEd n (by omega) (MacroAllCube.residualShift r kk om)
  exact calib3_holder_middle hd P Cp hCp hFO CPw hCPw hPoinc alpha hα0
    Kd hKd0 hKd M M' Sreg' _ hδC hαM hαα t1 e he hexp ht1Y H H' H0 om
    (MacroAllCube.residualShift r kk om) z r hr hr1 kk n hk1
    (aux_prop_growth_macro_energy_shiftC M M' kk n om) (aux_prop_growth_macro_energy_env M kk om)
    (aux_prop_growth_macro_energy_shiftC_pos M M' kk n om) (hshift n om).2
    (fun x => hcid n om x)
    (Lm n (MacroAllCube.residualShift r kk om)) (pow_pos (by norm_num) n)
    (Rs (MacroAllCube.residualShift r kk om)) Lc ⟨cF, hcF, hid, hk1', hk2'⟩ hpre
    (Λ (n + kk) om) (Kg (n + kk) om) (Mx (n + kk) om) (Kmac (n + kk) om) (hΛ0 _ _)
    (hKg0 _ _) (hKmac0 _ _) (hΛ _ _) hMx hfl F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    hglob hmacN x hx rad hradN hradr

end HolderAeBound

end Paper
