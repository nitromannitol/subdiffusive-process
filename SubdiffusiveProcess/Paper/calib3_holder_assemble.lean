module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib3_holder_ae_bound
public import SubdiffusiveProcess.Paper.calib3_holder_middle
public import SubdiffusiveProcess.Paper.prop_growth_holder_macro_campanato
public import SubdiffusiveProcess.Paper.prop_growth_trunc_holder_macro
public import SubdiffusiveProcess.Paper.prop_growth_trunc_macro_energy
public import SubdiffusiveProcess.Paper.aux_macro_energy_recurrence
public import SubdiffusiveProcess.Paper.in_6_16

@[expose] public section

/-! Stage 3 (calibration): assembly of the macro Campanato constant `Kosc` with its moments (guarded levels `N ≥ j + kk`).
Copy of `aux_prop_growth_trunc_holder_macro_assemble` with the frame data as hypotheses. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators Pointwise ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section HolderAssemble

theorem calib3_holder_assemble {d : ℕ} (hd : 2 ≤ d)
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
    (j : ℕ)
    (t1 e : ℝ) (_ht10 : 0 ≤ t1)
    (hδC : M'.delta ≤ (aux_prop_growth_macro_energy_nativeSreg M').C⁻¹)
    (hα' : 1 - ((d : ℝ) - t1) / 4 ∈ (aux_prop_growth_macro_energy_nativeSreg M').alphaRange)
    (hαM : alpha ≤ 1 - ((d : ℝ) - t1) / 4)
    (he : 0 < e) (hexp : 2 + t1 = 2 * alpha + d + e) (ht1Y : alpha + (d : ℝ) / 2 ≤ t1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (kk : ℕ)
    (hk1 : 1 ≤ r * (3 : ℝ) ^ kk) (hk3 : r * (3 : ℝ) ^ kk ≤ 3)
    (hT : MeasurePreserving (MacroAllCube.residualShift (d := d) r kk)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure)
    (hshift : ∀ n om, aux_prop_growth_macro_energy_shiftC M M' kk n om ≤
        aux_prop_growth_macro_energy_env M kk om ∧
      (aux_prop_growth_macro_energy_shiftC M M' kk n om)⁻¹ ≤ aux_prop_growth_macro_energy_env M kk om)
    (Lm : ℕ → BilateralField d → ℕ) (hLmeas : ∀ n, Measurable (Lm n))
    (hcid : ∀ (n : ℕ) (om : BilateralField d) (x : SpatialCoordinates d),
      cutoffCoefficient M H om (n + kk) (r • x) =
        aux_prop_growth_macro_energy_shiftC M M' kk n om *
          cutoffCoefficient M' H' (MacroAllCube.residualShift r kk om) n x)
    (Rs : BilateralField d → ℝ)
    (hFEd : aux_calib3_holder_ae_bound_FEData (aux_prop_growth_macro_energy_nativeSreg M') H' t1 z r Lm Rs j)
    (BX : ℝ≥0∞) (hBX : BX ≠ ⊤)
    (hX : ∀ n, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (Lm n om : ℝ)))
      (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure ≤ BX)
    (hRsm : Measurable Rs) (BR : ℝ≥0∞) (hBR : BR ≠ ⊤)
    (hR : eLpNorm Rs (ENNReal.ofReal (2 * Pexp)) (chaosSampleLaw M').toMeasure ≤ BR)
    (Kmac : ℕ → BilateralField d → ℝ) (BK : ℝ) (hKmac0 : ∀ N om, 0 ≤ Kmac N om)
    (hKmacmem : ∀ N, AEStronglyMeasurable (Kmac N) (chaosSampleLaw M).toMeasure)
    (hKmacnorm : ∀ N, eLpNorm (Kmac N) (ENNReal.ofReal Pexp) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal BK)
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
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hRs0 : ∀ om', 0 ≤ Rs om' := by
    intro om'
    obtain ⟨Lc, cF, hcF, -, hk1', -, -⟩ := hFEd j le_rfl om'
    have := mul_pos hcF ((aux_prop_growth_macro_energy_nativeSreg M').refAvg_pos Lc j
      ((3 : ℝ) ^ j • (r⁻¹ • z)) (aux_aux_macro_energy_recurrence_relabel j om'))
    linarith
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
    (Real.sqrt_nonneg _) hCPw P.C_pos.le Pexp hP1 hT Lm hLmeas BX hX Rs hRsm BR hR _ le_rfl
    (fun N om => (E.lam z r hr (cutoffPositiveCoefficient M H0 om N z hr) z r (1 / 8) 1)⁻¹) Kg Mx
    Kmac (ENNReal.ofReal BL) (ENNReal.ofReal BG) (ENNReal.ofReal BM) (ENNReal.ofReal BK)
    hLmem hLnorm hKgmem hKgnorm hMxm hMb hKmacmem hKmacnorm N
  set Btot := (ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * (aux_prop_growth_macro_energy_nativeSreg M').C *
            (3 * d))) +
          ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * (aux_prop_growth_macro_energy_nativeSreg M').C *
            Real.sqrt ((r⁻¹) ^ d * (P.C * r) ^ 2))) * (ENNReal.ofReal BL + ENNReal.ofReal BG) +
          ENNReal.ofReal (r ^ (-alpha) * Kd * (2 * (aux_prop_growth_macro_energy_nativeSreg M').C *
            (2 * Cp))) *
            (BR * eLpNorm (aux_prop_growth_macro_energy_env M kk) (ENNReal.ofReal (2 * Pexp))
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
    have hE := hEmem.eLpNorm_lt_top.ne
    rw [hBtot]
    simp only [ne_eq, ENNReal.add_eq_top, ENNReal.mul_eq_top, ENNReal.ofReal_ne_top, hBR, hE, hBX,
      false_and, and_false, or_self, not_false_eq_true]
  obtain ⟨hmem1, hmem2⟩ := aux_prop_growth_holder_macro_campanato_moment_conj
    (chaosSampleLaw M).toMeasure ps Pexp hpsP _ Btot hfin hmom
  exact ⟨_, _, aux_prop_growth_holder_macro_campanato_Kosc_nonneg M kk r t1 e alpha Kd _ Cp _ CPw
      P.C Lm _ _ Kg Mx Kmac hr (le_trans zero_le_one hKd1)
      (aux_prop_growth_macro_energy_nativeSreg M').C_pos.le hCp.le (Real.sqrt_nonneg _) hCPw
      P.C_pos.le hRs0 hΛ0 hKg0 hMx0 hKmac0, hmem1, hmem2,
    calib3_holder_ae_bound hd P Cp hCp.le hFO CPw hCPw hPoinc alpha
      ha0 Kd (le_trans zero_le_one hKd1) hKd M M' (aux_prop_growth_macro_energy_nativeSreg M') t1 e
      hδC hα' hαM he hexp ht1Y H H' H0 j z r hr hr1 kk hk1 hk3 hT hshift Lm hcid Rs hFEd _ Kg Mx Kmac hΛ0 hKg0 hKmac0 hΛle hKgsrc hext hmacE⟩


end HolderAssemble

end SubdiffusiveProcess.Paper
