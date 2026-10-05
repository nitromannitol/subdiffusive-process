module

public import SubdiffusiveProcess.Paper.goodext_coarse_poincare
public import SubdiffusiveProcess.Paper.goodext_adjacent_reference
public import SubdiffusiveProcess.Sobolev.WeakEquationRestrict
public import SubdiffusiveProcess.EllipticRegularity.CutoffCoefficientRepresentative
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Analysis.HolderEnergyScaling

@[expose] public section

/-! The padded enlargement of a finite good cell has a coarse Poincare bound in the cell's
own reference scalar and the parent energy. The padded root reference is compared with the
cell reference through the single intervening layer. No regularity estimate is asserted. -/

open Filter MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Scalar bookkeeping for the padded Poincare bound with an adjacent reference comparison. -/
theorem aux_lfgc_padded_poincare_scalar (d : ℕ) (PC c cell r s s' E G X Vol : ℝ)
    (hPC : 0 ≤ PC) (hc : 0 < c) (hcell : 0 < cell) (hr : 0 < r) (hs : 0 < s) (hs' : 0 < s')
    (hEG : E ≤ G) (hss : s ≤ Real.exp 2 * s') (hVol : Vol = (3 * r) ^ d)
    (hX : X ≤ PC * (3 * r) * (c * (cell * s')) ^ (-(1 / 2) : ℝ) * Real.sqrt (E / Vol)) :
    X ≤ PC * (c * cell) ^ (-(1 / 2) : ℝ) * Real.exp 2 * (3 : ℝ) ^ (((2 : ℝ) - d) / 2) *
        r ^ (((2 : ℝ) - d) / 2) * s ^ (-(1 : ℝ) / 2) * Real.sqrt G := by
  subst hVol
  have h3r : 0 < 3 * r := by positivity
  have hcc : 0 < c * cell := mul_pos hc hcell
  have hsplit : (c * (cell * s')) ^ (-(1 / 2) : ℝ) =
      (c * cell) ^ (-(1 / 2) : ℝ) * (Real.sqrt s')⁻¹ := by
    rw [← mul_assoc, Real.mul_rpow hcc.le hs'.le, Real.rpow_neg hs'.le, ← Real.sqrt_eq_rpow]
  have hinv : (Real.sqrt s')⁻¹ ≤ Real.exp 2 * s ^ (-(1 : ℝ) / 2) :=
    inv_sqrt_le_reference_factor hs hs' (Real.one_le_exp (by norm_num)) hss
  have hrad : 3 * r / Real.sqrt ((3 * r) ^ d) =
      (3 : ℝ) ^ (((2 : ℝ) - d) / 2) * r ^ (((2 : ℝ) - d) / 2) := by
    rw [radius_div_sqrt_volume d (3 * r) h3r, Real.mul_rpow (by norm_num) hr.le]
  have hsq : Real.sqrt (E / (3 * r) ^ d) = Real.sqrt E / Real.sqrt ((3 * r) ^ d) :=
    Real.sqrt_div' E (pow_nonneg h3r.le d)
  have hEq : PC * (3 * r) * (c * (cell * s')) ^ (-(1 / 2) : ℝ) * Real.sqrt (E / (3 * r) ^ d) =
      PC * (c * cell) ^ (-(1 / 2) : ℝ) * (Real.sqrt s')⁻¹ *
        ((3 : ℝ) ^ (((2 : ℝ) - d) / 2) * r ^ (((2 : ℝ) - d) / 2)) * Real.sqrt E := by
    rw [hsplit, hsq, ← hrad]
    ring
  have hA : 0 ≤ PC * (c * cell) ^ (-(1 / 2) : ℝ) :=
    mul_nonneg hPC (Real.rpow_nonneg hcc.le _)
  have hB : 0 ≤ (3 : ℝ) ^ (((2 : ℝ) - d) / 2) * r ^ (((2 : ℝ) - d) / 2) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hr.le _)
  calc X ≤ PC * (c * cell) ^ (-(1 / 2) : ℝ) * (Real.sqrt s')⁻¹ *
        ((3 : ℝ) ^ (((2 : ℝ) - d) / 2) * r ^ (((2 : ℝ) - d) / 2)) * Real.sqrt E := hEq ▸ hX
    _ ≤ PC * (c * cell) ^ (-(1 / 2) : ℝ) * (Real.exp 2 * s ^ (-(1 : ℝ) / 2)) *
        ((3 : ℝ) ^ (((2 : ℝ) - d) / 2) * r ^ (((2 : ℝ) - d) / 2)) * Real.sqrt G := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hinv hA) hB) (Real.sqrt_le_sqrt hEG)
        (Real.sqrt_nonneg _)
      exact mul_nonneg (mul_nonneg hA (mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg hs.le _))) hB
    _ = PC * (c * cell) ^ (-(1 / 2) : ℝ) * Real.exp 2 * (3 : ℝ) ^ (((2 : ℝ) - d) / 2) *
        r ^ (((2 : ℝ) - d) / 2) * s ^ (-(1 : ℝ) / 2) * Real.sqrt G := by ring

/-- The padded cube's coarse lower bound in its root reference, one bounded intervening layer,
and the cell reference give the centred oscillation on the padded cube in parent energy. -/
theorem lfgc_padded_poincare {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (sigma cell : ℝ) (hsigma : 0 < sigma)
    (hsigma1 : 2 * sigma ≤ 1) (hcell : 0 < cell) :
    ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), in_responses d M → M.delta ≤ 1 →
    ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
      (m k : ℕ) (z : SpatialCoordinates d) (r : ℝ), 0 < r → ∀ (hr3 : 0 < 3 * r),
      |omega (-((k : ℤ) - 1)) z| ≤ 1 →
      cell * aux_in_deterministic_onestep_sref M H omega (m + k) ((k : ℤ) - 1) z ≤
        I.lam z (3 * r) hr3 (cutoffPositiveCoefficient M H omega (m + k) z hr3)
          z (3 * r) sigma 2 →
      ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      (Metric.ball z (3 * r / 2) : Set (SpatialCoordinates d)) ⊆
        (centeredCube zP R hR : Set (SpatialCoordinates d)) →
      ∀ (u : weakSobolevGraph (centeredCube zP R hR)) (U : SpatialCoordinates d → ℝ),
      ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Metric.ball z (3 * r / 2))] U) →
      normalizedL2On (Metric.ball z (3 * r / 2))
        (fun y => U y - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
          ∫ v in Metric.ball z (3 * r / 2), U v) ≤
        Cp * r ^ (((2 : ℝ) - d) / 2) *
          (aux_in_deterministic_onestep_sref M H omega (m + k) (k : ℤ) z) ^ (-(1 : ℝ) / 2) *
          Real.sqrt (sobolevCoefficientForm (cutoffPositiveCoefficient M H omega (m + k) zP hR)
            u.val u.val) := by
  set c : ℝ := Homogenization.Book.Ch02.geometricDiscount sigma 2 /
    Homogenization.Book.Ch02.geometricDiscount 1 1 with hcdef
  have hc : 0 < c := div_pos
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by positivity))
    (Homogenization.Book.Ch02.book_geometricDiscount_pos (by norm_num))
  refine ⟨Pin.C * (c * cell) ^ (-(1 / 2) : ℝ) * Real.exp 2 * (3 : ℝ) ^ (((2 : ℝ) - d) / 2),
    by have := Pin.C_pos; positivity, ?_⟩
  intro M Rm hdelta1 H omega m k z r hr hr3 hlayer hell zP R hR hsubset u U hU
  set N := m + k with hN
  set V : Opens (SpatialCoordinates d) := centeredCube z (3 * r) hr3 with hVdef
  have hsub : V ≤ centeredCube zP R hR := hsubset
  set aV := cutoffPositiveCoefficient M H omega N z hr3 with haVdef
  set aP := cutoffPositiveCoefficient M H omega N zP hR with haPdef
  have hab : (aP.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))]
      aV.val := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubset
      (cutoffPositiveCoefficient_representative M H omega N zP hR).2.2.2,
      (cutoffPositiveCoefficient_representative M H omega N z hr3).2.2.2] with x hx hy
    exact hx.trans hy.symm
  let uV : weakSobolevGraph V :=
    ⟨sobolevDataRestrict hsub u.val, sobolevDataRestrict_mem_weak hsub u.property⟩
  have hUV : ((uV.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (V : Set (SpatialCoordinates d))] U) := by
    filter_upwards [domainLpRestrict_coeFn hsub u.val.1, hU] with x hx hy
    exact hx.trans hy
  have hs' := aux_in_deterministic_onestep_sref_pos M H omega N ((k : ℤ) - 1) z
  have hs := aux_in_deterministic_onestep_sref_pos M H omega N (k : ℤ) z
  have hpc := goodext_coarse_poincare hd I Pin z (3 * r) hr3 aV uV U hUV sigma cell
    (aux_in_deterministic_onestep_sref M H omega N ((k : ℤ) - 1) z) hsigma hsigma1 hcell hs' hell
  rw [localGradientEnergy_domain_eq_sobolevCoefficientForm] at hpc
  have hEG : sobolevCoefficientForm aV uV.val uV.val ≤ sobolevCoefficientForm aP u.val u.val :=
    sobolevCoefficientForm_restrict_le hsub aP aV hab u.val
  have hadj := goodext_adjacent_reference M Rm H omega N k (by omega) z
  have hexp : Real.exp (_root_.SubdiffusiveProcess.Model.tauSq M.P + |omega (-((k : ℤ) - 1)) z|) ≤
      Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    have htau := tauSq_le_delta_sq M
    have hd0 := M.shellPrefix.delta_pos
    have hd2 : M.delta ^ 2 ≤ 1 := by nlinarith only [hd0, hdelta1]
    have hlog : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith only [this]
    have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hprod : Real.log 2 / 2 * M.delta ^ 2 ≤ 1 := by
      nlinarith only [hd2, hlog, hlog0, sq_nonneg M.delta]
    linarith only [htau, hlayer, hprod]
  have hss : aux_in_deterministic_onestep_sref M H omega N (k : ℤ) z ≤
      Real.exp 2 * aux_in_deterministic_onestep_sref M H omega N ((k : ℤ) - 1) z := by
    calc _ ≤ _ := hadj
      _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hexp hs'.le
  exact aux_lfgc_padded_poincare_scalar d Pin.C c cell r _ _ _ _ _ _ Pin.C_pos.le hc hcell hr hs hs'
    hEG hss (centeredCube_volume_real z hr3) hpc

end SubdiffusiveProcess.Paper
