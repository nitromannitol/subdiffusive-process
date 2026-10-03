module

public import SubdiffusiveProcess.FiniteStopping.HarmonicStepComparison
public import SubdiffusiveProcess.Sobolev.WeakEquationRestrict

@[expose] public section

/-! Sourced per-cell comparison of the finite stopping construction (paper
`\label{mfd:lem-finite-source-comparison}`, first paragraph: "on a good padded cube `q` of side `r` and
parent `p`, the deterministic sourced estimate adds to the local comparison the term
`C η r_{N,M}(k) s_M(q)^{-1} r^{d+2} ‖f‖²`").

This is the source-carrying analogue of `comparison_of_reg_trace` / `comparison_at_stage`: `Reg` is applied at the
actual source `(F, Kf)` of the root solution instead of `(0, 0)`. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- Algebra of the sourced comparison: the trace closeness on a class whose norm is bounded by the two-term
Hölder estimate `Cfin r^{(2-d)/2} sS^{-1/2} √E + Cfin r² sS⁻¹ Kf`. -/
theorem conjunct2_core_src
    (r sT sS Cfin eta Q Eparent Kf X Y dreal : ℝ)
    (hr : 0 < r) (hsT : 0 < sT) (hsS : 0 < sS) (hCfin : 0 < Cfin) (heta : 0 < eta)
    (hQ0 : 0 ≤ Q) (hE0 : 0 ≤ Eparent) (hKf : 0 ≤ Kf)
    (hQ : Q ≤ Cfin * r ^ (((2 : ℝ) - dreal) / 2) * sS ^ (-(1 : ℝ) / 2) * Real.sqrt Eparent +
      Cfin * r ^ (2 : ℝ) * sS⁻¹ * Kf)
    (hTrace : |X / (r ^ (dreal - 2) * sT) - Y / (r ^ (dreal - 2) * sS)| ≤ eta * Q ^ 2) :
    X ≤ (sT / sS) * Y +
      2 * Cfin ^ 2 * eta * (sT / sS) * (Eparent + r ^ (dreal + 2) * sS⁻¹ * Kf ^ 2) := by
  set rp := r ^ (dreal - 2) with hrp_def
  have hrp : 0 < rp := Real.rpow_pos_of_pos hr _
  have hstep : X / (rp * sT) ≤ Y / (rp * sS) + eta * Q ^ 2 := by
    have h2 := (abs_le.mp hTrace).2
    linarith only [h2]
  have heqX : rp * sT * (X / (rp * sT)) = X := by
    field_simp
  have heqY : rp * sT * (Y / (rp * sS)) = (sT / sS) * Y := by
    field_simp
  have hmul : rp * sT * (X / (rp * sT)) ≤ rp * sT * (Y / (rp * sS) + eta * Q ^ 2) :=
    mul_le_mul_of_nonneg_left hstep (mul_pos hrp hsT).le
  rw [heqX, mul_add, heqY] at hmul
  set a := Cfin * r ^ (((2 : ℝ) - dreal) / 2) * sS ^ (-(1 : ℝ) / 2) * Real.sqrt Eparent with ha_def
  set b := Cfin * r ^ (2 : ℝ) * sS⁻¹ * Kf with hb_def
  have ha0 : 0 ≤ a := by
    rw [ha_def]
    have : 0 ≤ Cfin * r ^ (((2 : ℝ) - dreal) / 2) * sS ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (mul_nonneg hCfin.le (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hsS.le _)
    exact mul_nonneg this (Real.sqrt_nonneg _)
  have hb0 : 0 ≤ b := by
    rw [hb_def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCfin.le (Real.rpow_nonneg hr.le _))
      (inv_nonneg.2 hsS.le)) hKf
  have hQsq : Q ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    have h1 : Q ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
    nlinarith only [h1, sq_nonneg (a - b)]
  have ha2 : a ^ 2 = Cfin ^ 2 * r ^ (2 - dreal) * sS⁻¹ * Eparent := by
    rw [ha_def]
    have hexpand : (Cfin * r ^ (((2 : ℝ) - dreal) / 2) * sS ^ (-(1 : ℝ) / 2) *
        Real.sqrt Eparent) ^ 2 =
        Cfin ^ 2 * (r ^ (((2 : ℝ) - dreal) / 2)) ^ 2 * (sS ^ (-(1 : ℝ) / 2)) ^ 2 *
          (Real.sqrt Eparent) ^ 2 := by ring
    rw [hexpand]
    have hr2 : (r ^ (((2 : ℝ) - dreal) / 2)) ^ 2 = r ^ (2 - dreal) := by
      rw [← Real.rpow_natCast (r ^ (((2 : ℝ) - dreal) / 2)) 2, ← Real.rpow_mul hr.le]
      norm_num
    have hs2 : (sS ^ (-(1 : ℝ) / 2)) ^ 2 = sS⁻¹ := by
      rw [← Real.rpow_natCast (sS ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hsS.le]
      norm_num
      rw [Real.rpow_neg hsS.le, Real.rpow_one]
    have he2 : (Real.sqrt Eparent) ^ 2 = Eparent := Real.sq_sqrt hE0
    rw [hr2, hs2, he2]
  have hb2 : b ^ 2 = Cfin ^ 2 * r ^ (4 : ℝ) * sS⁻¹ ^ 2 * Kf ^ 2 := by
    rw [hb_def]
    have hr4 : (r ^ (2 : ℝ)) ^ 2 = r ^ (4 : ℝ) := by
      rw [← Real.rpow_natCast (r ^ (2 : ℝ)) 2, ← Real.rpow_mul hr.le]
      norm_num
    calc (Cfin * r ^ (2 : ℝ) * sS⁻¹ * Kf) ^ 2
        = Cfin ^ 2 * (r ^ (2 : ℝ)) ^ 2 * sS⁻¹ ^ 2 * Kf ^ 2 := by ring
      _ = _ := by rw [hr4]
  have hrr : rp * r ^ (2 - dreal) = 1 := by
    rw [hrp_def, ← Real.rpow_add hr]
    norm_num
  have hrr2 : rp * r ^ (4 : ℝ) = r ^ (dreal + 2) := by
    rw [hrp_def, ← Real.rpow_add hr]
    congr 1
    ring
  have herr : rp * sT * (eta * Q ^ 2) ≤
      2 * Cfin ^ 2 * eta * (sT / sS) * (Eparent + r ^ (dreal + 2) * sS⁻¹ * Kf ^ 2) := by
    have hstep2 : rp * sT * (eta * Q ^ 2) ≤
        rp * sT * (eta * (2 * a ^ 2 + 2 * b ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQsq heta.le) (mul_pos hrp hsT).le
    rw [ha2, hb2] at hstep2
    have heq : rp * sT * (eta * (2 * (Cfin ^ 2 * r ^ (2 - dreal) * sS⁻¹ * Eparent) +
        2 * (Cfin ^ 2 * r ^ (4 : ℝ) * sS⁻¹ ^ 2 * Kf ^ 2))) =
        2 * Cfin ^ 2 * eta * (sT / sS) * (Eparent * (rp * r ^ (2 - dreal)) +
          (rp * r ^ (4 : ℝ)) * sS⁻¹ * Kf ^ 2) := by
      rw [div_eq_mul_inv]; ring
    rw [heq, hrr, hrr2, mul_one] at hstep2
    exact hstep2
  linarith only [hmul, herr]

/-- The sourced comparison at one padded child `q` (centre `zQ`, side `3^{-H1 n}`) of a parent `p`
(centre `zP`, side `3^{H1}` times that): the paper's local estimate with the extra source term. `u` is ANY
weak solution of the sourced equation on the root (Dirichlet or Neumann), given through the Dirichlet-type
test identity `hsol`. -/
theorem comparison_of_reg_trace_src
    [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (alpha eta Cfin pad : ℝ) (heta : 0 < eta) (hCfin : 0 < Cfin) (hpad : 1 < pad)
    (H1 n target source : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hFm : Measurable F) (hKf : 0 ≤ Kf)
    (hFb : ∀ x ∈ centeredCube z r hr, |F x| ≤ Kf)
    (hsol : ∀ psi : killedSobolevGraph (centeredCube z r hr),
      sobolevCoefficientForm (cutoffPositiveCoefficient model H omega source z hr)
          (u : SobolevData (centeredCube z r hr)) (psi : SobolevData (centeredCube z r hr)) =
        ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          F x * (psi : SobolevData (centeredCube z r hr)).1 x)
    (zQ zP : SpatialCoordinates d) (rQ rP : ℝ) (hrQ : 0 < rQ) (hrP : 0 < rP)
    (hdepth : rQ = (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ)))
    (hsize : rP = (3 : ℝ) ^ H1 * rQ)
    (hQroot : centeredCube zQ rQ hrQ ≤ centeredCube z r hr)
    (hProot : centeredCube zP rP hrP ≤ centeredCube z r hr)
    (hQP : centeredCube zQ rQ hrQ ≤ centeredCube zP rP hrP)
    (idx : OddGridIndex d (subdivisionHalfWidth H1))
    (hcenter : zQ = oddGridCenter zP rP (subdivisionHalfWidth H1) idx)
    (hcontained : (closedCube zQ (pad * rQ) (mul_pos (lt_trans zero_lt_one hpad) hrQ) :
        Set (SpatialCoordinates d)) ⊆ centeredCube zP rP hrP)
    (hReg : SubdiffusiveProcess.FiniteStopping.Reg model H alpha H1 pad Cfin hpad
      source (H1 * n) zQ omega)
    (hTrace : SubdiffusiveProcess.FiniteStopping.trace_close model H alpha eta
      target source (H1 * n) zQ omega)
    (hPQ : ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube zQ rQ hrQ),
      ‖(v : SobolevData (centeredCube zQ rQ hrQ)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube zQ rQ hrQ)) v‖) :
    let aT := cutoffPositiveCoefficient model H omega target z hr
    let aS := cutoffPositiveCoefficient model H omega source z hr
    SubdiffusiveProcess.FiniteStopping.respOn aT u hQroot hPQ ≤
      SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source n *
        SubdiffusiveProcess.FiniteStopping.respOn aS u hQroot hPQ +
      2 * Cfin ^ 2 * eta *
        SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source n *
        (SubdiffusiveProcess.FiniteStopping.energyOn aS u.val (centeredCube zP rP hrP) +
          rQ ^ ((d : ℝ) + 2) *
            (SubdiffusiveProcess.FiniteStopping.reference model H omega source (H1 * n) zQ)⁻¹ *
              Kf ^ 2) := by
  subst rP
  subst rQ
  let aT := cutoffPositiveCoefficient model H omega target z hr
  let aS := cutoffPositiveCoefficient model H omega source z hr
  let uP : weakSobolevGraph _ :=
    ⟨sobolevDataRestrict hProot u.val, sobolevDataRestrict_mem_weak hProot u.property⟩
  let uQ : weakSobolevGraph _ :=
    ⟨sobolevDataRestrict hQroot u.val, sobolevDataRestrict_mem_weak hQroot u.property⟩
  have hweakP : ∀ psi : killedSobolevGraph (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP),
      sobolevCoefficientForm (cutoffPositiveCoefficient model H omega source zP hrP)
          (uP : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP))
          (psi : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP)) =
        ∫ x in (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP :
            Set (SpatialCoordinates d)),
          F x * (psi : SobolevData (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP)).1 x := by
    have hab : ((cutoffPositiveCoefficient model H omega source z hr).val :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube zP ((3 : ℝ) ^ H1 * (3 : ℝ) ^ (-((H1 * n : ℕ) : ℤ))) hrP :
          Set (SpatialCoordinates d))]
        (cutoffPositiveCoefficient model H omega source zP hrP).val := by
      have h1 := positiveCoefficientRestrict_coeFn hProot
        (cutoffPositiveCoefficient model H omega source z hr)
      rw [SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff model H omega
        source z hr zP hrP hProot] at h1
      exact h1.symm
    exact SubdiffusiveProcess.weakEquation_restrict hProot _ _ hab
      (u : SobolevData (centeredCube z r hr)) F hsol
  obtain ⟨U, c, hcont, hae, hholder, hnorm⟩ := hReg zP idx hcenter hcontained
    F Kf hFm hKf (fun x hx => hFb x (hProot hx)) uP hweakP
  have hclass := SubdiffusiveProcess.FiniteStopping.reg_to_boundary_class zQ _ hrQ alpha
    U c hcont hholder
  have hnorm' := SubdiffusiveProcess.FiniteStopping.cellBoundaryQuotientNorm_le zQ _ hrQ
    alpha U c _ hcont hholder hnorm
  have haeQ : (fun x => uQ.val.1 x) =ᵐ[
      volume.restrict (centeredCube zQ _ hrQ : Set (SpatialCoordinates d))] U :=
    SubdiffusiveProcess.FiniteStopping.domainLpRestrict_ae_trans hQP hProot u.val.1 U hae
  have ht := hTrace hPQ uQ U hcont hclass haeQ
  have hsS := SubdiffusiveProcess.FiniteStopping.reference_pos model H omega source (H1 * n) zQ
  have hresult := SubdiffusiveProcess.FiniteStopping.conjunct2_core_src _ _ _ Cfin eta
    (cellBoundaryQuotientNorm alpha zQ _ U) _ Kf _ _ (d : ℝ) hrQ
    (SubdiffusiveProcess.FiniteStopping.reference_pos model H omega target (H1 * n) zQ)
    hsS hCfin heta (SubdiffusiveProcess.FiniteStopping.boundary_norm_nonneg _ _ _ _)
    (sobolevCoefficientForm_nonneg _ uP.val) hKf hnorm' ht
  have henergy : sobolevCoefficientForm
      (cutoffPositiveCoefficient model H omega source zP hrP) uP.val uP.val =
      SubdiffusiveProcess.FiniteStopping.energyOn aS u.val (centeredCube zP _ hrP) := by
    rw [SubdiffusiveProcess.FiniteStopping.sobolevCoefficientForm_eq_energyOn,
      ← SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff
        model H omega source z hr zP hrP hProot]
    exact SubdiffusiveProcess.FiniteStopping.energyOn_restrict_eq hProot aS u.val
  have hratio : SubdiffusiveProcess.FiniteStopping.reference model H omega target (H1 * n) zQ /
      SubdiffusiveProcess.FiniteStopping.reference model H omega source (H1 * n) zQ =
      SubdiffusiveProcess.FiniteStopping.kappaRatio model H1 target source n :=
    (SubdiffusiveProcess.FiniteStopping.kappaRatio_eq_sRatio model H H1 target source n
      zQ omega).symm
  rw [henergy, hratio] at hresult
  dsimp only
  unfold SubdiffusiveProcess.FiniteStopping.respOn
  rw [SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff
      model H omega target z hr zQ hrQ hQroot,
    SubdiffusiveProcess.FiniteStopping.positiveCoefficientRestrict_cutoff
      model H omega source z hr zQ hrQ hQroot]
  exact hresult

end SubdiffusiveProcess.FiniteStopping
