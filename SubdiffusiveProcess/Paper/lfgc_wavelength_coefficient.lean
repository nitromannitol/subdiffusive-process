module

public import SubdiffusiveProcess.Paper.lfgc_sub_oscillation
public import SubdiffusiveProcess.EllipticRegularity.CutoffLogarithm

@[expose] public section

/-! At the wavelength, the padded finite-prefix gradient bound controls logarithmic oscillation
and the coefficient divided by its root reference. No absolute coefficient bound is claimed. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The middle child of a padded ternary cell has the original centre. -/
theorem aux_lfgc_wavelength_coefficient_center {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) :
    descendantCenter 1 z (3 * r) 1 (fun _ _ => (1 : Fin 3)) = z := by
  ext i
  norm_num [descendantCenter, oddGridCenter]

/-- A padded prefix at the wavelength controls log oscillation and the normalized lower coefficient. -/
theorem lfgc_wavelength_coefficient {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y))
    (hIR : Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∨ H = 0)
    (sigma eps : ℝ) (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal)
    (Zsc : ℕ → Vec d → ℝ) (goodEvt : ℕ → Vec d → Prop)
    (hPS : primitive_scores d M sigma eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (r : ℝ) (hr : 0 < r) (hrN : r = (3 : ℝ) ^ (-(N : ℤ)))
    (z : SpatialCoordinates d) (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hdelta1 : M.delta ≤ 1)
    (hpad : ∀ w : Fin 1 → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) 1 w) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) 1 w)).toReal ≤ lam) :
    ∀ x ∈ Metric.closedBall z r,
      |Real.log (cutoffCoefficient M H omega N x) -
        Real.log (cutoffCoefficient M H omega N z)| ≤ (d : ℝ) * lam ∧
      aux_in_deterministic_onestep_sref M H omega N N z ≤
        Real.exp ((d : ℝ) + 2) * cutoffCoefficient M H omega N x := by
  have hpad' := hpad (fun _ _ => (1 : Fin 3))
  rw [aux_lfgc_wavelength_coefficient_center] at hpad'
  have hlayer := (aux_in_deterministic_onestep_layer0_le_draw M sigma eps eta Fsc Psc Rsc Dsc
    Zsc goodEvt hPS _ hpad'.1).trans hpad'.2
  have hunscale : ((3 : ℝ) ^ (-(N : ℤ))) • (((3 : ℝ) ^ N) • z) = z := by
    rw [smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul]
  rw [hEta, Nat.cast_zero, zero_sub, hunscale] at hlayer
  have hNr : (3 : ℝ) ^ N * r = 1 := by
    rw [hrN, zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity)]
  intro x hx
  have hdist : ‖x - z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hcoord : ∀ i, |x i - z i| ≤ r := by
    intro i
    exact (show |x i - z i| ≤ ‖x - z‖ by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - z) i).trans hdist
  have hpadN : ∀ w : Fin (N - N + 1) → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) (N - N + 1) w) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) (N - N + 1) w)).toReal ≤ lam := by
    exact Eq.mpr (congrArg (fun n : ℕ => ∀ w : Fin n → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) n w) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ N) • descendantCenter 1 z (3 * r) n w)).toReal ≤ lam)
        (by omega : N - N + 1 = 1)) hpad
  have hosc := lfgc_sub_oscillation M H omega N eta hEta hIR sigma eps Fsc Psc Rsc Dsc Zsc
    goodEvt hPS N le_rfl r hr hrN z lam
    hpadN z x
    (fun i => by simpa only [sub_self, abs_zero] using hr.le) hcoord
  have hsmall : |cutoffPotential H omega N x - cutoffPotential H omega N z| ≤ (d : ℝ) * lam := by
    calc _ ≤ (d : ℝ) * lam * ((3 : ℝ) ^ N * ‖x - z‖) := hosc
      _ ≤ (d : ℝ) * lam * ((3 : ℝ) ^ N * r) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdist (by positivity))
          (mul_nonneg (Nat.cast_nonneg d) hlam)
      _ = (d : ℝ) * lam := by rw [hNr, mul_one]
  refine ⟨by simpa only [log_cutoffCoefficient_sub] using hsmall, ?_⟩
  have hdelta2 : M.delta ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ M.shellPrefix.delta_pos.le hdelta1 2
    simpa only [one_pow] using h
  have hinc : |cutoffPotential H omega N x - cutoffPotential H omega N z| +
      |omega (-(N : ℤ)) z| + M.delta ^ 2 ≤ (d : ℝ) + 2 := by
    have hdlam := mul_le_mul_of_nonneg_left hlam1 (Nat.cast_nonneg (α := ℝ) d)
    nlinarith only [hsmall, hlayer, hdelta2, hdlam, hlam1]
  calc _ ≤ cutoffCoefficient M H omega N x *
        Real.exp (|cutoffPotential H omega N x - cutoffPotential H omega N z| +
          |omega (-(N : ℤ)) z| + M.delta ^ 2) :=
      aux_in_deterministic_onestep_sref_N_le_coeff M H omega N x z
    _ ≤ cutoffCoefficient M H omega N x * Real.exp ((d : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hinc) (cutoffCoefficient_pos M H omega N x).le
    _ = _ := mul_comm _ _

end SubdiffusiveProcess.Paper
