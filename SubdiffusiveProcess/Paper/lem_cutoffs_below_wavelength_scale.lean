module

public import SubdiffusiveProcess.Paper.lem_extremes

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Fine proof step for lem_cutoffs, paper lines 1985--1988.

The scalar M is the finite-cutoff coefficient maximum and K is the pathwise
collar majorant. The hypothesis hM is the direct coefficient bound obtained
from lem_extremes; the conclusion is only the scale absorption needed for
cells below the ultraviolet wavelength. No below-ultraviolet grid estimate is
promoted to a parent-theorem premise.
-/
theorem lem_cutoffs_below_wavelength_scale
    (d : ℕ) (N J : ℕ) (hbelow : N < J)
    (eta rho K M : ℝ) (heta : 0 < eta) (hrho : 0 < rho)
    (hK : 0 ≤ K)
    (hrhoJ : rho = (3 : ℝ) ^ (-(J : ℝ)))
    (hM : M ≤ K * (3 : ℝ) ^ ((N : ℝ) * eta)) :
    M * rho ^ ((d : ℝ) - 2) ≤ K * rho ^ ((d : ℝ) - 2 - eta) := by
  have hNJ : (N : ℝ) ≤ (J : ℝ) := by
    exact_mod_cast Nat.le_of_lt hbelow
  have hNJ' : (N : ℝ) * eta ≤ (J : ℝ) * eta := by
    exact mul_le_mul_of_nonneg_right hNJ heta.le
  have hpow : (3 : ℝ) ^ ((N : ℝ) * eta) ≤ (3 : ℝ) ^ ((J : ℝ) * eta) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hNJ'
  have hrho_inv : rho ^ (-eta) = (3 : ℝ) ^ ((J : ℝ) * eta) := by
    rw [hrhoJ, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have h1 : (3 : ℝ) ^ ((N : ℝ) * eta) ≤ rho ^ (-eta) := hpow.trans_eq hrho_inv.symm
  have h2 : (3 : ℝ) ^ ((N : ℝ) * eta) * rho ^ ((d : ℝ) - 2) ≤
      rho ^ (-eta) * rho ^ ((d : ℝ) - 2) :=
    mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hrho.le ((d : ℝ) - 2))
  have h3 : rho ^ (-eta) * rho ^ ((d : ℝ) - 2) = rho ^ ((d : ℝ) - 2 - eta) := by
    rw [← Real.rpow_add hrho (-eta) ((d : ℝ) - 2)]
    congr 1
    ring
  calc M * rho ^ ((d : ℝ) - 2)
      ≤ (K * (3 : ℝ) ^ ((N : ℝ) * eta)) * rho ^ ((d : ℝ) - 2) :=
        mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hrho.le ((d : ℝ) - 2))
    _ = K * ((3 : ℝ) ^ ((N : ℝ) * eta) * rho ^ ((d : ℝ) - 2)) := by rw [mul_assoc]
    _ ≤ K * rho ^ ((d : ℝ) - 2 - eta) :=
        mul_le_mul_of_nonneg_left (h2.trans_eq h3) hK


end Paper
