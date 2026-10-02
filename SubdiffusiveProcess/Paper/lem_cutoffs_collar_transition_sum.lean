import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.lem_cutoffs_below_wavelength_scale
import SubdiffusiveProcess.Paper.lem_cutoffs_transition_cover

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Fine proof step for the collar energy sum in lem_cutoffs, paper lines
1985--1988. The scalar function e records the actual cell energies supplied by
the harmonic mesh interpolant; the hypotheses state the two preceding
concrete geometric and cellwise estimates, while the conclusion performs only
their finite sum.
-/
theorem lem_cutoffs_collar_transition_sum
    (d : ℕ) (eta rho : ℝ) (heta : 0 < eta) (hrho : 0 < rho)
    (J : ℕ) (I : Finset (OddGridIndex d (triadicHalf J)))
    (K : ℕ → ℝ) (e : OddGridIndex d (triadicHalf J) → ℕ → ℝ)
    (Ccover Ccell : ℝ) (hCcover : 0 ≤ Ccover) (hCcell : 0 ≤ Ccell)
    (hK : ∀ n : ℕ, 0 ≤ K n)
    (hcount : (I.card : ℝ) ≤ Ccover * rho ^ (-(d : ℝ) + 1))
    (hcell : ∀ n : ℕ, ∀ k : OddGridIndex d (triadicHalf J), k ∈ I →
      e k n ≤ Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) :
    ∃ Csum : ℝ, 0 ≤ Csum ∧
      ∀ n : ℕ, (∑ k ∈ I, e k n) ≤ Csum * K n * rho ^ (-1 - eta) := by
  refine ⟨Ccover * Ccell, mul_nonneg hCcover hCcell, fun n => ?_⟩
  have hrpow_pos : 0 < rho ^ ((d : ℝ) - 2 - eta) := Real.rpow_pos_of_pos hrho _
  have hXnn : 0 ≤ Ccell * K n * rho ^ ((d : ℝ) - 2 - eta) :=
    mul_nonneg (mul_nonneg hCcell (hK n)) hrpow_pos.le
  have hstep1 : (∑ k ∈ I, e k n)
      ≤ ∑ k ∈ I, Ccell * K n * rho ^ ((d : ℝ) - 2 - eta) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hcell n k hk
  have hsum_const : (∑ k ∈ I, Ccell * K n * rho ^ ((d : ℝ) - 2 - eta))
      = (I.card : ℝ) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hstep2 : (I.card : ℝ) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta))
      ≤ (Ccover * rho ^ (-(d : ℝ) + 1)) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) :=
    mul_le_mul_of_nonneg_right hcount hXnn
  have hexp : rho ^ (-(d : ℝ) + 1) * rho ^ ((d : ℝ) - 2 - eta) = rho ^ (-1 - eta) := by
    rw [← Real.rpow_add hrho]
    congr 1
    ring
  have hfinal : (Ccover * rho ^ (-(d : ℝ) + 1)) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta))
      = (Ccover * Ccell) * K n * rho ^ (-1 - eta) := by
    rw [show (Ccover * rho ^ (-(d : ℝ) + 1)) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta))
        = Ccover * Ccell * K n * (rho ^ (-(d : ℝ) + 1) * rho ^ ((d : ℝ) - 2 - eta)) by ring,
      hexp]
  calc (∑ k ∈ I, e k n)
      ≤ ∑ k ∈ I, Ccell * K n * rho ^ ((d : ℝ) - 2 - eta) := hstep1
    _ = (I.card : ℝ) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) := hsum_const
    _ ≤ (Ccover * rho ^ (-(d : ℝ) + 1)) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) := hstep2
    _ = (Ccover * Ccell) * K n * rho ^ (-1 - eta) := hfinal


end Paper
