module

public import SubdiffusiveProcess.CutoffsUniformGeometry
public import Mathlib.Tactic

@[expose] public section

/-!
# Uniform collar summation

The transition-cell count and the cellwise energy estimate combine with a
constant chosen before the mesh, collar width, plateau, and cutoff. This is
the finite-sum step in the corrected-cutoffs proof.
-/

open Set Metric
open SubdiffusiveProcess
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A fixed cellwise cost constant yields one collar cost constant for every
triadic mesh and every cutoff. The cell energies remain the actual quantities
to be bounded by the analytic part of the cutoff proof. -/
theorem aux_cutoffs_uniform_collar_sum
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (eta Ccell : ℝ) (hCcell : 0 ≤ Ccell) :
    ∃ Csum : ℝ, 0 < Csum ∧
      ∀ (J : ℕ) (rho : ℝ) (theta : SpatialCoordinates d → ℝ),
        (∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
          3 * rho ≤ Metric.infDist x
            (frontier (centeredCube z R hR : Set (SpatialCoordinates d))) →
            theta x = 1) →
        rho = R / (3 : ℝ) ^ J →
        ∃ I : Finset (OddGridIndex d (triadicHalf J)),
          (∀ k, k ∈ I ↔
            (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)) ∩
              {x : SpatialCoordinates d | 0 < theta x ∧ theta x < 1}).Nonempty) ∧
          ∀ (K : ℕ → ℝ) (e : OddGridIndex d (triadicHalf J) → ℕ → ℝ),
            (∀ n, 0 ≤ K n) →
            (∀ n k, k ∈ I →
              e k n ≤ Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) →
            ∀ n, (∑ k ∈ I, e k n) ≤
              Csum * K n * rho ^ (-1 - eta) := by
  classical
  obtain ⟨Ccover, hCcover, hfamily⟩ :=
    aux_cutoffs_uniform_transition_family d hd z R hR
  refine ⟨1 + Ccover * Ccell, by positivity, ?_⟩
  intro J rho theta hone hscale
  obtain ⟨I, hI, hcount⟩ := hfamily J rho theta hone hscale
  refine ⟨I, hI, ?_⟩
  intro K e hK hcell n
  have hrho : 0 < rho := by rw [hscale]; positivity
  have hcost : 0 ≤ Ccell * K n * rho ^ ((d : ℝ) - 2 - eta) :=
    mul_nonneg (mul_nonneg hCcell (hK n)) (Real.rpow_nonneg hrho.le _)
  have hsum : (∑ k ∈ I, e k n) ≤
      (I.card : ℝ) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) := by
    calc
      (∑ k ∈ I, e k n)
          ≤ ∑ k ∈ I, Ccell * K n * rho ^ ((d : ℝ) - 2 - eta) := by
              apply Finset.sum_le_sum
              intro k hk
              exact hcell n k hk
      _ = (I.card : ℝ) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hcount' :
      (I.card : ℝ) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) ≤
        (Ccover * rho ^ (-(d : ℝ) + 1)) *
          (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) :=
    mul_le_mul_of_nonneg_right hcount hcost
  have hexp :
      rho ^ (-(d : ℝ) + 1) * rho ^ ((d : ℝ) - 2 - eta) =
        rho ^ (-1 - eta) := by
    rw [← Real.rpow_add hrho]
    congr 1
    ring
  have hnonneg : 0 ≤ K n * rho ^ (-1 - eta) :=
    mul_nonneg (hK n) (Real.rpow_nonneg hrho.le _)
  calc
    (∑ k ∈ I, e k n)
        ≤ (I.card : ℝ) * (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) := hsum
    _ ≤ (Ccover * rho ^ (-(d : ℝ) + 1)) *
          (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) := hcount'
    _ = (Ccover * Ccell) * K n * rho ^ (-1 - eta) := by
          rw [show (Ccover * rho ^ (-(d : ℝ) + 1)) *
              (Ccell * K n * rho ^ ((d : ℝ) - 2 - eta)) =
              Ccover * Ccell * K n *
                (rho ^ (-(d : ℝ) + 1) * rho ^ ((d : ℝ) - 2 - eta)) by ring,
            hexp]
    _ ≤ (1 + Ccover * Ccell) * K n * rho ^ (-1 - eta) := by
          calc
            (Ccover * Ccell) * K n * rho ^ (-1 - eta) =
                (Ccover * Ccell) * (K n * rho ^ (-1 - eta)) := by ring
            _ ≤ (1 + Ccover * Ccell) * (K n * rho ^ (-1 - eta)) :=
              mul_le_mul_of_nonneg_right (by linarith) hnonneg
            _ = (1 + Ccover * Ccell) * K n * rho ^ (-1 - eta) := by ring

end SubdiffusiveProcess.Paper

