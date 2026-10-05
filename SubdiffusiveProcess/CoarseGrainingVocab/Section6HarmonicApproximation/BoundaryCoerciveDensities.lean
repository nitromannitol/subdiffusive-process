module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCoerciveIntegration

@[expose] public section

/-!
# Energy densities for the direct boundary test

This module expands the weak test by `eta^2 (u-h)` into the four nonnegative
densities used by the boundary Caccioppoli estimate.  Keeping this algebra
separate makes the later cutoff construction independent of integral
reassociation details.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

def boundaryCoerciveMainDensity (a eta : Vec d → ℝ)
    (U : Vec d → Vec d) : Vec d → ℝ :=
  fun x => a x * eta x ^ 2 * vecNormSq (U x)

def boundaryCoerciveDatumDensity (a eta : Vec d → ℝ)
    (H : Vec d → Vec d) : Vec d → ℝ :=
  fun x => a x * eta x ^ 2 * vecNormSq (H x)

def boundaryCoerciveCutoffDensity (a eta w : Vec d → ℝ) : Vec d → ℝ :=
  fun x => a x * w x ^ 2 * vecNormSq (euclideanGradient eta x)

def boundaryCoerciveForceDensity (a eta : Vec d → ℝ)
    (G : Vec d → Vec d) : Vec d → ℝ :=
  fun x => (a x)⁻¹ * eta x ^ 2 * vecNormSq (G x)

def boundaryCoerciveRhsDensity (a eta w : Vec d → ℝ)
    (U H G : Vec d → Vec d) : Vec d → ℝ :=
  fun x =>
    a x * eta x ^ 2 * vecDot (U x) (H x) -
      2 * a x * eta x * w x * vecDot (U x) (euclideanGradient eta x) -
      eta x ^ 2 * vecDot (G x) (U x) +
      eta x ^ 2 * vecDot (G x) (H x) -
      2 * eta x * w x * vecDot (G x) (euclideanGradient eta x)

def boundaryCoerciveWeakLeftDensity (a eta w : Vec d → ℝ)
    (U H : Vec d → Vec d) : Vec d → ℝ :=
  fun x => vecDot (a x • U x)
    (fun i => eta x ^ 2 * (U x i - H x i) +
      w x * (2 * eta x * euclideanGradient eta x i))

def boundaryCoerciveWeakForceDensity (eta w : Vec d → ℝ)
    (U H G : Vec d → Vec d) : Vec d → ℝ :=
  fun x => vecDot (G x)
    (fun i => eta x ^ 2 * (U x i - H x i) +
      w x * (2 * eta x * euclideanGradient eta x i))

theorem boundaryCoercive_main_sub_weakLeft
    (a eta w : Vec d → ℝ) (U H : Vec d → Vec d) (x : Vec d) :
    boundaryCoerciveMainDensity a eta U x -
        boundaryCoerciveWeakLeftDensity a eta w U H x =
      a x * eta x ^ 2 * vecDot (U x) (H x) -
        2 * a x * eta x * w x * vecDot (U x) (euclideanGradient eta x) := by
  simp only [boundaryCoerciveMainDensity, boundaryCoerciveWeakLeftDensity,
    vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem boundaryCoercive_rhs_add_weakForce
    (a eta w : Vec d → ℝ) (U H G : Vec d → Vec d) (x : Vec d) :
    boundaryCoerciveRhsDensity a eta w U H G x +
        boundaryCoerciveWeakForceDensity eta w U H G x =
      a x * eta x ^ 2 * vecDot (U x) (H x) -
        2 * a x * eta x * w x * vecDot (U x) (euclideanGradient eta x) := by
  simp only [boundaryCoerciveRhsDensity, boundaryCoerciveWeakForceDensity,
    vecDot, Finset.mul_sum]
  have hforce :
      ∑ i, G x i * (eta x ^ 2 * (U x i - H x i) +
          w x * (2 * eta x * euclideanGradient eta x i)) =
        ((∑ i, eta x ^ 2 * (G x i * U x i)) -
          ∑ i, eta x ^ 2 * (G x i * H x i)) +
          ∑ i, 2 * eta x * w x * (G x i * euclideanGradient eta x i) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hforce]
  ring

theorem boundaryCoerciveRhsDensity_le
    {a eta w : Vec d → ℝ} {U H G : Vec d → Vec d}
    {x : Vec d} (ha : 0 < a x) :
    boundaryCoerciveRhsDensity a eta w U H G x ≤
      (3 / 8 : ℝ) * boundaryCoerciveMainDensity a eta U x +
        (5 / 2 : ℝ) * boundaryCoerciveDatumDensity a eta H x +
        (17 / 2 : ℝ) * boundaryCoerciveCutoffDensity a eta w x +
        (9 / 2 : ℝ) * boundaryCoerciveForceDensity a eta G x := by
  exact scalar_boundary_coercive_rhs_le (d := d) ha

theorem boundaryCoerciveCutoffDensity_nonneg
    {a eta w : Vec d → ℝ} {x : Vec d} (ha : 0 ≤ a x) :
    0 ≤ boundaryCoerciveCutoffDensity a eta w x := by
  exact mul_nonneg (mul_nonneg ha (sq_nonneg _)) (vecNormSq_nonneg _)

theorem boundaryCoerciveForceDensity_nonneg
    {a eta : Vec d → ℝ} {G : Vec d → Vec d} {x : Vec d} (ha : 0 ≤ a x) :
    0 ≤ boundaryCoerciveForceDensity a eta G x := by
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr ha) (sq_nonneg _))
    (vecNormSq_nonneg _)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
