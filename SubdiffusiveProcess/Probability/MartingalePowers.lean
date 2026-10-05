module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

@[expose] public section

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace SubdiffusiveProcess

open MeasureTheory

theorem submartingale_natPow_of_nonneg_martingale
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (X : ℕ → Omega → ℝ) (hX : Martingale X F mu)
    (hnonneg : ∀ n, 0 ≤ᵐ[mu] X n) (p : ℕ) (hp : 1 ≤ p)
    (hint : ∀ n, Integrable (fun w => (X n w)^p) mu) :
    Submartingale (fun n w => (X n w)^p) F mu := by
  have hp0 : p ≠ 0 := Nat.one_le_iff_ne_zero.mp hp
  have htangent : ∀ a x : ℝ, 0 ≤ a → 0 ≤ x →
      a ^ p + (p : ℝ) * a ^ (p - 1) * (x - a) ≤ x ^ p := by
    intro a x ha hx
    by_cases hza : a = 0
    · subst a
      by_cases hp1 : p = 1
      · subst p
        simp
      · have hpminus : p - 1 ≠ 0 := by omega
        simp [hp0, hpminus, pow_nonneg hx p]
    by_cases hax : a < x
    · have hs := (convexOn_pow p).le_slope_of_hasDerivAt
          (show a ∈ Set.Ici (0 : ℝ) from ha)
          (show x ∈ Set.Ici (0 : ℝ) from hx) hax (hasDerivAt_pow p a)
      rw [slope_def_field] at hs
      have hmul := (le_div_iff₀ (sub_pos.mpr hax)).mp hs
      nlinarith
    · by_cases hxeq : x = a
      · subst x
        simp
      have hxa : x < a := lt_of_le_of_ne (le_of_not_gt hax) hxeq
      have hs := (convexOn_pow p).slope_le_of_hasDerivAt
          (show x ∈ Set.Ici (0 : ℝ) from hx)
          (show a ∈ Set.Ici (0 : ℝ) from ha) hxa (hasDerivAt_pow p a)
      rw [slope_def_field] at hs
      have hmul := (div_le_iff₀ (sub_pos.mpr hxa)).mp hs
      nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (hX.stronglyMeasurable i).pow p
  · intro i j hij
    let A : Omega → ℝ := fun w => (X i w) ^ p
    let B : Omega → ℝ := fun w => (X i w) ^ (p - 1) * X j w
    let C : Omega → ℝ := fun w => (X i w) ^ (p - 1) * X i w
    let D : Omega → ℝ := B - C
    let L : Omega → ℝ := A + (p : ℝ) • D
    have hXi : Integrable (X i) mu := hX.integrable i
    have hXj : Integrable (X j) mu := hX.integrable j
    have hBmeas : AEStronglyMeasurable B mu := by
      dsimp [B]
      exact hXi.aestronglyMeasurable.pow (p - 1) |>.mul hXj.aestronglyMeasurable
    have hBbound : ∀ᵐ w ∂mu, ‖B w‖ ≤ (X j w) ^ p + (X i w) ^ p := by
      filter_upwards [hnonneg i, hnonneg j] with w hia hja
      dsimp [B]
      rw [abs_of_nonneg (mul_nonneg (pow_nonneg hia _) hja)]
      rcases le_total (X j w) (X i w) with hji | hij'
      · calc
          (X i w) ^ (p - 1) * X j w ≤ (X i w) ^ (p - 1) * X i w :=
            mul_le_mul_of_nonneg_left hji (pow_nonneg hia _)
          _ = (X i w) ^ p := by
            rw [← pow_succ, Nat.sub_add_cancel hp]
          _ ≤ (X j w) ^ p + (X i w) ^ p :=
            le_add_of_nonneg_left (pow_nonneg hja _)
      · calc
          (X i w) ^ (p - 1) * X j w ≤ (X j w) ^ (p - 1) * X j w := by
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hia hij' (p - 1)) hja
          _ = (X j w) ^ p := by
            rw [← pow_succ, Nat.sub_add_cancel hp]
          _ ≤ (X j w) ^ p + (X i w) ^ p :=
            le_add_of_nonneg_right (pow_nonneg hia _)
    have hB : Integrable B mu := by
      exact (hint j).add (hint i) |>.mono' hBmeas hBbound
    have hC : Integrable C mu := by
      convert hint i using 1
      funext w
      dsimp [C]
      rw [← pow_succ, Nat.sub_add_cancel hp]
    have hD : Integrable D mu := hB.sub hC
    have hL : Integrable L mu := by
      dsimp [L]
      exact (hint i).add (hD.smul (p : ℝ))
    have hpoint : L ≤ᵐ[mu] (fun w => (X j w) ^ p) := by
      filter_upwards [hnonneg i, hnonneg j] with w hia hja
      dsimp [L, A, D, B, C]
      convert htangent (X i w) (X j w) hia hja using 1 ; ring
    have hmono := condExp_mono (m := F i) hL (hint j) hpoint
    have hiPowMeas : StronglyMeasurable[F i] (fun w => (X i w) ^ (p - 1)) :=
      (hX.stronglyMeasurable i).pow (p - 1)
    have hpullB := condExp_mul_of_stronglyMeasurable_left hiPowMeas hB hXj
    have hpullC := condExp_mul_of_stronglyMeasurable_left hiPowMeas hC hXi
    have hpullB' : mu[B | F i] =ᵐ[mu]
        (fun w => (X i w) ^ (p - 1)) * mu[X j | F i] := by
      simpa only [B, Pi.mul_def] using hpullB
    have hpullC' : mu[C | F i] =ᵐ[mu]
        (fun w => (X i w) ^ (p - 1)) * mu[X i | F i] := by
      simpa only [C, Pi.mul_def] using hpullC
    have hcondD := condExp_sub hB hC (F i)
    have hcondL := condExp_add (hint i) (hD.smul (p : ℝ)) (F i)
    have hcondL' : mu[L | F i] =ᵐ[mu]
        mu[A | F i] + mu[(p : ℝ) • D | F i] := by
      simpa only [L, A] using hcondL
    have hmart := hX.condExp_ae_eq hij
    have hmart_i := hX.condExp_ae_eq (le_refl i)
    have hcondA : mu[A | F i] = A := by
      simpa only [A, Pi.pow_def] using
        (condExp_of_stronglyMeasurable (F.le i)
          ((hX.stronglyMeasurable i).pow p) (hint i))
    have hcond : mu[L | F i] =ᵐ[mu] A := by
      filter_upwards [hcondL', condExp_smul (p : ℝ) D (F i), hcondD,
        hpullB', hpullC', hmart, hmart_i] with w hwL hwS hwD hwB hwC hwj hwi
      rw [hwL]
      change mu[A | F i] w + mu[(p : ℝ) • D | F i] w = A w
      rw [hcondA, hwS]
      change A w + (p : ℝ) * (mu[D | F i]) w = A w
      rw [hwD]
      simp only [Pi.sub_apply]
      rw [hwB, hwC]
      simp only [Pi.mul_apply]
      rw [hwj, hwi]
      dsimp [A, B, C]
      ring
    filter_upwards [hcond, hmono] with w hwc hwm
    exact hwc.symm.le.trans hwm

  · intro i
    exact hint i

end SubdiffusiveProcess
