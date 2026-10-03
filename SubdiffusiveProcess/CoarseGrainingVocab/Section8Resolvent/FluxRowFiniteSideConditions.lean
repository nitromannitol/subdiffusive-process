/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsEnlargedPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.CarrierComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DirichletPrebalance

@[expose] public section

/-!
# Finiteness side conditions for the flux-row per-cell price

The enlarged local price has four extended-real side conditions.  This file
discharges them without an exceptional set: positive fractional order makes
the response weights summable, the root coefficient object gives a uniform
bound on every descendant response, and the Sobolev and energy carriers are
finite by their defining data.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization Homogenization.Book Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Every positive-order, finite-outer-exponent paper homogenization error is
finite.  The result is deterministic and applies at every starting scale below
the root scale. -/
theorem fluxRowFinite_paperHomogenizationError_ne_top
    [NeZero d] (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    {s q : ℝ} (hs : 0 < s) (hq : 0 < q)
    (a : Ch02.TriadicCoeffFamily d)
    (ha : ∀ R : TriadicCube d, (a.coeffOn R).IsSymmetric)
    {alpha : ℝ} (halpha : 0 < alpha) :
    paperHomogenizationError Q n s .infinity (.finite q) a alpha ≠ ∞ := by
  let C : ℝ := Real.rpow
    (Ch02.normalizedBlockResponseUniformBound Q a
      (scalarMatrix (d := d) alpha)) (1 / 2 : ℝ)
  have hsumOld : Summable fun l : ℕ =>
      Homogenization.geometricWeight s q l *
        Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) .infinity a
          (scalarMatrix (d := d) alpha)) q := by
    refine Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (C := Real.rpow C q) (mul_pos hs hq) ?_ ?_
    · intro l
      exact Real.rpow_nonneg
        (Ch02.scaleResponseAtScale_infinity_nonneg Q
          ((sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn) a
          (scalarMatrix (d := d) alpha)) q
    · intro l
      exact Real.rpow_le_rpow
        (Ch02.scaleResponseAtScale_infinity_nonneg Q
          ((sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn) a
          (scalarMatrix (d := d) alpha))
        (Ch02.scaleResponseAtScale_infinity_le_uniform Q
          ((sub_le_self n (by exact_mod_cast Nat.zero_le l)).trans hn) a
          (scalarMatrix (d := d) alpha)) hq.le
  have hsum : Summable fun l : ℕ =>
      Ch02.geometricWeight s q l *
        Real.rpow (Ch02.scaleResponseAtScale Q (n - (l : ℤ)) .infinity a
          (scalarMatrix (d := d) alpha)) q := by
    simpa [Ch02.geometricWeight_eq_old] using hsumOld
  have hcap :=
    Section6FixedCutoffBridge.paperHomogenizationError_le_ofReal_finite
      Q hn hs.le hq a ha halpha hsum
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcap

/-- The `q = 1` homogenization-error side condition in the flux-row price. -/
theorem fluxRowFinite_paperHomogenizationError_one_ne_top
    [NeZero d] (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    {s : ℝ} (hs : 0 < s) (a : Ch02.TriadicCoeffFamily d)
    (ha : ∀ R : TriadicCube d, (a.coeffOn R).IsSymmetric)
    {alpha : ℝ} (halpha : 0 < alpha) :
    paperHomogenizationError Q n s .infinity (.finite 1) a alpha ≠ ∞ := by
  exact fluxRowFinite_paperHomogenizationError_ne_top Q hn hs (by norm_num)
    a ha halpha

/-- The `q = 2` homogenization-error side condition in the flux-row price. -/
theorem fluxRowFinite_paperHomogenizationError_two_ne_top
    [NeZero d] (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    {s : ℝ} (hs : 0 < s) (a : Ch02.TriadicCoeffFamily d)
    (ha : ∀ R : TriadicCube d, (a.coeffOn R).IsSymmetric)
    {alpha : ℝ} (halpha : 0 < alpha) :
    paperHomogenizationError Q n s .infinity (.finite 2) a alpha ≠ ∞ := by
  exact fluxRowFinite_paperHomogenizationError_ne_top Q hn hs (by norm_num)
    a ha halpha

/-- The positive fractional seminorm in the flux-row price is finite because
the datum is carried by `CubeEuclideanWspField`. -/
theorem fluxRowLocal_paperFractionalSeminorm_ne_top
    (Q : TriadicCube d) (s : FractionalOrder)
    (g : CubeEuclideanWspField Q s FiniteLpExponent.two) :
    paperFractionalSeminorm Q s FiniteLpExponent.two g.toField ≠ ∞ := by
  unfold paperFractionalSeminorm
  exact ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    g.eSeminorm_lt_top.ne

/-- The weighted local symmetric energy in the flux-row price is finite. -/
theorem fluxRowFinite_weightedLocalSymmetricEnergyLp_two_ne_top
    [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) (s1 s : FractionalOrder)
    (hgap : 0 < s.1 - s1.1) :
    weightedLocalSymmetricEnergyLp Q n hn a u s1 s
        FiniteLpExponent.two ≠ ∞ := by
  rw [Section6Dirichlet.weightedLocalSymmetricEnergyLp_two_eq
    Q n hn a u s1 s hgap]
  exact ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    (localSymmetricEnergyENorm_ne_top Q a u)

/-- The weighted-energy side condition in exactly the two flux-row orders. -/
theorem fluxRowFinite_weightedLocalSymmetricEnergyLp_ne_top
    [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Ch02.CoeffOn (Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q))
    {sigma : ℝ} (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) :
    weightedLocalSymmetricEnergyLp Q n hn a u
        (fluxRowLocalLowerOrder sigma hsigma)
        (fluxRowLocalOrder sigma hsigma) FiniteLpExponent.two ≠ ∞ := by
  apply fluxRowFinite_weightedLocalSymmetricEnergyLp_two_ne_top
  simp only [fluxRowLocalOrder, fluxRowLocalLowerOrder]
  nlinarith [hsigma.1]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
