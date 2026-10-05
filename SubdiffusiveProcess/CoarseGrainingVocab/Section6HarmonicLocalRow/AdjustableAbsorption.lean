module

public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Adjustable-parameter absorption between two radii

The fixed projected cover of `l.harmonic.approximation.good.scales.GMC` absorbs a remainder
against the energy of the *same* cube `D`.  The boundary residual mean
produced by the separate-datum ASD row is instead supported on the projected
parents `P_q`, whose union is the scale-`n-1` window `3D`, so a single
half-absorption step against `D` cannot close (see
`SubdiffusiveProcess/CoarseGrainingVocab/Section6HarmonicLocalRow/CoverAbsorptionObstruction.lean`).

What does close is the classical adjustable-radius scheme: the local row is
proved for *every* pair of radii `rho < R` inside the window with a free
Young parameter `theta`, and the resulting family is collapsed by the
iteration lemma below.  This file contains only that collapse, as a
self-contained real-analytic statement; it has no PDE content and no dependency on the surrounding argument.

The statement is the standard "hole-filling" iteration lemma (Giaquinta,
*Multiple Integrals in the Calculus of Variations*, Lemma V.3.1).  The
contraction witness `tau` is taken as an explicit parameter rather than being
produced by a root extraction, so the resulting constant is explicit and the
caller chooses it.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow

open Finset Filter

/-- Partial geometric sums are bounded by the limit of the series. -/
theorem geom_partial_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, x ^ i ≤ (1 - x)⁻¹ := by
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  induction k with
  | zero => simp [inv_nonneg.mpr hpos.le]
  | succ k ih =>
    rw [geom_sum_succ]
    have hx : x * ∑ i ∈ Finset.range k, x ^ i ≤ x * (1 - x)⁻¹ :=
      mul_le_mul_of_nonneg_left ih hx0
    have : x * (1 - x)⁻¹ + 1 = (1 - x)⁻¹ := by
      field_simp
      ring
    linarith

/-- The geometric radius ladder from `r0` up to `r1` with ratio `tau`. -/
noncomputable def radiusLadder (r0 r1 tau : ℝ) (i : ℕ) : ℝ :=
  r0 + (1 - tau ^ i) * (r1 - r0)

@[simp] theorem radiusLadder_zero (r0 r1 tau : ℝ) :
    radiusLadder r0 r1 tau 0 = r0 := by
  simp [radiusLadder]

theorem radiusLadder_le_of_lt_one {r0 r1 tau : ℝ} (hr : r0 ≤ r1)
    (htau0 : 0 < tau) (htau1 : tau < 1) (i : ℕ) :
    r0 ≤ radiusLadder r0 r1 tau i ∧ radiusLadder r0 r1 tau i ≤ r1 := by
  have hpow0 : 0 < tau ^ i := pow_pos htau0 i
  have hpow1 : tau ^ i ≤ 1 := pow_le_one₀ htau0.le htau1.le
  constructor
  · have : 0 ≤ (1 - tau ^ i) * (r1 - r0) :=
      mul_nonneg (by linarith) (by linarith)
    simpa [radiusLadder] using this
  · have hle : (1 - tau ^ i) * (r1 - r0) ≤ r1 - r0 := by
      nlinarith [sub_nonneg.mpr hr]
    simp only [radiusLadder]
    linarith

theorem radiusLadder_succ_sub {r0 r1 tau : ℝ} (i : ℕ) :
    radiusLadder r0 r1 tau (i + 1) - radiusLadder r0 r1 tau i =
      (1 - tau) * tau ^ i * (r1 - r0) := by
  simp only [radiusLadder, pow_succ]
  ring

theorem radiusLadder_lt_succ {r0 r1 tau : ℝ} (hr : r0 < r1)
    (htau0 : 0 < tau) (htau1 : tau < 1) (i : ℕ) :
    radiusLadder r0 r1 tau i < radiusLadder r0 r1 tau (i + 1) := by
  have hd := radiusLadder_succ_sub (r0 := r0) (r1 := r1) (tau := tau) i
  have : 0 < (1 - tau) * tau ^ i * (r1 - r0) :=
    mul_pos (mul_pos (by linarith) (pow_pos htau0 i)) (by linarith)
  linarith

/-- **Adjustable-parameter absorption.**  A family of estimates
`f rho ≤ theta * f R + A / (R - rho) ^ alpha + B`, valid for every pair of
radii `r0 ≤ rho < R ≤ r1` with a contraction factor `theta` strictly below
`tau ^ alpha`, collapses to a single estimate at the inner radius with the
remainder removed.

This is the correct replacement for a one-step half-absorption whenever the
remainder is supported on a strictly larger window than the set being
estimated. -/
theorem iterate_absorb_le_of_sum
    {r0 r1 tau theta Mbd S : ℝ} (f price : ℝ → ℝ)
    (hr : r0 < r1)
    (htau0 : 0 < tau) (htau1 : tau < 1)
    (htheta0 : 0 ≤ theta) (htheta1 : theta < 1)
    (hbdd : ∀ r, r0 ≤ r → r ≤ r1 → f r ≤ Mbd)
    (hstep : ∀ rho R, r0 ≤ rho → rho < R → R ≤ r1 →
      f rho ≤ theta * f R + price (R - rho))
    (hseries : ∀ k : ℕ,
      ∑ i ∈ Finset.range k,
        theta ^ i * price ((1 - tau) * tau ^ i * (r1 - r0)) ≤ S) :
    f r0 ≤ S := by
  set term : ℕ → ℝ := fun i =>
    theta ^ i * price ((1 - tau) * tau ^ i * (r1 - r0)) with htermdef
  have hiter : ∀ k : ℕ,
      f r0 ≤ theta ^ k * f (radiusLadder r0 r1 tau k)
        + ∑ i ∈ Finset.range k, term i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hlo := (radiusLadder_le_of_lt_one hr.le htau0 htau1 k).1
      have hhi := (radiusLadder_le_of_lt_one hr.le htau0 htau1 (k + 1)).2
      have hlt := radiusLadder_lt_succ hr htau0 htau1 k
      have hstepk := hstep (radiusLadder r0 r1 tau k)
        (radiusLadder r0 r1 tau (k + 1)) hlo hlt hhi
      rw [radiusLadder_succ_sub] at hstepk
      have hmul : theta ^ k * f (radiusLadder r0 r1 tau k) ≤
          theta ^ k * (theta * f (radiusLadder r0 r1 tau (k + 1))
            + price ((1 - tau) * tau ^ k * (r1 - r0))) :=
        mul_le_mul_of_nonneg_left hstepk (pow_nonneg htheta0 k)
      have hexpand : theta ^ k * (theta * f (radiusLadder r0 r1 tau (k + 1))
          + price ((1 - tau) * tau ^ k * (r1 - r0)))
          = theta ^ (k + 1) * f (radiusLadder r0 r1 tau (k + 1)) + term k := by
        rw [htermdef]
        ring
      rw [Finset.sum_range_succ]
      linarith [ih, hmul, hexpand ▸ hmul]
  have hMbdk : ∀ k : ℕ, f r0 ≤ theta ^ k * Mbd + S := by
    intro k
    have hlo := (radiusLadder_le_of_lt_one hr.le htau0 htau1 k).1
    have hhi := (radiusLadder_le_of_lt_one hr.le htau0 htau1 k).2
    have h1 : theta ^ k * f (radiusLadder r0 r1 tau k) ≤ theta ^ k * Mbd :=
      mul_le_mul_of_nonneg_left (hbdd _ hlo hhi) (pow_nonneg htheta0 k)
    linarith [hiter k, hseries k]
  have hlim : Tendsto (fun k : ℕ => theta ^ k * Mbd + S) atTop (nhds S) := by
    have hpow : Tendsto (fun k : ℕ => theta ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one htheta0 htheta1
    have := (hpow.mul_const Mbd).add_const S
    simpa using this
  exact ge_of_tendsto' hlim hMbdk

/-- The explicit-price specialization: price `A / (R - rho) ^ alpha + B`.  The
additive budget `B` is what the four manuscript budgets occupy, and `theta` is
free below `tau ^ alpha`. -/
theorem iterate_absorb_le
    {r0 r1 tau theta A B Mbd : ℝ} {alpha : ℕ} (f : ℝ → ℝ)
    (hr : r0 < r1)
    (htau0 : 0 < tau) (htau1 : tau < 1)
    (htheta0 : 0 ≤ theta) (hcontract : theta < tau ^ alpha)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbdd : ∀ r, r0 ≤ r → r ≤ r1 → f r ≤ Mbd)
    (hstep : ∀ rho R, r0 ≤ rho → rho < R → R ≤ r1 →
      f rho ≤ theta * f R + A / (R - rho) ^ alpha + B) :
    f r0 ≤
      (1 - theta / tau ^ alpha)⁻¹ *
          (A / ((1 - tau) ^ alpha * (r1 - r0) ^ alpha))
        + (1 - theta)⁻¹ * B := by
  have hgap : (0 : ℝ) < r1 - r0 := sub_pos.mpr hr
  have htaupow : (0 : ℝ) < tau ^ alpha := pow_pos htau0 alpha
  have htaupow_le : tau ^ alpha ≤ 1 := pow_le_one₀ htau0.le htau1.le
  have htheta1 : theta < 1 := lt_of_lt_of_le hcontract htaupow_le
  set x : ℝ := theta / tau ^ alpha with hxdef
  have hx0 : 0 ≤ x := div_nonneg htheta0 htaupow.le
  have hx1 : x < 1 := (div_lt_one htaupow).mpr hcontract
  set P : ℝ := (1 - tau) ^ alpha * (r1 - r0) ^ alpha with hPdef
  have hPpos : 0 < P := by
    have h1 : (0 : ℝ) < (1 - tau) ^ alpha := pow_pos (by linarith) alpha
    have h2 : (0 : ℝ) < (r1 - r0) ^ alpha := pow_pos hgap alpha
    exact mul_pos h1 h2
  refine iterate_absorb_le_of_sum f (fun t => A / t ^ alpha + B) hr htau0 htau1
    htheta0 htheta1 hbdd (fun rho R h1 h2 h3 => by
      have := hstep rho R h1 h2 h3
      linarith) ?_
  intro k
  have hterm : ∀ i : ℕ,
      theta ^ i * (A / ((1 - tau) * tau ^ i * (r1 - r0)) ^ alpha + B)
        = (A / P) * x ^ i + B * theta ^ i := by
    intro i
    have hne : ((1 - tau) * tau ^ i * (r1 - r0)) ^ alpha
        = P * (tau ^ alpha) ^ i := by
      rw [hPdef, mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm i alpha]
      ring
    have htaupow_i : (0 : ℝ) < (tau ^ alpha) ^ i := pow_pos htaupow i
    rw [hne, hxdef, div_pow]
    have hPne : P ≠ 0 := hPpos.ne'
    have htine : ((tau : ℝ) ^ alpha) ^ i ≠ 0 := htaupow_i.ne'
    field_simp
  have hrw : ∑ i ∈ Finset.range k,
        theta ^ i * (A / ((1 - tau) * tau ^ i * (r1 - r0)) ^ alpha + B)
      = (A / P) * (∑ i ∈ Finset.range k, x ^ i)
        + B * (∑ i ∈ Finset.range k, theta ^ i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hterm i
  have hAP : 0 ≤ A / P := div_nonneg hA hPpos.le
  have h1 : (A / P) * (∑ i ∈ Finset.range k, x ^ i) ≤ (A / P) * (1 - x)⁻¹ :=
    mul_le_mul_of_nonneg_left (geom_partial_le hx0 hx1 k) hAP
  have h2 : B * (∑ i ∈ Finset.range k, theta ^ i) ≤ B * (1 - theta)⁻¹ :=
    mul_le_mul_of_nonneg_left (geom_partial_le htheta0 htheta1 k) hB
  rw [hrw]
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
