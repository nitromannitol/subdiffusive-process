module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.CollapseAlgebra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffHarmonicComparison
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.CutoffExcessDecayInput
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.ComparisonCollapse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.WellPosed

@[expose] public section

/-!
# The cutoff harmonic-approximation input, closed

`Section6HarmonicInterior.ComparisonCollapse.interiorHarmonicComparisonClause_holds`
closes clause (C) of the frozen interior harmonic anchor from
`exists_interiorHarmonicComparison_le_sharpLoopBound` by three steps: the window
shrink `x + 𝔠_{n-4} ⊆ y + 𝔠_{n-2}`, the indicator split, and the arithmetic
collapse of the sharp loop carrier into the two printed terms.

This module runs the identical script against the finite-cutoff comparison
`exists_interiorCutoffHarmonicComparison_le_sharpLoopBound`, whose only
differences are the deleted binder `m ≤ L` and the good event
`𝒢^{(L)}_{n+2,z}`.  Exactly two lines change:

* the error cap is `CutoffErrorCap.exists_section6HomogenizationError_le_of_cutoffGoodEvent`
  (conjunct 5 of the **proved** `SubdiffusiveProcess.Frozen.Section6.cutoff_regularity_good_scales`,
  which carries no `k ≤ L`) in place of the `p.good.scale.mathcal.E` cap;
* the `m ≤ L` argument disappears from the loop application.

Clauses (A) and (B) — existence and a.e. uniqueness of the harmonic replacement
— are the unconditional `Section6HarmonicInterior.interiorHarmonic_wellPosed`,
exactly as in the uncut provider.

The three polynomial legs of the collapse are the private arithmetic lemmas of
`ComparisonCollapse`, restated here verbatim (they are inaccessible outside that
module); they contain no cutoff-sensitive content.

 (`l.cutoff.regularity.good.scale.estimates`),

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 Homogenization.Book.Ch03.ABK26 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior
open scoped ENNReal

noncomputable section

/-! ### The three polynomial legs of the collapse -/

private theorem collapse_term1_cut
    {A cs sgi p1 Ct p2 R e3 E Sv V Er SK S1 N3 T W G Cerr : ℝ}
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hV : 0 ≤ V) (hSK : 0 ≤ SK)
    (hR : 0 < R) (hS1 : 0 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T)
    (hEr : 0 ≤ Er) (_hW : 0 ≤ W) (hG : 0 ≤ G) (hErC : Er ≤ Cerr)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (_hp10 : 0 ≤ p1) (hp1 : p1 ≤ 2 * S1)
    (hp2 : p2 = 2 * S1 ^ 2)
    (he30 : 0 ≤ e3) (he3 : e3 ≤ 3)
    (hE0 : 0 ≤ E) (hE : E ≤ V * 3 * Er)
    (hSv0 : 0 ≤ Sv)
    (hSv : Sv ≤ 2 * S1 * SK * (R * N3⁻¹ * W + S1 ^ 12 * R⁻¹ * T * G)) :
    A * cs * sgi * (p1 * (Ct * p2 * R * e3 * E * Sv)) ≤
      (8 * A * Ct * V * SK) * S1 ^ 4 * Er * W +
        (8 * A * Ct * V * SK) * Cerr * S1 ^ 16 * (R * R)⁻¹ * N3 * T * G := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicInterior.aux_dedup_d051_collapse_term1 (A := A) (cs := cs) (sgi := sgi) (p1 := p1) (Ct := Ct) (p2 := p2) (R := R) (e3 := e3) (E := E) (Sv := Sv) (V := V) (Er := Er) (SK := SK) (S1 := S1) (N3 := N3) (T := T) (W := W) (G := G) (Cerr := Cerr) (hA := hA) (hCt := hCt) (hV := hV) (hSK := hSK) (hR := hR) (hS1 := hS1) (hN3 := hN3) (hT := hT) (hEr := hEr) (_hW := _hW) (hG := hG) (hErC := hErC) (hcs := hcs) (hsgi := hsgi) (_hp10 := _hp10) (hp1 := hp1) (hp2 := hp2) (he30 := he30) (he3 := he3) (hE0 := hE0) (hE := hE) (hSv0 := hSv0) (hSv := hSv)

private theorem collapse_term2_cut
    {A cs sgi p1 Ct p9 pinv q3 t3 Dv Cdc CY1 R S1 N3 T G : ℝ}
    (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hCdc : 0 ≤ Cdc) (hCY1 : 0 ≤ CY1)
    (hR : 0 < R) (hS1 : 1 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (_hp10 : 0 ≤ p1) (hp1 : p1 ≤ 2 * S1)
    (hp90 : 0 ≤ p9) (hp9 : p9 ≤ 32 * S1 ^ 9)
    (hpinv : pinv = 2 * S1 ^ 2)
    (hq30 : 0 ≤ q3) (hq3 : q3 ≤ CY1)
    (ht30 : 0 ≤ t3) (ht3 : t3 ≤ T)
    (hDv : Dv = Cdc * S1 * G) :
    A * cs * sgi * (p1 * (Ct * p9 * pinv * q3 * t3 * Dv)) ≤
      ((128 / 9) * A * Ct * Cdc * CY1) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * G := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.bcollapse_term2 (A := A) (cs := cs) (sgi := sgi) (p1 := p1) (Ct := Ct) (p9 := p9) (pinv := pinv) (q3 := q3) (t3 := t3) (Dv := Dv) (Cdc := Cdc) (CY1 := CY1) (R := R) (S1 := S1) (N3 := N3) (T := T) (G := G) (hA := hA) (hCt := hCt) (hCdc := hCdc) (hCY1 := hCY1) (hR := hR) (hS1 := hS1) (hN3 := hN3) (hT := hT) (hG := hG) (hcs := hcs) (hsgi := hsgi) (_hp10 := _hp10) (hp1 := hp1) (hp90 := hp90) (hp9 := hp9) (hpinv := hpinv) (hq30 := hq30) (hq3 := hq3) (ht30 := ht30) (ht3 := ht3) (hDv := hDv)

private theorem collapse_term3_cut
    {UD cs dd sgi SC Bv CB R S1 N3 T G : ℝ}
    (hUD : 0 ≤ UD) (hdd : 0 ≤ dd) (hSC : 0 ≤ SC) (hCB : 0 ≤ CB)
    (hR : 0 < R) (hS1 : 1 ≤ S1) (hN3 : 0 < N3) (hT : 0 ≤ T) (hG : 0 ≤ G)
    (hcs : cs = N3 / 9) (hsgi : sgi = (R * R)⁻¹)
    (_hBv0 : 0 ≤ Bv) (hBv : Bv ≤ CB * T * S1 * G) :
    UD * cs * dd * sgi * (SC * Bv) ≤
      ((1 / 9) * UD * dd * SC * CB) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * G := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.bcollapse_term3 (UD := UD) (cs := cs) (dd := dd) (sgi := sgi) (SC := SC) (Bv := Bv) (CB := CB) (R := R) (S1 := S1) (N3 := N3) (T := T) (G := G) (hUD := hUD) (hdd := hdd) (hSC := hSC) (hCB := hCB) (hR := hR) (hS1 := hS1) (hN3 := hN3) (hT := hT) (hG := hG) (hcs := hcs) (hsgi := hsgi) (_hBv0 := _hBv0) (hBv := hBv)

/-! ### Clause (C), closed -/

private theorem aux_comparison_power_dictionary (s sigma : ℝ) (n : ℕ)
    (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma) :
    let R : ℝ := Real.sqrt sigma
    let S1 : ℝ := s ^ (-(1 / 2 : ℝ))
    let N3 : ℝ := (3 : ℝ) ^ n
    let T : ℝ := (3 : ℝ) ^ (s * (n : ℝ))
    0 < R ∧
    R * R = sigma ∧
    (2 : ℝ) ≤ S1 ∧
    (1 : ℝ) ≤ S1 ∧
    (0 : ℝ) ≤ S1 ∧
    0 < N3 ∧
    0 ≤ T ∧
    S1 ^ 4 = s ^ (-2 : ℝ) ∧
    S1 ^ 16 = s ^ (-8 : ℝ) ∧
    S1 ^ 2 = s⁻¹ ∧
    S1 ^ 9 = s ^ (-(9 / 2 : ℝ)) ∧
    S1 ^ 24 = s ^ (-12 : ℝ) ∧
    (R * R)⁻¹ = sigma⁻¹ ∧
    N3 * T = (3 : ℝ) ^ ((1 + s) * (n : ℝ)) ∧
    (3 : ℝ) ^ (-(2 * (n : ℤ))) = (N3 * N3)⁻¹ ∧
    (3 : ℝ) ^ ((n : ℤ) - 2) = N3 / 9 ∧
    centeredCubeScale ((n : ℤ) - 2) = N3 / 9 ∧
    (s / 2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * S1 ∧
    (0 : ℝ) ≤ (s / 2 : ℝ) ^ (-(1 / 2 : ℝ)) ∧
    (s / 2 : ℝ)⁻¹ = 2 * S1 ^ 2 ∧
    (s - s / 2 : ℝ)⁻¹ = 2 * S1 ^ 2 ∧
    (0 : ℝ) ≤ (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) ∧
    (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) ≤ 32 * S1 ^ 9 := by
  dsimp only
  set R : ℝ := Real.sqrt sigma with hRdef
  set S1 : ℝ := s ^ (-(1 / 2 : ℝ)) with hS1def
  set N3 : ℝ := (3 : ℝ) ^ (n : ℕ) with hN3def
  set T : ℝ := (3 : ℝ) ^ (s * (n : ℝ)) with hTdef
  have hR : 0 < R := Real.sqrt_pos.mpr hsigma
  have hRR : R * R = sigma := Real.mul_self_sqrt hsigma.le
  have hS12 : (2 : ℝ) ≤ S1 := two_le_rpow_neg_half hs0 hs4
  have hS11 : (1 : ℝ) ≤ S1 := by linarith
  have hS10 : (0 : ℝ) ≤ S1 := by linarith
  have hN3 : 0 < N3 := by rw [hN3def]; positivity
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hS4 : S1 ^ 4 = s ^ (-2 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 4]
    congr 1
    norm_num
  have hS16 : S1 ^ 16 = s ^ (-8 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 16]
    congr 1
    norm_num
  have hS2 : S1 ^ 2 = s⁻¹ := by
    rw [hS1def, rpow_neg_half_pow hs0 2,
      show (-((2 : ℕ) : ℝ) / 2) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
  have hS9 : S1 ^ 9 = s ^ (-(9 / 2 : ℝ)) := by
    rw [hS1def, rpow_neg_half_pow hs0 9]
    congr 1
    norm_num
  have hS24 : S1 ^ 24 = s ^ (-12 : ℝ) := by
    rw [hS1def, rpow_neg_half_pow hs0 24]
    congr 1
    norm_num
  have hRRinv : (R * R)⁻¹ = sigma⁻¹ := by rw [hRR]
  have hN3T : N3 * T = (3 : ℝ) ^ ((1 + s) * (n : ℝ)) := by
    rw [hN3def, hTdef, ← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hpow1 : (3 : ℝ) ^ (-(2 * (n : ℤ))) = (N3 * N3)⁻¹ := by
    rw [hN3def, zpow_neg,
      show (2 * (n : ℤ)) = ((n : ℕ) : ℤ) + ((n : ℕ) : ℤ) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  have hcsB : (3 : ℝ) ^ ((n : ℤ) - 2) = N3 / 9 := by
    rw [hN3def,
      show ((n : ℤ) - 2) = ((n : ℕ) : ℤ) + (-2 : ℤ) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    norm_num
    ring
  have hcsA : centeredCubeScale ((n : ℤ) - 2) = N3 / 9 := by
    simpa only [centeredCubeScale] using hcsB
  have hp1 : (s / 2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * S1 := by
    have hc : (2 : ℝ) ^ (-(-(1 / 2 : ℝ))) ≤ 2 := by
      rw [neg_neg]
      calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    exact rpow_half_le_two_mul_rpow hs0 hc
  have hp10 : (0 : ℝ) ≤ (s / 2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hp2 : (s / 2 : ℝ)⁻¹ = 2 * S1 ^ 2 := by
    rw [hS2]
    simp only [div_eq_mul_inv]
    ring
  have hpinv : (s - s / 2 : ℝ)⁻¹ = 2 * S1 ^ 2 := by
    rw [hS2, show s - s / 2 = s / 2 by ring]
    simp only [div_eq_mul_inv]
    ring
  have hp90 : (0 : ℝ) ≤ (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hp9 : (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) ≤ 32 * S1 ^ 9 := by
    have hc : (2 : ℝ) ^ (-(-(9 / 2 : ℝ))) ≤ 32 := by
      rw [neg_neg]
      have h5 : (2 : ℝ) ^ ((5 : ℕ) : ℝ) = 32 := by
        rw [Real.rpow_natCast]; norm_num
      calc (2 : ℝ) ^ (9 / 2 : ℝ) ≤ (2 : ℝ) ^ ((5 : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 32 := h5
    have h := rpow_half_le_two_mul_rpow (c := 32) hs0 hc
    rw [hS9]
    exact h
  exact ⟨hR, hRR, hS12, hS11, hS10, hN3, hT0, hS4, hS16, hS2, hS9, hS24, hRRinv, hN3T, hpow1, hcsB, hcsA, hp1, hp10, hp2, hpinv, hp90, hp9⟩

/-- Scalar factor estimates in a context free of solution and geometry data. -/
private theorem aux_comparison_factor_bounds (s sigma Kslot V Er Cerr Wq Gq : ℝ) (n : ℕ)
    (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma) (hKslot : 0 < Kslot)
    (hV0 : 0 ≤ V) (hEr0 : 0 ≤ Er) (hWq0 : 0 ≤ Wq) (hGq0 : 0 ≤ Gq)
    (hErC : Er ≤ Cerr) :
    let R := Real.sqrt sigma
    let S1 := s ^ (-(1 / 2 : ℝ))
    let N3 := (3 : ℝ) ^ n
    let T := (3 : ℝ) ^ (s * (n : ℝ))
    let SK := Real.sqrt Kslot
    let Efull := V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er)
    let Sfull := Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
      Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
        s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) * Gq ^ 2))
    (0 ≤ Efull) ∧
    (Efull ≤ V * 3 * Er) ∧
    (Efull ≤ V * 3 * Cerr) ∧
    ((0 : ℝ) ≤ (3 : ℝ) ^ (s / 3 : ℝ)) ∧
    ((3 : ℝ) ^ (s / 3 : ℝ) ≤ 3) ∧
    ((0 : ℝ) ≤ 1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2) ∧
    (1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2 ≤
      1 + 9 * (V * 3 * Cerr) ^ 2) ∧
    ((0 : ℝ) ≤ (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ))) ∧
    ((3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) ≤ T) ∧
    (0 ≤ Sfull) ∧
    (Sfull ≤ 2 * S1 * SK * (R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq)) := by
  dsimp only
  set R : ℝ := Real.sqrt sigma with hRdef
  set S1 : ℝ := s ^ (-(1 / 2 : ℝ)) with hS1def
  set N3 : ℝ := (3 : ℝ) ^ n with hN3def
  set T : ℝ := (3 : ℝ) ^ (s * (n : ℝ)) with hTdef
  set SK : ℝ := Real.sqrt Kslot with hSKdef
  set Efull : ℝ := V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er) with hEfulldef
  set Sfull : ℝ := Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
    Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
      s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) * Gq ^ 2)) with hSfulldef
  have hSK0 : 0 ≤ SK := Real.sqrt_nonneg _
  obtain ⟨hR, hRR, hS12, hS11, hS10, hN3, hT0, hS4, hS16, hS2, hS9, hS24, hRRinv, hN3T, hpow1, hcsB, hcsA, hp1, hp10, hp2, hpinv, hp90, hp9⟩ :=
    aux_comparison_power_dictionary s sigma n hs0 hs4 hsigma
  -- the elementary factor bounds
  have hthree : ∀ a : ℝ, 0 ≤ a → a ≤ 1 → (3 : ℝ) ^ a ≤ 3 := by
    intro a _ha1 ha2
    calc (3 : ℝ) ^ a ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2
      _ = 3 := Real.rpow_one 3
  have hE0 : 0 ≤ Efull := by rw [hEfulldef]; positivity
  have hEB : Efull ≤ V * 3 * Er := by
    rw [hEfulldef]
    have h := hthree (s / 8 * (4 : ℝ)) (by positivity) (by linarith)
    calc V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er) ≤ V * (3 * Er) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h hEr0) hV0
      _ = V * 3 * Er := by ring
  have hEC : Efull ≤ V * 3 * Cerr := by
    refine hEB.trans ?_
    exact mul_le_mul_of_nonneg_left hErC (by positivity)
  have he30 : (0 : ℝ) ≤ (3 : ℝ) ^ (s / 3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have he3 : (3 : ℝ) ^ (s / 3 : ℝ) ≤ 3 := hthree _ (by positivity) (by linarith)
  have hq30 : (0 : ℝ) ≤ 1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2 := by positivity
  have hq3 : 1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2 ≤
      1 + 9 * (V * 3 * Cerr) ^ 2 := by
    have hbase : (3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull ≤ 3 * (V * 3 * Cerr) := by
      refine mul_le_mul (hthree _ (by positivity) (by linarith)) hEC hE0 (by norm_num)
    have hnn : 0 ≤ (3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull := by positivity
    have hsq := pow_le_pow_left₀ hnn hbase 2
    refine le_trans (add_le_add (le_refl (1 : ℝ)) hsq) (le_of_eq ?_)
    ring
  have ht30 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have ht3 : (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) ≤ T := by
    rw [hTdef]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hcast : ((((n : ℤ) - 3 : ℤ)) : ℝ) ≤ (n : ℝ) := by push_cast; linarith
    exact mul_le_mul_of_nonneg_left hcast hs0.le
  -- the parent-energy slot
  have hSv0 : 0 ≤ Sfull := by
    rw [hSfulldef]
    exact mul_nonneg (Section6Dirichlet.dirichletWeightedEnergyFactor_nonneg _ _)
      (Real.sqrt_nonneg _)
  have ha0 : (0 : ℝ) ≤ sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 :=
    mul_nonneg (mul_nonneg hsigma.le (zpow_nonneg (by norm_num) _)) (sq_nonneg _)
  have hb0 : (0 : ℝ) ≤ s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) *
      Gq ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (inv_nonneg.mpr hsigma.le)) (Real.rpow_nonneg (by norm_num) _)) (sq_nonneg _)
  have hsqa : Real.sqrt (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2) =
      R * N3⁻¹ * Wq := by
    have hid : sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 = (R * N3⁻¹ * Wq) ^ 2 := by
      rw [hpow1, ← hRR, mul_inv_rev]
      ring
    rw [hid, Real.sqrt_sq (by positivity)]
  have hsqb : Real.sqrt (s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) *
      Gq ^ 2) = S1 ^ 12 * R⁻¹ * T * Gq := by
    have hT2 : T ^ 2 = (3 : ℝ) ^ (2 * s * (n : ℝ)) := by
      rw [hTdef, ← Real.rpow_natCast ((3 : ℝ) ^ (s * (n : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
    have hRinv2 : (R⁻¹) ^ 2 = sigma⁻¹ := by
      rw [inv_pow, pow_two, hRR]
    have hid : s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) * Gq ^ 2 =
        (S1 ^ 12 * R⁻¹ * T * Gq) ^ 2 := by
      rw [← hS24, ← hT2, ← hRinv2]
      ring
    rw [hid, Real.sqrt_sq (by positivity)]
  have hSv : Sfull ≤ 2 * S1 * SK * (R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq) := by
    have hsum : Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
        s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) * Gq ^ 2)) ≤
        SK * (R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq) := by
      rw [Real.sqrt_mul hKslot.le]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      calc Real.sqrt (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
              s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) * Gq ^ 2) ≤
            Real.sqrt (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2) +
              Real.sqrt (s ^ (-12 : ℝ) * sigma⁻¹ *
                (3 : ℝ) ^ (2 * s * (n : ℝ)) * Gq ^ 2) :=
            sqrt_add_le_add_sqrt' ha0 hb0
        _ = R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq := by rw [hsqa, hsqb]
    have hdw := dirichletWeightedEnergyFactor_third_half_le hs0 hs4
    rw [hSfulldef]
    calc Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
          Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
            s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) * Gq ^ 2)) ≤
          (2 * S1) * (SK * (R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq)) :=
        mul_le_mul hdw hsum (Real.sqrt_nonneg _) (by positivity)
      _ = 2 * S1 * SK * (R * N3⁻¹ * Wq + S1 ^ 12 * R⁻¹ * T * Gq) := by ring
  exact ⟨hE0, hEB, hEC, he30, he3, hq30, hq3, ht30, ht3, hSv0, hSv⟩

/-- Arithmetic collapse of the three loop slots, independent of the geometric readout. -/
private theorem aux_comparison_three_slots
    (n : ℕ) (s sigma A Ct V Kslot Cdslot UD dd SC Cb Cerr Er Wq Gq Bsv : ℝ)
    (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) (hsigma : 0 < sigma)
    (hA0 : 0 ≤ A) (hCt0 : 0 ≤ Ct) (hV0 : 0 ≤ V)
    (hKslot : 0 < Kslot) (hCdslot : 0 < Cdslot)
    (hUD0 : 0 ≤ UD) (hdd0 : 0 ≤ dd) (hSC0 : 0 ≤ SC) (hCb : 0 < Cb)
    (hEr0 : 0 ≤ Er) (hWq0 : 0 ≤ Wq) (hGq0 : 0 ≤ Gq) (hErC : Er ≤ Cerr)
    (hBv0 : 0 ≤ Bsv)
    (hBv : Bsv ≤ Cb * ((3 : ℝ) ^ (s * (n : ℝ))) * (s ^ (-(1 / 2 : ℝ))) * Gq) :
    let R := Real.sqrt sigma
    let S1 := s ^ (-(1 / 2 : ℝ))
    let SK := Real.sqrt Kslot
    let Efull := V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er)
    let Sfull := Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
      Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
        s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) * Gq ^ 2))
    let Dfull := Cdslot * S1 * Gq
    let CXv := 8 * A * Ct * V * SK
    let CYv := (128 / 9) * A * Ct * Cdslot * (1 + 9 * (V * 3 * Cerr) ^ 2)
    let CZv := (1 / 9) * UD * dd * SC * Cb
    let P0 := A * centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹
    let Q0 := (s / 2 : ℝ) ^ (-(1 / 2 : ℝ))
    let X1 := Ct * (s / 2 : ℝ)⁻¹ * R * (3 : ℝ) ^ (s / 3 : ℝ) * Efull * Sfull
    let Y1 := Ct * (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) * (s - s / 2 : ℝ)⁻¹ *
      (1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2) *
      (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) * Dfull
    let Z1 := UD * (3 : ℝ) ^ ((n : ℤ) - 2) * dd * sigma⁻¹ * (SC * Bsv)
    (P0 * (Q0 * (X1 + Y1)) + Z1 ≤
      CXv * s ^ (-2 : ℝ) * Er * Wq +
        (CXv * Cerr + CYv + CZv) * s ^ (-8 : ℝ) * sigma⁻¹ *
          (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq) ∧
      0 ≤ CXv ∧ 0 ≤ CYv ∧ 0 ≤ CZv := by
  dsimp only
  set R : ℝ := Real.sqrt sigma with hRdef
  set S1 : ℝ := s ^ (-(1 / 2 : ℝ)) with hS1def
  set N3 : ℝ := (3 : ℝ) ^ n with hN3def
  set T : ℝ := (3 : ℝ) ^ (s * (n : ℝ)) with hTdef
  set SK : ℝ := Real.sqrt Kslot with hSKdef
  have hSK0 : 0 ≤ SK := Real.sqrt_nonneg _
  obtain ⟨hR, hRR, hS12, hS11, hS10, hN3, hT0, hS4, hS16, hS2, hS9, hS24, hRRinv, hN3T, hpow1, hcsB, hcsA, hp1, hp10, hp2, hpinv, hp90, hp9⟩ :=
    aux_comparison_power_dictionary s sigma n hs0 hs4 hsigma
  set Efull : ℝ := V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er) with hEfulldef
  set Sfull : ℝ := Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
    Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
      s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) * Gq ^ 2)) with hSfulldef
  set Dfull : ℝ := Cdslot * S1 * Gq with hDfulldef
  set CXv : ℝ := 8 * A * Ct * V * SK with hCXvdef
  set CYv : ℝ := (128 / 9) * A * Ct * Cdslot * (1 + 9 * (V * 3 * Cerr) ^ 2)
    with hCYvdef
  set CZv : ℝ := (1 / 9) * UD * dd *
    SC * Cb with hCZvdef
  set P0 : ℝ := A * centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ with hP0def
  set Q0 : ℝ := (s / 2 : ℝ) ^ (-(1 / 2 : ℝ)) with hQ0def
  set X1 : ℝ := Ct * (s / 2 : ℝ)⁻¹ * R * (3 : ℝ) ^ (s / 3 : ℝ) * Efull * Sfull
    with hX1def
  set Y1 : ℝ := Ct * (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) * (s - s / 2 : ℝ)⁻¹ *
    (1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2) *
    (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) * Dfull with hY1def
  set Z1 : ℝ := UD * (3 : ℝ) ^ ((n : ℤ) - 2) * dd *
    sigma⁻¹ * (SC * Bsv) with hZ1def
  obtain ⟨hE0, hEB, hEC, he30, he3, hq30, hq3, ht30, ht3, hSv0, hSv⟩ :=
    aux_comparison_factor_bounds s sigma Kslot V Er Cerr Wq Gq n
      hs0 hs4 hsigma hKslot hV0 hEr0 hWq0 hGq0 hErC
  -- the collapse itself
  have hkey : P0 * (Q0 * (X1 + Y1)) + Z1 ≤
      CXv * S1 ^ 4 * Er * Wq +
        (CXv * Cerr + CYv + CZv) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq := by
    have h1 : P0 * (Q0 * X1) ≤
        CXv * S1 ^ 4 * Er * Wq +
          CXv * Cerr * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq :=
      collapse_term1_cut hA0 hCt0 hV0 hSK0 hR hS10 hN3 hT0 hEr0 hWq0 hGq0 hErC
        hcsA hRRinv.symm hp10 hp1 hp2 he30 he3 hE0 hEB hSv0 hSv
    have h2 : P0 * (Q0 * Y1) ≤ CYv * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq :=
      collapse_term2_cut hA0 hCt0 hCdslot.le (by positivity) hR hS11 hN3 hT0 hGq0
        hcsA hRRinv.symm hp10 hp1 hp90 hp9 hpinv hq30 hq3 ht30 ht3 rfl
    have h3 : Z1 ≤ CZv * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq :=
      collapse_term3_cut hUD0 hdd0 hSC0 hCb.le hR hS11 hN3
        hT0 hGq0 hcsB hRRinv.symm hBv0 hBv
    have hsplit : P0 * (Q0 * (X1 + Y1)) + Z1 =
        P0 * (Q0 * X1) + P0 * (Q0 * Y1) + Z1 := by ring
    rw [hsplit]
    refine le_trans (add_le_add (add_le_add h1 h2) h3) (le_of_eq ?_)
    ring
  have hCXv0 : 0 ≤ CXv := by rw [hCXvdef]; positivity
  have hCYv0 : 0 ≤ CYv := by rw [hCYvdef]; positivity
  have hCZv0 : 0 ≤ CZv := by rw [hCZvdef]; positivity
  have hconv : CXv * S1 ^ 4 * Er * Wq +
      (CXv * Cerr + CYv + CZv) * S1 ^ 16 * (R * R)⁻¹ * N3 * T * Gq =
      CXv * s ^ (-2 : ℝ) * Er * Wq +
        (CXv * Cerr + CYv + CZv) * s ^ (-8 : ℝ) * sigma⁻¹ *
          (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq := by
    rw [hS4, hS16, hRRinv, ← hN3T]
    ring
  exact ⟨hkey.trans (le_of_eq hconv), hCXv0, hCYv0, hCZv0⟩

/-- **The interior harmonic-approximation clause of
`l.cutoff.regularity.good.scale.estimates`.**

The three clauses of the frozen interior anchor, with `m ≤ L` deleted and the
good event replaced by `𝒢^{(L)}_{n+2,z}`: (A) and (B) are
`interiorHarmonic_wellPosed`, and (C) is discharged from
`exists_interiorCutoffHarmonicComparison_le_sharpLoopBound` by the window
shrink, the indicator split, and the arithmetic collapse of the sharp loop
carrier. -/
theorem interiorCutoffHarmonicApproximationInput_holds (d : ℕ) [NeZero d] :
    InteriorCutoffHarmonicApproximationInput d (-2 : ℝ) (-8 : ℝ) := by
  classical
  obtain ⟨Cloop, Kslot, Cdslot, hCloopTop, hKslot, hCdslot, hloop⟩ :=
    exists_interiorCutoffHarmonicComparison_le_sharpLoopBound d
  obtain ⟨Cerr, hCerr, herr⟩ :=
    exists_section6HomogenizationError_le_of_cutoffGoodEvent (d := d)
  obtain ⟨Cb, hCb, hbesov⟩ := exists_interiorForceBesov_le_windowSeminorm d
  have hA0 : (0 : ℝ) ≤ (flatComparatorSharpSpectralConstant d).toReal :=
    ENNReal.toReal_nonneg
  have hCt0 : (0 : ℝ) ≤ Cloop.toReal := ENNReal.toReal_nonneg
  have hUD0 : (0 : ℝ) ≤ unitDirichletPoincareConst d :=
    unitDirichletPoincareConst_nonneg d
  refine ⟨(9 : ℝ) ^ d *
      ((8 * (flatComparatorSharpSpectralConstant d).toReal * Cloop.toReal *
          Real.sqrt (192 * (d : ℝ)) * Real.sqrt Kslot) * (1 + Cerr) +
        ((128 / 9) * (flatComparatorSharpSpectralConstant d).toReal *
          Cloop.toReal * Cdslot *
          (1 + 9 * (Real.sqrt (192 * (d : ℝ)) * 3 * Cerr) ^ 2)) +
        ((1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
          Real.sqrt (Fintype.card (Fin d) : ℝ) * Cb) + 1), by positivity, ?_⟩
  intro M s hs L m n hnm z hz x hx hbd ω u g hweak hgex y hy hcov hloc uD
    hfval hfgrad
  refine ⟨(Section6HarmonicInterior.interiorHarmonic_wellPosed d n y uD).1,
    (Section6HarmonicInterior.interiorHarmonic_wellPosed d n y uD).2, ?_⟩
  intro v hharm htrace
  -- corridor parameters
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < s := (mul_pos (by norm_num) (pow_pos hdelta 2)).trans_le hs.1
  have hs4 : s ≤ 1 / 4 := hs.2
  have hslt : s < 1 := by linarith
  have hxDomain : x ∈ cube d (m : ℤ) :=
    Section6ExcessDecay.truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 3) z hx
  set U : Set (Vec d) := truncatedCube d (m : ℤ) (n : ℤ) x with hUdef
  set sigma : ℝ :=
    tailAverage M L (n + 2) ω (translatedCube d ((n : ℤ) + 2) z) with hsigmadef
  set Er : ℝ := section6HomogenizationError M (s / 8) L (n + 2) ω z with hErdef
  set Wq : ℝ := normalizedL2On U (fun q ↦ u.toFun q - averageOn U u.toFun)
    with hWqdef
  set Gq : ℝ := (fractionalSeminormOn U s g).toReal with hGqdef
  have hsigma : 0 < sigma := by
    rw [hsigmadef, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega,
      ← Section6Covariance.tailCoefficientCubeAverage_translatePotentialSample]
    exact tailCoefficientCubeAverage_pos M L (n + 2) (translatePotentialSample z ω)
  have hEr0 : 0 ≤ Er := ENNReal.toReal_nonneg
  have hWq0 : 0 ≤ Wq := Section6Iteration.normalizedL2On_nonneg _ _
  have hGq0 : 0 ≤ Gq := ENNReal.toReal_nonneg
  refine Section6HarmonicApproximation.indicatorValue_le_of_mem_imp _ _ _
    (by positivity) ?_
  intro hgood
  -- the constants of the collapse
  set A : ℝ := (flatComparatorSharpSpectralConstant d).toReal with hAdef
  set Ct : ℝ := Cloop.toReal with hCtdef
  set V : ℝ := Real.sqrt (192 * (d : ℝ)) with hVdef
  set SK : ℝ := Real.sqrt Kslot with hSKdef
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  have hSK0 : 0 ≤ SK := Real.sqrt_nonneg _
  -- the polynomial variables
  set R : ℝ := Real.sqrt sigma with hRdef
  set S1 : ℝ := s ^ (-(1 / 2 : ℝ)) with hS1def
  set N3 : ℝ := (3 : ℝ) ^ (n : ℕ) with hN3def
  set T : ℝ := (3 : ℝ) ^ (s * (n : ℝ)) with hTdef

  -- the error cap on the good event
  have hErC : Er ≤ Cerr := herr M s hs L (n + 2) ω z hgood
  -- the fractional datum at the anchor's own order
  obtain ⟨sOrder, hsval, hgWsp⟩ := hgex
  have hsO : sOrder = (⟨s, hs0, hslt⟩ : FractionalOrder) := Subtype.ext hsval
  rw [hsO] at hgWsp
  -- the harmonic difference is an `H¹₀` element
  have hH10 : MemH10 (translatedCube d ((n : ℤ) - 2) y)
      (fun p ↦ v.toFun p - u.toFun p) :=
    Section6HarmonicApproximation.memH10_sub_physical_of_hasZeroTraceDifferenceOn
      htrace hfval
  -- the sharp loop
  have hL := hloop M s hs L m n hnm z x y ω hz hx hloc hbd hgood u g hweak
    hgWsp v hharm hH10
  -- the window shrink
  have hvolW : (volume (translatedCube d ((n : ℤ) - 2) y)).toReal =
      ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d := by
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet,
      volume_translateSet_eq, volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
    simp only [originCube]
  have hWpos : 0 < (volume (translatedCube d ((n : ℤ) - 2) y)).toReal := by
    rw [hvolW]; positivity
  have hVpos : 0 < (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)).toReal :=
    Section6ExcessDecay.volume_toReal_truncatedCube_pos x hxDomain (by omega)
  have hshrink := Section6HarmonicApproximation.normalizedL2On_sub_physical_le_of_subset
    (uD := uD) (v := v) (u := u.toFun) hfval hcov hWpos hVpos
  have hratio : (volume (translatedCube d ((n : ℤ) - 2) y)).toReal /
      (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)).toReal ≤ (81 : ℝ) ^ d := by
    have hlow :=
      (Section6ExcessDecay.volume_toReal_truncatedCube_bounds x hxDomain
        (show (n : ℤ) - 4 - 1 ≤ (m : ℤ) by omega)).1
    have hlowpos : (0 : ℝ) < ((3 : ℝ) ^ ((n : ℤ) - 4 - 2)) ^ d := by positivity
    have hquot : ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d /
        ((3 : ℝ) ^ ((n : ℤ) - 4 - 2)) ^ d = (81 : ℝ) ^ d := by
      rw [← div_pow, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0),
        show (n : ℤ) - 2 - ((n : ℤ) - 4 - 2) = 4 by ring]
      norm_num
    rw [hvolW, ← hquot]
    exact div_le_div_of_nonneg_left (by positivity) hlowpos hlow
  have hratio9 : Real.sqrt ((volume (translatedCube d ((n : ℤ) - 2) y)).toReal /
      (volume (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)).toReal) ≤ (9 : ℝ) ^ d := by
    have h81 : ((9 : ℝ) ^ d) ^ 2 = (81 : ℝ) ^ d := by
      rw [← pow_mul, show d * 2 = 2 * d by ring, pow_mul]
      norm_num
    have hq := Real.sqrt_le_sqrt hratio
    rwa [← h81, Real.sqrt_sq (by positivity)] at hq
  -- the three slots of the loop carrier, written in the polynomial variables
  set Efull : ℝ := V * ((3 : ℝ) ^ (s / 8 * (4 : ℝ)) * Er) with hEfulldef
  set Sfull : ℝ := Section6Dirichlet.dirichletWeightedEnergyFactor (s / 3) (s / 2) *
    Real.sqrt (Kslot * (sigma * (3 : ℝ) ^ (-(2 * (n : ℤ))) * Wq ^ 2 +
      s ^ (-12 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ (2 * s * (n : ℝ)) * Gq ^ 2)) with hSfulldef
  set Dfull : ℝ := Cdslot * S1 * Gq with hDfulldef
  set CXv : ℝ := 8 * A * Ct * V * SK with hCXvdef
  set CYv : ℝ := (128 / 9) * A * Ct * Cdslot * (1 + 9 * (V * 3 * Cerr) ^ 2)
    with hCYvdef
  set CZv : ℝ := (1 / 9) * unitDirichletPoincareConst d * (d : ℝ) *
    Real.sqrt (Fintype.card (Fin d) : ℝ) * Cb with hCZvdef
  -- power dictionary
  obtain ⟨hE0, hEB, hEC, he30, he3, hq30, hq3, ht30, ht3, hSv0, hSv⟩ :=
    aux_comparison_factor_bounds s sigma Kslot V Er Cerr Wq Gq n
      hs0 hs4 hsigma hKslot hV0 hEr0 hWq0 hGq0 hErC
  -- the direct forcing slot
  set Bsv : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo
    (originCube d ((n : ℤ) - 2)) (s / 2 : ℝ) (fun p ↦ g (p + y)) with hBsvdef
  have hglocalS : Ch03.ABK26.MemCubeEuclideanFullWsp
      (originCube d ((n : ℤ) - 2)) (⟨s, hs0, hslt⟩ : FractionalOrder)
      FiniteLpExponent.two (fun p ↦ g (p + y)) := by
    refine memCubeEuclideanFullWsp_translate_of_subset
      (originCube d ((n : ℤ) - 2)) (originCube d (m : ℤ)) y _
      FiniteLpExponent.two g ?_ hgWsp
    intro p hp
    refine (hloc ?_).2
    rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
    exact hp
  have hbesovReg : ForceBesovRegularity (originCube d ((n : ℤ) - 2)) s
      (fun p ↦ g (p + y)) :=
    (cubeEuclideanWspField_forceSobolevRegularity
      (⟨s, hs0, hslt⟩ : FractionalOrder)
      { toField := fun p ↦ g (p + y)
        euclideanMemLp := hglocalS.1
        euclideanMemWsp := hglocalS.2 }).toForceBesovRegularity hs0 hslt.le
  have hBv0 : 0 ≤ Bsv :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove _ _ _
      (cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_exponent_le _ _
        (show (s / 2 : ℝ) ≤ s by linarith) hbesovReg.partialSeminorms_bddAbove)
  have hBv : Bsv ≤ Cb * T * S1 * Gq :=
    hbesov (⟨s, hs0, hslt⟩ : FractionalOrder) m n hnm z x y hx hloc g hgWsp
      (s / 2) (by linarith)
  -- the three summands of the loop readout
  set P0 : ℝ := A * centeredCubeScale ((n : ℤ) - 2) * sigma⁻¹ with hP0def
  set Q0 : ℝ := (s / 2 : ℝ) ^ (-(1 / 2 : ℝ)) with hQ0def
  set X1 : ℝ := Ct * (s / 2 : ℝ)⁻¹ * R * (3 : ℝ) ^ (s / 3 : ℝ) * Efull * Sfull
    with hX1def
  set Y1 : ℝ := Ct * (s / 2 : ℝ) ^ (-(9 / 2 : ℝ)) * (s - s / 2 : ℝ)⁻¹ *
    (1 + ((3 : ℝ) ^ ((s / 3 : ℝ) / 2) * Efull) ^ 2) *
    (3 : ℝ) ^ (s * ((((n : ℤ) - 3 : ℤ)) : ℝ)) * Dfull with hY1def
  set Z1 : ℝ := unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) * (d : ℝ) *
    sigma⁻¹ * (Real.sqrt (Fintype.card (Fin d) : ℝ) * Bsv) with hZ1def
  obtain ⟨hcollapse, hCXv0, hCYv0, hCZv0⟩ :=
    aux_comparison_three_slots n s sigma A Ct V Kslot Cdslot
      (unitDirichletPoincareConst d) (d : ℝ) (Real.sqrt (Fintype.card (Fin d) : ℝ))
      Cb Cerr Er Wq Gq Bsv hs0 hs4 hsigma hA0 hCt0 hV0 hKslot hCdslot
      hUD0 (by positivity) (Real.sqrt_nonneg _) hCb hEr0 hWq0 hGq0 hErC hBv0 hBv
  change 0 ≤ CXv at hCXv0
  change 0 ≤ CYv at hCYv0
  change 0 ≤ CZv at hCZv0
  change P0 * (Q0 * (X1 + Y1)) + Z1 ≤
    CXv * s ^ (-2 : ℝ) * Er * Wq +
      (CXv * Cerr + CYv + CZv) * s ^ (-8 : ℝ) * sigma⁻¹ *
        (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq at hcollapse
  clear_value CXv CYv CZv
  -- assemble
  have hreadout := flatComparatorSharpGoodEventLoopBound_le_realReadout
    Cloop d n sigma (⟨s / 2, by positivity, by linarith⟩ : FractionalOrder)
    (⟨s / 3, by positivity, by linarith⟩ : FractionalOrder)
    (⟨s, hs0, hslt⟩ : FractionalOrder) Efull Sfull Dfull
    (originCube d ((n : ℤ) - 2)) (fun p ↦ g (p + y))
    (by dsimp only; linarith) hsigma hE0 hSv0
    (by rw [hDfulldef]; positivity)
  refine le_trans (le_trans hshrink
    (mul_le_mul hratio9 (hL.trans hreadout)
      (Section6Iteration.normalizedL2On_nonneg _ _) (by positivity)))
    (le_trans (mul_le_mul_of_nonneg_left hcollapse
      (by positivity)) ?_)
  have hP1 : (0 : ℝ) ≤ s ^ (-2 : ℝ) * Er * Wq :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) hEr0) hWq0
  have hP2 : (0 : ℝ) ≤ s ^ (-8 : ℝ) * sigma⁻¹ *
      (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _)
      (inv_nonneg.mpr hsigma.le)) (Real.rpow_nonneg (by norm_num) _)) hGq0
  have hCerr0 : (0 : ℝ) ≤ Cerr := hCerr.le
  have hprod : (0 : ℝ) ≤ CXv * Cerr := mul_nonneg hCXv0 hCerr0
  have hb1 : (9 : ℝ) ^ d * CXv ≤
      (9 : ℝ) ^ d * (CXv * (1 + Cerr) + CYv + CZv + 1) :=
    mul_le_mul_of_nonneg_left
      (by linarith only [hprod, hCYv0, hCZv0]) (by positivity)
  have hb2 : (9 : ℝ) ^ d * (CXv * Cerr + CYv + CZv) ≤
      (9 : ℝ) ^ d * (CXv * (1 + Cerr) + CYv + CZv + 1) :=
    mul_le_mul_of_nonneg_left
      (by linarith only [hCXv0, hCYv0, hCZv0]) (by positivity)
  calc (9 : ℝ) ^ d * (CXv * s ^ (-2 : ℝ) * Er * Wq +
        (CXv * Cerr + CYv + CZv) * s ^ (-8 : ℝ) * sigma⁻¹ *
          (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq)
      = ((9 : ℝ) ^ d * CXv) * (s ^ (-2 : ℝ) * Er * Wq) +
        ((9 : ℝ) ^ d * (CXv * Cerr + CYv + CZv)) *
          (s ^ (-8 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq) := by
        ring
    _ ≤ ((9 : ℝ) ^ d * (CXv * (1 + Cerr) + CYv + CZv + 1)) *
          (s ^ (-2 : ℝ) * Er * Wq) +
        ((9 : ℝ) ^ d * (CXv * (1 + Cerr) + CYv + CZv + 1)) *
          (s ^ (-8 : ℝ) * sigma⁻¹ * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq) :=
        add_le_add (mul_le_mul_of_nonneg_right hb1 hP1)
          (mul_le_mul_of_nonneg_right hb2 hP2)
    _ = (9 : ℝ) ^ d * (CXv * (1 + Cerr) + CYv + CZv + 1) * s ^ (-2 : ℝ) * Er * Wq +
        (9 : ℝ) ^ d * (CXv * (1 + Cerr) + CYv + CZv + 1) * s ^ (-8 : ℝ) * sigma⁻¹ *
          (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Gq := by ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff
