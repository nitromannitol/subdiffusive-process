
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszEnlargedCellPrice

@[expose] public section

/-!
# Satisfiability of the enlarged price's energy budget

The enlarged local flux price
(`exists_fluxRowSlots_repairedStoppingCell_enlargedLocalFluxPrice`) pays the
whole re-normalization to the physical dual coefficient in two per-cell
budgets, through the volume-free ratio

```
fluxRowRieszEnlargedNqRatio m σ = 2 · 3^{2σ(m+1)} .
```

That ratio **grows with the cell scale**, so the budget must be tested against
the manuscript's scale slack `(size(Q)/R)^{d+6}` — which the datum budget
already carries and the energy budget, as first established, did not.

* `fluxRowSlots_energy_budget_of_smallness_ratio` is
  `fluxRowSlots_energy_budget_of_smallness` with that slack made available;
* `fluxRowSlots_enlarged_energy_smallness` shows the resulting budget **is**
  satisfiable, uniformly over the family, by a scale-free smallness on `η`:
  since `R ≤ 3^m` and `2σ < 2 ≤ d + 6`,

```
  R^{2σ} (3^m/R)^{d+6} ≥ (3^m)^{2σ} ,     3^{2σ(m+1)} = 3^{2σ} (3^m)^{2σ} ≤ 9 (3^m)^{2σ} ,
```

so `W² · 18 · Kcut · Cm · η ≤ 1` suffices at every cell.  Without the slack the
requirement would be `η ≲ (R/3^{m+1})^{2σ}`, which degenerates as the cell scale
leaves the source scale, and no uniform `η` exists — recorded as
`not_forall_enlarged_energy_budget_scaleFree`.

## Source

* `s.fixed.coefficient` and `mfd:sec-speed` (the `(size(Q)/R)^{d+6}` bookkeeping).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Homogenization

noncomputable section

variable {d : ℕ}

/-- `fluxRowSlots_energy_budget_of_smallness` with the manuscript's scale slack
available on the right of the smallness hypothesis. -/
theorem fluxRowSlots_energy_budget_of_smallness_ratio
    {alpha t R sigma cellSize K Cc lambdaInv : ℝ}
    (halpha : 0 < alpha) (ht : 0 < t) (hR : 0 < R) (hRS : R ≤ cellSize)
    (hsmall : K ^ 2 * Cc ≤
      t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6)) :
    alpha * K ^ 2 * Cc ≤
      alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6) *
        (1 + (alpha * lambdaInv) ^ 2) := by
  have hW : (1 : ℝ) ≤ 1 + (alpha * lambdaInv) ^ 2 := by
    nlinarith [sq_nonneg (alpha * lambdaInv)]
  have hratio : 1 ≤ cellSize / R := fluxRowSlots_one_le_ratio hR hRS
  have hpow : (1 : ℝ) ≤ (cellSize / R) ^ (d + 6) := one_le_pow₀ hratio
  have hnn : 0 ≤ t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6) := by
    have h1 : (0 : ℝ) ≤ t⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ Real.rpow R (2 * sigma) := Real.rpow_nonneg hR.le _
    have h3 : (0 : ℝ) ≤ (cellSize / R) ^ (d + 6) := by linarith
    positivity
  have hbase : alpha * K ^ 2 * Cc ≤
      alpha * (t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6)) := by
    nlinarith [halpha.le, hsmall]
  calc alpha * K ^ 2 * Cc
      ≤ alpha * (t⁻¹ * Real.rpow R (2 * sigma) *
          (cellSize / R) ^ (d + 6)) := hbase
    _ ≤ alpha * (t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6)) *
          (1 + (alpha * lambdaInv) ^ 2) := by
        refine le_mul_of_one_le_right (by positivity) hW
    _ = alpha * t⁻¹ * Real.rpow R (2 * sigma) * (cellSize / R) ^ (d + 6) *
          (1 + (alpha * lambdaInv) ^ 2) := by ring

/-- **The enlarged energy budget is satisfiable, uniformly in the cell scale.**

The ratio's growth `3^{2σ(m+1)} = 3^{2σ}(3^m)^{2σ}` is absorbed by the slack
`R^{2σ}(3^m/R)^{d+6} ≥ (3^m)^{2σ}`, leaving the scale-free requirement
`W² · 18 · Kcut · Cm · η ≤ 1`. -/
theorem fluxRowSlots_enlarged_energy_smallness
    (d : ℕ) {Wfac Kcut Cm eta R sigma : ℝ} {m : ℤ}
    (hsigma : sigma ∈ Set.Ioo (0 : ℝ) 1) (hR : 0 < R)
    (hRle : R ≤ (3 : ℝ) ^ m)
    (hKcut : 0 ≤ Kcut) (hCm : 0 ≤ Cm) (heta : 0 ≤ eta)
    (hsmall : Wfac ^ 2 * (18 * Kcut * (Cm * eta)) ≤ 1) :
    Wfac ^ 2 * (fluxRowRieszEnlargedNqRatio m sigma * Kcut * (Cm * eta)) ≤
      Real.rpow R (2 * sigma) * (((3 : ℝ) ^ m) / R) ^ (d + 6) := by
  obtain ⟨hs0, hs1⟩ := hsigma
  set L : ℝ := (3 : ℝ) ^ m with hLdef
  have hL : 0 < L := zpow_pos (by norm_num) _
  have hLR : 1 ≤ L / R := (one_le_div hR).mpr hRle
  have hLrpow : L = Real.rpow 3 (m : ℝ) := by
    rw [hLdef]
    exact (Real.rpow_intCast 3 m).symm
  -- the ratio splits into a scale-free factor and the cell's own scale factor
  have hsplit : Real.rpow 3 (sigma * ((m + 1 : ℤ) : ℝ)) ^ 2 =
      Real.rpow 3 (2 * sigma) * Real.rpow L (2 * sigma) := by
    rw [hLrpow]
    show ((3 : ℝ) ^ (sigma * ((m + 1 : ℤ) : ℝ))) ^ (2 : ℕ) =
      (3 : ℝ) ^ (2 * sigma) * ((3 : ℝ) ^ (m : ℝ)) ^ (2 * sigma)
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (sigma * ((m + 1 : ℤ) : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  -- the manuscript's scale slack dominates the cell's scale factor
  have hkey : Real.rpow L (2 * sigma) ≤
      Real.rpow R (2 * sigma) * (L / R) ^ (d + 6) := by
    have hLeq : L = R * (L / R) := by field_simp
    have hmul : Real.rpow L (2 * sigma) =
        Real.rpow R (2 * sigma) * Real.rpow (L / R) (2 * sigma) := by
      rw (occs := .pos [1]) [hLeq]
      exact Real.mul_rpow hR.le (by linarith)
    have hdeg : 2 * sigma ≤ ((d + 6 : ℕ) : ℝ) := by
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have h6 : (6 : ℝ) ≤ ((d + 6 : ℕ) : ℝ) := by push_cast; linarith
      linarith
    have hexp : Real.rpow (L / R) (2 * sigma) ≤
        Real.rpow (L / R) ((d + 6 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hLR hdeg
    have hnat : Real.rpow (L / R) ((d + 6 : ℕ) : ℝ) = (L / R) ^ (d + 6) :=
      Real.rpow_natCast _ _
    rw [hmul]
    exact mul_le_mul_of_nonneg_left (hexp.trans_eq hnat)
      (Real.rpow_nonneg hR.le _)
  -- the scale-free factor is at most nine
  have hnine : Real.rpow 3 (2 * sigma) ≤ 9 := by
    have h : Real.rpow (3 : ℝ) (2 * sigma) ≤ Real.rpow (3 : ℝ) (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : Real.rpow (3 : ℝ) (2 : ℝ) = 9 := by
      show (3 : ℝ) ^ (2 : ℝ) = 9
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
      norm_num
    linarith [h, h2.le, h2.ge]
  have hLpow : 0 ≤ Real.rpow L (2 * sigma) := Real.rpow_nonneg hL.le _
  have hPnn : 0 ≤ Wfac ^ 2 * (Kcut * (Cm * eta)) := by positivity
  have hchain : Wfac ^ 2 * (fluxRowRieszEnlargedNqRatio m sigma * Kcut *
      (Cm * eta)) ≤ Real.rpow L (2 * sigma) := by
    rw [fluxRowRieszEnlargedNqRatio, hsplit]
    have hstep1 : Wfac ^ 2 * (2 * (Real.rpow 3 (2 * sigma) *
          Real.rpow L (2 * sigma)) * Kcut * (Cm * eta)) ≤
        Wfac ^ 2 * (Kcut * (Cm * eta)) * 18 * Real.rpow L (2 * sigma) := by
      have hgap : 0 ≤ Wfac ^ 2 * (Kcut * (Cm * eta)) * Real.rpow L (2 * sigma) *
          (9 - Real.rpow 3 (2 * sigma)) :=
        mul_nonneg (mul_nonneg hPnn hLpow) (by linarith)
      nlinarith [hgap]
    have hstep2 : Wfac ^ 2 * (Kcut * (Cm * eta)) * 18 ≤ 1 := by
      nlinarith [hsmall]
    have hstep3 := mul_le_mul_of_nonneg_right hstep2 hLpow
    linarith
  exact hchain.trans hkey

/-- **The datum budget's scale balance.**

Every scale factor of the datum slot at the enlarged cell collects into
`3^{(1+σ)((m+1) + n)}`: the cell volume `3^{d(m+1)}`, the renormalization ratio
`3^{2σ(m+1)}`, the datum prefactor `3^{(1+σ)n}`, the residual-lift factor
`fluxRowSlotsSourceDatumFactor`'s `3^{-(m+1)(1+s)}` squared at `s = (1+σ)/2`,
and the `K`-scale `3^{(m+1)(4-d)}`, since

```
d(m+1) + 2σ(m+1) + (1+σ)n − (m+1)(3+σ) + (m+1)(4−d) = (1+σ)((m+1) + n) .
```

That total is dominated by the manuscript's slack, uniformly over the family:
for `n ≤ m + 1`, `0 < R ≤ 3^m` and `2 + 2σ ≤ 4 ≤ d + 6`,

```
3^{(1+σ)((m+1)+n)} ≤ 81 · R² · R^{2σ} (3^m/R)^{d+6} .
```

`R² = ahom·t` at the row's regime `R = √(ahom t)`, so the datum budget holds
with `α` a dimensional constant times `ahom` — the manuscript's own constant. -/
theorem fluxRowSlots_enlarged_datum_scale_le
    (d : ℕ) {sigma R : ℝ} {m n : ℤ}
    (hs0 : 0 < sigma) (hs1 : sigma < 1)
    (hR : 0 < R) (hRle : R ≤ (3 : ℝ) ^ m) (hn : n ≤ m + 1) :
    Real.rpow 3 ((1 + sigma) * (((m + 1 : ℤ) : ℝ) + (n : ℝ))) ≤
      81 * R ^ 2 * (Real.rpow R (2 * sigma) * (((3 : ℝ) ^ m) / R) ^ (d + 6)) := by
  set L : ℝ := (3 : ℝ) ^ m with hLdef
  have hL : 0 < L := zpow_pos (by norm_num) _
  have hS : 1 ≤ L / R := (one_le_div hR).mpr hRle
  have hLrpow : L = Real.rpow 3 (m : ℝ) := by
    rw [hLdef]; exact (Real.rpow_intCast 3 m).symm
  have hnR : (n : ℝ) ≤ ((m + 1 : ℤ) : ℝ) := by exact_mod_cast hn
  -- 1. exponent monotonicity in `n`
  have hstep1 : Real.rpow 3 ((1 + sigma) * (((m + 1 : ℤ) : ℝ) + (n : ℝ))) ≤
      Real.rpow 3 ((2 + 2 * sigma) * ((m + 1 : ℤ) : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    nlinarith [hnR, hs0]
  -- 2. split off the scale-free factor
  have hsplit : Real.rpow 3 ((2 + 2 * sigma) * ((m + 1 : ℤ) : ℝ)) =
      Real.rpow 3 (2 + 2 * sigma) * Real.rpow L (2 + 2 * sigma) := by
    rw [hLrpow]
    show (3 : ℝ) ^ ((2 + 2 * sigma) * ((m + 1 : ℤ) : ℝ)) =
      (3 : ℝ) ^ (2 + 2 * sigma) * ((3 : ℝ) ^ (m : ℝ)) ^ (2 + 2 * sigma)
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  -- 3. the scale-free factor is at most 81
  have h81 : Real.rpow 3 (2 + 2 * sigma) ≤ 81 := by
    have h : Real.rpow (3 : ℝ) (2 + 2 * sigma) ≤ Real.rpow (3 : ℝ) (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : Real.rpow (3 : ℝ) (4 : ℝ) = 81 := by
      show (3 : ℝ) ^ (4 : ℝ) = 81
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
      norm_num
    linarith [h, h4.le, h4.ge]
  -- 4-6. the cell's scale factor against the slack
  have hLeq : L = R * (L / R) := by field_simp
  have hmul : Real.rpow L (2 + 2 * sigma) =
      Real.rpow R (2 + 2 * sigma) * Real.rpow (L / R) (2 + 2 * sigma) := by
    rw (occs := .pos [1]) [hLeq]
    exact Real.mul_rpow hR.le (by positivity)
  have hdeg : 2 + 2 * sigma ≤ ((d + 6 : ℕ) : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h6 : (6 : ℝ) ≤ ((d + 6 : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hexp : Real.rpow (L / R) (2 + 2 * sigma) ≤ (L / R) ^ (d + 6) := by
    refine (Real.rpow_le_rpow_of_exponent_le hS hdeg).trans_eq ?_
    exact Real.rpow_natCast _ _
  have hRsplit : Real.rpow R (2 + 2 * sigma) = R ^ 2 * Real.rpow R (2 * sigma) := by
    show (R : ℝ) ^ (2 + 2 * sigma) = R ^ 2 * R ^ (2 * sigma)
    rw [Real.rpow_add hR]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  -- assemble
  have hRnn : 0 ≤ Real.rpow R (2 + 2 * sigma) := Real.rpow_nonneg hR.le _
  have hLnn : 0 ≤ Real.rpow L (2 + 2 * sigma) := Real.rpow_nonneg hL.le _
  have h3nn : 0 ≤ Real.rpow 3 (2 + 2 * sigma) :=
    Real.rpow_nonneg (by norm_num) _
  have hSlack : Real.rpow L (2 + 2 * sigma) ≤
      R ^ 2 * (Real.rpow R (2 * sigma) * (L / R) ^ (d + 6)) := by
    rw [hmul, hRsplit]
    have hpos : 0 ≤ R ^ 2 * Real.rpow R (2 * sigma) := by
      have := Real.rpow_nonneg hR.le (2 * sigma); positivity
    calc R ^ 2 * Real.rpow R (2 * sigma) * Real.rpow (L / R) (2 + 2 * sigma)
        ≤ R ^ 2 * Real.rpow R (2 * sigma) * (L / R) ^ (d + 6) :=
          mul_le_mul_of_nonneg_left hexp hpos
      _ = R ^ 2 * (Real.rpow R (2 * sigma) * (L / R) ^ (d + 6)) := by ring
  have hfinal : Real.rpow 3 (2 + 2 * sigma) * Real.rpow L (2 + 2 * sigma) ≤
      81 * R ^ 2 * (Real.rpow R (2 * sigma) * (L / R) ^ (d + 6)) := by
    have hslacknn : 0 ≤ R ^ 2 * (Real.rpow R (2 * sigma) * (L / R) ^ (d + 6)) := by
      have h1 := Real.rpow_nonneg hR.le (2 * sigma)
      have h2 : (0 : ℝ) ≤ (L / R) ^ (d + 6) := by positivity
      positivity
    nlinarith [h81, hLnn, hSlack, hslacknn, h3nn]
  exact (hstep1.trans_eq hsplit).trans hfinal

/-- **Without the scale slack the budget has no solution.**

`fluxRowRieszEnlargedNqRatio m σ = 2 · 3^{2σ(m+1)}` is unbounded in the cell
scale, so no positive `η` can meet the scale-free requirement
`W² · ratio · Kcut · Cm · η ≤ R^{2σ}` at every cell of the family.  This is why
`exists_fluxRowSlots_repairedStoppingCell_enlargedLocalFluxPrice` tests its
energy budget against `R^{2σ}(3^m/R)^{d+6}`. -/
theorem not_forall_enlarged_energy_budget_scaleFree
    {Wfac Kcut Cm eta R sigma : ℝ} (hW : 0 < Wfac) (hKcut : 0 < Kcut)
    (hCm : 0 < Cm) (heta : 0 < eta) (hs0 : 0 < sigma) :
    ¬ ∀ m : ℤ, Wfac ^ 2 *
        (fluxRowRieszEnlargedNqRatio m sigma * Kcut * (Cm * eta)) ≤
      Real.rpow R (2 * sigma) := by
  intro hall
  set c : ℝ := Wfac ^ 2 * (2 * (Kcut * (Cm * eta))) with hc
  have hcpos : 0 < c := by positivity
  have hb : 1 < Real.rpow 3 (2 * sigma) := by
    have : (1 : ℝ) < (3 : ℝ) ^ (2 * sigma) :=
      Real.one_lt_rpow_iff_of_pos (by norm_num) |>.mpr (Or.inl ⟨by norm_num, by linarith⟩)
    exact this
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Real.rpow R (2 * sigma) / c <
      Real.rpow 3 (2 * sigma) ^ k := pow_unbounded_of_one_lt _ hb
  have hkey : Wfac ^ 2 *
      (fluxRowRieszEnlargedNqRatio ((k : ℤ) - 1) sigma * Kcut * (Cm * eta)) =
      c * Real.rpow 3 (2 * sigma) ^ k := by
    have hexp : Real.rpow 3 (sigma * ((((k : ℤ) - 1) + 1 : ℤ) : ℝ)) ^ 2 =
        Real.rpow 3 (2 * sigma) ^ k := by
      show ((3 : ℝ) ^ (sigma * ((((k : ℤ) - 1) + 1 : ℤ) : ℝ))) ^ (2 : ℕ) =
        ((3 : ℝ) ^ (2 * sigma)) ^ k
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (sigma * ((((k : ℤ) - 1) + 1 : ℤ) : ℝ))) 2,
        ← Real.rpow_natCast ((3 : ℝ) ^ (2 * sigma)) k,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
    rw [fluxRowRieszEnlargedNqRatio, hexp, hc]
    ring
  have hbud := hall ((k : ℤ) - 1)
  rw [hkey] at hbud
  have := (div_lt_iff₀ hcpos).mp hk
  nlinarith [hbud, this, hcpos]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
