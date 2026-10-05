module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalBandDepth
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalLogGrowth
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalLengthTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalUniformProvider

@[expose] public section

/-!
# The chemical-distance bound at a **linear** length budget
This file assembles the pieces into the frozen clause (iii) of
the chemical-distance bound at the budget `Clen * L` with `Clen` a constant fixed before `L`
(a scale-independent constant).

The three inputs are

* `Section9ChemicalBandBudget.adaptiveTubeFailureEvent_subset_bandUnion` — the deterministic
  reduction of the linear budget to a bad-component reach cutoff at `3 ^ J` plus the band
  excesses;
* `Section9ChemicalBandTail.measure_bandExcessEvent_le` — the `m`-fold union bound for one
  band;
* `Section9ChemicalBandDepth` — the choice of `J` making every band produce the *same* gain
  `3 ^ J` up to a factor `2`, with `3 ^ J ≍ L ^ (1/(d+2))`.

The residual gain is therefore `c q L ^ (1/(d+2))`, comfortably above the `c q (log L) ^ 2` the
frozen display asks for; the polylogarithmic inflation of the budget that
`Section9ChemicalLengthTail` had to accept is gone.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Ω : Type*}

/-! ## Elementary monotonicity -/

theorem bandExcessEvent_mono (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (v w : Lattice d)
    (j : ℕ) {m m' : ℕ} (h : m' ≤ m) :
    bandExcessEvent E Cbox v w j m ⊆ bandExcessEvent E Cbox v w j m' :=
  fun _ hω => le_trans h hω

/-- The elementary cell count of a band. -/
theorem two_pow_mul_pow_le (d j : ℕ) : 2 ^ d * (3 ^ j + 1) ^ d ≤ 4 ^ d * 3 ^ (j * d) := by
  have h1 : (1 : ℕ) ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
  have h2 : (3 ^ j + 1) ^ d ≤ (2 * 3 ^ j) ^ d := Nat.pow_le_pow_left (by omega) d
  calc 2 ^ d * (3 ^ j + 1) ^ d ≤ 2 ^ d * (2 * 3 ^ j) ^ d := Nat.mul_le_mul_left _ h2
    _ = 4 ^ d * 3 ^ (j * d) := by
        rw [Nat.mul_pow, ← pow_mul, ← mul_assoc, ← Nat.mul_pow]

/-! ## Two real-analytic steps -/

/-- The root entropy of a band is absorbed by its exponential gain. -/
private theorem le_exp_of_log_bound {dd j : ℕ} {C8 t P : ℝ} (hC81 : 1 ≤ C8) (hPpos : 0 < P)
    (hPle : P ≤ C8 * ((3 ^ (j * (2 * dd + 2)) : ℕ) : ℝ))
    (hent : (2 * (dd : ℝ) + 2) * Real.log 3 + Real.log C8 ≤ t) :
    P ≤ Real.exp (t * (3 : ℝ) ^ j) := by
  have hcast : ((3 ^ (j * (2 * dd + 2)) : ℕ) : ℝ) = (3 : ℝ) ^ (j * (2 * dd + 2)) := by
    push_cast
    ring
  rw [hcast] at hPle
  have hlog1 : Real.log P ≤ Real.log (C8 * (3 : ℝ) ^ (j * (2 * dd + 2))) :=
    Real.log_le_log hPpos hPle
  have hsplit : Real.log (C8 * (3 : ℝ) ^ (j * (2 * dd + 2)))
      = Real.log C8 + ((2 * (dd : ℝ) + 2) * Real.log 3) * (j : ℝ) := by
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    push_cast
    ring
  have hlin := linear_le_mul_three_pow (a := (2 * (dd : ℝ) + 2) * Real.log 3)
    (b := Real.log C8) (t := t) (by positivity) (Real.log_nonneg hC81) hent j
  rw [hsplit] at hlog1
  exact (Real.log_le_iff_le_exp hPpos).mp (by linarith)

/-- The `m`-fold gain of a band dominates the cutoff gain. -/
private theorem band_pow_le_exp {dd j m : ℕ} {P beta q Ac C8 gainJ : ℝ}
    (hPpos : 0 < P) (hbeta : 0 < beta) (hq : 0 < q) (hAc : 0 < Ac) (hC81 : 1 ≤ C8)
    (hPle : P ≤ C8 * ((3 ^ (j * (2 * dd + 2)) : ℕ) : ℝ))
    (hent : (2 * (dd : ℝ) + 2) * Real.log 3 + Real.log C8 ≤ beta * q / (2 * Ac))
    (hgain : gainJ ≤ 2 * ((m : ℝ) * ((3 ^ j : ℕ) : ℝ))) :
    (P * Real.exp (-beta * q * (((3 ^ j : ℕ) : ℝ) / Ac))) ^ m ≤
      Real.exp (-(beta / (4 * Ac)) * q * gainJ) := by
  have hcast : ((3 ^ j : ℕ) : ℝ) = (3 : ℝ) ^ j := by push_cast; ring
  rw [hcast] at hgain ⊢
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hPexp : P ≤ Real.exp (beta * q / (2 * Ac) * (3 : ℝ) ^ j) :=
    le_exp_of_log_bound hC81 hPpos hPle hent
  have hstep : P * Real.exp (-beta * q * ((3 : ℝ) ^ j / Ac)) ≤
      Real.exp (-(beta * q / (2 * Ac)) * (3 : ℝ) ^ j) := by
    have hmul := mul_le_mul_of_nonneg_right hPexp
      (le_of_lt (Real.exp_pos (-beta * q * ((3 : ℝ) ^ j / Ac))))
    refine hmul.trans (le_of_eq ?_)
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ P * Real.exp (-beta * q * ((3 : ℝ) ^ j / Ac)) := by positivity
  refine (pow_le_pow_left₀ hnn hstep m).trans ?_
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have hkey : beta / (4 * Ac) * q * gainJ ≤
      (m : ℝ) * (beta * q / (2 * Ac) * (3 : ℝ) ^ j) := by
    have hc : (0 : ℝ) ≤ beta / (4 * Ac) * q := by positivity
    have h1 : beta / (4 * Ac) * q * gainJ ≤
        beta / (4 * Ac) * q * (2 * ((m : ℝ) * (3 : ℝ) ^ j)) :=
      mul_le_mul_of_nonneg_left hgain hc
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
  nlinarith [hkey]

/-! ## The tail of one band, at the cutoff rate -/

/-- **The band tail, at the uniform rate `exp (-c q 3 ^ J)`.**

Every band `j ≤ J` produces the same gain: the multiplicity `bandMult` is inversely
proportional to `3 ^ (j (d+2))` while the per-root gain is `3 ^ j`, and the root entropy
`log (3 (n+1) / m) + j (2d+2) log 3` is linear in the band index, hence absorbed by the
exponential gain at a single threshold on `q`. -/
theorem measure_bandExcessEvent_le_exp [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep : ℕ)
    {Cprob cprob q : ℝ} (hd : 1 ≤ d) (hCbox : 1 ≤ Cbox)
    (_hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hq : 1 ≤ q)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ crossBeta d cprob * q)
    (hth2 : Real.log (8 * ((2 ^ d * (1 + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ crossBeta d cprob * q)
    (hent : (2 * (d : ℝ) + 2) * Real.log 3 +
        Real.log (36 * ((bandBase Cbox Cdep : ℕ) : ℝ) * (4 : ℝ) ^ d *
          (1 + 2 * crossScaleConst d Cbox Cdep Cprob))
      ≤ crossBeta d cprob * q / (2 * crossAc Cbox Cdep 1))
    (L : ℕ) (hL1 : 1 ≤ L) (hLbase : bandBase Cbox Cdep ≤ L)
    (v w : Lattice d) (hvw : latticeDist v w ≤ 2 * L)
    (j : ℕ) (hj : j ≤ bandDepth d Cbox Cdep L) :
    mu (bandExcessEvent E Cbox v w j
        (bandMult d Cbox Cdep L j * (bandSep Cbox Cdep j + 1))) ≤
      ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
        ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hcq : 0 ≤ cprob * q := by positivity
  have hbetapos : 0 < crossBeta d cprob := crossBeta_pos hcprob
  have hAcpos : 0 < crossAc Cbox Cdep 1 := crossAc_pos hCbox
  have hBpos : 0 < crossScaleConst d Cbox Cdep Cprob := crossScaleConst_pos d Cbox Cdep Cprob
  have hbe : crossBeta d cprob = cprob / 2 / 2 ^ d := rfl
  have hKS1 : (1 : ℝ) ≤ 1 + 2 * crossScaleConst d Cbox Cdep Cprob := by linarith
  have hKS0 : (0 : ℝ) ≤ 1 + 2 * crossScaleConst d Cbox Cdep Cprob := by linarith
  have hpi : 8 * crossBranch d 1 * crossBranch d 1 *
      crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤ 2 * crossBranch d 1 :=
    crossScaleSum_small d Cbox Cdep 1
      (by rw [crossBeta] at hth1; exact hth1) (by rw [crossBeta] at hth2; exact hth2)
  have hKS : 1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤
      ENNReal.ofReal (1 + 2 * crossScaleConst d Cbox Cdep Cprob) := by
    have hss : crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤
        ENNReal.ofReal (2 * (crossScaleConst d Cbox Cdep Cprob *
          Real.exp (-(crossBeta d cprob * q)))) := by
      have h := crossScaleSum_le d Cbox Cdep (Cprob := Cprob) (cprob := cprob / 2)
        (q := q) (by rw [crossBeta] at hth1; exact hth1)
      rw [crossBeta]
      exact h
    refine le_trans (add_le_add le_rfl hss) ?_
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp1 : Real.exp (-(crossBeta d cprob * q)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 < crossBeta d cprob * q := mul_pos hbetapos hqpos
      linarith
    nlinarith [hBpos]
  have hm1 : 1 ≤ bandMult d Cbox Cdep L j := one_le_bandMult hLbase hj
  have hmR : (1 : ℝ) ≤ ((bandMult d Cbox Cdep L j : ℕ) : ℝ) := by exact_mod_cast hm1
  have hbase := measure_bandExcessEvent_le mu E Cbox Cdep hd hCbox hcq hsc hr hprob hpi
    hKS0 hKS v w j (bandMult d Cbox Cdep L j) hm1
  refine hbase.trans (ENNReal.ofReal_le_ofReal ?_)
  have hrate : crossRate d Cbox Cdep 1 cprob =
      (cprob / 2 / 2 ^ d) / (4 * crossAc Cbox Cdep 1) := by
    rw [crossRate, hbe]
  rw [hrate]
  -- the entropy of the roots
  have hC81 : (1 : ℝ) ≤ 36 * ((bandBase Cbox Cdep : ℕ) : ℝ) * (4 : ℝ) ^ d *
      (1 + 2 * crossScaleConst d Cbox Cdep Cprob) := by
    have h1 : (1 : ℝ) ≤ ((bandBase Cbox Cdep : ℕ) : ℝ) := by
      exact_mod_cast one_le_bandBase Cbox Cdep
    have h2 : (1 : ℝ) ≤ (4 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ 36 * ((bandBase Cbox Cdep : ℕ) : ℝ) := by linarith
    have h4 : (1 : ℝ) ≤ 36 * ((bandBase Cbox Cdep : ℕ) : ℝ) * (4 : ℝ) ^ d := by nlinarith
    nlinarith
  have hPpos : (0 : ℝ) < 3 * ((latticeDist v w + 1 : ℕ) : ℝ) /
      ((bandMult d Cbox Cdep L j : ℕ) : ℝ) *
      ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2 *
        (1 + 2 * crossScaleConst d Cbox Cdep Cprob)) := by
    have h1 : (0 : ℝ) < 3 * ((latticeDist v w + 1 : ℕ) : ℝ) /
        ((bandMult d Cbox Cdep L j : ℕ) : ℝ) := by
      have hn0 : (0 : ℝ) < ((latticeDist v w + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos _
      have : (0 : ℝ) < ((bandMult d Cbox Cdep L j : ℕ) : ℝ) := by linarith
      positivity
    have h2 : (1 : ℝ) ≤ (((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h3 : (0 : ℝ) < (((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2 *
        (1 + 2 * crossScaleConst d Cbox Cdep Cprob) := by nlinarith
    exact mul_pos h1 h3
  have hPle : 3 * ((latticeDist v w + 1 : ℕ) : ℝ) /
      ((bandMult d Cbox Cdep L j : ℕ) : ℝ) *
      ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2 *
        (1 + 2 * crossScaleConst d Cbox Cdep Cprob)) ≤
      (36 * ((bandBase Cbox Cdep : ℕ) : ℝ) * (4 : ℝ) ^ d *
        (1 + 2 * crossScaleConst d Cbox Cdep Cprob)) *
        ((3 ^ (j * (2 * d + 2)) : ℕ) : ℝ) := by
    have hfrac : 3 * ((latticeDist v w + 1 : ℕ) : ℝ) /
        ((bandMult d Cbox Cdep L j : ℕ) : ℝ) ≤
        18 * ((bandBase Cbox Cdep : ℕ) : ℝ) * ((3 ^ (j * (d + 2)) : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      have hnat : 9 * L < 18 * bandBase Cbox Cdep * 3 ^ (j * (d + 2)) *
          bandMult d Cbox Cdep L j := by
        have h := lt_two_mul_bandMult (d := d) hLbase hj
        calc 9 * L < 9 * (2 * bandMult d Cbox Cdep L j *
              (bandBase Cbox Cdep * 3 ^ (j * (d + 2)))) := by omega
          _ = 18 * bandBase Cbox Cdep * 3 ^ (j * (d + 2)) *
              bandMult d Cbox Cdep L j := by ring
      have hn3 : 3 * (latticeDist v w + 1) ≤ 9 * L := by omega
      have hcast : (3 : ℝ) * ((latticeDist v w + 1 : ℕ) : ℝ) ≤ ((9 * L : ℕ) : ℝ) := by
        have h2 := (Nat.cast_le (α := ℝ)).mpr hn3
        push_cast at h2 ⊢
        linarith
      have hcast2 : ((9 * L : ℕ) : ℝ) ≤ ((18 * bandBase Cbox Cdep * 3 ^ (j * (d + 2)) *
          bandMult d Cbox Cdep L j : ℕ) : ℝ) := by exact_mod_cast hnat.le
      have hfin : ((18 * bandBase Cbox Cdep * 3 ^ (j * (d + 2)) *
          bandMult d Cbox Cdep L j : ℕ) : ℝ) =
          18 * ((bandBase Cbox Cdep : ℕ) : ℝ) * ((3 ^ (j * (d + 2)) : ℕ) : ℝ) *
            ((bandMult d Cbox Cdep L j : ℕ) : ℝ) := by push_cast; ring
      rw [← hfin]
      linarith
    have hcell : (((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2 *
        (1 + 2 * crossScaleConst d Cbox Cdep Cprob) ≤
        (4 : ℝ) ^ d * ((3 ^ (j * d) : ℕ) : ℝ) * 2 *
          (1 + 2 * crossScaleConst d Cbox Cdep Cprob) := by
      have hnat : ((2 ^ d * (3 ^ j + 1) ^ d : ℕ) : ℝ) ≤
          ((4 ^ d * 3 ^ (j * d) : ℕ) : ℝ) := by exact_mod_cast two_pow_mul_pow_le d j
      have hcast : ((4 ^ d * 3 ^ (j * d) : ℕ) : ℝ) =
          (4 : ℝ) ^ d * ((3 ^ (j * d) : ℕ) : ℝ) := by push_cast; ring
      rw [hcast] at hnat
      nlinarith [hnat, hKS0]
    have hnn2 : (0 : ℝ) ≤ (((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2 *
        (1 + 2 * crossScaleConst d Cbox Cdep Cprob) := by positivity
    have hnn3 : (0 : ℝ) ≤ 18 * ((bandBase Cbox Cdep : ℕ) : ℝ) *
        ((3 ^ (j * (d + 2)) : ℕ) : ℝ) := by positivity
    have hprod := mul_le_mul hfrac hcell hnn2 hnn3
    refine hprod.trans (le_of_eq ?_)
    have hexp : ((3 ^ (j * (d + 2)) : ℕ) : ℝ) * ((3 ^ (j * d) : ℕ) : ℝ) =
        ((3 ^ (j * (2 * d + 2)) : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, ← pow_add]
      congr 2
      ring
    calc (18 * ((bandBase Cbox Cdep : ℕ) : ℝ) * ((3 ^ (j * (d + 2)) : ℕ) : ℝ)) *
          ((4 : ℝ) ^ d * ((3 ^ (j * d) : ℕ) : ℝ) * 2 *
            (1 + 2 * crossScaleConst d Cbox Cdep Cprob))
        = (36 * ((bandBase Cbox Cdep : ℕ) : ℝ) * (4 : ℝ) ^ d *
            (1 + 2 * crossScaleConst d Cbox Cdep Cprob)) *
            (((3 ^ (j * (d + 2)) : ℕ) : ℝ) * ((3 ^ (j * d) : ℕ) : ℝ)) := by ring
      _ = (36 * ((bandBase Cbox Cdep : ℕ) : ℝ) * (4 : ℝ) ^ d *
            (1 + 2 * crossScaleConst d Cbox Cdep Cprob)) *
            ((3 ^ (j * (2 * d + 2)) : ℕ) : ℝ) := by rw [hexp]
  have hgain : ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ) ≤
      2 * (((bandMult d Cbox Cdep L j : ℕ) : ℝ) * ((3 ^ j : ℕ) : ℝ)) := by
    have h := three_pow_bandDepth_lt (d := d) hLbase hj
    have hcast : ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ) ≤
        ((2 * bandMult d Cbox Cdep L j * 3 ^ j : ℕ) : ℝ) := by exact_mod_cast h.le
    push_cast at hcast ⊢
    linarith
  exact band_pow_le_exp (dd := d) hPpos (by rw [← hbe]; exact hbetapos) hqpos hAcpos hC81
    hPle (by rw [← hbe] at *; exact hent) hgain

/-! ## The linear budget constant -/

/-- The length budget of the band route: `5 ^ d (2L+1) + 9 ^ d · 3L / 2` rounded up to a
multiple of `L`.  It is a constant fixed before `L`, which is exactly what the frozen clause
demands. -/
def linearBudgetConst (dim : ℕ) : ℝ := ((3 * 5 ^ dim + 2 * 9 ^ dim : ℕ) : ℝ)

theorem linearBudgetConst_nonneg (dim : ℕ) : 0 ≤ linearBudgetConst dim :=
  Nat.cast_nonneg _

theorem two_mul_pow_add_le (dim L : ℕ) (hL : 1 ≤ L) :
    2 * (5 ^ dim * (2 * L + 1)) + 9 ^ dim * (3 * L) ≤
      2 * ((3 * 5 ^ dim + 2 * 9 ^ dim) * L) := by
  have h5 : 5 ^ dim ≤ 5 ^ dim * L := by
    have := Nat.mul_le_mul_left (5 ^ dim) hL
    omega
  calc 2 * (5 ^ dim * (2 * L + 1)) + 9 ^ dim * (3 * L)
      = 4 * (5 ^ dim * L) + 2 * 5 ^ dim + 3 * (9 ^ dim * L) := by ring
    _ ≤ 4 * (5 ^ dim * L) + 2 * (5 ^ dim * L) + 3 * (9 ^ dim * L) := by omega
    _ ≤ 6 * (5 ^ dim * L) + 4 * (9 ^ dim * L) := by omega
    _ = 2 * ((3 * 5 ^ dim + 2 * 9 ^ dim) * L) := by ring

/-! ## The adaptive-tube residual at the linear budget -/

/-- **The whole length residual, at the linear budget and the cutoff rate.**

The cutoff over `B_L(z)` and the band excesses over the pairs of endpoints and the bands
`j < J` are all bounded by `exp (-c q 3 ^ J)`; only the entropy factor differs. -/
theorem measure_adaptiveTubeFailureEvent_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep : ℕ)
    {Cprob cprob q : ℝ} (hd : 1 ≤ d) (hCbox : 1 ≤ Cbox)
    (hCprob : 0 < Cprob) (hcprob : 0 < cprob) (hq : 1 ≤ q)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ crossBeta d cprob * q)
    (hth2 : Real.log (8 * ((2 ^ d * (1 + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ crossBeta d cprob * q)
    (hth3 : crossEntropy d Cbox Cdep 1 Cprob ≤
      crossBeta d cprob * q / (4 * crossAc Cbox Cdep 1))
    (hent : (2 * (d : ℝ) + 2) * Real.log 3 +
        Real.log (36 * ((bandBase Cbox Cdep : ℕ) : ℝ) * (4 : ℝ) ^ d *
          (1 + 2 * crossScaleConst d Cbox Cdep Cprob))
      ≤ crossBeta d cprob * q / (2 * crossAc Cbox Cdep 1))
    (z : Lattice d) (L : ℕ) (hL1 : 1 ≤ L) (hLbase : bandBase Cbox Cdep ≤ L)
    (h24 : 24 ≤ 3 ^ bandDepth d Cbox Cdep L) :
    mu (adaptiveTubeFailureEvent E Cbox z L (linearBudgetConst d * L)) ≤
      ENNReal.ofReal ((((2 * L + 1) ^ d + (2 * L + 1) ^ (2 * d) *
          bandDepth d Cbox Cdep L : ℕ) : ℝ) *
        Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
          ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
  classical
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hgainpos : (0 : ℝ) < Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
      ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ)) := Real.exp_pos _
  -- the deterministic reduction
  have hbud : ((2 * (5 ^ d * (2 * L + 1)) + 9 ^ d * (3 * L) : ℕ) : ℝ) ≤
      2 * (linearBudgetConst d * L) := by
    have h := two_mul_pow_add_le d L hL1
    have hcast := (Nat.cast_le (α := ℝ)).mpr h
    rw [linearBudgetConst]
    push_cast at hcast ⊢
    linarith
  have hsub := adaptiveTubeFailureEvent_subset_bandUnion E Cbox z L
    (bandDepth d Cbox Cdep L) L hbud
  -- the cutoff
  have hcut : mu (⋃ x ∈ latticeBallFinset z L,
        badDiameterEvent E Cbox x (3 ^ bandDepth d Cbox Cdep L)) ≤
      ENNReal.ofReal ((((2 * L + 1) ^ d : ℕ) : ℝ) *
        Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
          ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
    calc mu (⋃ x ∈ latticeBallFinset z L,
          badDiameterEvent E Cbox x (3 ^ bandDepth d Cbox Cdep L))
        ≤ ∑ x ∈ latticeBallFinset z L,
            mu (badDiameterEvent E Cbox x (3 ^ bandDepth d Cbox Cdep L)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _x ∈ latticeBallFinset z L,
            ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
              ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) :=
          Finset.sum_le_sum fun x _ =>
            measure_badDiameterEvent_le_exp mu E Cbox Cdep hcprob hqpos.le hCbox hsc hr
              hprob hth1 hth2 hth3 x _ h24
      _ = (((2 * L + 1) ^ d : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
              ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
          rw [Finset.sum_const, card_latticeBallFinset, nsmul_eq_mul]
      _ = ENNReal.ofReal ((((2 * L + 1) ^ d : ℕ) : ℝ) *
            Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
              ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  -- the bands
  have hband : mu (⋃ v ∈ latticeBallFinset z L, ⋃ w ∈ latticeBallFinset z L,
        ⋃ j ∈ Finset.range (bandDepth d Cbox Cdep L),
          bandExcessEvent E Cbox v w j (L / 3 ^ (j * (d + 1)) + 1)) ≤
      ENNReal.ofReal ((((2 * L + 1) ^ (2 * d) * bandDepth d Cbox Cdep L : ℕ) : ℝ) *
        Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
          ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
    have hterm : ∀ v ∈ latticeBallFinset z L, ∀ w ∈ latticeBallFinset z L,
        ∀ j ∈ Finset.range (bandDepth d Cbox Cdep L),
        mu (bandExcessEvent E Cbox v w j (L / 3 ^ (j * (d + 1)) + 1)) ≤
          ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
            ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
      intro v hv w hw j hj
      have hvw : latticeDist v w ≤ 2 * L := by
        have h1 : latticeDist z v ≤ L := mem_latticeBallFinset_iff.mp hv
        have h2 : latticeDist z w ≤ L := mem_latticeBallFinset_iff.mp hw
        have htri := latticeDist_triangle v z w
        rw [latticeDist_comm v z] at htri
        omega
      have hjle : j ≤ bandDepth d Cbox Cdep L := le_of_lt (Finset.mem_range.mp hj)
      refine le_trans (measure_mono (bandExcessEvent_mono E Cbox v w j
        (m := L / 3 ^ (j * (d + 1)) + 1)
        (m' := bandMult d Cbox Cdep L j * (bandSep Cbox Cdep j + 1))
        (le_trans (bandMult_mul_le d Cbox Cdep L j) (Nat.le_succ _)))) ?_
      exact measure_bandExcessEvent_le_exp mu E Cbox Cdep hd hCbox hCprob hcprob hq hsc
        hr hprob hth1 hth2 hent L hL1 hLbase v w hvw j hjle
    calc mu (⋃ v ∈ latticeBallFinset z L, ⋃ w ∈ latticeBallFinset z L,
          ⋃ j ∈ Finset.range (bandDepth d Cbox Cdep L),
            bandExcessEvent E Cbox v w j (L / 3 ^ (j * (d + 1)) + 1))
        ≤ ∑ v ∈ latticeBallFinset z L, mu (⋃ w ∈ latticeBallFinset z L,
            ⋃ j ∈ Finset.range (bandDepth d Cbox Cdep L),
              bandExcessEvent E Cbox v w j (L / 3 ^ (j * (d + 1)) + 1)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _v ∈ latticeBallFinset z L,
            ((((2 * L + 1) ^ d * bandDepth d Cbox Cdep L : ℕ)) : ℝ≥0∞) *
              ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
                ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
          refine Finset.sum_le_sum fun v hv => ?_
          calc mu (⋃ w ∈ latticeBallFinset z L,
                ⋃ j ∈ Finset.range (bandDepth d Cbox Cdep L),
                  bandExcessEvent E Cbox v w j (L / 3 ^ (j * (d + 1)) + 1))
              ≤ ∑ w ∈ latticeBallFinset z L, mu (⋃ j ∈ Finset.range (bandDepth d Cbox Cdep L),
                  bandExcessEvent E Cbox v w j (L / 3 ^ (j * (d + 1)) + 1)) :=
                measure_biUnion_finset_le _ _
            _ ≤ ∑ _w ∈ latticeBallFinset z L,
                  (((bandDepth d Cbox Cdep L : ℕ)) : ℝ≥0∞) *
                    ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
                      ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
                refine Finset.sum_le_sum fun w hw => ?_
                calc mu (⋃ j ∈ Finset.range (bandDepth d Cbox Cdep L),
                      bandExcessEvent E Cbox v w j (L / 3 ^ (j * (d + 1)) + 1))
                    ≤ ∑ j ∈ Finset.range (bandDepth d Cbox Cdep L),
                        mu (bandExcessEvent E Cbox v w j (L / 3 ^ (j * (d + 1)) + 1)) :=
                      measure_biUnion_finset_le _ _
                  _ ≤ ∑ _j ∈ Finset.range (bandDepth d Cbox Cdep L),
                        ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
                          ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) :=
                      Finset.sum_le_sum fun j hj => hterm v hv w hw j hj
                  _ = (((bandDepth d Cbox Cdep L : ℕ)) : ℝ≥0∞) *
                        ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
                          ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
                      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ = ((((2 * L + 1) ^ d * bandDepth d Cbox Cdep L : ℕ)) : ℝ≥0∞) *
                  ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
                    ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
                rw [Finset.sum_const, card_latticeBallFinset, nsmul_eq_mul]
                push_cast
                ring
      _ = ((((2 * L + 1) ^ d * ((2 * L + 1) ^ d * bandDepth d Cbox Cdep L) : ℕ)) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
              ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
          rw [Finset.sum_const, card_latticeBallFinset, nsmul_eq_mul]
          push_cast
          ring
      _ = ENNReal.ofReal ((((2 * L + 1) ^ (2 * d) * bandDepth d Cbox Cdep L : ℕ) : ℝ) *
            Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
              ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 2
          have hdd : 2 * d = d + d := two_mul d
          have hpow : (2 * L + 1) ^ (2 * d) = (2 * L + 1) ^ d * (2 * L + 1) ^ d := by
            rw [hdd, pow_add]
          rw [hpow]
          push_cast
          ring
  calc mu (adaptiveTubeFailureEvent E Cbox z L (linearBudgetConst d * L))
      ≤ mu ((⋃ x ∈ latticeBallFinset z L,
            badDiameterEvent E Cbox x (3 ^ bandDepth d Cbox Cdep L)) ∪
          ⋃ v ∈ latticeBallFinset z L, ⋃ w ∈ latticeBallFinset z L,
            ⋃ j ∈ Finset.range (bandDepth d Cbox Cdep L),
              bandExcessEvent E Cbox v w j (L / 3 ^ (j * (d + 1)) + 1)) :=
        measure_mono hsub
    _ ≤ mu (⋃ x ∈ latticeBallFinset z L,
            badDiameterEvent E Cbox x (3 ^ bandDepth d Cbox Cdep L)) +
          mu (⋃ v ∈ latticeBallFinset z L, ⋃ w ∈ latticeBallFinset z L,
            ⋃ j ∈ Finset.range (bandDepth d Cbox Cdep L),
              bandExcessEvent E Cbox v w j (L / 3 ^ (j * (d + 1)) + 1)) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((((2 * L + 1) ^ d : ℕ) : ℝ) *
            Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
              ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) +
          ENNReal.ofReal ((((2 * L + 1) ^ (2 * d) * bandDepth d Cbox Cdep L : ℕ) : ℝ) *
            Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
              ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := add_le_add hcut hband
    _ = ENNReal.ofReal ((((2 * L + 1) ^ d + (2 * L + 1) ^ (2 * d) *
            bandDepth d Cbox Cdep L : ℕ) : ℝ) *
          Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
            ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        ring

/-- A quadratic dominates a linear function above the obvious threshold. -/
private theorem entropy_le_rate_sq {rate A B X : ℝ} (hA0 : 0 ≤ A) (_hB0 : 0 ≤ B)
    (hX1 : 1 ≤ X) (hdiv : A + B + 1 ≤ X * rate) : A + B * X ≤ rate * X ^ 2 := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hmul : (A + B + 1) * X ≤ X * rate * X := mul_le_mul_of_nonneg_right hdiv hX0
  nlinarith [hmul, mul_nonneg hA0 (sub_nonneg.mpr hX1), hX0]

/-- The connectivity half is at a rate above `c q (log L) ^ 2`. -/
private theorem conn_exponent_le {crate c q Y S : ℝ} (hc0 : 0 ≤ c) (hq : 0 ≤ q)
    (hc : c ≤ crate / 64) (_hY0 : 0 ≤ Y) (hS0 : 0 ≤ S) (hY : Y ≤ 64 * S) :
    c * q * Y ≤ crate * q * S := by
  have h1 : c * Y ≤ crate * S := by nlinarith
  nlinarith [h1, hq]

/-- Half the cutoff gain absorbs the entropy of the union bound. -/
private theorem gain_exponent_le {rate c q Y G : ℝ} (hrate0 : 0 ≤ rate) (hq1 : 1 ≤ q)
    (hc : c ≤ rate) (_hc0 : 0 ≤ c) (hY0 : 0 ≤ Y) (hG : 2 * Y ≤ G) :
    rate * Y + -rate * q * G ≤ -(c * q * Y) := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have h1 : rate * Y ≤ rate * q * Y := by
    nlinarith [mul_nonneg (mul_nonneg hrate0 hY0) (sub_nonneg.mpr hq1)]
  have h2 : c * q * Y ≤ rate * q * Y := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) hq0) hY0]
  have hrq : (0 : ℝ) ≤ rate * q := mul_nonneg hrate0 hq0
  have h3 : rate * q * (2 * Y) ≤ rate * q * G := mul_le_mul_of_nonneg_left hG hrq
  linarith [h1, h2, h3]

/-! ## The chemical-distance tail at the linear budget -/

/-- **The frozen display, at the linear budget, above a threshold scale.**

For every dimension `d ≥ 2` and box constant `Cbox ≥ 1` there are `q0`, `L0` and a rate `c > 0`
such that every field satisfying the multiscale-percolation hypotheses at `q ≥ q0` obeys

```text
    mu (chemicalDistanceFailureEventAt E Cbox (linearBudgetConst d * L) z L)
      ≤ 2 exp (-(c q (log L) ^ 2))
```

at every centre and every scale `L ≥ L0`.  The budget `linearBudgetConst d * L` is **linear**
in `L`, which is the frozen shape; the residual gain is in fact `c q L ^ (1/(d+2))`, and the
`(log L) ^ 2` of the display is all that is being asked of it. -/
theorem exists_chemicalDistance_linear_tail (d Cbox Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 L0 : ℕ, ∃ c : ℝ, 1 ≤ L0 ∧ 0 < c ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∀ (z : Lattice d) (L : ℕ), L0 ≤ L →
          mu (chemicalDistanceFailureEventAt E Cbox (linearBudgetConst d * L) z L) ≤
            ENNReal.ofReal (2 * Real.exp (-(c * q * Real.log (L : ℝ) ^ 2))) := by
  classical
  obtain ⟨q0c, L0c, crate, hL0c1, hcrate, hconn⟩ :=
    exists_connectivity_tail d Cbox Cdep Cprob cprob hd hCbox hCprob hcprob
  have hbetapos : 0 < crossBeta d cprob := crossBeta_pos hcprob
  have hAcpos : 0 < crossAc Cbox Cdep 1 := crossAc_pos hCbox
  have hratepos : 0 < crossRate d Cbox Cdep 1 cprob := crossRate_pos hcprob hCbox
  set V1 : ℝ := (3 * (d : ℝ) * Real.log 3 + 1) / crossBeta d cprob with hV1
  set V2 : ℝ := Real.log (8 * ((2 ^ d * (1 + 1) ^ d : ℕ) : ℝ) *
    crossScaleConst d Cbox Cdep Cprob) / crossBeta d cprob with hV2
  set V3 : ℝ := 4 * crossAc Cbox Cdep 1 * crossEntropy d Cbox Cdep 1 Cprob /
    crossBeta d cprob with hV3
  set V5 : ℝ := 2 * crossAc Cbox Cdep 1 * ((2 * (d : ℝ) + 2) * Real.log 3 +
    Real.log (36 * ((bandBase Cbox Cdep : ℕ) : ℝ) * (4 : ℝ) ^ d *
      (1 + 2 * crossScaleConst d Cbox Cdep Cprob))) / crossBeta d cprob with hV5
  set Q : ℝ := max (max V1 V2) (max (max V3 V5) 1) with hQ
  obtain ⟨Lg, hLg1, hLg⟩ := exists_log_pow_threshold
    (((bandBase Cbox Cdep * 3 ^ (d + 2) * 2 ^ (d + 2) : ℕ) : ℝ)) (2 * (d + 2))
  set X0 : ℝ := max 1 ((Real.log 2 + (2 * (d : ℝ) + 1) * Real.log 3 +
    (2 * (d : ℝ) + 1) + 1) / crossRate d Cbox Cdep 1 cprob) with hX0
  refine ⟨max 1 (max q0c ⌈Q⌉₊),
    max (max 1 L0c) (max (bandBase Cbox Cdep * 3 ^ (d + 2) * 24 ^ (d + 2))
      (max Lg (⌈Real.exp X0⌉₊ + 1))),
    min (crate / 64) (crossRate d Cbox Cdep 1 cprob), ?_, ?_, ?_⟩
  · exact le_trans (Nat.le_max_left 1 L0c) (Nat.le_max_left _ _)
  · exact lt_min (by positivity) hratepos
  intro Omega _ mu _ E q hq hprob hsc hr hlaw z L hLL0
  -- the `q` thresholds
  have hq1 : (1 : ℝ) ≤ q := le_trans (by exact_mod_cast Nat.le_max_left 1 _) hq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hq0c : (q0c : ℝ) ≤ q :=
    le_trans (by exact_mod_cast (Nat.le_max_left q0c ⌈Q⌉₊).trans (Nat.le_max_right 1 _)) hq
  have hQq : Q ≤ q := le_trans (Nat.le_ceil Q)
    (le_trans (by exact_mod_cast (Nat.le_max_right q0c ⌈Q⌉₊).trans (Nat.le_max_right 1 _)) hq)
  have hth1 : 3 * (d : ℝ) * Real.log 3 + 1 ≤ crossBeta d cprob * q := by
    have h : V1 ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQq
    rw [hV1, div_le_iff₀ hbetapos] at h
    linarith
  have hth2 : Real.log (8 * ((2 ^ d * (1 + 1) ^ d : ℕ) : ℝ) *
      crossScaleConst d Cbox Cdep Cprob) ≤ crossBeta d cprob * q := by
    have h : V2 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQq
    rw [hV2, div_le_iff₀ hbetapos] at h
    linarith
  have hth3 : crossEntropy d Cbox Cdep 1 Cprob ≤
      crossBeta d cprob * q / (4 * crossAc Cbox Cdep 1) := by
    have h : V3 ≤ q :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hQq)
    rw [hV3, div_le_iff₀ hbetapos] at h
    rw [le_div_iff₀ (by linarith)]
    nlinarith [h]
  have hent : (2 * (d : ℝ) + 2) * Real.log 3 +
      Real.log (36 * ((bandBase Cbox Cdep : ℕ) : ℝ) * (4 : ℝ) ^ d *
        (1 + 2 * crossScaleConst d Cbox Cdep Cprob))
      ≤ crossBeta d cprob * q / (2 * crossAc Cbox Cdep 1) := by
    have h : V5 ≤ q :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hQq)
    rw [hV5, div_le_iff₀ hbetapos] at h
    rw [le_div_iff₀ (by linarith)]
    nlinarith [h]
  -- the `L` thresholds
  have hL1 : 1 ≤ L := le_trans ((Nat.le_max_left 1 L0c).trans (Nat.le_max_left _ _)) hLL0
  have hL0c : L0c ≤ L := le_trans ((Nat.le_max_right 1 L0c).trans (Nat.le_max_left _ _)) hLL0
  have hLbig : bandBase Cbox Cdep * 3 ^ (d + 2) * 24 ^ (d + 2) ≤ L :=
    le_trans ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)) hLL0
  have hLgL : Lg ≤ L :=
    le_trans (((Nat.le_max_left Lg _).trans (Nat.le_max_right _ _)).trans
      (Nat.le_max_right _ _)) hLL0
  have hLexp : ⌈Real.exp X0⌉₊ + 1 ≤ L :=
    le_trans (((Nat.le_max_right Lg _).trans (Nat.le_max_right _ _)).trans
      (Nat.le_max_right _ _)) hLL0
  have hLbase : bandBase Cbox Cdep ≤ L := by
    have h1 : (1 : ℕ) ≤ 3 ^ (d + 2) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (1 : ℕ) ≤ 24 ^ (d + 2) := Nat.one_le_pow _ _ (by norm_num)
    have h3 : bandBase Cbox Cdep * 1 * 1 ≤ bandBase Cbox Cdep * 3 ^ (d + 2) * 24 ^ (d + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
    omega
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hLRpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hlognn : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hLR
  -- the cutoff is above `24`
  have h24 : 24 ≤ 3 ^ bandDepth d Cbox Cdep L := by
    by_contra hcon
    push Not at hcon
    have hpow : (3 ^ bandDepth d Cbox Cdep L) ^ (d + 2) ≤ 24 ^ (d + 2) :=
      Nat.pow_le_pow_left (by omega) _
    have hlt := lt_bandBase_mul_pow d Cbox Cdep L
    have h2 : bandBase Cbox Cdep * 3 ^ (d + 2) * (3 ^ bandDepth d Cbox Cdep L) ^ (d + 2) ≤
        bandBase Cbox Cdep * 3 ^ (d + 2) * 24 ^ (d + 2) := Nat.mul_le_mul_left _ hpow
    omega
  -- the cutoff dominates `2 (log L) ^ 2`
  have hgainlog : 2 * Real.log (L : ℝ) ^ 2 ≤
      ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hnn : (0 : ℝ) ≤ ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpow : ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ) ^ (d + 2) ≤
        (2 * Real.log (L : ℝ) ^ 2) ^ (d + 2) :=
      pow_le_pow_left₀ hnn hcon.le _
    have hlt := lt_bandBase_mul_pow d Cbox Cdep L
    have hcast : (L : ℝ) < ((bandBase Cbox Cdep * 3 ^ (d + 2) : ℕ) : ℝ) *
        ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ) ^ (d + 2) := by
      have h := (Nat.cast_lt (α := ℝ)).mpr hlt
      push_cast at h ⊢
      linarith
    have hexpand : (2 * Real.log (L : ℝ) ^ 2) ^ (d + 2) =
        (2 : ℝ) ^ (d + 2) * Real.log (L : ℝ) ^ (2 * (d + 2)) := by
      rw [mul_pow, ← pow_mul]
    have hgrow := hLg L hLgL
    have hbnn : (0 : ℝ) ≤ ((bandBase Cbox Cdep * 3 ^ (d + 2) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hkey : ((bandBase Cbox Cdep * 3 ^ (d + 2) : ℕ) : ℝ) *
        ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ) ^ (d + 2) ≤
        ((bandBase Cbox Cdep * 3 ^ (d + 2) * 2 ^ (d + 2) : ℕ) : ℝ) *
          Real.log (L : ℝ) ^ (2 * (d + 2)) := by
      have h1 : ((bandBase Cbox Cdep * 3 ^ (d + 2) : ℕ) : ℝ) *
          ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ) ^ (d + 2) ≤
          ((bandBase Cbox Cdep * 3 ^ (d + 2) : ℕ) : ℝ) *
            ((2 : ℝ) ^ (d + 2) * Real.log (L : ℝ) ^ (2 * (d + 2))) := by
        rw [← hexpand]
        exact mul_le_mul_of_nonneg_left hpow hbnn
      refine h1.trans (le_of_eq ?_)
      push_cast
      ring
    linarith
  -- the entropy of the union bound
  have hX0L : X0 ≤ Real.log (L : ℝ) := by
    have hexpL : Real.exp X0 ≤ (L : ℝ) := by
      have h1 : Real.exp X0 ≤ (⌈Real.exp X0⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈Real.exp X0⌉₊ : ℕ) : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast le_trans (Nat.le_succ _) hLexp
      linarith
    exact (Real.le_log_iff_exp_le hLRpos).mpr hexpL
  have hX01 : (1 : ℝ) ≤ Real.log (L : ℝ) := le_trans (le_max_left _ _) hX0L
  have hcountlog : Real.log 2 + (2 * (d : ℝ) + 1) * (Real.log 3 + Real.log (L : ℝ)) ≤
      crossRate d Cbox Cdep 1 cprob * Real.log (L : ℝ) ^ 2 := by
    have hdiv : (Real.log 2 + (2 * (d : ℝ) + 1) * Real.log 3 + (2 * (d : ℝ) + 1) + 1) /
        crossRate d Cbox Cdep 1 cprob ≤ Real.log (L : ℝ) :=
      le_trans (le_max_right _ _) hX0L
    rw [div_le_iff₀ hratepos] at hdiv
    have hA0 : (0 : ℝ) ≤ Real.log 2 + (2 * (d : ℝ) + 1) * Real.log 3 := by
      have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have h3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      positivity
    have hB0 : (0 : ℝ) ≤ 2 * (d : ℝ) + 1 := by positivity
    have hmain := entropy_le_rate_sq (rate := crossRate d Cbox Cdep 1 cprob)
      (A := Real.log 2 + (2 * (d : ℝ) + 1) * Real.log 3) (B := 2 * (d : ℝ) + 1)
      (X := Real.log (L : ℝ)) hA0 hB0 hX01 hdiv
    linarith [hmain]
  clear_value V1 V2 V3 V5 Q X0
  clear hV1 hV2 hV3 hV5 hQ hX0
  -- the two halves
  set c : ℝ := min (crate / 64) (crossRate d Cbox Cdep 1 cprob) with hc
  have hc1 : c ≤ crate / 64 := min_le_left _ _
  have hc2 : c ≤ crossRate d Cbox Cdep 1 cprob := min_le_right _ _
  have hcpos : 0 < c := lt_min (by positivity) hratepos
  clear_value c
  set X : ℝ := Real.exp (-(c * q * Real.log (L : ℝ) ^ 2)) with hX
  have hXnn : (0 : ℝ) ≤ X := (Real.exp_pos _).le
  clear_value X
  have hA : mu {omega | ¬ GoodConnectedInDoubleBallAt E Cbox omega z L ((L : ℝ) / 20)} ≤
      ENNReal.ofReal X := by
    refine le_trans (hconn mu E q hq0c hprob hsc hr hlaw z L hL0c ((L : ℝ) / 20) le_rfl) ?_
    rw [hX]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hsq := log_sq_le_sqrt hL1
    have h := conn_exponent_le (crate := crate) (c := c) (q := q)
      (Y := Real.log (L : ℝ) ^ 2) (S := Real.sqrt (L : ℝ)) hcpos.le hqpos.le hc1
      (by positivity) (Real.sqrt_nonneg _) hsq
    linarith
  have hB : mu (adaptiveTubeFailureEvent E Cbox z L (linearBudgetConst d * L)) ≤
      ENNReal.ofReal X := by
    refine le_trans (measure_adaptiveTubeFailureEvent_le mu E Cbox Cdep (by omega) hCbox
      hCprob hcprob hq1 hsc hr hprob hth1 hth2 hth3 hent z L hL1 hLbase h24) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    -- the entropy factor is dominated by half the gain
    have hcount : ((2 * L + 1) ^ d + (2 * L + 1) ^ (2 * d) * bandDepth d Cbox Cdep L : ℕ) ≤
        2 * (3 * L) ^ (2 * d + 1) := by
      have hJL : bandDepth d Cbox Cdep L ≤ L := by
        have h1 : Nat.log 3 (L / bandBase Cbox Cdep) / (d + 2) ≤
            Nat.log 3 (L / bandBase Cbox Cdep) := Nat.div_le_self _ _
        have h2 : Nat.log 3 (L / bandBase Cbox Cdep) ≤ L / bandBase Cbox Cdep :=
          Nat.log_le_self _ _
        have h3 : L / bandBase Cbox Cdep ≤ L := Nat.div_le_self _ _
        rw [bandDepth]
        omega
      have hb1 : (2 * L + 1) ^ d ≤ (3 * L) ^ (2 * d) := by
        have h1 : (2 * L + 1) ^ d ≤ (3 * L) ^ d := Nat.pow_le_pow_left (by omega) d
        have h2 : (3 * L) ^ d ≤ (3 * L) ^ (2 * d) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have hb2 : (2 * L + 1) ^ (2 * d) ≤ (3 * L) ^ (2 * d) :=
        Nat.pow_le_pow_left (by omega) _
      have hb3 : (2 * L + 1) ^ (2 * d) * bandDepth d Cbox Cdep L ≤ (3 * L) ^ (2 * d) * L :=
        Nat.mul_le_mul hb2 hJL
      have hb4 : (3 * L) ^ (2 * d) * L ≤ (3 * L) ^ (2 * d + 1) := by
        rw [pow_succ]
        exact Nat.mul_le_mul_left _ (by omega)
      have hb5 : (3 * L) ^ (2 * d) ≤ (3 * L) ^ (2 * d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hcountR : (((2 * L + 1) ^ d + (2 * L + 1) ^ (2 * d) *
        bandDepth d Cbox Cdep L : ℕ) : ℝ) ≤ 2 * (3 * (L : ℝ)) ^ (2 * d + 1) := by
      have h := (Nat.cast_le (α := ℝ)).mpr hcount
      push_cast at h ⊢
      linarith
    have hcountpos : (0 : ℝ) < (((2 * L + 1) ^ d + (2 * L + 1) ^ (2 * d) *
        bandDepth d Cbox Cdep L : ℕ) : ℝ) := by
      have h1 : (1 : ℕ) ≤ (2 * L + 1) ^ d := Nat.one_le_pow _ _ (by omega)
      have : (0 : ℕ) < (2 * L + 1) ^ d + (2 * L + 1) ^ (2 * d) *
          bandDepth d Cbox Cdep L := by omega
      exact_mod_cast this
    have hlogcount : Real.log (((2 * L + 1) ^ d + (2 * L + 1) ^ (2 * d) *
        bandDepth d Cbox Cdep L : ℕ) : ℝ) ≤
        crossRate d Cbox Cdep 1 cprob * Real.log (L : ℝ) ^ 2 := by
      refine le_trans (Real.log_le_log hcountpos hcountR) ?_
      have hsplit : Real.log (2 * (3 * (L : ℝ)) ^ (2 * d + 1)) =
          Real.log 2 + ((2 * (d : ℝ) + 1) * (Real.log 3 + Real.log (L : ℝ))) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
          Real.log_mul (by norm_num) (by linarith)]
        push_cast
        ring
      rw [hsplit]
      linarith [hcountlog]
    have hexpcount : (((2 * L + 1) ^ d + (2 * L + 1) ^ (2 * d) *
        bandDepth d Cbox Cdep L : ℕ) : ℝ) ≤
        Real.exp (crossRate d Cbox Cdep 1 cprob * Real.log (L : ℝ) ^ 2) :=
      (Real.log_le_iff_le_exp hcountpos).mp hlogcount
    have hgain : Real.exp (crossRate d Cbox Cdep 1 cprob * Real.log (L : ℝ) ^ 2) *
        Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
          ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ)) ≤ X := by
      rw [hX, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      exact gain_exponent_le (rate := crossRate d Cbox Cdep 1 cprob) (c := c) (q := q)
        (Y := Real.log (L : ℝ) ^ 2)
        (G := ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ)) hratepos.le hq1 hc2 hcpos.le
        (by positivity) hgainlog
    calc (((2 * L + 1) ^ d + (2 * L + 1) ^ (2 * d) * bandDepth d Cbox Cdep L : ℕ) : ℝ) *
          Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
            ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ))
        ≤ Real.exp (crossRate d Cbox Cdep 1 cprob * Real.log (L : ℝ) ^ 2) *
            Real.exp (-(crossRate d Cbox Cdep 1 cprob) * q *
              ((3 ^ bandDepth d Cbox Cdep L : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hexpcount (Real.exp_pos _).le
      _ ≤ X := hgain
  calc mu (chemicalDistanceFailureEventAt E Cbox (linearBudgetConst d * L) z L)
      ≤ mu ({omega | ¬ GoodConnectedInDoubleBallAt E Cbox omega z L ((L : ℝ) / 20)} ∪
          adaptiveTubeFailureEvent E Cbox z L (linearBudgetConst d * L)) :=
        measure_mono (chemicalDistanceFailureEventAt_subset_union_adaptive E Cbox z L _)
    _ ≤ mu {omega | ¬ GoodConnectedInDoubleBallAt E Cbox omega z L ((L : ℝ) / 20)} +
          mu (adaptiveTubeFailureEvent E Cbox z L (linearBudgetConst d * L)) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal X + ENNReal.ofReal X := add_le_add hA hB
    _ = ENNReal.ofReal (2 * X) := by
        rw [← ENNReal.ofReal_add hXnn hXnn]
        ring_nf

/-! ## The chemical-distance bound at every scale -/

/-- **`UniformChemicalDistanceBoundBox` at the linear budget, at every scale `L ≥ 1`.**

Same conclusion as `exists_chemicalDistance_linear_tail`, extended to the finitely many scales
below the threshold by the bad-site union bound of `Section9ChemicalLengthTail`. -/
theorem exists_chemicalDistance_linear_bound (d Cbox Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCbox : 1 ≤ Cbox) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 : ℕ, ∃ c Cfail : ℝ, 0 < c ∧ 0 < Cfail ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∀ (z : Lattice d) (L : ℕ), 1 ≤ L →
          mu (chemicalDistanceFailureEventAt E Cbox (linearBudgetConst d * L) z L) ≤
            ENNReal.ofReal (Cfail * Real.exp (-c * q * Real.log (L : ℝ) ^ 2)) := by
  classical
  obtain ⟨q0t, L0, ctail, hL01, hctail, htail⟩ :=
    exists_chemicalDistance_linear_tail d Cbox Cdep Cprob cprob hd hCbox hCprob hcprob
  obtain ⟨q0s, hq0s⟩ := exists_uniform_threshold (c := cprob)
    (X := Real.log ((3 : ℝ) ^ d) + Real.log 2) hcprob
  set B : ℝ := Real.log (L0 : ℝ) ^ 2 + 1 with hB
  have hB1 : (1 : ℝ) ≤ B := by
    have : (0 : ℝ) ≤ Real.log (L0 : ℝ) ^ 2 := by positivity
    rw [hB]; linarith
  set Cfail : ℝ := 2 + (((2 * L0 + 1) ^ d : ℕ) : ℝ) *
    (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ))) with hCfail
  have hCfailpos : 0 < Cfail := by
    have h1 : (0 : ℝ) ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (((3 * Cbox) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hCfail]; positivity
  refine ⟨max 1 (max q0t q0s), min ctail (cprob / B), Cfail,
    lt_min hctail (by positivity), hCfailpos, ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw z L hL1
  clear_value B Cfail
  have hq0t : (q0t : ℝ) ≤ q :=
    le_trans (by exact_mod_cast (Nat.le_max_left q0t q0s).trans (Nat.le_max_right 1 _)) hq
  have hq0s' : (q0s : ℝ) ≤ q :=
    le_trans (by exact_mod_cast (Nat.le_max_right q0t q0s).trans (Nat.le_max_right 1 _)) hq
  have hqone : (1 : ℝ) ≤ q := le_trans (by exact_mod_cast Nat.le_max_left 1 _) hq
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hqone
  set c : ℝ := min ctail (cprob / B) with hc
  have hc1 : c ≤ ctail := min_le_left _ _
  have hc2 : c ≤ cprob / B := min_le_right _ _
  have hcpos : 0 < c := lt_min hctail (by positivity)
  clear_value c
  have hlognn : (0 : ℝ) ≤ Real.log (L : ℝ) ^ 2 := by positivity
  by_cases hLL0 : L0 ≤ L
  · refine le_trans (htail mu E q hq0t hprob hsc hr hlaw z L hLL0) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp : Real.exp (-(ctail * q * Real.log (L : ℝ) ^ 2)) ≤
        Real.exp (-c * q * Real.log (L : ℝ) ^ 2) := by
      refine Real.exp_le_exp.mpr ?_
      have hkey : c * (q * Real.log (L : ℝ) ^ 2) ≤ ctail * (q * Real.log (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hc1 (by positivity)
      nlinarith [hkey]
    have hpos : (0 : ℝ) < Real.exp (-c * q * Real.log (L : ℝ) ^ 2) := Real.exp_pos _
    have hCf : (2 : ℝ) ≤ Cfail := by
      have h1 : (0 : ℝ) ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (((3 * Cbox) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
      have hnn : (0 : ℝ) ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) *
          (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ))) := by positivity
      rw [hCfail]; linarith
    nlinarith [Real.exp_pos (-(ctail * q * Real.log (L : ℝ) ^ 2))]
  · push Not at hLL0
    have hbudget : ((2 * L + 1 : ℕ) : ℝ) ≤ linearBudgetConst d * L := by
      have h5 : 5 ≤ 3 * 5 ^ d + 2 * 9 ^ d := by
        have h1 : 1 ≤ 5 ^ d := Nat.one_le_pow _ _ (by norm_num)
        have h2 : 1 ≤ 9 ^ d := Nat.one_le_pow _ _ (by norm_num)
        omega
      have hnat : 2 * L + 1 ≤ (3 * 5 ^ d + 2 * 9 ^ d) * L := by
        have h : 5 * L ≤ (3 * 5 ^ d + 2 * 9 ^ d) * L := Nat.mul_le_mul_right _ h5
        omega
      have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
      rw [linearBudgetConst]
      push_cast at hcast ⊢
      linarith
    have hA : (0 : ℝ) ≤ cprob * q := by positivity
    have hqlog : Real.log ((3 : ℝ) ^ d) + Real.log 2 ≤ cprob * q := hq0s q hq0s'
    refine le_trans (measure_chemicalDistanceFailureEventAt_le_badSites mu hCbox hCprob.le hA
      hqlog hprob z L hbudget) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hcard : (((2 * L + 1) ^ d : ℕ) : ℝ) ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) := by
      have : ((2 * L + 1) ^ d : ℕ) ≤ ((2 * L0 + 1) ^ d : ℕ) :=
        Nat.pow_le_pow_left (by omega) d
      exact_mod_cast this
    have hlogle : Real.log (L : ℝ) ^ 2 ≤ B := by
      have hLcast : (L : ℝ) ≤ (L0 : ℝ) := by exact_mod_cast hLL0.le
      have hL1' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
      have h1 : Real.log (L : ℝ) ≤ Real.log (L0 : ℝ) := Real.log_le_log (by linarith) hLcast
      have h2 : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1'
      rw [hB]; nlinarith
    have hrate : c * q * Real.log (L : ℝ) ^ 2 ≤ cprob * q := by
      have h1 : c * Real.log (L : ℝ) ^ 2 ≤ c * B :=
        mul_le_mul_of_nonneg_left hlogle hcpos.le
      have h2 : c * B ≤ cprob := by
        have h := mul_le_mul_of_nonneg_right hc2 (by linarith : (0 : ℝ) ≤ B)
        rw [div_mul_eq_mul_div, mul_div_assoc, div_self (by linarith : B ≠ 0), mul_one] at h
        linarith
      nlinarith [hqpos.le]
    have hexp : Real.exp (-(cprob * q)) ≤ Real.exp (-c * q * Real.log (L : ℝ) ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [hrate])
    have hCf : (((2 * L0 + 1) ^ d : ℕ) : ℝ) * (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)))
        ≤ Cfail := by rw [hCfail]; linarith
    have hnn1 : (0 : ℝ) ≤ 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) := by
      have : (0 : ℝ) ≤ (((3 * Cbox) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
      positivity
    have hexppos : (0 : ℝ) < Real.exp (-c * q * Real.log (L : ℝ) ^ 2) := Real.exp_pos _
    have hstep : 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) * Real.exp (-(cprob * q))
        ≤ 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) *
          Real.exp (-c * q * Real.log (L : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hexp hnn1
    have hnn2 : (0 : ℝ) ≤ 2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) *
        Real.exp (-(cprob * q)) := mul_nonneg hnn1 (Real.exp_pos _).le
    have hnn3 : (0 : ℝ) ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (((2 * L + 1) ^ d : ℕ) : ℝ) *
          (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) * Real.exp (-(cprob * q)))
        ≤ (((2 * L0 + 1) ^ d : ℕ) : ℝ) *
          (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) *
            Real.exp (-c * q * Real.log (L : ℝ) ^ 2)) :=
          mul_le_mul hcard hstep hnn2 hnn3
      _ = ((((2 * L0 + 1) ^ d : ℕ) : ℝ) * (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)))) *
            Real.exp (-c * q * Real.log (L : ℝ) ^ 2) := by ring
      _ ≤ Cfail * Real.exp (-c * q * Real.log (L : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hCf hexppos.le

/-! ## The frozen residual -/

/-- **`UniformChemicalDistanceBoundBox` is PROVED, at the linear budget of the frozen clause.**

This is the sole residual of the percolation anchor at the length budget
`linearBudgetConst d * L` — a constant times `L`, exactly the shape a scale-independent constant
demands.  Nothing external is used: the connectivity half is
`Section9ChemicalConnectivityTail.exists_connectivity_tail`, and the length half is the band
route of this package. -/
theorem uniformChemicalDistanceBoundBox_linear (d Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    UniformChemicalDistanceBoundBox d Cdep Cprob cprob := by
  obtain ⟨q0, c, Cfail, hc, hCfail, hbound⟩ :=
    exists_chemicalDistance_linear_bound d 1 Cdep Cprob cprob hd le_rfl hCprob hcprob
  refine ⟨q0, 1, c, Cfail, linearBudgetConst d, le_rfl, hc, hCfail,
    linearBudgetConst_nonneg d, ?_⟩
  intro Omega _ mu _ E q hq hprob hsc hr hlaw z L hL
  rw [chemicalDistanceFailureEvent_eq_at]
  exact hbound mu E q hq hprob hsc hr hlaw z L hL

/-- **The frozen percolation conclusion, with the chemical-distance citation discharged.**

`Section9ChemicalUniformProvider.weightedMultiscalePercolation_of_uniformChemicalDistanceBoundBox`
turns `UniformChemicalDistanceBoundBox` into the block of
`SubdiffusiveProcess.Frozen.Section9.weighted_multiscale_percolation` verbatim; the residual is now proved, so
the conclusion holds with no hypothesis beyond the frozen binders and no external input. -/
theorem weightedMultiscalePercolation_of_linearBudget (d Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 L0 Cbox : ℕ, ∃ c C : ℝ,
      0 < c ∧ 0 < C ∧ 1 ≤ L0 ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (crossing z omega : ℝ) - L0)) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          AEFiniteRangePercolationGeometry mu E Cbox
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
            c C q crossing component :=
  weightedMultiscalePercolation_of_uniformChemicalDistanceBoundBox d Cdep Cprob cprob hd
    hCprob hcprob (uniformChemicalDistanceBoundBox_linear d Cdep Cprob cprob hd hCprob hcprob)

/-- **The frozen percolation conclusion with the two measurability facts appended.**

Identical to `weightedMultiscalePercolation_of_linearBudget` except that the crossing and
component heights are additionally returned as measurable maps — as required by the Section 9 stopping construction's `hF`.  This is the measurable-map form of the percolation conclusion. -/
theorem weightedMultiscalePercolationMeasurable_of_linearBudget (d Cdep : ℕ) (Cprob cprob : ℝ)
    (hd : 2 ≤ d) (hCprob : 0 < Cprob) (hcprob : 0 < cprob) :
    ∃ q0 L0 Cbox : ℕ, ∃ c C : ℝ,
      0 < c ∧ 0 < C ∧ 1 ≤ L0 ∧
      ∀ {Omega : Type} [MeasurableSpace Omega] (mu : Measure Omega)
        [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Omega) (q : ℝ),
        (q0 : ℝ) ≤ q →
        (∀ j z, mu (E j z) ≤
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))) →
        IndependentEventScales mu E →
        MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E →
        TranslationInvariantEventLaw mu E →
        ∃ crossing component : Lattice d → Omega → ℕ,
          (∀ z omega, 1 ≤ crossing z omega) ∧
          (∀ z omega, 1 ≤ component z omega) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (crossing z omega : ℝ) - L0)) ∧
          (∀ z, SubdiffusiveProcess.OGammaLE mu 1 (C / q) (fun omega => (component z omega : ℝ) - 1)) ∧
          AEFiniteRangePercolationGeometry mu E Cbox
            (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.section9CrossingSteps d)
            c C q crossing component ∧
          (∀ z, Measurable (crossing z)) ∧
          (∀ z, Measurable (component z)) :=
  weightedMultiscalePercolationMeasurable_of_uniformChemicalDistanceBoundBox d Cdep Cprob cprob
    hd hCprob hcprob
    (uniformChemicalDistanceBoundBox_linear d Cdep Cprob cprob hd hCprob hcprob)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
