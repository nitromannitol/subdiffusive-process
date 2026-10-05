module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# The bad-site bound, and the seeds of `[DRS, Lemmas 4.2 and 4.4]`

 supplies the two seed conditions of the
DRS renormalization by the sentence

> "both seed conditions in `[DRS, Lemmas 4.2 and 4.4]` hold whenever every site
> in their finitely many scale-`L₀` boxes is good.  A union bound and
>  therefore bound the probability of
> either unfavorable seed event by `C e^{-c q}`."

This file performs both steps.

## The bad-site bound

`IsPercolationGoodSite E Cbox ω z` fails exactly when some level-`j` bad event
occurs at a site whose influence box `Q_j(u)` contains `z`
(`percolationBadSite_eq_iUnion`), so the union bound over `j` and over the
`(2 Cbox 3^j + 1)^d` centres gives

```text
P[z is bad] ≤ ∑_j (2 Cbox 3^j + 1)^d Cprob exp (-cprob q 3^(3 j / 2)).
```

The series is summed in closed form: the entropy grows like `(3^d)^j` while the
decay `3^(3 j / 2) ≥ j + 1` is at least geometric, so for
`cprob q ≥ d log 3 + log 2` the sum is at most **twice its first term**,

```text
P[z is bad] ≤ 2 Cprob (3 Cbox)^d exp (-cprob q).
```

That is the manuscript's `C e^{-c q}` with `C(d, Cbox, Cprob)` explicit, and the
`q₀(d)` it needs is `(d log 3 + log 2) / cprob`.

## The seeds

`measure_seedFailure_le` is the union bound over the finitely many scale-`L₀`
sites the DRS seeds involve: if the seed event is contained in "some site of the
finite set `F` is bad", its probability is at most `#F` times the bad-site
bound.  This is the entire probabilistic content; what remains
external is the *combinatorial* statement that a fully good `F` implies the DRS
seed conditions (`[DRS, Lemmas 4.2, 4.4]`).

## Source

* the event probability -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set Finset
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The scalar series -/

/-- `j + 1 ≤ 3 ^ (3 j / 2)`: the DRS decay exponent is at least linear. -/
theorem three_rpow_three_halves_mul_ge (j : ℕ) :
    ((j : ℝ) + 1) ≤ (3 : ℝ) ^ ((3 : ℝ) * j / 2) := by
  have ht : (3 : ℝ) ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
      (by norm_num : (1:ℝ) ≤ (3:ℝ)/2)
    simpa using h
  have hsplit : (3 : ℝ) ^ ((3 : ℝ) * j / 2) = ((3 : ℝ) ^ ((3 : ℝ) / 2)) ^ j := by
    rw [← Real.rpow_natCast ((3:ℝ) ^ ((3:ℝ)/2)) j,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    ring
  set t : ℝ := (3 : ℝ) ^ ((3 : ℝ) / 2) with htdef
  have hb : 1 + (j : ℝ) * (t - 1) ≤ (1 + (t - 1)) ^ j :=
    one_add_mul_le_pow (by linarith) j
  rw [hsplit]
  have hrw : (1 : ℝ) + (t - 1) = t := by ring
  rw [hrw] at hb
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

/-- The geometric rewriting of the bad-site series. -/
theorem pow_mul_exp_neg_eq {Cp N A : ℝ} (j : ℕ) :
    Cp * N ^ j * Real.exp (-(A * ((j : ℝ) + 1))) =
      (Cp * Real.exp (-A)) * (N * Real.exp (-A)) ^ j := by
  rw [mul_pow, ← Real.exp_nat_mul,
    show -(A * ((j : ℝ) + 1)) = -A + (j : ℝ) * -A by ring, Real.exp_add]
  ring

/-- The threshold `log N + log 2 ≤ A` makes the geometric ratio at most `1 / 2`. -/
theorem ratio_le_half {N A : ℝ} (hN : 1 ≤ N) (hA : Real.log N + Real.log 2 ≤ A) :
    N * Real.exp (-A) ≤ 1 / 2 := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have h1 : Real.log (2 * N) ≤ A := by
    rw [Real.log_mul (by norm_num) hNpos.ne']
    linarith
  have h2 : 2 * N ≤ Real.exp A := by
    have h := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by positivity)] at h
  have h3 : (0 : ℝ) < Real.exp A := Real.exp_pos A
  rw [Real.exp_neg, mul_inv_le_iff₀ h3]
  linarith

theorem summable_pow_mul_exp_neg {Cp N A : ℝ} (hN : 1 ≤ N)
    (hA : Real.log N + Real.log 2 ≤ A) :
    Summable fun j : ℕ => Cp * N ^ j * Real.exp (-(A * ((j : ℝ) + 1))) := by
  have hr := ratio_le_half hN hA
  have hr0 : (0 : ℝ) ≤ N * Real.exp (-A) := by
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
    positivity
  have := (summable_geometric_of_lt_one hr0 (by linarith)).mul_left (Cp * Real.exp (-A))
  simpa only [pow_mul_exp_neg_eq] using this

/-- **The series is at most twice its first term.** -/
theorem tsum_pow_mul_exp_neg_le {Cp N A : ℝ} (hCp : 0 ≤ Cp) (hN : 1 ≤ N)
    (hA : Real.log N + Real.log 2 ≤ A) :
    ∑' j : ℕ, Cp * N ^ j * Real.exp (-(A * ((j : ℝ) + 1))) ≤
      2 * Cp * Real.exp (-A) := by
  have hr := ratio_le_half hN hA
  have hr0 : (0 : ℝ) ≤ N * Real.exp (-A) := by
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
    positivity
  have hexp : (0 : ℝ) < Real.exp (-A) := Real.exp_pos _
  rw [tsum_congr (fun j => pow_mul_exp_neg_eq (Cp := Cp) (N := N) (A := A) j), tsum_mul_left,
    tsum_geometric_of_lt_one hr0 (by linarith)]
  have hinv : (1 - N * Real.exp (-A))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  nlinarith [mul_nonneg hCp hexp.le]

/-! ## The bad-site bound -/

/-- The event that `z` is **not** percolation-good. -/
def percolationBadSite (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (z : Lattice d) :
    Set Ω := {ω | ¬ IsPercolationGoodSite E Cbox ω z}

omit [MeasurableSpace Ω] in
/-- Being bad is exactly suffering an influence failure at some scale. -/
theorem percolationBadSite_eq_iUnion (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (z : Lattice d) :
    percolationBadSite E Cbox z = ⋃ j : ℕ, influenceFailure (E j) (Cbox * 3 ^ j) z := by
  ext ω
  simp only [percolationBadSite, mem_ofPred_eq, IsPercolationGoodSite, InInfluenceBox,
    not_forall, not_not, mem_iUnion, influenceFailure, mem_latticeBallFinset_iff,
    exists_prop]
  constructor
  · rintro ⟨j, u, hu, hmem⟩
    exact ⟨j, u, by rwa [latticeDist_comm], hmem⟩
  · rintro ⟨j, u, hu, hmem⟩
    exact ⟨j, u, by rwa [latticeDist_comm], hmem⟩

/-- The union bound over scales and over influence-box centres. -/
theorem measure_percolationBadSite_le_tsum (μ : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (z : Lattice d) (p : ℕ → ℝ≥0∞)
    (hp : ∀ j u, μ (E j u) ≤ p j) :
    μ (percolationBadSite E Cbox z) ≤
      ∑' j : ℕ, (((2 * (Cbox * 3 ^ j) + 1) ^ d : ℕ) : ℝ≥0∞) * p j := by
  rw [percolationBadSite_eq_iUnion]
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_)
  have h := measure_influenceFailure_le (μ := μ) (E j) (Cbox * 3 ^ j) z (p j) (hp j)
  rwa [nsmul_eq_mul] at h

/-- The entropy count `(2 Cbox 3^j + 1)^d ≤ (3 Cbox)^d (3^d)^j`. -/
theorem card_influenceBox_le {Cbox : ℕ} (hCbox : 1 ≤ Cbox) (d j : ℕ) :
    ((2 * (Cbox * 3 ^ j) + 1) ^ d : ℕ) ≤ (3 * Cbox) ^ d * (3 ^ d) ^ j := by
  have hone : 1 ≤ Cbox * 3 ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hstep : 2 * (Cbox * 3 ^ j) + 1 ≤ 3 * Cbox * 3 ^ j := by
    have hm : 3 * Cbox * 3 ^ j = 3 * (Cbox * 3 ^ j) := by ring
    omega
  calc ((2 * (Cbox * 3 ^ j) + 1) ^ d : ℕ) ≤ (3 * Cbox * 3 ^ j) ^ d :=
        Nat.pow_le_pow_left hstep d
    _ = (3 * Cbox) ^ d * (3 ^ d) ^ j := by
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm d j]

/-- **The bad-site bound.**  Summing 
over the scales:

```text
P[z is not percolation-good] ≤ 2 Cprob (3 Cbox)^d exp (-cprob q)
```

for every `q` with `cprob q ≥ d log 3 + log 2`.  The constant is explicit and
the rate is the printed `c q`.
-/
theorem measure_percolationBadSite_le (μ : Measure Ω)
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} (hCbox : 1 ≤ Cbox)
    {Cprob cprob q : ℝ} (hCprob : 0 ≤ Cprob) (hA : 0 ≤ cprob * q)
    (hq : Real.log ((3 : ℝ) ^ d) + Real.log 2 ≤ cprob * q)
    (hE : ∀ j u, μ (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (z : Lattice d) :
    μ (percolationBadSite E Cbox z) ≤
      ENNReal.ofReal (2 * (Cprob * (((3 * Cbox) ^ d : ℕ) : ℝ)) *
        Real.exp (-(cprob * q))) := by
  set Cp : ℝ := Cprob * ((3 * Cbox : ℕ) ^ d : ℕ) with hCp
  set N : ℝ := ((3 ^ d : ℕ) : ℝ) with hN
  set A : ℝ := cprob * q with hAdef
  have hNone : (1 : ℝ) ≤ N := by
    rw [hN]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hNlog : Real.log N + Real.log 2 ≤ A := by
    rw [hN]
    push_cast
    exact hq
  have hCpnn : 0 ≤ Cp := by
    rw [hCp]
    positivity
  refine le_trans (measure_percolationBadSite_le_tsum μ E Cbox z _ hE) ?_
  have hterm : ∀ j : ℕ,
      (((2 * (Cbox * 3 ^ j) + 1) ^ d : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))) ≤
        ENNReal.ofReal (Cp * N ^ j * Real.exp (-(A * ((j : ℝ) + 1)))) := by
    intro j
    have hdecay : Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)) ≤
        Real.exp (-(A * ((j : ℝ) + 1))) := by
      refine Real.exp_le_exp.mpr ?_
      have hj := three_rpow_three_halves_mul_ge j
      have : A * ((j : ℝ) + 1) ≤ A * (3 : ℝ) ^ ((3 : ℝ) * j / 2) :=
        mul_le_mul_of_nonneg_left hj hA
      rw [hAdef] at this ⊢
      nlinarith
    have hcount : (((2 * (Cbox * 3 ^ j) + 1) ^ d : ℕ) : ℝ) ≤ ((3 * Cbox : ℕ) ^ d : ℕ) * N ^ j := by
      have h := card_influenceBox_le (d := d) (j := j) hCbox
      have hcast : (((3 * Cbox) ^ d * (3 ^ d) ^ j : ℕ) : ℝ) =
          ((3 * Cbox : ℕ) ^ d : ℕ) * N ^ j := by
        rw [hN]
        push_cast
        ring
      calc (((2 * (Cbox * 3 ^ j) + 1) ^ d : ℕ) : ℝ) ≤ (((3 * Cbox) ^ d * (3 ^ d) ^ j : ℕ) : ℝ) := by
            exact_mod_cast h
        _ = ((3 * Cbox : ℕ) ^ d : ℕ) * N ^ j := hcast
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hNj : (0 : ℝ) ≤ N ^ j := by positivity
    have hexpnn : (0 : ℝ) ≤ Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)) := (Real.exp_pos _).le
    calc (((2 * (Cbox * 3 ^ j) + 1) ^ d : ℕ) : ℝ) *
          (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2)))
        ≤ (((3 * Cbox : ℕ) ^ d : ℕ) * N ^ j) *
            (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))) := by
          refine mul_le_mul_of_nonneg_right hcount ?_
          positivity
      _ ≤ (((3 * Cbox : ℕ) ^ d : ℕ) * N ^ j) * (Cprob * Real.exp (-(A * ((j : ℝ) + 1)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hdecay hCprob
      _ = Cp * N ^ j * Real.exp (-(A * ((j : ℝ) + 1))) := by
          rw [hCp]
          ring
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  have hnonneg : ∀ j : ℕ, 0 ≤ Cp * N ^ j * Real.exp (-(A * ((j : ℝ) + 1))) := by
    intro j
    have : (0 : ℝ) ≤ N ^ j := by positivity
    positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg (summable_pow_mul_exp_neg hNone hNlog)]
  exact ENNReal.ofReal_le_ofReal (tsum_pow_mul_exp_neg_le hCpnn hNone hNlog)

/-! ## The seeds -/

/-- **The seed union bound**.  A seed
event contained in "some site of the finite set `F` is bad" has probability at
most `#F` times the bad-site bound.

What remains external is `[DRS, Lemmas 4.2 and 4.4]` themselves: the statement
that all sites of `F` being good forces the two seed conditions. -/
theorem measure_seedFailure_le (μ : Measure Ω)
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {Seed : Set Ω} {F : Finset (Lattice d)}
    {bound : ℝ≥0∞}
    (hSeed : Seed ⊆ ⋃ z ∈ F, percolationBadSite E Cbox z)
    (hbad : ∀ z, μ (percolationBadSite E Cbox z) ≤ bound) :
    μ Seed ≤ F.card * bound := by
  refine (measure_mono hSeed).trans ?_
  calc μ (⋃ z ∈ F, percolationBadSite E Cbox z)
      ≤ ∑ z ∈ F, μ (percolationBadSite E Cbox z) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ F, bound := Finset.sum_le_sum fun z _ => hbad z
    _ = F.card * bound := by rw [Finset.sum_const, nsmul_eq_mul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
