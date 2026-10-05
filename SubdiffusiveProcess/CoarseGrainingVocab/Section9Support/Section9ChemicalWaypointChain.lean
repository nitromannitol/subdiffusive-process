module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalPathConstruction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalRenormalizationStep

@[expose] public section

/-!
# The waypoint chain of `[DRS, Lemmas 5.2--5.3]`, with a summable cost

`Section9ChemicalPathConstruction` reduces the third clause of
`FiniteRangePercolationGeometry` to the datum `GoodWaypointChain`, and records in
`le_prod_mul_of_scale_recursion` why the naive level-by-level concatenation of
good paths does **not** produce it: if the level-`(k+1)` chemical length costs
`M_k` level-`k` lengths while the scale only grows by `ρ_k`, the linear constant
picks up `∏ M_i / ρ_i`, and any *multiplicative* overhead `M_k = κ ρ_k` with
`κ > 1` makes that product diverge — the chemical length then grows like
`L ^ (1 + log κ / log ρ)`, not like `L`.

This file supplies the shape in which the constant does converge, and runs the
induction.

## The correct recursion: an additive detour, not a multiplicative one

The DRS construction crosses a level-`(k+1)` box along a chain of `ρ_k`
level-`k` boxes and only *detours* around the bad ones.  On the favourable event
of the renormalization the bad level-`k` boxes met by the chain are confined to a
single cluster (`Section9ChemicalForcing.ClusteredBadForcing`), so the extra
length is not proportional to the whole crossing: it is the total size of the
detours, which is a *fraction* `δ_k` of the level-`(k+1)` scale, with
`δ_k ≲ p_k ≤ exp (-(c q / 2) 2 ^ k)` summable.  The recursion is therefore

```text
Len_{k+1} ≤ ρ_k · Len_k + δ_k · L_{k+1},         L_{k+1} = ρ_k L_k,
```

which, after dividing by `L_{k+1}`, is the **additive** recursion
`c_{k+1} ≤ c_k + δ_k` for `c_k = Len_k / L_k`.  Hence

```text
Len_k ≤ (C + ∑_i δ_i) · L_k                     for every k,
```

with the constant a convergent *sum*, not a divergent product
(`le_add_tsum_mul_of_scale_recursion`).  For the `√2` schedule
`L_k = exp (√2 ^ k)`, `ρ_k = exp ((√2 - 1) √2 ^ k)`, the level failure
probabilities are `p_k ≤ exp (-(c q / 2) 2 ^ k)`
(`Section9ChemicalRenormalizationStep`), so `∑_k δ_k` converges geometrically
(`summable_exp_neg_mul_pow`) and the constant is explicit.

## What is proved here

* `summable_exp_neg_mul_pow` — `∑_k exp (-(a r ^ k)) < ∞` for `a > 0`, `1 < r`;
  in particular for the level rates `r = 2` and for the schedule ratios
  `r = √2`.
* `le_add_tsum_mul_of_scale_recursion` — the additive recursion above.
* `ChemicalBudgetAt` — "every admissible pair in a box of radius `R` is joined by
  a good path of at most `bud` vertices", the level-`k` chemical budget.
* `ChemicalRefinementStep` — `[DRS, Lemmas 5.2--5.3]` at one level, in exactly
  the additive shape.
* `chemicalBudgetAt_of_refinement` — the induction: the budget stays
  `(C + ∑ δ) · L_k` at **every** level.
* `goodWaypointChain_of_chemicalBudgetAt`,
  `not_mem_chemicalDistanceFailureEvent_of_chemicalBudgetAt` — the passage to the
  proved vocabulary, and hence to clause (iii).

## What is *not* proved here, stated exactly

The induction delivers clause (iii) **at the schedule scales `L_k` only**.  The
`√2` schedule is sparse — `L_{k+1} / L_k = L_k ^ (√2 - 1) → ∞` — so a radius `l`
strictly between two schedule scales is *not* within a bounded factor of either,
and no deterministic interpolation can convert the level budget into a linear
bound at `l`: enlarging `l` to `L_{k+1}` costs a factor `l ^ (√2 - 1)`.
This is not a defect of the argument: the manuscript never interpolates
deterministically.  It bounds `P[D_l(z)]` at **every** `l` by the *probabilistic*
estimate `C exp (-c q (log l) ^ 2)` and then reads clause (iii) off the dyadic
height `H₂(z)` (`Section9ChemicalDistance.goodPathClause_of_dyadic_threshold`,
`Section9ChemicalHeightTail`).  The interface between this file and that route is
`isShortGoodPath_of_chemicalBudgetAt`, which is the deterministic passage that
*is* available: from a schedule scale `L_k` with `l ≤ L_k ≤ 2 l`.  For the `√2`
schedule that hypothesis fails at most radii, and the probabilistic route is the
one the formalization must use.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## Summability of the level costs -/

/-- `∑_k exp (-(a r ^ k))` converges for `a > 0` and `r > 1`.

Bernoulli gives `r ^ k ≥ 1 + k (r - 1)`, so the summand is dominated by the
geometric series of ratio `exp (-(a (r - 1))) < 1`. -/
theorem summable_exp_neg_mul_pow {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    Summable fun k : ℕ => Real.exp (-(a * r ^ k)) := by
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  set q : ℝ := Real.exp (-(a * (r - 1))) with hq
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    nlinarith
  have hgeom : Summable fun k : ℕ => Real.exp (-a) * q ^ k :=
    (summable_geometric_of_lt_one hqpos.le hqlt).mul_left _
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_) hgeom
  have hbern : 1 + (k : ℝ) * (r - 1) ≤ r ^ k := by
    have h := one_add_mul_le_pow (a := r - 1) (by linarith) k
    simpa using h
  have hexp : Real.exp (-a) * q ^ k = Real.exp (-(a * (1 + (k : ℝ) * (r - 1)))) := by
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  rw [hexp]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-! ## The additive scale recursion -/

/-- **The summable-cost recursion.**  If the level-`(k+1)` chemical length is at
most `ρ_k` level-`k` lengths *plus* a detour of relative size `δ_k`, and the
detours are summable, the chemical length stays linear in the scale with the
constant `C + ∑ δ`.

This is the correct replacement for `le_prod_mul_of_scale_recursion`, whose
product `∏ M_i / ρ_i` diverges for any multiplicative overhead. -/
theorem le_add_tsum_mul_of_scale_recursion {Len L rho delta : ℕ → ℝ} {C : ℝ}
    (hrho : ∀ k, 0 < rho k) (hLnn : ∀ k, 0 ≤ L k)
    (hdelta : ∀ k, 0 ≤ delta k) (hsum : Summable delta)
    (hL : ∀ k, L (k + 1) = rho k * L k)
    (hstep : ∀ k, Len (k + 1) ≤ rho k * Len k + delta k * L (k + 1))
    (h0 : Len 0 ≤ C * L 0) :
    ∀ k, Len k ≤ (C + ∑' i, delta i) * L k := by
  have hpartial : ∀ k, Len k ≤ (C + ∑ i ∈ Finset.range k, delta i) * L k := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      have hkey : rho k * Len k ≤ (C + ∑ i ∈ Finset.range k, delta i) * L (k + 1) := by
        have := mul_le_mul_of_nonneg_left ih (hrho k).le
        calc rho k * Len k
            ≤ rho k * ((C + ∑ i ∈ Finset.range k, delta i) * L k) := this
          _ = (C + ∑ i ∈ Finset.range k, delta i) * L (k + 1) := by rw [hL k]; ring
      have hgoal : (C + ∑ i ∈ Finset.range (k + 1), delta i) * L (k + 1) =
          (C + ∑ i ∈ Finset.range k, delta i) * L (k + 1) + delta k * L (k + 1) := by
        rw [Finset.sum_range_succ]; ring
      rw [hgoal]
      exact (hstep k).trans (by linarith)
  intro k
  refine (hpartial k).trans (mul_le_mul_of_nonneg_right ?_ (hLnn k))
  have hle : ∑ i ∈ Finset.range k, delta i ≤ ∑' i, delta i :=
    Summable.sum_le_tsum _ (fun i _ => hdelta i) hsum
  linarith

/-! ## The level budget and its refinement -/

/-- **The chemical budget at radius `R`.**  Every pair of sites of `B_R(z)` lying
in good components of `ℓ^∞` diameter at least `R / 20` is joined by a good
nearest-neighbour path with at most `bud` vertices.

This is the conclusion of `[DRS, Lemmas 5.2--5.3]` at one scale, and it is the
exact negation of `chemicalDistanceFailureEvent` once `bud ≤ Clen * R`. -/
def ChemicalBudgetAt (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (R : ℕ) (bud : ℝ) : Prop :=
  ∀ z v w : Lattice d,
    InLatticeBallReal z v R → InLatticeBallReal z w R →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((R : ℝ) / 20) v →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((R : ℝ) / 20) w →
    IsShortGoodPath E Cbox ω bud v w

/-- Enlarging the budget weakens `ChemicalBudgetAt`. -/
theorem ChemicalBudgetAt.mono {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω}
    {R : ℕ} {bud bud' : ℝ} (hb : bud ≤ bud')
    (h : ChemicalBudgetAt E Cbox ω R bud) : ChemicalBudgetAt E Cbox ω R bud' :=
  fun z v w hv hw hvc hwc => (h z v w hv hw hvc hwc).mono hb

/-- **`[DRS, Lemmas 5.2--5.3]` at one level, in the additive shape.**

From a level-`k` budget, the construction produces a level-`(k+1)` budget in
which the crossing costs `ρ_k` level-`k` budgets and the detours around the
single bad cluster cost the additional fraction `δ_k` of the level-`(k+1)` scale.

-/
def ChemicalRefinementStep (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (Lsc : ℕ → ℕ) (rho delta : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ bud : ℝ, ChemicalBudgetAt E Cbox ω (Lsc k) bud →
    ChemicalBudgetAt E Cbox ω (Lsc (k + 1))
      (rho k * bud + delta k * ((Lsc (k + 1) : ℕ) : ℝ))

/-- **The induction.**  A summable family of detour costs keeps the chemical
budget linear in the scale at *every* level, with the explicit constant
`C + ∑ δ`. -/
theorem chemicalBudgetAt_of_refinement {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {ω : Ω} {Lsc : ℕ → ℕ} {rho delta : ℕ → ℝ} {C : ℝ}
    (hdelta : ∀ k, 0 ≤ delta k) (hsum : Summable delta)
    (hL : ∀ k, ((Lsc (k + 1) : ℕ) : ℝ) = rho k * ((Lsc k : ℕ) : ℝ))
    (hstep : ∀ k, ChemicalRefinementStep E Cbox ω Lsc rho delta k)
    (h0 : ChemicalBudgetAt E Cbox ω (Lsc 0) (C * ((Lsc 0 : ℕ) : ℝ))) :
    ∀ k, ChemicalBudgetAt E Cbox ω (Lsc k)
      ((C + ∑' i, delta i) * ((Lsc k : ℕ) : ℝ)) := by
  have hpartial : ∀ k, ChemicalBudgetAt E Cbox ω (Lsc k)
      ((C + ∑ i ∈ Finset.range k, delta i) * ((Lsc k : ℕ) : ℝ)) := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      refine ((hstep k) _ ih).mono (le_of_eq ?_)
      rw [Finset.sum_range_succ, hL k]
      ring
  intro k
  refine (hpartial k).mono (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
  have hle : ∑ i ∈ Finset.range k, delta i ≤ ∑' i, delta i :=
    Summable.sum_le_tsum _ (fun i _ => hdelta i) hsum
  linarith

/-! ## The explicit constant of the `√2` renormalization -/

/-- The detour costs are summable at the geometric level rate
`p_k ≤ exp (-(a/2) 2 ^ k)` proved in `Section9ChemicalRenormalizationStep`. -/
theorem summable_levelDetour {a Cdet : ℝ} (ha : 0 < a) :
    Summable fun k : ℕ => Cdet * Real.exp (-(a / 2 * 2 ^ k)) := by
  have h := summable_exp_neg_mul_pow (a := a / 2) (r := 2) (by linarith) (by norm_num)
  exact h.mul_left Cdet

/-- **The chemical budget with the renormalization rate.**  Feeding the level
rate of the `√2` schedule into the additive recursion gives the chemical length
constant in closed form,

```text
C_∞ = C + Cdet · ∑_k exp (-(a/2) 2 ^ k),        a = c q,
```

a convergent sum whose value decreases as `q` grows. -/
theorem chemicalBudgetAt_of_renormalizationRate {E : ℕ → Lattice d → Set Ω}
    {Cbox : ℕ} {ω : Ω} {Lsc : ℕ → ℕ} {rho : ℕ → ℝ} {C Cdet a : ℝ}
    (ha : 0 < a) (hCdet : 0 ≤ Cdet)
    (hL : ∀ k, ((Lsc (k + 1) : ℕ) : ℝ) = rho k * ((Lsc k : ℕ) : ℝ))
    (hstep : ∀ k, ChemicalRefinementStep E Cbox ω Lsc rho
      (fun i => Cdet * Real.exp (-(a / 2 * 2 ^ i))) k)
    (h0 : ChemicalBudgetAt E Cbox ω (Lsc 0) (C * ((Lsc 0 : ℕ) : ℝ))) :
    ∀ k, ChemicalBudgetAt E Cbox ω (Lsc k)
      ((C + ∑' i : ℕ, Cdet * Real.exp (-(a / 2 * 2 ^ i))) * ((Lsc k : ℕ) : ℝ)) :=
  chemicalBudgetAt_of_refinement
    (fun _ => mul_nonneg hCdet (Real.exp_nonneg _)) (summable_levelDetour ha) hL hstep h0

/-! ## Passage to the proved vocabulary -/

/-- A chemical budget is a one-step waypoint chain. -/
theorem goodWaypointChain_of_chemicalBudgetAt {E : ℕ → Lattice d → Set Ω}
    {Cbox : ℕ} {ω : Ω} {R : ℕ} {bud : ℝ} {z : Lattice d}
    (h : ChemicalBudgetAt E Cbox ω R bud) :
    GoodWaypointChain E Cbox ω 1 bud z R := by
  intro v w hv hw hvc hwc
  refine ⟨fun i => if i = 0 then v else w, 1, Nat.one_pos, le_rfl, by simp, by simp, ?_⟩
  intro i hi
  interval_cases i
  simpa using h z v w hv hw hvc hwc

/-- **`GoodWaypointChain` from the good-box hierarchy.**  The level induction plus
the one-step packaging: at every schedule scale the DRS datum holds with a single
waypoint and the budget `(C + ∑ δ) L_k`. -/
theorem goodWaypointChain_of_refinement {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {ω : Ω} {Lsc : ℕ → ℕ} {rho delta : ℕ → ℝ} {C : ℝ} {z : Lattice d}
    (hdelta : ∀ k, 0 ≤ delta k) (hsum : Summable delta)
    (hL : ∀ k, ((Lsc (k + 1) : ℕ) : ℝ) = rho k * ((Lsc k : ℕ) : ℝ))
    (hstep : ∀ k, ChemicalRefinementStep E Cbox ω Lsc rho delta k)
    (h0 : ChemicalBudgetAt E Cbox ω (Lsc 0) (C * ((Lsc 0 : ℕ) : ℝ))) (k : ℕ) :
    GoodWaypointChain E Cbox ω 1
      ((C + ∑' i, delta i) * ((Lsc k : ℕ) : ℝ)) z (Lsc k) :=
  goodWaypointChain_of_chemicalBudgetAt
    (chemicalBudgetAt_of_refinement hdelta hsum hL hstep h0 k)

/-- A chemical budget linear in the radius rules out the chemical-distance
failure event at that radius. -/
theorem not_mem_chemicalDistanceFailureEvent_of_chemicalBudgetAt
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω} {R : ℕ} {bud Clen : ℝ}
    {z : Lattice d} (hbud : bud ≤ Clen * R) (h : ChemicalBudgetAt E Cbox ω R bud) :
    ω ∉ chemicalDistanceFailureEvent E Cbox Clen z R := by
  rintro ⟨v, w, hv, hw, hvc, hwc, hno⟩
  exact hno ((h z v w hv hw hvc hwc).mono hbud)

/-- **The deterministic scale matching that *is* available.**  A schedule scale
`R` with `l ≤ R ≤ 2 l` transfers the level budget to the clause-(iii)
normalisation at radius `l`: the clause-(iii) hypothesis asks only for good
components of diameter `l / 10`, and `R / 20 ≤ l / 10`.

The `20`-versus-`10` asymmetry is the manuscript's, and it is exactly what makes
the passage possible in this direction and impossible in the other: a *larger*
schedule scale demands a *larger* component diameter, so a scale `R ≫ 2 l` is
useless.  For the `√2` schedule consecutive scales satisfy
`L_{k+1} / L_k = L_k ^ (√2 - 1) → ∞`, so the hypothesis `R ≤ 2 l` fails for most
radii `l` and the formalization must go through the dyadic height of
`Section9ChemicalHeightTail` instead — see the module docstring. -/
theorem isShortGoodPath_of_chemicalBudgetAt {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {ω : Ω} {l R : ℕ} {bud : ℝ} {z v w : Lattice d}
    (hlR : l ≤ R) (hR2l : (R : ℝ) ≤ 2 * l)
    (h : ChemicalBudgetAt E Cbox ω R bud)
    (hv : InLatticeBallReal z v l) (hw : InLatticeBallReal z w l)
    (hvc : InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((l : ℝ) / 10) v)
    (hwc : InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((l : ℝ) / 10) w) :
    IsShortGoodPath E Cbox ω bud v w :=
  h z v w (inLatticeBallReal_mono (by exact_mod_cast hlR) hv)
    (inLatticeBallReal_mono (by exact_mod_cast hlR) hw)
    (inGoodComponentOfDiameterAtLeast_mono (by linarith) hvc)
    (inGoodComponentOfDiameterAtLeast_mono (by linarith) hwc)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
