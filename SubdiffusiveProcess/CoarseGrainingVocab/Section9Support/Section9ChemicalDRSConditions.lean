module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalASDClauses
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalSeed

@[expose] public section

/-!
# The `[DRS]` conditions P1–P3, S1–S2, and the entropy of the renormalization

 verifies the hypotheses of
`[DRS, Theorem 1.3]` for the good-site field of the multiscale percolation lemma
and then re-runs its proof with the dependence on `q` retained.  This file states
those hypotheses exactly in the library percolation vocabulary, proves the
ones that are formal, and supplies the combinatorial half of the renormalization
level count.

## What is proved

* `card_separatedPairs_latticeBall_le_exp_sqrtTwoScheduleEntropy` — **M3's
  combinatorial half.**  The level-`k` sub-box centres covering a level-`(k+1)`
  box are `(2 M + 1) ^ d` many, so the separated pairs number at most
  `(2 M + 1) ^ (2 d)`; when `2 M + 1 ≤ 3 ρ_k` this is exactly
  `exp (e_k)` for the printed entropy `e_k = log (3 ^ (2 d) ρ_k ^ (2 d))`.
  This is the hypothesis `hcard` of `measure_le_ofReal_twoSeedStep`, and with
  `Section9ChemicalForcing.twoSeedDecomposition_of_clusteredBadForcing` it
  completes the inputs of the one-step recursion.
* `drsConditionP2` — **P2** holds by inspection: the manuscript's family
  `(P^u)_{u ∈ (0,1)}` is the constant family, because the good-site indicator is
  defined from the fixed event field with no auxiliary parameter.
* `not_inInfiniteGoodComponent_subset` — the decomposition behind **S2**: the
  origin fails to lie in the infinite good component only if it is bad, or good
  with a finite good component.  Combined with
  `Section9ChemicalSeed.measure_percolationBadSite_le` this is the printed
  `P[0 bad] ≤ C e^{-c q}` half of S2.
* `goodConnectedInDoubleBall_of_badComponentDiameterBound` — the deterministic
  half of **S1**: once the bad-component diameter bound of clause (ii) is below
  `L / 100` on `B_{2L}(z)`, `[Timár, Lemma 2]` connects any two good sites of
  `B_L(z)` lying in good components of diameter at least `L / 10`, inside
  `B_{2L}(z)`.

## What remains external, stated exactly

* `DRSConditionP1` — mixing and ergodicity of the good-site indicator field.  The
  manuscript's justification is the truncation estimate: an event `E_j(v)` with
  `j > j₀` changes whether the origin is good with probability at most
  `C exp (-c q 3 ^ (3 j₀ / 2))`, which is the tail of the series already summed
  in `Section9ChemicalSeed.measure_percolationBadSite_le_tsum`.
* `DRSConditionP3` — the finite-range decoupling with `f_P(L) = c q L ^ (3/2)`.
* `TimarBoundaryInput` — `[Timár, Lemma 2]`, the only genuinely external
  ingredient of S1.
* `DRSConditionS2` — the density of the infinite good component exceeds `4/5`;
  the ergodic theorem converts the two bad-site bounds into it.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## M3's combinatorial half: the level entropy -/

/-- **The renormalization entropy.**  A level-`(k+1)` box is covered by the
`(2 M + 1) ^ d` level-`k` sub-box centres of a lattice ball of radius `M`, so the
separated pairs number at most `(2 M + 1) ^ (2 d)`.  With `2 M + 1 ≤ 3 ρ_k` —
which the `√2` schedule provides, since `M ≍ ρ_k` — this is exactly `exp (e_k)`
for the printed entropy `e_k = log (C l_k ^ (2 d))` with `C = 3 ^ (2 d)`.
-/
theorem card_separatedPairs_latticeBall_le_exp_sqrtTwoScheduleEntropy
    (R M k : ℕ) (x : Lattice d)
    (hM : ((2 * M + 1 : ℕ) : ℝ) ≤ 3 * sqrtTwoRatio k) :
    (((separatedPairs R (latticeBallFinset x M)).card : ℕ) : ℝ) ≤
      Real.exp (sqrtTwoScheduleEntropy ((3 : ℝ) ^ (2 * d)) d k) := by
  have hCpos : (0 : ℝ) < (3 : ℝ) ^ (2 * d) := by positivity
  have hrho : (0 : ℝ) < sqrtTwoRatio k := sqrtTwoRatio_pos k
  have hcount : (separatedPairs R (latticeBallFinset x M)).card ≤ ((2 * M + 1) ^ d) ^ 2 := by
    have := card_separatedPairs_le R (latticeBallFinset x M)
    rwa [card_latticeBallFinset x M] at this
  have hcountR : (((separatedPairs R (latticeBallFinset x M)).card : ℕ) : ℝ) ≤
      (((2 * M + 1 : ℕ) : ℝ) ^ d) ^ 2 := by
    have : (((separatedPairs R (latticeBallFinset x M)).card : ℕ) : ℝ) ≤
        ((((2 * M + 1) ^ d) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcount
    simpa using this
  have hstep : (((2 * M + 1 : ℕ) : ℝ) ^ d) ^ 2 ≤ ((3 : ℝ) * sqrtTwoRatio k ^ 1) ^ (2 * d) := by
    have hbase : (0 : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) := by positivity
    have hpow : (((2 * M + 1 : ℕ) : ℝ)) ^ (2 * d) ≤ (3 * sqrtTwoRatio k) ^ (2 * d) :=
      pow_le_pow_left₀ hbase hM (2 * d)
    calc (((2 * M + 1 : ℕ) : ℝ) ^ d) ^ 2 = ((2 * M + 1 : ℕ) : ℝ) ^ (2 * d) := by
          rw [← pow_mul]; ring_nf
      _ ≤ (3 * sqrtTwoRatio k) ^ (2 * d) := hpow
      _ = ((3 : ℝ) * sqrtTwoRatio k ^ 1) ^ (2 * d) := by rw [pow_one]
  refine hcountR.trans (hstep.trans (le_of_eq ?_))
  rw [sqrtTwoScheduleEntropy_eq_log hCpos, Real.exp_log (by positivity), pow_one, mul_pow]

/-! ## P1 and P2 -/

/-- The shift of a multiscale indicator configuration by a lattice vector. -/
def configShift (a : Lattice d) (f : ℕ × Lattice d → ℝ) : ℕ × Lattice d → ℝ :=
  fun p => f (p.1, p.2 + a)

/-- **`[DRS]` condition P1**: the good-site indicator field is translation
invariant and ergodic.

The argument justifies this by the level-truncation
estimate: after truncating at level `j₀` the field is finite range, and the
probability that a level `j > j₀` event changes whether the origin is good is at
most `C exp (-c q 3 ^ (3 j₀ / 2))` — the tail of the series summed in
`Section9ChemicalSeed.measure_percolationBadSite_le_tsum`.
-/
def DRSConditionP1 [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) : Prop :=
  TranslationInvariantEventLaw mu E ∧
    ∀ A : Set (ℕ × Lattice d → ℝ), MeasurableSet A →
      (∀ a : Lattice d, configShift a ⁻¹' A = A) →
      Measure.map (eventFieldConfiguration E) mu A = 0 ∨
        Measure.map (eventFieldConfiguration E) mu A = 1

/-- **`[DRS]` condition P2**: the family `(P^u)_{u ∈ (0,1)}` is constant.

In this application the good-site indicator carries no auxiliary parameter `u`,
so the family is literally constant and the condition holds by inspection.
-/
theorem drsConditionP2 [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (law : ℝ → Measure (ℕ × Lattice d → ℝ))
    (hconst : ∀ u : ℝ, law u = Measure.map (eventFieldConfiguration E) mu) :
    ∀ u v : ℝ, law u = law v := fun u v => by rw [hconst u, hconst v]

/-- **`[DRS]` condition P3**: decoupling at range `R L` with rate
`f_P(L) = c q L ^ (3/2)`.

Retaining in an event measurable in `B_{10 L}(x_i)` only the levels with
`Cdep 3 ^ j ≤ R L / 100` makes the two events independent once
`|x₁ - x₂|_∞ ≥ R L`, and the probability that either truncation changes the
original event is at most `C exp (-c q (R L) ^ (3/2))`.
-/
def DRSConditionP3 [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (Cdep : ℕ) (cP : ℝ) : Prop :=
  ∀ (L R : ℕ), 1 ≤ L → 1 ≤ R →
    ∀ (A B : Set Ω) (x1 x2 : Lattice d),
      R * L ≤ latticeDist x1 x2 →
      MeasurableSet[⨆ j, eventFieldSigma (E j)
        (latticeBallFinset x1 (10 * L) : Set (Lattice d))] A →
      MeasurableSet[⨆ j, eventFieldSigma (E j)
        (latticeBallFinset x2 (10 * L) : Set (Lattice d))] B →
      ∃ (j0 : ℕ) (A' B' : Set Ω),
        100 * (Cdep * 3 ^ j0) ≤ R * L ∧
        MeasurableSet[⨆ j ∈ Finset.range (j0 + 1), eventFieldSigma (E j)
          (latticeBallFinset x1 (10 * L) : Set (Lattice d))] A' ∧
        MeasurableSet[⨆ j ∈ Finset.range (j0 + 1), eventFieldSigma (E j)
          (latticeBallFinset x2 (10 * L) : Set (Lattice d))] B' ∧
        mu (A' \ A) + mu (A \ A') + mu (B' \ B) + mu (B \ B') ≤
          ENNReal.ofReal (Real.exp (-(cP * ((R * L : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))) ∧
        mu (A' ∩ B') = mu A' * mu B'

/-- The truncation error of P1 and P3: some level above `j0` influences `z`.

 bounds its probability by
`C exp (-c q 3 ^ (3 j₀ / 2))`, which is the tail, from `j₀ + 1` on, of the
series summed in `Section9ChemicalSeed.measure_percolationBadSite_le_tsum`. -/
def highLevelInfluence (E : ℕ → Lattice d → Set Ω) (Cbox j0 : ℕ)
    (z : Lattice d) : Set Ω :=
  ⋃ j : ℕ, influenceFailure (E (j + j0 + 1)) (Cbox * 3 ^ (j + j0 + 1)) z

/-- **The truncation tail.**  The same union bound as the bad-site estimate, run
from level `j₀ + 1` on. -/
theorem measure_highLevelInfluence_le_tsum [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (Cbox j0 : ℕ) (z : Lattice d) (p : ℕ → ℝ≥0∞)
    (hp : ∀ j u, mu (E j u) ≤ p j) :
    mu (highLevelInfluence E Cbox j0 z) ≤
      ∑' j : ℕ, (((2 * (Cbox * 3 ^ (j + j0 + 1)) + 1) ^ d : ℕ) : ℝ≥0∞) *
        p (j + j0 + 1) := by
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_)
  have h := measure_influenceFailure_le (μ := mu) (E (j + j0 + 1))
    (Cbox * 3 ^ (j + j0 + 1)) z (p (j + j0 + 1)) (hp (j + j0 + 1))
  rwa [nsmul_eq_mul] at h

/-! ## S1: connectivity in the double ball, from `[Timár]` -/

/-- The conclusion of `[DRS]` condition S1: two good sites of `B_L(z)` in good
components of `ℓ^∞` diameter at least `L / 10` are joined by good sites inside
`B_{2L}(z)`.
-/
def GoodConnectedInDoubleBall (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (z : Lattice d) (L : ℕ) : Prop :=
  ∀ v w : Lattice d, InLatticeBallReal z v L → InLatticeBallReal z w L →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 10) v →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 10) w →
    JStepReachableIn 1
      {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)} v w

/-- **S1 with the good-component diameter left free.**

`GoodConnectedInDoubleBall` fixes the diameter threshold at `L / 10`, which is
the constant printed.  The
chemical-distance failure event `D_L(z)` of `Section9ChemicalDistance` supplies
components of diameter at least `L / 20` at the same radius `L`, and no
rescaling of `L` reconciles the two: enlarging `L` is needed for the ball and
shrinking it for the diameter.  The separation step does not use the value
`L / 10` at all — only that it exceeds twice the bad-component diameter — so the
threshold is carried as a parameter here and the two consumers are the
specializations `D = L / 10` and `D = L / 20`.
-/
def GoodConnectedInDoubleBallAt (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (z : Lattice d) (L : ℕ) (D : ℝ) : Prop :=
  ∀ v w : Lattice d, InLatticeBallReal z v L → InLatticeBallReal z w L →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω D v →
    InGoodComponentOfDiameterAtLeast E Cbox 1 ω D w →
    JStepReachableIn 1
      {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)} v w

/-- `GoodConnectedInDoubleBall` is the case `D = L / 10`. -/
theorem goodConnectedInDoubleBall_iff_at (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (ω : Ω) (z : Lattice d) (L : ℕ) :
    GoodConnectedInDoubleBall E Cbox ω z L ↔
      GoodConnectedInDoubleBallAt E Cbox ω z L ((L : ℝ) / 10) := Iff.rfl

/-- **`[Timár, Lemma 2]` in the form the manuscript uses.**

If every bad `J`-step component meeting `B_{2L}(z)` has `ℓ^∞` diameter below
`L / 100`, then no bad component separates two good components of diameter at
least `L / 10` inside `B_{2L}(z)`, and the two are joined by good sites there.

This is the one genuinely external ingredient of S1: the boundary of a finite
nearest-neighbour good component is a `*`-connected — that is, `1`-step, in the
`ℓ^∞` convention of this development — set of bad sites.

`[TimarBoundary, Lemma 2]`. -/
def TimarBoundaryInput (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (ω : Ω)
    (z : Lattice d) (L : ℕ) : Prop :=
  (∀ v : Lattice d, InLatticeBallReal z v (2 * L : ℝ) →
      ¬ IsPercolationGoodSite E Cbox ω v →
      HasLatticeDiameterAtMost
        (jStepComponent J {u | ¬ IsPercolationGoodSite E Cbox ω u} v) ((L : ℝ) / 100)) →
    GoodConnectedInDoubleBall E Cbox ω z L

/-- **The deterministic half of S1.**  Clause (ii) at the centre `z`, once its
right-hand side is below `L / 100` at the radius `2 L`, feeds `[Timár, Lemma 2]`
and delivers S1 at scale `L`. -/
theorem goodConnectedInDoubleBall_of_badComponentDiameterBound
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} {ω : Ω} {z : Lattice d} {C q : ℝ}
    {h L : ℕ}
    (hbad : BadComponentDiameterBound E Cbox J ω z C q h)
    (hsmall : C * (1 + h + q⁻¹ * Real.log (2 + (2 * L : ℝ))) ^ 2 ≤ (L : ℝ) / 100)
    (htimar : TimarBoundaryInput E Cbox J ω z L) :
    GoodConnectedInDoubleBall E Cbox ω z L := by
  refine htimar fun v hv hvbad => ?_
  have hL : (0 : ℝ) ≤ 2 * L := by positivity
  exact fun a ha b hb i => ((hbad (2 * L : ℝ) hL v hv hvbad) a ha b hb i).trans hsmall

/-! ## S2: the density of the infinite good component -/

/-- A site lies in the infinite good component. -/
def InInfiniteGoodComponent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (ω : Ω)
    (v : Lattice d) : Prop :=
  IsPercolationGoodSite E Cbox ω v ∧
    ¬ (jStepComponent 1 {u | IsPercolationGoodSite E Cbox ω u} v).Finite

/-- The event that `v` is good but its good component is finite. -/
def goodFiniteComponentEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (v : Lattice d) : Set Ω :=
  {ω | IsPercolationGoodSite E Cbox ω v ∧
    (jStepComponent 1 {u | IsPercolationGoodSite E Cbox ω u} v).Finite}

/-- **The S2 decomposition.**  The origin misses the infinite good component only
by being bad or by having a finite good component.  The first has probability at
most `C e^{-c q}` (`Section9ChemicalSeed.measure_percolationBadSite_le`); the
manuscript bounds the second by decomposing over the dyadic diameter of the
finite component and applying clause (ii) to its boundary.
-/
theorem not_inInfiniteGoodComponent_subset (E : ℕ → Lattice d → Set Ω)
    (Cbox : ℕ) (v : Lattice d) :
    {ω : Ω | ¬ InInfiniteGoodComponent E Cbox ω v} ⊆
      percolationBadSite E Cbox v ∪ goodFiniteComponentEvent E Cbox v := by
  intro ω hω
  by_cases hgood : IsPercolationGoodSite E Cbox ω v
  · refine Or.inr ⟨hgood, ?_⟩
    by_contra hfin
    exact hω ⟨hgood, hfin⟩
  · exact Or.inl hgood

/-- **`[DRS]` condition S2**: the density of the infinite good component exceeds
`4/5`, and is independent of the parameter `u`.
-/
def DRSConditionS2 [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) : Prop :=
  ENNReal.ofReal (4 / 5) ≤
    mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)}

/-- **S2 from the two bad-site bounds.**  If being bad and being good with a
finite component each have probability at most `b`, and `2 b ≤ 1/5`, then S2
holds. -/
theorem drsConditionS2_of_bounds [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {b : ℝ≥0∞}
    (hmeas : MeasurableSet {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)})
    (hbad : mu (percolationBadSite E Cbox (fun _ => 0)) ≤ b)
    (hfin : mu (goodFiniteComponentEvent E Cbox (fun _ => 0)) ≤ b)
    (hb : 2 * b ≤ ENNReal.ofReal (1 / 5)) :
    DRSConditionS2 mu E Cbox := by
  have hcompl : mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)}ᶜ ≤ 2 * b := by
    refine (measure_mono (not_inInfiniteGoodComponent_subset E Cbox _)).trans ?_
    refine (measure_union_le _ _).trans ?_
    have := add_le_add hbad hfin
    simpa [two_mul] using this
  have hle : mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)}ᶜ ≤
      ENNReal.ofReal (1 / 5) := hcompl.trans hb
  have hprob : mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)} +
      mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)}ᶜ = 1 := by
    rw [measure_add_measure_compl hmeas, measure_univ]
  have hsplit : ENNReal.ofReal (4 / 5) + ENNReal.ofReal (1 / 5) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  by_contra hcon
  simp only [DRSConditionS2, not_le] at hcon
  have : mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)} +
      mu {ω : Ω | InInfiniteGoodComponent E Cbox ω (fun _ => 0)}ᶜ <
      ENNReal.ofReal (4 / 5) + ENNReal.ofReal (1 / 5) :=
    ENNReal.add_lt_add_of_lt_of_le (by finiteness) hcon hle
  rw [hprob, hsplit] at this
  exact lt_irrefl _ this

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
