module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalBandBudget
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalBandSelection
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossFamilyTail

@[expose] public section

/-!
# The tail of a band excess

The probabilistic half of the linear length budget.

`Section9ChemicalBandBudget` reduces the linear clause to the events

```text
    bandExcessEvent E Cbox v w j m : at least m sites of the geodesic from v to w carry a
                                     bad component of reach in the band [3^j, 3^(j+1)] .
```

This file estimates them.  Three inputs meet here.

* `Section9ChemicalBandSelection.exists_separated_subset` — from `m (s+1)` band sites on the
  geodesic, `m` of them are separated by more than `s` **in the index**, hence — the geodesic
  being one-dimensional — by more than `s` in `ℓ∞` distance
  (`sub_le_latticeDist_latticeGeodesic`).  This is the step that fails for a `d`-dimensional
  Peierls accounting, where separating `m` sites costs `3 ^ (j d)` rather than `3 ^ j`.
* `Section9ChemicalBandCap.exists_bandCrossChain` — each band site carries a certificate whose
  cells all sit within `(1 + Cbox + Cdep) 3 ^ (j+1)` of it, so certificates at sites separated
  by more than `bandSep Cbox Cdep j` are **cell-disjoint**.
* `Section9ChemicalCrossFamilyTail.measure_le_of_forall_exists_crossChainFamily` — a
  cell-disjoint family of `m` certificates costs the `m`-th power of the one-certificate bound.

The root entropy is the binomial coefficient `C(n+1, m)`, bounded by `(3 (n+1) / m) ^ m`
(`Section9ChemicalBandSelection.choose_le_pow_div`); it is the *ratio* `(n+1)/m`, not `n+1`,
that appears, which is exactly why the union bound survives at `m` proportional to `L`.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Ω : Type*}

/-! ## The separation that makes band certificates disjoint -/

/-- Two band-`j` certificates rooted farther apart than this are cell-disjoint, because every
cell of a band-`j` certificate lies within `(1 + Cbox + Cdep) 3 ^ (j+1)` of its root. -/
def bandSep (Cbox Cdep j : ℕ) : ℕ := 2 * (1 + Cbox + Cdep) * 3 ^ (j + 1)

/-! ## The disjoint family of certificates -/

/-- **A separated family of band sites carries a cell-disjoint family of certificates.**

Every root contributes a certificate at scale `3 ^ j` with no good-vertex cell, and two
certificates whose roots are farther apart than `bandSep Cbox Cdep j` cannot share a cell. -/
theorem exists_crossChainFamily_of_bandSites (E : ℕ → Lattice d → Set Ω) (Cbox Cdep : ℕ)
    (hd : 1 ≤ d) (hCbox : 1 ≤ Cbox) (ω : Ω) (j : ℕ) :
    ∀ xs : List (Lattice d),
      xs.Pairwise (fun a b => bandSep Cbox Cdep j < latticeDist a b) →
      (∀ x ∈ xs, ω ∈ bandSiteEvent E Cbox x j) →
      ∃ Ls : List (List (CrossCell d)),
        List.Forall₂ (fun (x : Lattice d) (L : List (CrossCell d)) =>
          CrossChain Cbox Cdep 1 x (3 ^ j) L ∧ goodCellCount L = 0) xs Ls ∧
        Ls.flatten.Nodup ∧ ω ∈ chainEvent E Cdep Ls.flatten ∧
        ∀ c ∈ Ls.flatten, ∃ x ∈ xs,
          latticeDist x (cellCenter Cdep c) ≤ (1 + Cbox + Cdep) * 3 ^ (j + 1) := by
  classical
  intro xs
  induction xs with
  | nil =>
      intro _ _
      exact ⟨[], List.Forall₂.nil, by simp, by intro c hc; simp at hc, by intro c hc; simp at hc⟩
  | cons x rest ih =>
      intro hsep hband
      obtain ⟨hxrest, hrest⟩ := List.pairwise_cons.mp hsep
      obtain ⟨Ls, hF, hnd, hev, hloc⟩ :=
        ih hrest fun y hy => hband y (List.mem_cons_of_mem x hy)
      obtain ⟨hbr, hbc⟩ := hband x List.mem_cons_self
      obtain ⟨L, hcc, hLnd, hLev, hgc, hLloc⟩ :=
        exists_bandCrossChain E Cbox Cdep hd hCbox ω x (3 ^ (j + 1)) (3 ^ j)
          (Nat.one_le_pow _ _ (by norm_num)) hbr hbc
      have hdisj : ∀ a ∈ L, ∀ b ∈ Ls.flatten, a ≠ b := by
        intro c hcL c' hcF hcc'
        subst hcc'
        obtain ⟨y, hy, hyc⟩ := hloc c hcF
        have h1 : latticeDist x (cellCenter Cdep c) ≤ (1 + Cbox + Cdep) * 3 ^ (j + 1) :=
          hLloc c hcL
        have htri := latticeDist_triangle x (cellCenter Cdep c) y
        rw [latticeDist_comm (cellCenter Cdep c) y] at htri
        have hB : bandSep Cbox Cdep j = 2 * ((1 + Cbox + Cdep) * 3 ^ (j + 1)) := by
          rw [bandSep]; ring
        have hxy := hxrest y hy
        rw [hB] at hxy
        omega
      refine ⟨L :: Ls, List.Forall₂.cons ⟨hcc, hgc⟩ hF, ?_, ?_, ?_⟩
      · rw [List.flatten_cons]
        exact List.nodup_append.mpr ⟨hLnd, hnd, hdisj⟩
      · intro c hc
        rw [List.flatten_cons] at hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hLev c hc
        · exact hev c hc
      · intro c hc
        rw [List.flatten_cons] at hc
        rcases List.mem_append.mp hc with hc | hc
        · exact ⟨x, List.mem_cons_self, hLloc c hc⟩
        · obtain ⟨y, hy, hyc⟩ := hloc c hc
          exact ⟨y, List.mem_cons_of_mem x hy, hyc⟩

/-! ## The union over the separated root sets -/

/-- The event that a prescribed, `s`-separated set of geodesic indices all carry band-`j`
sites.  The separation is recorded inside the event, so that the union below can be indexed by
*all* index sets of the right size and its cardinality is exactly a binomial coefficient. -/
def bandRootEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (v w : Lattice d) (j s : ℕ)
    (S : Finset ℕ) : Set Ω :=
  {ω | (∀ a ∈ S, ∀ b ∈ S, a < b → a + s < b) ∧
      ∀ k ∈ S, ω ∈ bandSiteEvent E Cbox (latticeGeodesic v w k) j}

/-- **The band excess produces a separated set of band sites.**  Greedy selection along the
one-dimensional geodesic: `m (s+1)` band sites contain `m` that are `s`-separated. -/
theorem bandExcessEvent_subset_biUnion (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (v w : Lattice d) (j m s : ℕ) :
    bandExcessEvent E Cbox v w j (m * (s + 1)) ⊆
      ⋃ S ∈ (Finset.range (latticeDist v w + 1)).powersetCard m,
        bandRootEvent E Cbox v w j s S := by
  classical
  intro ω hω
  obtain ⟨T, hTsub, hTcard, hTsep⟩ := exists_separated_subset s m _ hω
  have hTrange : T ⊆ Finset.range (latticeDist v w + 1) :=
    hTsub.trans (Finset.filter_subset _ _)
  refine Set.mem_iUnion₂.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨hTrange, hTcard⟩, hTsep, ?_⟩
  intro k hk
  exact (Finset.mem_filter.mp (hTsub hk)).2

/-! ## The roots of a separated index set -/

/-- The geodesic sites at a set of indices, listed in increasing order. -/
def bandRoots (v w : Lattice d) (S : Finset ℕ) : List (Lattice d) :=
  (S.sort (· ≤ ·)).map (latticeGeodesic v w)

theorem length_bandRoots (v w : Lattice d) (S : Finset ℕ) :
    (bandRoots v w S).length = S.card := by
  rw [bandRoots, List.length_map, Finset.length_sort]

/-- **Index separation along the geodesic is `ℓ∞` separation.**  This is the one-dimensional
gain: separating `m` roots along the geodesic costs a factor `s`, not `s ^ d`. -/
theorem pairwise_bandRoots {v w : Lattice d} {S : Finset ℕ} {s : ℕ}
    (hS : S ⊆ Finset.range (latticeDist v w + 1))
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a < b → a + s < b) :
    (bandRoots v w S).Pairwise (fun a b => s < latticeDist a b) := by
  classical
  rw [bandRoots, List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ (Finset.sortedLT_sort S).pairwise
  intro a b ha hb hab
  have haS : a ∈ S := (Finset.mem_sort (· ≤ ·)).mp ha
  have hbS : b ∈ S := (Finset.mem_sort (· ≤ ·)).mp hb
  have hbn : b ≤ latticeDist v w :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (hS hbS))
  have hsub := sub_le_latticeDist_latticeGeodesic (v := v) (w := w) (k := a) (k' := b)
    (le_of_lt hab) hbn
  have := hsep a haS b hbS hab
  omega

/-- Every root of a separated index set carries a band site. -/
theorem forall_mem_bandRoots_bandSiteEvent {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {v w : Lattice d} {j s : ℕ} {S : Finset ℕ} {ω : Ω}
    (hω : ω ∈ bandRootEvent E Cbox v w j s S) :
    ∀ x ∈ bandRoots v w S, ω ∈ bandSiteEvent E Cbox x j := by
  classical
  intro x hx
  rw [bandRoots, List.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  exact hω.2 k ((Finset.mem_sort (· ≤ ·)).mp hk)

/-! ## The tail of a band excess -/

/-- **The `m`-fold bound at one separated set of roots.**

The `m` certificates are cell-disjoint, so their joint occurrence costs the `m`-th power of the
one-certificate bound of `Section9ChemicalCrossFamilyTail`; the gain per certificate is the
full radial coverage `3 ^ j`, because a bad component contributes no good-vertex cell. -/
theorem measure_bandRootEvent_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep : ℕ)
    {Cprob cprob q : ℝ} (hd : 1 ≤ d) (hCbox : 1 ≤ Cbox) (hcq : 0 ≤ cprob * q)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hpi : 8 * crossBranch d 1 * crossBranch d 1 *
      crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤ 2 * crossBranch d 1)
    (v w : Lattice d) (j m : ℕ) (S : Finset ℕ)
    (hS : S ∈ (Finset.range (latticeDist v w + 1)).powersetCard m) :
    mu (bandRootEvent E Cbox v w j (bandSep Cbox Cdep j) S) ≤
      (ENNReal.ofReal (Real.exp (-(cprob / 2 / 2 ^ d) * q *
          (((3 ^ j : ℕ) : ℝ) / crossAc Cbox Cdep 1))) *
        ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ≥0∞) * 2 *
          (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q))) ^ m := by
  classical
  obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
  have hlen : (bandRoots v w S).length = m := by rw [length_bandRoots, hScard]
  have hmain := measure_le_of_forall_exists_crossChainFamily mu E Cbox Cdep hcq hCbox hsc hr
    hprob hpi (3 ^ j) (bandRoots v w S) (bandRootEvent E Cbox v w j (bandSep Cbox Cdep j) S)
    (fun ω hω => by
      obtain ⟨Ls, hF, hnd, hev, -⟩ :=
        exists_crossChainFamily_of_bandSites E Cbox Cdep hd hCbox ω j (bandRoots v w S)
          (pairwise_bandRoots hSsub hω.1) (forall_mem_bandRoots_bandSiteEvent hω)
      exact ⟨Ls, hF, hnd, hev⟩)
  rwa [hlen] at hmain

/-- **The tail of a band excess.**

Union bound over the separated sets of roots: the entropy is the binomial coefficient
`C(n+1, m)`, so the cost per root is the *ratio* `(n+1)/m` and not `n+1`. -/
theorem measure_bandExcessEvent_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep : ℕ)
    {Cprob cprob q KS : ℝ} (hd : 1 ≤ d) (hCbox : 1 ≤ Cbox) (hcq : 0 ≤ cprob * q)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hpi : 8 * crossBranch d 1 * crossBranch d 1 *
      crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤ 2 * crossBranch d 1)
    (hKS0 : 0 ≤ KS)
    (hKS : 1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤ ENNReal.ofReal KS)
    (v w : Lattice d) (j m : ℕ) (hm : 1 ≤ m) :
    mu (bandExcessEvent E Cbox v w j (m * (bandSep Cbox Cdep j + 1))) ≤
      ENNReal.ofReal ((3 * ((latticeDist v w + 1 : ℕ) : ℝ) / (m : ℝ) *
        ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2 * KS) *
        Real.exp (-(cprob / 2 / 2 ^ d) * q *
          (((3 ^ j : ℕ) : ℝ) / crossAc Cbox Cdep 1))) ^ m) := by
  classical
  set n : ℕ := latticeDist v w with hn
  set g : ℝ := Real.exp (-(cprob / 2 / 2 ^ d) * q *
    (((3 ^ j : ℕ) : ℝ) / crossAc Cbox Cdep 1)) with hg
  set kr : ℝ := (((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2 * KS with hkr
  have hgpos : 0 < g := Real.exp_pos _
  have hkr0 : 0 ≤ kr := by
    have h1 : (0 : ℝ) ≤ (((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) := Nat.cast_nonneg _
    rw [hkr]; positivity
  have hcell : ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ≥0∞) * 2 *
      (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q)) ≤ ENNReal.ofReal kr := by
    have h1 : ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ≥0∞) * 2) =
        ENNReal.ofReal ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
        ENNReal.ofReal_ofNat]
    rw [h1]
    calc ENNReal.ofReal ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2) *
          (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q)
        ≤ ENNReal.ofReal ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2) *
            ENNReal.ofReal KS := mul_le_mul' le_rfl hKS
      _ = ENNReal.ofReal ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ) * 2 * KS) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  have hstep : ∀ S ∈ (Finset.range (n + 1)).powersetCard m,
      mu (bandRootEvent E Cbox v w j (bandSep Cbox Cdep j) S) ≤
        ENNReal.ofReal ((g * kr) ^ m) := by
    intro S hS
    refine le_trans (measure_bandRootEvent_le mu E Cbox Cdep hd hCbox hcq hsc hr hprob hpi
      v w j m S (by rwa [← hn])) ?_
    have hmul : ENNReal.ofReal g *
        ((((2 ^ d * (3 ^ j + 1) ^ d : ℕ)) : ℝ≥0∞) * 2 *
          (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q)) ≤
        ENNReal.ofReal (g * kr) := by
      rw [ENNReal.ofReal_mul hgpos.le]
      exact mul_le_mul' le_rfl hcell
    refine le_trans (pow_le_pow_left' hmul m) ?_
    rw [← ENNReal.ofReal_pow (by positivity)]
  have hsub := bandExcessEvent_subset_biUnion E Cbox v w j m (bandSep Cbox Cdep j)
  have hcount : ((Finset.range (n + 1)).powersetCard m).card = (n + 1).choose m := by
    rw [Finset.card_powersetCard, Finset.card_range]
  calc mu (bandExcessEvent E Cbox v w j (m * (bandSep Cbox Cdep j + 1)))
      ≤ mu (⋃ S ∈ (Finset.range (n + 1)).powersetCard m,
          bandRootEvent E Cbox v w j (bandSep Cbox Cdep j) S) := measure_mono (by rwa [← hn] at hsub)
    _ ≤ ∑ S ∈ (Finset.range (n + 1)).powersetCard m,
          mu (bandRootEvent E Cbox v w j (bandSep Cbox Cdep j) S) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _S ∈ (Finset.range (n + 1)).powersetCard m, ENNReal.ofReal ((g * kr) ^ m) :=
        Finset.sum_le_sum hstep
    _ = (((n + 1).choose m : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((g * kr) ^ m) := by
        rw [Finset.sum_const, hcount, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((3 * ((n + 1 : ℕ) : ℝ) / (m : ℝ)) ^ m) *
          ENNReal.ofReal ((g * kr) ^ m) := by
        refine mul_le_mul' ?_ le_rfl
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (choose_le_pow_div (n + 1) m hm)
    _ = ENNReal.ofReal ((3 * ((n + 1 : ℕ) : ℝ) / (m : ℝ) * kr * g) ^ m) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
        congr 2
        ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
