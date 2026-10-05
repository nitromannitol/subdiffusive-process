module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalBadChain

@[expose] public section

/-!
# Families of contour chains, and their joint weight
`Section9ChemicalCrossingTail` bounds the weight of **one** contour chain from
one root cell.  The linear length budget needs the joint bound for `m` chains rooted at `m`
sites of the `ℓ∞` geodesic: the failure of the budget forces a *total* detour cost above
`ε L`, and the gain that has to be produced is the sum of the individual chain coverages.

Two facts are proved here.

* `measure_chainEvent_flatten_le` — if the concatenation of a family of chains is
  repetition-free, its joint occurrence costs the **product** of the individual chain weights.
  This is `measure_chainEvent_le` applied to the flattened list; the point is that the
  separation the product formula needs is supplied cell by cell, so no relation between
  different chains of the family is required beyond their being cell-disjoint.
* `tsum_chainFamily_le` — the total weight of all families of chains rooted at a prescribed
  list of cells is at most the product of the one-chain sums `chainSumAll`.  The proof is the
  list induction of `tsum_list_eq`, one root at a time.

Together these turn a family certificate into
`∏_{i} (2 (rad cᵢ + 1)^d (4 κ)^{gb})` times the joint gain, which is the shape the layered
union bound over `m`-tuples of separated chains consumes.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Ω : Type*}

/-! ## The predicate summed by `chainSumAll` -/

/-- A chain admissible from the root cell `c`, with good-vertex budget `gb`: exactly the
predicate whose weights `chainSumAll` adds up. -/
def RootedChain (Cbox Cdep J gb : ℕ) (c : CrossCell d) (L : List (CrossCell d)) : Prop :=
  L.IsChain (cellReach Cbox Cdep J) ∧
    (∀ c' ∈ L.head?, cellReach Cbox Cdep J c c') ∧ goodCellCount L ≤ gb

theorem tsum_rootedChain_le (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ) (gb : ℕ)
    (c : CrossCell d) :
    (∑' L : List (CrossCell d),
        if RootedChain Cbox Cdep J gb c L then
          (L.map (cellWeight d Cdep Cprob cprob q)).prod else 0) ≤
      chainSumAll Cbox Cdep J Cprob cprob q gb c := by
  rw [chainSumAll]
  refine ENNReal.tsum_le_tsum fun L => ?_
  by_cases h : RootedChain Cbox Cdep J gb c L
  · have hc : List.IsChain (cellReach Cbox Cdep J) L ∧
        (∀ c' ∈ L.head?, cellReach Cbox Cdep J c c') ∧ goodCellCount L ≤ gb := h
    rw [ite_eq_left h, ite_eq_left hc]
  · rw [ite_eq_right h]
    exact zero_le

/-! ## The joint probability of a family of chains -/

/-- The event that every cell of every chain of the family occurs. -/
theorem chainEvent_flatten (E : ℕ → Lattice d → Set Ω) (Cdep : ℕ)
    (Ls : List (List (CrossCell d))) :
    chainEvent E Cdep Ls.flatten = ⋂ L ∈ Ls, chainEvent E Cdep L := by
  ext ω
  simp only [chainEvent, mem_ofPred_eq, Set.mem_iInter, List.mem_flatten]
  constructor
  · intro h L hL
    exact fun c hc => h c ⟨L, hL, hc⟩
  · rintro h c ⟨L, hL, hc⟩
    exact h L hL c hc

/-- **A cell-disjoint family of chains costs the product of the chain weights.** -/
theorem measure_chainEvent_flatten_le [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] {E : ℕ → Lattice d → Set Ω} (Cdep : ℕ)
    {Cprob cprob q : ℝ}
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (Ls : List (List (CrossCell d))) (hnd : Ls.flatten.Nodup) :
    mu (chainEvent E Cdep Ls.flatten) ≤
      (Ls.map (fun L => (L.map (cellWeight d Cdep Cprob cprob q)).prod)).prod := by
  refine (measure_chainEvent_le mu Cdep hsc hr hprob Ls.flatten hnd).trans ?_
  rw [List.map_flatten, List.prod_flatten, List.map_map]
  exact le_rfl

/-! ## The weight of all families rooted at a prescribed list of cells -/

/-- **The joint weight sum factorises over the roots.**

The sum of `∏ᵢ (weight of the i-th chain)` over all families of chains rooted, in order, at
the cells of `cs` is at most `∏ᵢ chainSumAll cᵢ`.  No cell-disjointness is imposed on the
families summed over, so the bound also covers the disjoint ones. -/
theorem tsum_chainFamily_le (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ) (gb : ℕ) :
    ∀ cs : List (CrossCell d),
      (∑' Ls : List (List (CrossCell d)),
        if List.Forall₂ (RootedChain Cbox Cdep J gb) cs Ls then
          (Ls.map (fun L => (L.map (cellWeight d Cdep Cprob cprob q)).prod)).prod
        else 0) ≤
      (cs.map (chainSumAll Cbox Cdep J Cprob cprob q gb)).prod := by
  classical
  intro cs
  induction cs with
  | nil =>
      have hterm : ∀ Ls : List (List (CrossCell d)),
          (if List.Forall₂ (RootedChain Cbox Cdep J gb) ([] : List (CrossCell d)) Ls then
            (Ls.map (fun L => (L.map (cellWeight d Cdep Cprob cprob q)).prod)).prod
          else 0) = if Ls = [] then 1 else 0 := by
        intro Ls
        by_cases h : Ls = []
        · subst h
          rw [ite_eq_left (List.Forall₂.nil), ite_eq_left rfl]
          simp
        · rw [ite_eq_right (fun hc => h (List.forall₂_nil_left_iff.mp hc)), ite_eq_right h]
      rw [tsum_congr hterm,
        tsum_eq_sum
          (f := fun Ls : List (List (CrossCell d)) => if Ls = [] then (1 : ℝ≥0∞) else 0)
          (s := ({[]} : Finset (List (List (CrossCell d)))))
          (fun b hb => ite_eq_right (by simpa using hb))]
      simp only [Finset.sum_singleton, List.map_nil, List.prod_nil, ite_true, le_refl]
  | cons c cs ih =>
      have hnil : (if List.Forall₂ (RootedChain Cbox Cdep J gb) (c :: cs)
          ([] : List (List (CrossCell d))) then
            (([] : List (List (CrossCell d))).map
              (fun L => (L.map (cellWeight d Cdep Cprob cprob q)).prod)).prod
          else 0) = 0 := by
        rw [ite_eq_right]
        intro hc
        have := List.forall₂_nil_right_iff.mp hc
        exact absurd this (by simp)
      have hterm : ∀ p : List (CrossCell d) × List (List (CrossCell d)),
          (if List.Forall₂ (RootedChain Cbox Cdep J gb) (c :: cs) (p.1 :: p.2) then
            ((p.1 :: p.2).map
              (fun L => (L.map (cellWeight d Cdep Cprob cprob q)).prod)).prod
          else 0) =
          (if RootedChain Cbox Cdep J gb c p.1 then
            (p.1.map (cellWeight d Cdep Cprob cprob q)).prod else 0) *
          (if List.Forall₂ (RootedChain Cbox Cdep J gb) cs p.2 then
            (p.2.map (fun L => (L.map (cellWeight d Cdep Cprob cprob q)).prod)).prod
          else 0) := by
        rintro ⟨L, Ls⟩
        by_cases h1 : RootedChain Cbox Cdep J gb c L
        · by_cases h2 : List.Forall₂ (RootedChain Cbox Cdep J gb) cs Ls
          · rw [ite_eq_left (List.Forall₂.cons h1 h2), ite_eq_left h1, ite_eq_left h2]
            simp [List.map_cons, List.prod_cons]
          · rw [ite_eq_right (fun hc => h2 (List.forall₂_cons.mp hc).2), ite_eq_left h1, ite_eq_right h2,
              mul_zero]
        · rw [ite_eq_right (fun hc => h1 (List.forall₂_cons.mp hc).1), ite_eq_right h1, zero_mul]
      rw [tsum_list_eq (fun Ls => if List.Forall₂ (RootedChain Cbox Cdep J gb) (c :: cs) Ls then
          (Ls.map (fun L => (L.map (cellWeight d Cdep Cprob cprob q)).prod)).prod else 0),
        hnil, zero_add, tsum_congr hterm, ENNReal.tsum_prod']
      simp only []
      rw [tsum_congr (fun a : List (CrossCell d) => ENNReal.tsum_mul_left),
        ENNReal.tsum_mul_right, List.map_cons, List.prod_cons]
      exact mul_le_mul' (tsum_rootedChain_le Cbox Cdep J Cprob cprob q gb c) ih

/-- **The family bound in closed form.**  Every root cell contributes the one-chain bound of
`chainSumAll_le`. -/
theorem tsum_chainFamily_le_prod (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ)
    (hpi : 8 * crossBranch d J * crossBranch d J *
      crossScaleSum d Cbox Cdep Cprob cprob q ≤ 2 * crossBranch d J)
    (gb : ℕ) (cs : List (CrossCell d)) :
    (∑' Ls : List (List (CrossCell d)),
      if List.Forall₂ (RootedChain Cbox Cdep J gb) cs Ls then
        (Ls.map (fun L => (L.map (cellWeight d Cdep Cprob cprob q)).prod)).prod
      else 0) ≤
      (cs.map (fun c => 2 * (((cellRadius Cbox Cdep c + 1) ^ d : ℕ) : ℝ≥0∞) *
        (4 * crossBranch d J) ^ gb)).prod := by
  refine (tsum_chainFamily_le Cbox Cdep J Cprob cprob q gb cs).trans ?_
  exact List.prod_le_prod fun c _ => chainSumAll_le Cbox Cdep J Cprob cprob q hpi gb c

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
