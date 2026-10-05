module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalChainFamily

@[expose] public section

/-!
# The tail of a family of crossing certificates

bundle P-407.  `Section9ChemicalCrossingTail` bounds the weight of **one** crossing
certificate rooted at one lattice point, and `Section9ChemicalBadChain` turns that weight
bound into a probability bound for any event that produces such a certificate.  The linear
length budget consumes the same estimate for an `m`-fold family of certificates rooted at
`m` prescribed points of the `ℓ∞` geodesic: each root contributes its own gain, so the
bound is the `m`-th power of the one-root bound.

Three facts are proved here.

* `tsum_forall₂_prod_le` — the abstract factorisation: if the weight sum of the lists
  satisfying `P a` is at most `B` for every root `a`, then the weight sum of the families
  matched to a list `xs` of roots by `List.Forall₂ P` is at most `B ^ xs.length`.  This is
  the list induction of `tsum_chainFamily_le` with the admissibility predicate abstracted.
* `tsum_crossChainFamily_le` — the same statement for crossing certificates, obtained by
  feeding `tsum_crossChain_le` into the previous item.
* `measure_le_of_forall_exists_crossChainFamily` — the `m`-fold union bound: an event all
  of whose outcomes produce a cell-disjoint family of good-vertex-free certificates rooted
  at `xs` has probability at most the `xs.length`-th power of the one-certificate bound.
  Because the certificates carry no good vertex, `le_sum_cellTau` gives the clean coverage
  `(l : ℝ) ≤ crossAc Cbox Cdep 1 * (L.map cellTau).sum`, hence the gain
  `exp (-c q (l / crossAc Cbox Cdep 1))` per root.

## Source

`mfd:in-deterministic` and `s.tightness`; .
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {d : ℕ} {Ω : Type*}

/-! ## The abstract factorisation of a family weight sum -/

/-- **A family weight sum factorises over the roots.**

If, for every root `a`, the total weight of the lists `L` with `P a L` is at most `B`, then
the total weight of the families matched to the roots `xs` by `List.Forall₂ P` is at most
`B ^ xs.length`.  This is the list induction of `tsum_chainFamily_le`, with the
admissibility predicate left abstract; no disjointness is imposed on the families summed
over, so the bound also covers the disjoint ones. -/
theorem tsum_forall₂_prod_le {alpha : Type*} [Countable alpha]
    (P : alpha → List (CrossCell d) → Prop) (w : CrossCell d → ℝ≥0∞) (B : ℝ≥0∞)
    (hB : ∀ a : alpha,
      (∑' L : List (CrossCell d), if P a L then (L.map w).prod else 0) ≤ B) :
    ∀ xs : List alpha,
      (∑' Ls : List (List (CrossCell d)),
        if List.Forall₂ P xs Ls then
          (Ls.map (fun L => (L.map w).prod)).prod else 0) ≤ B ^ xs.length := by
  classical
  intro xs
  induction xs with
  | nil =>
      have hterm : ∀ Ls : List (List (CrossCell d)),
          (if List.Forall₂ P ([] : List alpha) Ls then
            (Ls.map (fun L => (L.map w).prod)).prod
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
      simp only [Finset.sum_singleton, ite_true, List.length_nil, pow_zero, le_refl]
  | cons a xs ih =>
      have hnil : (if List.Forall₂ P (a :: xs) ([] : List (List (CrossCell d))) then
            (([] : List (List (CrossCell d))).map
              (fun L => (L.map w).prod)).prod
          else 0) = 0 := by
        rw [ite_eq_right]
        intro hc
        have := List.forall₂_nil_right_iff.mp hc
        exact absurd this (by simp)
      have hterm : ∀ p : List (CrossCell d) × List (List (CrossCell d)),
          (if List.Forall₂ P (a :: xs) (p.1 :: p.2) then
            ((p.1 :: p.2).map (fun L => (L.map w).prod)).prod
          else 0) =
          (if P a p.1 then (p.1.map w).prod else 0) *
          (if List.Forall₂ P xs p.2 then
            (p.2.map (fun L => (L.map w).prod)).prod
          else 0) := by
        rintro ⟨L, Ls⟩
        by_cases h1 : P a L
        · by_cases h2 : List.Forall₂ P xs Ls
          · rw [ite_eq_left (List.Forall₂.cons h1 h2), ite_eq_left h1, ite_eq_left h2]
            simp [List.map_cons, List.prod_cons]
          · rw [ite_eq_right (fun hc => h2 (List.forall₂_cons.mp hc).2), ite_eq_left h1, ite_eq_right h2,
              mul_zero]
        · rw [ite_eq_right (fun hc => h1 (List.forall₂_cons.mp hc).1), ite_eq_right h1, zero_mul]
      rw [tsum_list_eq (fun Ls => if List.Forall₂ P (a :: xs) Ls then
          (Ls.map (fun L => (L.map w).prod)).prod else 0),
        hnil, zero_add, tsum_congr hterm, ENNReal.tsum_prod']
      simp only []
      rw [tsum_congr (fun c : List (CrossCell d) => ENNReal.tsum_mul_left),
        ENNReal.tsum_mul_right, List.length_cons]
      calc (∑' L : List (CrossCell d), if P a L then (L.map w).prod else 0) *
            (∑' Ls : List (List (CrossCell d)),
              if List.Forall₂ P xs Ls then
                (Ls.map (fun L => (L.map w).prod)).prod else 0)
          ≤ B * B ^ xs.length := mul_le_mul' (hB a) ih
        _ = B ^ (xs.length + 1) := by ring

/-! ## The weight of all families of crossing certificates -/

/-- **The family weight sum for crossing certificates.**

The total weight of the families of crossing certificates rooted, in order, at the lattice
points of `xs`, each with good-vertex budget `gb`, is at most the `xs.length`-th power of
the one-certificate bound of `tsum_crossChain_le`. -/
theorem tsum_crossChainFamily_le (Cbox Cdep J : ℕ) (Cprob cprob q : ℝ) (l gb : ℕ)
    (hpi : 8 * crossBranch d J * crossBranch d J *
      crossScaleSum d Cbox Cdep Cprob cprob q ≤ 2 * crossBranch d J)
    (xs : List (Lattice d)) :
    (∑' Ls : List (List (CrossCell d)),
      if List.Forall₂ (fun (x : Lattice d) (L : List (CrossCell d)) =>
          CrossChain Cbox Cdep J x l L ∧ goodCellCount L ≤ gb) xs Ls then
        (Ls.map (fun L => (L.map (cellWeight d Cdep Cprob cprob q)).prod)).prod
      else 0) ≤
      ((((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * (2 * (4 * crossBranch d J) ^ gb) *
        (1 + crossScaleSum d Cbox Cdep Cprob cprob q)) ^ xs.length := by
  have key := tsum_forall₂_prod_le
    (fun (x : Lattice d) (L : List (CrossCell d)) =>
      CrossChain Cbox Cdep J x l L ∧ goodCellCount L ≤ gb)
    (cellWeight d Cdep Cprob cprob q)
    ((((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * (2 * (4 * crossBranch d J) ^ gb) *
      (1 + crossScaleSum d Cbox Cdep Cprob cprob q))
    (fun x => by
      refine le_trans (le_of_eq (tsum_congr fun L => ?_))
        (tsum_crossChain_le Cbox Cdep J Cprob cprob q x l gb hpi)
      congr) xs
  refine le_trans (le_of_eq (tsum_congr fun Ls => ?_)) key
  congr

/-! ## The `m`-fold certificate union bound -/

/-- **The union bound over families of certificates.**

Verbatim the assembly of `Section9ChemicalBadChain.measure_le_of_forall_exists_crossChain`,
run for a family of `xs.length` certificates: the joint occurrence of a cell-disjoint family
costs the product of the individual weights (`measure_chainEvent_flatten_le`), each
certificate carries its own gain, and the total weight of all families is the power bound
`tsum_crossChainFamily_le`.  The certificates are required to carry **no** good vertex, so
the coverage `le_sum_cellTau` gives the clean gain `exp (-c q (l / crossAc Cbox Cdep 1))`
per root, with no good-budget loss and constant `2` in place of `2 (4 κ) ^ gb`. -/
theorem measure_le_of_forall_exists_crossChainFamily [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (E : ℕ → Lattice d → Set Ω) (Cbox Cdep : ℕ)
    {Cprob cprob q : ℝ} (hcq : 0 ≤ cprob * q) (hCbox : 1 ≤ Cbox)
    (hsc : IndependentEventScales mu E)
    (hr : MultiscaleFiniteRangeIndependentEvents mu (fun j => Cdep * 3 ^ j) E)
    (hprob : ∀ j u, mu (E j u) ≤
      ENNReal.ofReal (Cprob * Real.exp (-cprob * q * 3 ^ ((3 : ℝ) * j / 2))))
    (hpi : 8 * crossBranch d 1 * crossBranch d 1 *
      crossScaleSum d Cbox Cdep Cprob (cprob / 2) q ≤ 2 * crossBranch d 1)
    (l : ℕ) (xs : List (Lattice d)) (A : Set Ω)
    (hA : ∀ ω ∈ A, ∃ Ls : List (List (CrossCell d)),
      List.Forall₂ (fun (x : Lattice d) (L : List (CrossCell d)) =>
        CrossChain Cbox Cdep 1 x l L ∧ goodCellCount L = 0) xs Ls ∧
      Ls.flatten.Nodup ∧ ω ∈ chainEvent E Cdep Ls.flatten) :
    mu A ≤
      (ENNReal.ofReal (Real.exp (-(cprob / 2 / 2 ^ d) * q *
          ((l : ℝ) / crossAc Cbox Cdep 1))) *
        ((((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * 2 *
          (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q))) ^ xs.length := by
  classical
  set w : CrossCell d → ℝ≥0∞ := cellWeight d Cdep Cprob cprob q with hw
  set wh : CrossCell d → ℝ≥0∞ := cellWeight d Cdep Cprob (cprob / 2) q with hwh
  set G : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(cprob / 2 / 2 ^ d) * q *
    ((l : ℝ) / crossAc Cbox Cdep 1))) with hG
  set C : ℝ≥0∞ := (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) * 2 *
    (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q) with hC
  set S : Set (List (List (CrossCell d))) :=
    {Ls | List.Forall₂ (fun (x : Lattice d) (L : List (CrossCell d)) =>
      CrossChain Cbox Cdep 1 x l L ∧ goodCellCount L = 0) xs Ls ∧ Ls.flatten.Nodup}
    with hS
  have hAcpos : 0 < crossAc Cbox Cdep 1 := crossAc_pos hCbox
  -- the event is covered by the families of certificates
  have hsub : A ⊆ ⋃ Ls ∈ S, chainEvent E Cdep Ls.flatten := by
    intro ω hω
    obtain ⟨Ls, hf, hnd, hev⟩ := hA ω hω
    exact Set.mem_biUnion (show Ls ∈ S from ⟨hf, hnd⟩) hev
  -- one certificate carries the gain
  have hgain : ∀ (x : Lattice d) (L : List (CrossCell d)),
      CrossChain Cbox Cdep 1 x l L → goodCellCount L = 0 →
      (L.map w).prod ≤ G * (L.map wh).prod := by
    intro x L hcc hgc
    rw [hw, hwh, prod_map_cellWeight_eq d Cdep Cprob cprob q L,
      prod_map_crossGain d cprob q L]
    refine mul_le_mul' ?_ le_rfl
    rw [hG]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hkey := le_sum_cellTau hcc (le_of_eq hgc)
    have hbq : 0 ≤ cprob / 2 / 2 ^ d * q := by
      have h2 : (0 : ℝ) < 2 ^ d := by positivity
      have hrw : cprob / 2 / 2 ^ d * q = cprob * q / 2 / 2 ^ d := by ring
      rw [hrw]
      positivity
    have hdiv : (l : ℝ) / crossAc Cbox Cdep 1 ≤ (L.map cellTau).sum := by
      rw [div_le_iff₀ hAcpos, crossAc]
      push_cast at hkey ⊢
      linarith
    nlinarith [hdiv, hbq]
  -- the family carries the product of the gains
  have hfam : ∀ (ys : List (Lattice d)) (Ls : List (List (CrossCell d))),
      List.Forall₂ (fun (x : Lattice d) (L : List (CrossCell d)) =>
        CrossChain Cbox Cdep 1 x l L ∧ goodCellCount L = 0) ys Ls →
      (Ls.map (fun L => (L.map w).prod)).prod ≤
        G ^ ys.length * (Ls.map (fun L => (L.map wh).prod)).prod := by
    intro ys Ls h
    induction h with
    | nil => simp
    | @cons x L ys' Ls' hxL h ih =>
        rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
          List.length_cons]
        calc (L.map w).prod * (Ls'.map (fun L => (L.map w).prod)).prod
            ≤ (G * (L.map wh).prod) *
                (G ^ ys'.length * (Ls'.map (fun L => (L.map wh).prod)).prod) :=
              mul_le_mul' (hgain x L hxL.1 hxL.2) ih
          _ = G ^ (ys'.length + 1) *
                ((L.map wh).prod * (Ls'.map (fun L => (L.map wh).prod)).prod) := by
              ring
  -- the constant at good-vertex budget `0`
  have hconst : (((2 ^ d * (l + 1) ^ d : ℕ)) : ℝ≥0∞) *
      (2 * (4 * crossBranch d 1) ^ 0) *
      (1 + crossScaleSum d Cbox Cdep Cprob (cprob / 2) q) = C := by
    rw [hC, pow_zero, mul_one]
  -- assemble
  calc mu A
      ≤ mu (⋃ Ls ∈ S, chainEvent E Cdep Ls.flatten) := measure_mono hsub
    _ ≤ ∑' Ls : S, mu (chainEvent E Cdep (Ls : List (List (CrossCell d))).flatten) :=
        measure_biUnion_le mu S.to_countable _
    _ ≤ ∑' Ls : S, G ^ xs.length *
          ((Ls : List (List (CrossCell d))).map
            (fun L => (L.map wh).prod)).prod := by
        refine ENNReal.tsum_le_tsum fun Ls => ?_
        exact le_trans (measure_chainEvent_flatten_le mu Cdep hsc hr hprob
          (Ls : List (List (CrossCell d))) Ls.2.2) (hfam xs _ Ls.2.1)
    _ = G ^ xs.length * ∑' Ls : S,
          ((Ls : List (List (CrossCell d))).map
            (fun L => (L.map wh).prod)).prod := ENNReal.tsum_mul_left
    _ ≤ G ^ xs.length * ∑' Ls : List (List (CrossCell d)),
          (if List.Forall₂ (fun (x : Lattice d) (L : List (CrossCell d)) =>
              CrossChain Cbox Cdep 1 x l L ∧ goodCellCount L ≤ 0) xs Ls then
            (Ls.map (fun L => (L.map wh).prod)).prod else 0) := by
        refine mul_le_mul' le_rfl ?_
        rw [tsum_subtype S (fun Ls => (Ls.map (fun L => (L.map wh).prod)).prod)]
        refine ENNReal.tsum_le_tsum fun Ls => ?_
        by_cases hLS : Ls ∈ S
        · rw [Set.indicator_of_mem hLS,
            ite_eq_left (hLS.1.imp (fun a b h => ⟨h.1, le_of_eq h.2⟩))]
        · rw [Set.indicator_of_notMem hLS]
          exact zero_le
    _ ≤ G ^ xs.length * C ^ xs.length := by
        refine mul_le_mul' le_rfl ?_
        rw [← hconst]
        exact tsum_crossChainFamily_le Cbox Cdep 1 Cprob (cprob / 2) q l 0 hpi xs
    _ = (G * C) ^ xs.length := (mul_pow G C xs.length).symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
