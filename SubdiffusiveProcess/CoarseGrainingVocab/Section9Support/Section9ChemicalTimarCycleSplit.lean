module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimarCycleCells

@[expose] public section

/-!
# `[Timár, Lemma 2]` reduced to a symmetric statement about a two-piece partition of `ℤ^d`

`TimarBoundaryComponentConnectivity d` (`Section9ChemicalTimarComponent`) quantifies over a
finite `1`-step connected `S`, a site `c ∉ S`, and the component of `c` in `Sᶜ`.  This file
removes every one of those decorations.

## The reduction

Write `K = jStepComponent 1 Sᶜ c`.  Then:

* `K` is `1`-step connected (it is a component);
* **`Kᶜ` is `1`-step connected too** (`jStepReachableIn_compl_jStepComponent`): `Kᶜ` is
  `S` together with the other components of `Sᶜ`, and every site of `Kᶜ` walks straight towards
  a fixed site of `S` without ever entering `K` — the step map `latticeStepToward` of
  `Section9ChemicalTimarCycleCells` does the walking, and the component property of `K` forbids
  the walk from crossing into it;
* `visibleBoundary S c = innerBoundary K` (`visibleBoundary_eq_innerBoundary`).

So the whole statement is an instance of

    SplitBoundaryConnectivity d :
      ∀ K, K.Nonempty → Kᶜ.Nonempty → K `1`-step connected → Kᶜ `1`-step connected →
        innerBoundary K is `1`-step connected

(`timarBoundaryComponentConnectivity_of_splitBoundaryConnectivity`).  Neither finiteness nor
`2 ≤ d` appears: `SplitBoundaryConnectivity d` is a statement about a partition of `ℤ^d` into two
`1`-step connected pieces, symmetric in the two pieces.  It is proved here directly for `d = 0`
and `d = 1` (short arguments that need nothing), and for every `d` in
`Section9ChemicalTimarCycleBoundary`.

What this file contributes is that the statement has no side conditions left: no finiteness, no
distinguished component, no outer-boundary bookkeeping, and no dimension hypothesis.  The
symmetric statement itself is then *proved for every `d`* in
`Section9ChemicalTimarCycleBoundary` (`splitBoundaryConnectivity`), from the cycle-space theorem
of `Section9ChemicalTimarCycleCoboundary`.

## Source

`[TimarBoundary, Lemma 2]`;.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ}

/-! ## The complement of a complementary component is `1`-step connected -/

/-- **The complement of a component of `Sᶜ` is `1`-step connected**, for every `1`-step
connected `S`: walking straight towards a fixed site `s₀ ∈ S` never crosses into the component,
because a site of `Sᶜ` adjacent to the component belongs to it. -/
theorem jStepReachableIn_compl_jStepComponent_aux {S : Set (Lattice d)} {c s₀ : Lattice d}
    (hSconn : ∀ u ∈ S, ∀ v ∈ S, JStepReachableIn 1 S u v) (hs₀ : s₀ ∈ S) :
    ∀ (n : ℕ) (x : Lattice d), x ∈ (jStepComponent 1 Sᶜ c)ᶜ → latticeDist x s₀ ≤ n →
      JStepReachableIn 1 (jStepComponent 1 Sᶜ c)ᶜ x s₀ := by
  have hSK : S ⊆ (jStepComponent 1 Sᶜ c)ᶜ := fun s hs hmem => (jStepComponent_subset hmem) hs
  intro n
  induction n with
  | zero =>
    intro x hx hn
    have hxs : x = s₀ := eq_of_latticeDist_eq_zero (Nat.le_zero.mp hn)
    subst hxs
    exact jStepReachableIn_of_dist hx hx (by simp)
  | succ n ih =>
    intro x hx hn
    by_cases hxS : x ∈ S
    · exact jStepReachableIn_mono_set hSK (hSconn x hxS s₀ hs₀)
    · have hxSc : x ∈ Sᶜ := hxS
      have h' : latticeStepToward s₀ x ∈ (jStepComponent 1 Sᶜ c)ᶜ := by
        intro hmem
        refine hx (mem_jStepComponent_of_dist_le hmem hxSc ?_)
        rw [latticeDist_comm]
        exact latticeDist_latticeStepToward_le_one s₀ x
      have hdist : latticeDist (latticeStepToward s₀ x) s₀ ≤ n := by
        simpa using latticeDist_latticeStepToward_le_pred (t := s₀) (x := x) hn
      exact (jStepReachableIn_of_dist hx h' (latticeDist_latticeStepToward_le_one s₀ x)).trans
        (ih _ h' hdist)

/-- The complement of a component of `Sᶜ` is `1`-step connected. -/
theorem jStepReachableIn_compl_jStepComponent {S : Set (Lattice d)} {c : Lattice d}
    (hSne : S.Nonempty) (hSconn : ∀ u ∈ S, ∀ v ∈ S, JStepReachableIn 1 S u v) :
    ∀ u ∈ (jStepComponent 1 Sᶜ c)ᶜ, ∀ v ∈ (jStepComponent 1 Sᶜ c)ᶜ,
      JStepReachableIn 1 (jStepComponent 1 Sᶜ c)ᶜ u v := by
  obtain ⟨s₀, hs₀⟩ := hSne
  intro u hu v hv
  exact (jStepReachableIn_compl_jStepComponent_aux hSconn hs₀ _ u hu le_rfl).trans
    (jStepReachableIn_compl_jStepComponent_aux hSconn hs₀ _ v hv le_rfl).symm

/-- The inner boundary of `K` is the outer boundary of `Kᶜ`: the two pieces of the partition
carry the same boundary notion, read from either side. -/
theorem innerBoundary_eq_outerBoundary_compl (K : Set (Lattice d)) :
    innerBoundary K = outerBoundary Kᶜ := by
  ext x
  simp only [innerBoundary, outerBoundary, mem_ofPred_eq, Set.mem_compl_iff, not_not]

/-! ## The symmetric statement -/

/-- **`[Timár, Lemma 2]`, symmetric form.**  If `ℤ^d` is partitioned into two nonempty `1`-step
connected pieces `K` and `Kᶜ`, then the inner boundary of `K` is `1`-step connected.

This is `TimarBoundaryComponentConnectivity d` with every side condition removed: no finiteness,
no distinguished component, no dimension hypothesis, and symmetric in the two pieces. -/
def SplitBoundaryConnectivity (d : ℕ) : Prop :=
  ∀ K : Set (Lattice d), K.Nonempty → Kᶜ.Nonempty →
    (∀ u ∈ K, ∀ v ∈ K, JStepReachableIn 1 K u v) →
    (∀ u ∈ Kᶜ, ∀ v ∈ Kᶜ, JStepReachableIn 1 Kᶜ u v) →
      ∀ u ∈ innerBoundary K, ∀ v ∈ innerBoundary K,
        JStepReachableIn 1 (innerBoundary K) u v

/-- **The reduction.**  The symmetric statement implies the corrected `[Timár, Lemma 2]`. -/
theorem timarBoundaryComponentConnectivity_of_splitBoundaryConnectivity
    (h : SplitBoundaryConnectivity d) : TimarBoundaryComponentConnectivity d := by
  intro S _ hSne hSconn c hc u hu v hv
  have hKne : (jStepComponent 1 Sᶜ c).Nonempty := ⟨c, self_mem_jStepComponent hc⟩
  obtain ⟨s₀, hs₀⟩ := hSne
  have hSK : S ⊆ (jStepComponent 1 Sᶜ c)ᶜ := fun s hs hmem => (jStepComponent_subset hmem) hs
  have heq : visibleBoundary S c = innerBoundary (jStepComponent 1 Sᶜ c) :=
    visibleBoundary_eq_innerBoundary S c
  rw [heq] at hu hv ⊢
  exact h (jStepComponent 1 Sᶜ c) hKne ⟨s₀, hSK hs₀⟩
    (fun a ha b hb => jStepReachableIn_within_jStepComponent ha hb)
    (jStepReachableIn_compl_jStepComponent ⟨s₀, hs₀⟩ hSconn) u hu v hv

/-! ## The symmetric statement in dimensions zero and one -/

/-- In dimension `0` the lattice is a single site, so no partition into two nonempty pieces
exists and the statement is vacuous. -/
theorem splitBoundaryConnectivity_zero : SplitBoundaryConnectivity 0 := by
  have hall : ∀ x y : Lattice 0, x = y := fun x y => funext fun i => absurd i.2 (by omega)
  intro K _ hKc _ _ u hu v _
  obtain ⟨t, ht⟩ := hKc
  exact absurd ((hall u t) ▸ hu.1) ht

/-- **The symmetric statement holds on the line.**  A partition of `ℤ` into two `1`-step
connected pieces is a pair of complementary rays, so the inner boundary of either piece is a
single site. -/
theorem splitBoundaryConnectivity_one : SplitBoundaryConnectivity 1 := by
  intro K _ _ hKconn hKcconn u hu v hv
  have huv : u = v := by
    by_contra hcon
    obtain ⟨huK, s, hsK, hsu⟩ := hu
    obtain ⟨hvK, t, htK, htv⟩ := hv
    have hKpath : JStepReachableIn 1 K u v := hKconn u huK v hvK
    have hKcpath : JStepReachableIn 1 Kᶜ s t := hKcconn s hsK t htK
    have hs1 : (s 0 - u 0).natAbs ≤ 1 := latticeDist_le_iff.mp hsu 0
    have ht1 : (t 0 - v 0).natAbs ≤ 1 := latticeDist_le_iff.mp htv 0
    have hs2 : s 0 ≠ u 0 := fun hz => hsK (lattice_one_ext hz ▸ huK)
    have ht2 : t 0 ≠ v 0 := fun hz => htK (lattice_one_ext hz ▸ hvK)
    have hab : u 0 ≠ v 0 := fun hz => hcon (lattice_one_ext hz)
    have hI : min (u 0) (v 0) ≤ max (min (u 0) (v 0)) (min (s 0) (t 0)) ∧
        max (min (u 0) (v 0)) (min (s 0) (t 0)) ≤ max (u 0) (v 0) ∧
        min (s 0) (t 0) ≤ max (min (u 0) (v 0)) (min (s 0) (t 0)) ∧
        max (min (u 0) (v 0)) (min (s 0) (t 0)) ≤ max (s 0) (t 0) := by omega
    exact false_of_coord_mem_and_mem_compl
      (exists_mem_eq_of_jStepReachableIn_one' hKpath hI.1 hI.2.1)
      (exists_mem_eq_of_jStepReachableIn_one' hKcpath hI.2.2.1 hI.2.2.2)
  subst huv
  exact jStepReachableIn_self_iff.mpr hu

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
