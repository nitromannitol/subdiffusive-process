module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalDRSConditions
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolationConnectivity

@[expose] public section

/-!
# `[Timár, Lemma 2]` in finitary form, and what S1 actually needs

`Section9ChemicalDRSConditions.TimarBoundaryInput` is the one genuinely external
ingredient of `[DRS]` condition S1 in this development.  This file isolates its
lattice content — the *boundary connectivity* statement of `[Timár, Lemma 2]` — from
its percolation packaging, and proves everything about outer boundaries that the
packaging needs.

## The convention

Everything in `Section9Percolation` measures distance with `latticeDist`, the `ℓ^∞`
distance, so `1`-step adjacency is `*`-adjacency and there is a single boundary notion:
`outerBoundary S` is the set of sites off `S` at `ℓ^∞`-distance at most `1` from `S`.
`[Timár, Lemma 2]`'s two dual statements ("the outer boundary of a finite connected set
is `*`-connected" and "the outer `*`-boundary of a finite `*`-connected set is
connected") collapse in this convention to the single statement
`TimarBoundaryConnectivity` below.  The manuscript works at this level too: its proof
opens by "increasing `J` by a dimensional constant so that inner and outer vertex
boundaries are `J`-step connected" (`mfd:in-deterministic` and `s.tightness`).

## What is proved here

* the outer-boundary calculus: `outerBoundary_disjoint`, `mem_outerBoundary_iff`,
  `outerBoundary_subset_thickening`, and the diameter bound
  `hasLatticeDiameterAtMost_outerBoundary` (`diam ∂S ≤ diam S + 2`);
* `isPercolationGoodSite_of_mem_outerBoundary_badComponent` — **the outer boundary of a
  bad `J`-step component consists of good sites**, for every `J ≥ 1`.  This is the fact
  that makes a boundary detour a *good* detour, and it is what clause (ii) is for;
* `hasLatticeDiameterAtMost_outerBoundary_badComponent` — a detour around a bad
  component of diameter `≤ D` stays within diameter `D + 2` of it.

## What is left external, exactly

`TimarBoundaryConnectivity d` (below) is the pure lattice statement, with no measure,
no field and no percolation in it.  `[Timár, Lemma 2]`'s proof is a graph-theoretic
argument about `ℤ^d` and is the residual of item (C).

`TimarBoundaryInput` is *not* equal to `TimarBoundaryConnectivity`: it also contains the
manuscript's separation step (`mfd:in-deterministic` and `s.tightness`) — the coordinate path from `v` to `w`, the observation that the inner
boundary of each finite component of the complement of the good set lies in a single bad
component, and the detour of the coordinate path along the outer boundaries.  The
ingredients proved in this file are exactly the ones that step consumes; the step itself is
recorded, not proved.

## Source

* `mfd:in-deterministic` and `s.tightness`;
  `[TimarBoundary, Lemma 2]`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*}




/-- A `J`-step path is a `J'`-step path for every larger step count. -/
theorem isJStepListPath_mono {J J' : ℕ} (h : J ≤ J') {path : List (Lattice d)}
    (hp : IsJStepListPath J path) : IsJStepListPath J' path :=
  fun k hk => (hp k hk).trans h

/-- Reachability is monotone in the step count. -/
theorem jStepReachableIn_mono_step {J J' : ℕ} (hJ : J ≤ J') {S : Set (Lattice d)}
    {v w : Lattice d} (h : JStepReachableIn J S v w) : JStepReachableIn J' S v w := by
  obtain ⟨path, hhead, hlast, hstep, hmem⟩ := h
  exact ⟨path, hhead, hlast, isJStepListPath_mono hJ hstep, hmem⟩

/-- Reachability is monotone in the ambient site set. -/
theorem jStepReachableIn_mono_set {J : ℕ} {S T : Set (Lattice d)} (hST : S ⊆ T)
    {v w : Lattice d} (h : JStepReachableIn J S v w) : JStepReachableIn J T v w := by
  obtain ⟨path, hhead, hlast, hstep, hmem⟩ := h
  exact ⟨path, hhead, hlast, hstep, fun u hu => hST (hmem u hu)⟩

/-- `[Timár]`'s conclusion is stated for `1`-step connectivity; clause (ii) of the
percolation lemma is about `J`-step components.  For `J ≥ 1` the former implies the
latter. -/
theorem jStepReachableIn_of_one_step {J : ℕ} (hJ : 1 ≤ J) {S : Set (Lattice d)}
    {v w : Lattice d} (h : JStepReachableIn 1 S v w) : JStepReachableIn J S v w :=
  jStepReachableIn_mono_step hJ h

/-! ## Outer and inner vertex boundaries -/

/-- The outer vertex boundary of `S`: the sites off `S` within `ℓ^∞`-distance `1` of it. -/
def outerBoundary (S : Set (Lattice d)) : Set (Lattice d) :=
  {v | v ∉ S ∧ ∃ u ∈ S, latticeDist u v ≤ 1}

/-- The inner vertex boundary of `S`: the sites of `S` within `ℓ^∞`-distance `1` of the
complement. -/
def innerBoundary (S : Set (Lattice d)) : Set (Lattice d) :=
  {v | v ∈ S ∧ ∃ u ∉ S, latticeDist u v ≤ 1}

theorem mem_outerBoundary_iff {S : Set (Lattice d)} {v : Lattice d} :
    v ∈ outerBoundary S ↔ v ∉ S ∧ ∃ u ∈ S, latticeDist u v ≤ 1 := Iff.rfl

theorem mem_innerBoundary_iff {S : Set (Lattice d)} {v : Lattice d} :
    v ∈ innerBoundary S ↔ v ∈ S ∧ ∃ u ∉ S, latticeDist u v ≤ 1 := Iff.rfl

theorem outerBoundary_disjoint (S : Set (Lattice d)) : Disjoint (outerBoundary S) S :=
  Set.disjoint_left.mpr fun _ hv hS => hv.1 hS

theorem innerBoundary_subset (S : Set (Lattice d)) : innerBoundary S ⊆ S := fun _ hv => hv.1

theorem mem_outerBoundary {S : Set (Lattice d)} {u v : Lattice d}
    (hu : u ∈ S) (hv : v ∉ S) (h : latticeDist u v ≤ 1) : v ∈ outerBoundary S :=
  ⟨hv, u, hu, h⟩

/-- The outer boundary sits in the `1`-thickening of `S`. -/
theorem outerBoundary_subset_thickening (S : Set (Lattice d)) :
    outerBoundary S ⊆ {v | ∃ u ∈ S, latticeDist u v ≤ 1} := fun _ hv => hv.2

/-- A coordinate difference bounded by the lattice distance, in `ℝ`. -/
theorem abs_coord_sub_le_of_latticeDist_le {x y : Lattice d} {r : ℕ}
    (h : latticeDist x y ≤ r) (i : Fin d) : |((x i - y i : ℤ) : ℝ)| ≤ (r : ℝ) := by
  have hnat : (x i - y i).natAbs ≤ r := (coord_le_latticeDist x y i).trans h
  have hz : |(x i - y i : ℤ)| ≤ (r : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hnat
  exact_mod_cast (by exact_mod_cast hz : ((|x i - y i| : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ))

/-- **The boundary of a small set is small.**  `diam_∞ (∂S) ≤ diam_∞ S + 2`. -/
theorem hasLatticeDiameterAtMost_outerBoundary {S : Set (Lattice d)} {R : ℝ}
    (hS : HasLatticeDiameterAtMost S R) :
    HasLatticeDiameterAtMost (outerBoundary S) (R + 2) := by
  rintro v ⟨-, u, huS, hu⟩ w ⟨-, u', hu'S, hu'⟩ i
  have h1 : |((u i - v i : ℤ) : ℝ)| ≤ (1 : ℝ) := by
    simpa using abs_coord_sub_le_of_latticeDist_le hu i
  have h2 : |((u' i - w i : ℤ) : ℝ)| ≤ (1 : ℝ) := by
    simpa using abs_coord_sub_le_of_latticeDist_le hu' i
  have h3 : |((u i - u' i : ℤ) : ℝ)| ≤ R := by exact_mod_cast hS u huS u' hu'S i
  have hsplit : ((v i - w i : ℤ) : ℝ) =
      -((u i - v i : ℤ) : ℝ) + ((u i - u' i : ℤ) : ℝ) + ((u' i - w i : ℤ) : ℝ) := by
    push_cast; ring
  have hb1 := abs_le.mp h1
  have hb2 := abs_le.mp h2
  have hb3 := abs_le.mp h3
  have : |((v i - w i : ℤ) : ℝ)| ≤ R + 2 := by
    rw [hsplit, abs_le]
    constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2]
  exact_mod_cast this

/-- The outer boundary of a finite set is finite: it sits in the union of the `ℓ^∞`-unit
balls around the finitely many sites of `S`, and each such ball is a finite box. -/
theorem finite_outerBoundary {S : Set (Lattice d)} (hS : S.Finite) :
    (outerBoundary S).Finite := by
  have hcover : outerBoundary S ⊆ ⋃ u ∈ S, {v : Lattice d | latticeDist u v ≤ 1} := by
    intro v hv
    obtain ⟨-, u, hu, hd⟩ := hv
    exact Set.mem_biUnion hu hd
  refine Set.Finite.subset (Set.Finite.biUnion hS fun u _ => ?_) hcover
  refine Set.Finite.subset (Finset.finite_toSet
    (Fintype.piFinset fun i => Finset.Icc (u i - 1) (u i + 1))) ?_
  intro v hv
  simp only [mem_ofPred_eq] at hv
  have h := latticeDist_le_iff.mp hv
  refine Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_)
  have hi := h i
  have habs : |u i - v i| ≤ 1 := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hi
  have := abs_le.mp habs
  omega

/-! ## The outer boundary of a bad component is good -/

/-- **The detour is a good detour.**  For `J ≥ 1`, every site of the outer boundary of a
bad `J`-step component is a good site: a bad neighbour of the component would itself be
in the component.

Source: `mfd:in-deterministic` and `s.tightness`. -/
theorem isPercolationGoodSite_of_mem_outerBoundary_badComponent
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} {ω : Ω} {u w : Lattice d} (hJ : 1 ≤ J)
    (hw : w ∈ outerBoundary
      (jStepComponent J {x | ¬ IsPercolationGoodSite E Cbox ω x} u)) :
    IsPercolationGoodSite E Cbox ω w := by
  by_contra hbad
  refine hw.1 ?_
  obtain ⟨v, hv, hvw⟩ := hw.2
  have hvbad : v ∈ {x | ¬ IsPercolationGoodSite E Cbox ω x} := mem_of_jStepReachableIn hv
  have hlink : JStepReachableIn J {x | ¬ IsPercolationGoodSite E Cbox ω x} v w := by
    refine ⟨[v, w], rfl, rfl, ?_, ?_⟩
    · intro k hk
      have hk' : k = 0 := by
        simp only [List.length_cons, List.length_nil] at hk
        omega
      subst hk'
      simpa using hvw.trans hJ
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hvbad
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hbad
        · exact absurd hx (List.not_mem_nil)
  exact hv.trans hlink

/-- **The detour is a short detour.**  If the bad component of `u` has diameter at most
`D`, its outer boundary has diameter at most `D + 2`. -/
theorem hasLatticeDiameterAtMost_outerBoundary_badComponent
    {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ} {ω : Ω} {u : Lattice d} {D : ℝ}
    (hD : HasLatticeDiameterAtMost
      (jStepComponent J {x | ¬ IsPercolationGoodSite E Cbox ω x} u) D) :
    HasLatticeDiameterAtMost
      (outerBoundary (jStepComponent J {x | ¬ IsPercolationGoodSite E Cbox ω x} u))
      (D + 2) :=
  hasLatticeDiameterAtMost_outerBoundary hD

/-! ## `[Timár, Lemma 2]`, stated with no percolation content -/

/-- **`[Timár, Lemma 2]` in finitary form.**  In the `ℓ^∞` convention of this development
there is one boundary notion, and the lemma reads: *the outer vertex boundary of a finite
`1`-step-connected set of `ℤ^d` is `1`-step connected.*

This is the residual of external item (C).  It contains no measure, no event field and no
percolation: it is a statement about `ℤ^d` alone.

Source: `[TimarBoundary, Lemma 2]`; used at `mfd:in-deterministic` and `s.tightness`. -/
def TimarBoundaryConnectivity (d : ℕ) : Prop :=
  ∀ S : Set (Lattice d), S.Finite → S.Nonempty →
    (∀ u ∈ S, ∀ v ∈ S, JStepReachableIn 1 S u v) →
    ∀ u ∈ outerBoundary S, ∀ v ∈ outerBoundary S,
      JStepReachableIn 1 (outerBoundary S) u v

/-- In dimension `0` the lattice is a single site, every set has empty outer boundary, and
`[Timár, Lemma 2]` is vacuous. -/
theorem timarBoundaryConnectivity_zero : TimarBoundaryConnectivity 0 := by
  have hall : ∀ x y : Lattice 0, x = y := fun x y => funext fun i => absurd i.2 (by omega)
  intro S _ _ _ u hu v _
  obtain ⟨hnot, w, hwS, -⟩ := hu
  exact absurd ((hall w u) ▸ hwS) hnot

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
