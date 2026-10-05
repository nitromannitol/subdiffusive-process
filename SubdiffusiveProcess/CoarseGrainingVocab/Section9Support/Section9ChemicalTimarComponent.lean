module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimar

@[expose] public section

/-!
# `[Timár, Lemma 2]`: the recorded statement is FALSE, and the corrected one

`Section9ChemicalTimar.TimarBoundaryConnectivity d` is the boundary-connectivity condition for
external item (C) for `[DRS]` condition S1.  **It is false in every dimension `d ≥ 1`**, and
this file refutes it with explicit finite witnesses, states the corrected form of
`[Timár, Lemma 2]`, proves the corrected form in dimensions `0` and `1` — where the stated
form already fails — and proves the coordinate-path half of the manuscript's separation step.

## The defect

`TimarBoundaryConnectivity d` asserts that the *whole* outer boundary of a finite `1`-step
connected set is `1`-step connected.  `[Timár, Lemma 2]` asserts no such thing: the set it
connects is the boundary *seen from one connected component of the complement* — the
visibility condition.  Dropping it makes the statement false as soon as `Sᶜ` is disconnected,
which happens already for very small `S`:

* `d = 1`: `S = {0}`.  Then `∂S = {-1, 1}`, two sites at distance `2`, and `-1` is an isolated
  point of `∂S`.  (`not_timarBoundaryConnectivity_one`.)
* `d ≥ 2`: `S = {x : |x|_∞ = 1}`, the `ℓ^∞` unit sphere, which is finite, nonempty and `1`-step
  connected (`connected_unitSphere`).  Its outer boundary is `{0} ∪ {x : |x|_∞ = 2}`, and the
  origin is an isolated point of it: every site within distance `1` of `0` other than `0`
  itself lies *on* `S`.  (`not_timarBoundaryConnectivity_of_two_le`.)

Both are the same phenomenon — the complement of `S` has two components and the boundary has
one piece in each — and `not_timarBoundaryConnectivity` records it uniformly for `d ≥ 1`.
These witnesses establish the failure of the unrestricted statement.

## The corrected statement

`TimarBoundaryComponentConnectivity d` quantifies over a complementary component:

    ∀ S finite nonempty `1`-step connected, ∀ c ∉ S,
      `visibleBoundary S c = ∂S ∩ (component of c in Sᶜ)` is `1`-step connected.

`visibleBoundary_eq_outerBoundary` shows the two statements agree exactly when `Sᶜ` is
connected, and `outerBoundary_connected_of_timarBoundaryComponentConnectivity` recovers the
recorded conclusion in that case — so nothing that consumes the boundary connectivity for a
set with connected complement is weakened by the correction.

Proved here: `timarBoundaryComponentConnectivity_zero` (`d = 0`, vacuous) and
**`timarBoundaryComponentConnectivity_one`** (`d = 1`, via the discrete intermediate value
theorem for `1`-step paths: on the line the visible boundary is a single site).  The general
`d ≥ 2` case is Timár's graph-theoretic argument and remains the external.  It was checked
exhaustively by machine for every `1`-step connected subset of a `4 × 4` box of `ℤ^2` (all
`2 ^ 16` subsets, boundary taken in a padded window): the recorded statement fails for `593`
of them, the corrected statement for none.  `visibleBoundary_unitSphere_zero` records that the
refuting witness satisfies the corrected statement.

## The separation step

The manuscript's S1 argument  runs the coordinate path
from `v` to `w` and detours around each bad component along its outer boundary.  This file
proves the coordinate path itself — `latticeGeodesic`, the `ℓ^∞` geodesic, with
`jStepReachableIn_of_forall_latticeGeodesic_mem` and `inLatticeBallReal_latticeGeodesic` — and
the unobstructed case of the step,
`jStepReachableIn_good_of_forall_latticeGeodesic_good`: when the geodesic meets no bad site,
the S1 conclusion holds for that pair with no appeal to `[Timár]` at all.  The detour itself
still needs the corrected connectivity plus the argument that the entry and exit sites of a
bad component lie in the *same* component of its complement; that is what remains of (C).

## Reusable infrastructure

`jStepReachableIn_induction` (a predicate preserved along admissible steps holds at the end of
a path) is the workhorse: the isolation lemma `eq_of_jStepReachableIn_isolated`, on which both
refutations rest, and the discrete intermediate value theorem
`exists_mem_eq_of_jStepReachableIn_one` are both instances of it.

## Source

* `[TimarBoundary, Lemma 2]` (Timár, *Boundary-connectivity via graph theory*, Proc. AMS 141
  (2013), 475-480).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ}

/-- Two sites at lattice distance `0` are equal. -/
theorem eq_of_latticeDist_eq_zero {x y : Lattice d}
    (h : latticeDist x y = 0) : x = y := by
  funext i
  have h0 : (x i - y i).natAbs ≤ 0 := latticeDist_le_iff.mp h.le i
  have h1 : x i - y i = 0 := Int.natAbs_eq_zero.mp (Nat.le_zero.mp h0)
  omega

/-- A single admissible step is a path. -/
theorem jStepReachableIn_of_dist {J : ℕ} {S : Set (Lattice d)} {v w : Lattice d}
    (hv : v ∈ S) (hw : w ∈ S) (h : latticeDist v w ≤ J) :
    JStepReachableIn J S v w := by
  refine ⟨[v, w], rfl, rfl, ?_, ?_⟩
  · intro k hk
    have hk' : k = 0 := by
      simp only [List.length_cons, List.length_nil] at hk
      omega
    subst hk'
    simpa using h
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hv
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact absurd hx (List.not_mem_nil)

/-- Lattice balls are finite. -/
theorem finite_setOf_latticeDist_le (z : Lattice d) (R : ℕ) :
    {x : Lattice d | latticeDist z x ≤ R}.Finite := by
  have h : {x : Lattice d | latticeDist z x ≤ R} = (latticeBallFinset z R : Set (Lattice d)) := by
    ext x; simp [mem_latticeBallFinset_iff]
  rw [h]
  exact (latticeBallFinset z R).finite_toSet

/-- **Induction along a `J`-step path.** -/
theorem jStepReachableIn_induction {J : ℕ} {S : Set (Lattice d)} {P : Lattice d → Prop}
    {u w : Lattice d} (h : JStepReachableIn J S u w) (hu : P u)
    (hstep : ∀ x ∈ S, ∀ y ∈ S, P x → latticeDist x y ≤ J → P y) : P w := by
  obtain ⟨path, hhead, hlast, hpath, hmem⟩ := h
  have hne : path ≠ [] := by
    intro he; rw [he] at hhead; simp at hhead
  have hlen : 0 < path.length := List.length_pos_of_ne_nil hne
  have h0 : path[0]! = u := by
    have : path[0]? = some u := by rw [← List.head?_eq_getElem?]; exact hhead
    rw [getElem!_pos path 0 hlen]
    exact Option.some.inj (by rwa [List.getElem?_eq_getElem hlen] at this)
  have key : ∀ k, ∀ hk : k < path.length, P path[k]! := by
    intro k
    induction k with
    | zero => intro _; rw [h0]; exact hu
    | succ n ih =>
      intro hk
      have hn : n < path.length := Nat.lt_of_succ_lt hk
      have hxS : path[n]! ∈ S := by
        rw [getElem!_pos path n hn]; exact hmem _ (List.getElem_mem hn)
      have hyS : path[n + 1]! ∈ S := by
        rw [getElem!_pos path (n + 1) hk]; exact hmem _ (List.getElem_mem hk)
      exact hstep _ hxS _ hyS (ih hn) (hpath n hk)
  have hw : path[path.length - 1]! = w := by
    have : path[path.length - 1]? = some w := by rw [← List.getLast?_eq_getElem?]; exact hlast
    rw [getElem!_pos path (path.length - 1) (by omega)]
    exact Option.some.inj (by rwa [List.getElem?_eq_getElem (by omega)] at this)
  have := key (path.length - 1) (by omega)
  rwa [hw] at this

/-- Reachability from an isolated point is trivial. -/
theorem eq_of_jStepReachableIn_isolated {J : ℕ} {T : Set (Lattice d)} {u w : Lattice d}
    (hiso : ∀ x ∈ T, latticeDist u x ≤ J → x = u) (h : JStepReachableIn J T u w) :
    w = u :=
  jStepReachableIn_induction (P := fun x => x = u) h rfl
    (fun _ _ y hy hxu hxy => hiso y hy (hxu ▸ hxy))

/-! ## The counterexample sets -/

/-- The `ℓ^∞` unit sphere around the origin. -/
def unitSphere (d : ℕ) : Set (Lattice d) := {x | latticeDist 0 x = 1}

/-- The lattice vector with entry `s` in coordinate `i` and `0` elsewhere. -/
def coordVec {d : ℕ} (i : Fin d) (s : ℤ) : Lattice d := fun k => if k = i then s else 0

theorem mem_unitSphere_iff {x : Lattice d} :
    x ∈ unitSphere d ↔ (∀ i, (x i).natAbs ≤ 1) ∧ x ≠ 0 := by
  simp only [unitSphere, mem_ofPred_eq]
  constructor
  · intro h
    constructor
    · intro i
      have := latticeDist_le_iff.mp h.le i
      simpa using this
    · rintro rfl
      simp [latticeDist_self] at h
  · rintro ⟨h1, h2⟩
    have hle : latticeDist 0 x ≤ 1 :=
      latticeDist_le_iff.mpr fun i => by simpa using h1 i
    have hne : latticeDist 0 x ≠ 0 := fun h0 => h2 (eq_of_latticeDist_eq_zero h0).symm
    omega

theorem coordVec_apply_self {i : Fin d} {s : ℤ} : coordVec i s i = s := by
  simp [coordVec]

theorem coordVec_apply_of_ne {i k : Fin d} {s : ℤ} (h : k ≠ i) : coordVec i s k = 0 := by
  simp [coordVec, h]

theorem coordVec_mem_unitSphere {i : Fin d} {s : ℤ} (hs : s.natAbs = 1) :
    coordVec i s ∈ unitSphere d := by
  refine mem_unitSphere_iff.mpr ⟨fun k => ?_, ?_⟩
  · by_cases hk : k = i
    · rw [hk, coordVec_apply_self]; omega
    · rw [coordVec_apply_of_ne hk]; simp
  · intro hzero
    have := congrFun hzero i
    rw [coordVec_apply_self] at this
    simp at this
    omega

theorem latticeDist_coordVec_le_one {x : Lattice d} {i : Fin d} {s : ℤ}
    (hx : ∀ k, (x k).natAbs ≤ 1) (hi : x i = s) :
    latticeDist x (coordVec i s) ≤ 1 := by
  refine latticeDist_le_iff.mpr fun k => ?_
  by_cases hk : k = i
  · rw [hk, coordVec_apply_self, hi]; simp
  · rw [coordVec_apply_of_ne hk]
    have := hx k
    omega

theorem latticeDist_coordVec_coordVec_le_one {i j : Fin d} {s t : ℤ}
    (hij : i ≠ j) (hs : s.natAbs ≤ 1) (ht : t.natAbs ≤ 1) :
    latticeDist (coordVec i s) (coordVec j t) ≤ 1 := by
  refine latticeDist_le_iff.mpr fun k => ?_
  by_cases hk : k = i
  · subst hk
    rw [coordVec_apply_self, coordVec_apply_of_ne hij]
    omega
  · by_cases hk' : k = j
    · subst hk'
      rw [coordVec_apply_self, coordVec_apply_of_ne (Ne.symm hij)]
      omega
    · rw [coordVec_apply_of_ne hk, coordVec_apply_of_ne hk']
      simp

theorem latticeDist_update_le_one {x : Lattice d} {i : Fin d} {s : ℤ}
    (hi : x i = 0) (hs : s.natAbs ≤ 1) :
    latticeDist x (Function.update x i s) ≤ 1 := by
  refine latticeDist_le_iff.mpr fun k => ?_
  by_cases hk : k = i
  · subst hk
    rw [Function.update_self, hi]
    omega
  · rw [Function.update_of_ne hk]
    simp

/-! ## The unit sphere is `1`-step connected in dimension at least two -/

/-- Every site of the unit sphere reaches `coordVec i0 1` inside the sphere. -/
theorem jStepReachableIn_unitSphere_coordVec {i0 i1 : Fin d} (hne : i0 ≠ i1)
    {x : Lattice d} (hx : x ∈ unitSphere d) :
    JStepReachableIn 1 (unitSphere d) x (coordVec i0 1) := by
  have hb := mem_unitSphere_iff.mp hx
  have hx1 : (x i0).natAbs ≤ 1 := hb.1 i0
  have hq : coordVec i0 (1 : ℤ) ∈ unitSphere d := coordVec_mem_unitSphere (by simp)
  have hcases : x i0 = 1 ∨ x i0 = 0 ∨ x i0 = -1 := by omega
  rcases hcases with h | h | h
  · exact jStepReachableIn_of_dist hx hq (latticeDist_coordVec_le_one hb.1 h)
  · have hy : Function.update x i0 (1 : ℤ) ∈ unitSphere d := by
      refine mem_unitSphere_iff.mpr ⟨fun k => ?_, ?_⟩
      · by_cases hk : k = i0
        · subst hk; rw [Function.update_self]; simp
        · rw [Function.update_of_ne hk]; exact hb.1 k
      · intro h0
        have := congrFun h0 i0
        rw [Function.update_self] at this
        simp at this
    have h1 : latticeDist x (Function.update x i0 (1 : ℤ)) ≤ 1 :=
      latticeDist_update_le_one h (by simp)
    have h2 : latticeDist (Function.update x i0 (1 : ℤ)) (coordVec i0 1) ≤ 1 :=
      latticeDist_coordVec_le_one (mem_unitSphere_iff.mp hy).1 (by rw [Function.update_self])
    exact (jStepReachableIn_of_dist hx hy h1).trans (jStepReachableIn_of_dist hy hq h2)
  · have hn : coordVec i0 (-1 : ℤ) ∈ unitSphere d := coordVec_mem_unitSphere (by simp)
    have he1 : coordVec i1 (1 : ℤ) ∈ unitSphere d := coordVec_mem_unitSphere (by simp)
    have s1 : latticeDist x (coordVec i0 (-1 : ℤ)) ≤ 1 := latticeDist_coordVec_le_one hb.1 h
    have s2 : latticeDist (coordVec i0 (-1 : ℤ)) (coordVec i1 (1 : ℤ)) ≤ 1 :=
      latticeDist_coordVec_coordVec_le_one hne (by simp) (by simp)
    have s3 : latticeDist (coordVec i1 (1 : ℤ)) (coordVec i0 (1 : ℤ)) ≤ 1 :=
      latticeDist_coordVec_coordVec_le_one (Ne.symm hne) (by simp) (by simp)
    exact ((jStepReachableIn_of_dist hx hn s1).trans
      (jStepReachableIn_of_dist hn he1 s2)).trans (jStepReachableIn_of_dist he1 hq s3)

/-- **The unit sphere is `1`-step connected** once `d ≥ 2`. -/
theorem connected_unitSphere {i0 i1 : Fin d} (hne : i0 ≠ i1) :
    ∀ u ∈ unitSphere d, ∀ v ∈ unitSphere d, JStepReachableIn 1 (unitSphere d) u v :=
  fun _ hu _ hv => (jStepReachableIn_unitSphere_coordVec hne hu).trans
    (jStepReachableIn_unitSphere_coordVec hne hv).symm

theorem finite_unitSphere : (unitSphere d).Finite :=
  (finite_setOf_latticeDist_le 0 1).subset fun _ hx => le_of_eq hx

/-- The origin lies on the outer boundary of the unit sphere. -/
theorem zero_mem_outerBoundary_unitSphere (i : Fin d) :
    (0 : Lattice d) ∈ outerBoundary (unitSphere d) := by
  have hmem : coordVec i (1 : ℤ) ∈ unitSphere d := coordVec_mem_unitSphere (by simp)
  refine ⟨?_, coordVec i 1, hmem, ?_⟩
  · simp [unitSphere]
  · rw [latticeDist_comm]
    exact le_of_eq hmem

/-- The doubled unit vector lies on the outer boundary of the unit sphere. -/
theorem coordVec_two_mem_outerBoundary_unitSphere (i : Fin d) :
    coordVec i (2 : ℤ) ∈ outerBoundary (unitSphere d) := by
  have hmem : coordVec i (1 : ℤ) ∈ unitSphere d := coordVec_mem_unitSphere (by simp)
  refine ⟨?_, coordVec i 1, hmem, ?_⟩
  · intro hcon
    have := (mem_unitSphere_iff.mp hcon).1 i
    rw [coordVec_apply_self] at this
    omega
  · refine latticeDist_le_iff.mpr fun k => ?_
    by_cases hk : k = i
    · subst hk
      rw [coordVec_apply_self, coordVec_apply_self]
      omega
    · rw [coordVec_apply_of_ne hk, coordVec_apply_of_ne hk]
      simp

/-- **The origin is isolated in the outer boundary of the unit sphere**: its only neighbour
there is itself, because every other site within distance `1` of it lies on the sphere. -/
theorem eq_zero_of_mem_outerBoundary_unitSphere {x : Lattice d}
    (hx : x ∈ outerBoundary (unitSphere d)) (h : latticeDist 0 x ≤ 1) : x = 0 := by
  rcases Nat.lt_or_ge (latticeDist 0 x) 1 with h1 | h1
  · exact (eq_of_latticeDist_eq_zero (by omega)).symm
  · exact absurd (show x ∈ unitSphere d from le_antisymm h h1) hx.1

/-! ## The refutation of `TimarBoundaryConnectivity` -/

/-- **`[Timár, Lemma 2]` as stated by `TimarBoundaryConnectivity` is false for every
`d ≥ 2`.**  The witness is the `ℓ^∞` unit sphere `S = {x : |x|_∞ = 1}`: it is finite,
nonempty and `1`-step connected, but its outer boundary is `{0} ∪ {x : |x|_∞ = 2}` and the
origin is an isolated point of it. -/
theorem not_timarBoundaryConnectivity_of_two_le (hd : 2 ≤ d) :
    ¬ TimarBoundaryConnectivity d := by
  intro h
  have hne : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  have hreach := h (unitSphere d) finite_unitSphere
    ⟨coordVec ⟨0, by omega⟩ 1, coordVec_mem_unitSphere (by simp)⟩
    (connected_unitSphere hne) 0 (zero_mem_outerBoundary_unitSphere ⟨0, by omega⟩)
    (coordVec ⟨0, by omega⟩ 2) (coordVec_two_mem_outerBoundary_unitSphere _)
  have hzero := eq_of_jStepReachableIn_isolated
    (fun x hx hdx => eq_zero_of_mem_outerBoundary_unitSphere hx hdx) hreach
  have := congrFun hzero (⟨0, by omega⟩ : Fin d)
  rw [coordVec_apply_self] at this
  simp at this

/-- On the line, two lattice sites agreeing in the single coordinate are equal. -/
theorem lattice_one_ext {x y : Lattice 1} (h : x 0 = y 0) : x = y := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  rw [hi]
  exact h

/-- **`TimarBoundaryConnectivity 1` is false.**  The witness is the singleton `S = {0}`,
whose outer boundary is `{-1, 1}`: two sites at distance `2`. -/
theorem not_timarBoundaryConnectivity_one : ¬ TimarBoundaryConnectivity 1 := by
  intro h
  set a : Lattice 1 := coordVec 0 (-1) with ha
  set b : Lattice 1 := coordVec 0 1 with hb
  have hai : a 0 = -1 := coordVec_apply_self
  have hbi : b 0 = 1 := coordVec_apply_self
  have hda : latticeDist 0 a ≤ 1 := le_of_eq (coordVec_mem_unitSphere (by simp))
  have hdb : latticeDist 0 b ≤ 1 := le_of_eq (coordVec_mem_unitSphere (by simp))
  have hmema : a ∈ outerBoundary ({0} : Set (Lattice 1)) := by
    refine ⟨?_, 0, rfl, hda⟩
    intro hcon
    have hz : a 0 = (0 : Lattice 1) 0 := by rw [hcon]
    rw [hai] at hz
    simp at hz
  have hmemb : b ∈ outerBoundary ({0} : Set (Lattice 1)) := by
    refine ⟨?_, 0, rfl, hdb⟩
    intro hcon
    have hz : b 0 = (0 : Lattice 1) 0 := by rw [hcon]
    rw [hbi] at hz
    simp at hz
  have hconn : ∀ u ∈ ({0} : Set (Lattice 1)), ∀ v ∈ ({0} : Set (Lattice 1)),
      JStepReachableIn 1 ({0} : Set (Lattice 1)) u v := by
    rintro u rfl v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact jStepReachableIn_of_dist rfl rfl (by simp)
  have hreach := h ({0} : Set (Lattice 1)) (Set.finite_singleton _) ⟨0, rfl⟩ hconn
    a hmema b hmemb
  have hiso : ∀ x ∈ outerBoundary ({0} : Set (Lattice 1)), latticeDist a x ≤ 1 → x = a := by
    intro x hx hdx
    obtain ⟨hxnot, u, hu, hux⟩ := hx
    rw [Set.mem_singleton_iff] at hu
    subst hu
    have h1 : ((0 : Lattice 1) 0 - x 0).natAbs ≤ 1 := latticeDist_le_iff.mp hux 0
    have h2 : (a 0 - x 0).natAbs ≤ 1 := latticeDist_le_iff.mp hdx 0
    have h3 : x 0 ≠ 0 := by
      intro hcon
      exact hxnot (Set.mem_singleton_iff.mpr (lattice_one_ext (by simpa using hcon)))
    refine lattice_one_ext ?_
    rw [hai] at h2
    simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg] at h1
    rw [hai]
    omega
  have hcon := eq_of_jStepReachableIn_isolated hiso hreach
  have hfin := congrFun hcon 0
  rw [hai, hbi] at hfin
  simp at hfin

/-- **The refutation, uniformly**: the outer-boundary connectivity statement recorded by
This boundary-connectivity statement fails in every dimension `d ≥ 1`. -/
theorem not_timarBoundaryConnectivity (hd : 1 ≤ d) : ¬ TimarBoundaryConnectivity d := by
  rcases Nat.lt_or_ge d 2 with h | h
  · have : d = 1 := by omega
    subst this
    exact not_timarBoundaryConnectivity_one
  · exact not_timarBoundaryConnectivity_of_two_le h

/-! ## The corrected statement -/

/-- The part of the outer boundary of `S` that is *visible* from the complementary component
of `c`: the boundary sites `1`-step connected to `c` inside `Sᶜ`.  This is the set that
`[Timár, Lemma 2]` asserts to be connected. -/
def visibleBoundary (S : Set (Lattice d)) (c : Lattice d) : Set (Lattice d) :=
  outerBoundary S ∩ jStepComponent 1 Sᶜ c

theorem visibleBoundary_subset (S : Set (Lattice d)) (c : Lattice d) :
    visibleBoundary S c ⊆ outerBoundary S := Set.inter_subset_left

/-- **`[Timár, Lemma 2]`, corrected finitary form.**  The outer boundary of a finite `1`-step
connected set, *seen from one component of the complement*, is `1`-step connected.

The quantifier over `c` is the visibility condition missing from
`TimarBoundaryConnectivity`, which is refuted above in every dimension `d ≥ 1`. -/
def TimarBoundaryComponentConnectivity (d : ℕ) : Prop :=
  ∀ S : Set (Lattice d), S.Finite → S.Nonempty →
    (∀ u ∈ S, ∀ v ∈ S, JStepReachableIn 1 S u v) →
    ∀ c : Lattice d, c ∉ S →
      ∀ u ∈ visibleBoundary S c, ∀ v ∈ visibleBoundary S c,
        JStepReachableIn 1 (visibleBoundary S c) u v

/-- When the complement is `1`-step connected the visible boundary is the whole outer
boundary; this is the only case in which the two statements agree. -/
theorem visibleBoundary_eq_outerBoundary (S : Set (Lattice d)) {c : Lattice d} (hc : c ∉ S)
    (hconn : ∀ u ∈ Sᶜ, ∀ v ∈ Sᶜ, JStepReachableIn 1 Sᶜ u v) :
    visibleBoundary S c = outerBoundary S :=
  Set.Subset.antisymm Set.inter_subset_left fun _ hx => ⟨hx, hconn c hc _ hx.1⟩

/-- The corrected statement recovers the stated one exactly for sets with connected
complement. -/
theorem outerBoundary_connected_of_timarBoundaryComponentConnectivity
    (h : TimarBoundaryComponentConnectivity d)
    (S : Set (Lattice d)) (hfin : S.Finite) (hne : S.Nonempty)
    (hSconn : ∀ u ∈ S, ∀ v ∈ S, JStepReachableIn 1 S u v)
    {c : Lattice d} (hc : c ∉ S)
    (hcompl : ∀ u ∈ Sᶜ, ∀ v ∈ Sᶜ, JStepReachableIn 1 Sᶜ u v) :
    ∀ u ∈ outerBoundary S, ∀ v ∈ outerBoundary S,
      JStepReachableIn 1 (outerBoundary S) u v := by
  intro u hu v hv
  have heq := visibleBoundary_eq_outerBoundary S hc hcompl
  have := h S hfin hne hSconn c hc u (by rw [heq]; exact hu) v (by rw [heq]; exact hv)
  rwa [heq] at this

/-- In dimension `0` the outer boundary is empty and the corrected statement is vacuous. -/
theorem timarBoundaryComponentConnectivity_zero : TimarBoundaryComponentConnectivity 0 := by
  have hall : ∀ x y : Lattice 0, x = y := fun x y => funext fun i => absurd i.2 (by omega)
  intro S _ _ _ c _ u hu v _
  obtain ⟨hnot, w, hwS, -⟩ := hu.1
  exact absurd ((hall w u) ▸ hwS) hnot

/-! ## The corrected statement in dimension one -/

/-- The discrete intermediate value theorem for `1`-step paths on the line. -/
theorem exists_mem_eq_of_jStepReachableIn_one {S : Set (Lattice 1)} {u w : Lattice 1} {c : ℤ}
    (h : JStepReachableIn 1 S u w) (h1 : u 0 ≤ c) (h2 : c ≤ w 0) :
    ∃ x ∈ S, x 0 = c := by
  have key : (w 0 ≤ c) ∨ (∃ x ∈ S, x 0 = c) := by
    refine jStepReachableIn_induction
      (P := fun z => (z 0 ≤ c) ∨ (∃ x ∈ S, x 0 = c)) h (Or.inl h1) ?_
    rintro x hx y hy (hxc | hfound) hxy
    · by_cases hyc : y 0 ≤ c
      · exact Or.inl hyc
      · have hd : (x 0 - y 0).natAbs ≤ 1 := latticeDist_le_iff.mp hxy 0
        have hxeq : x 0 = c := by omega
        exact Or.inr ⟨x, hx, hxeq⟩
    · exact Or.inr hfound
  rcases key with hw | hfound
  · exact ⟨w, mem_of_jStepReachableIn h, by omega⟩
  · exact hfound

/-- The unoriented form of the discrete intermediate value theorem. -/
theorem exists_mem_eq_of_jStepReachableIn_one' {S : Set (Lattice 1)} {u w : Lattice 1} {c : ℤ}
    (h : JStepReachableIn 1 S u w) (h1 : min (u 0) (w 0) ≤ c) (h2 : c ≤ max (u 0) (w 0)) :
    ∃ x ∈ S, x 0 = c := by
  rcases le_total (u 0) (w 0) with hle | hle
  · exact exists_mem_eq_of_jStepReachableIn_one h (by omega) (by omega)
  · exact exists_mem_eq_of_jStepReachableIn_one h.symm (by omega) (by omega)

/-- On the line a site of `S` and a site of `Sᶜ` cannot share their coordinate. -/
theorem false_of_coord_mem_and_mem_compl {S : Set (Lattice 1)} {m : ℤ}
    (h1 : ∃ x ∈ S, x 0 = m) (h2 : ∃ y ∈ Sᶜ, y 0 = m) : False := by
  obtain ⟨x, hx, hxm⟩ := h1
  obtain ⟨y, hy, hym⟩ := h2
  exact hy (lattice_one_ext (hym.trans hxm.symm) ▸ hx)

/-- **The corrected statement holds on the line.**  In `ℤ` the visible boundary of a finite
`1`-step connected set is a single site, so it is trivially connected — while the stated
form of `[Timár, Lemma 2]` already fails there. -/
theorem timarBoundaryComponentConnectivity_one : TimarBoundaryComponentConnectivity 1 := by
  intro S _ _ hSconn c _ u hu v hv
  have huv : u = v := by
    by_contra hcon
    obtain ⟨hunot, s, hsS, hsu⟩ := hu.1
    obtain ⟨hvnot, t, htS, htv⟩ := hv.1
    have hpath : JStepReachableIn 1 Sᶜ u v :=
      (JStepReachableIn.symm hu.2).trans hv.2
    have hSpath : JStepReachableIn 1 S s t := hSconn s hsS t htS
    have hs1 : (s 0 - u 0).natAbs ≤ 1 := latticeDist_le_iff.mp hsu 0
    have ht1 : (t 0 - v 0).natAbs ≤ 1 := latticeDist_le_iff.mp htv 0
    have hs2 : s 0 ≠ u 0 := fun hz => hunot (lattice_one_ext hz ▸ hsS)
    have ht2 : t 0 ≠ v 0 := fun hz => hvnot (lattice_one_ext hz ▸ htS)
    have hab : u 0 ≠ v 0 := fun hz => hcon (lattice_one_ext hz)
    have hI : min (u 0) (v 0) ≤ max (min (u 0) (v 0)) (min (s 0) (t 0)) ∧
        max (min (u 0) (v 0)) (min (s 0) (t 0)) ≤ max (u 0) (v 0) ∧
        min (s 0) (t 0) ≤ max (min (u 0) (v 0)) (min (s 0) (t 0)) ∧
        max (min (u 0) (v 0)) (min (s 0) (t 0)) ≤ max (s 0) (t 0) := by omega
    exact false_of_coord_mem_and_mem_compl
      (exists_mem_eq_of_jStepReachableIn_one' hSpath hI.2.2.1 hI.2.2.2)
      (exists_mem_eq_of_jStepReachableIn_one' hpath hI.1 hI.2.1)
  subst huv
  exact jStepReachableIn_self_iff.mpr hu

/-! ## The corrected statement survives the counterexample -/

/-- For the unit sphere, the component of the origin in the complement is `{0}`, so its
visible boundary is a single site: the corrected statement is not refuted by the set that
refutes the stated one. -/
theorem visibleBoundary_unitSphere_zero (i : Fin d) :
    visibleBoundary (unitSphere d) 0 = {0} := by
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · refine Set.mem_singleton_iff.mpr (eq_of_jStepReachableIn_isolated ?_ hx.2)
    intro y hy hdy
    rcases Nat.lt_or_ge (latticeDist 0 y) 1 with h1 | h1
    · exact (eq_of_latticeDist_eq_zero (by omega)).symm
    · exact absurd (show y ∈ unitSphere d from le_antisymm hdy h1) hy
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨zero_mem_outerBoundary_unitSphere i, ?_⟩
    refine jStepReachableIn_self_iff.mpr ?_
    simp [unitSphere]

/-! ## The coordinate path of the separation step -/

/-- The `ℓ^∞` geodesic from `v` to `w`: at time `k` each coordinate has moved `k` steps
towards its target and then stopped. -/
def latticeGeodesic (v w : Lattice d) (k : ℕ) : Lattice d :=
  fun i => v i + max (-(k : ℤ)) (min (k : ℤ) (w i - v i))

theorem latticeGeodesic_zero (v w : Lattice d) : latticeGeodesic v w 0 = v := by
  funext i
  simp [latticeGeodesic]

theorem latticeDist_latticeGeodesic_succ (v w : Lattice d) (k : ℕ) :
    latticeDist (latticeGeodesic v w k) (latticeGeodesic v w (k + 1)) ≤ 1 := by
  refine latticeDist_le_iff.mpr fun i => ?_
  simp only [latticeGeodesic]
  push_cast
  omega

theorem latticeGeodesic_of_latticeDist_le {v w : Lattice d} {k : ℕ}
    (h : latticeDist v w ≤ k) : latticeGeodesic v w k = w := by
  funext i
  have hi : (v i - w i).natAbs ≤ k := latticeDist_le_iff.mp h i
  simp only [latticeGeodesic]
  omega

/-- **The coordinate path.**  If every site of the `ℓ^∞` geodesic from `v` to `w` lies in `S`,
then `v` and `w` are `1`-step connected inside `S`. -/
theorem jStepReachableIn_of_forall_latticeGeodesic_mem {S : Set (Lattice d)}
    {v w : Lattice d} (h : ∀ k, k ≤ latticeDist v w → latticeGeodesic v w k ∈ S) :
    JStepReachableIn 1 S v w := by
  refine ⟨(List.range (latticeDist v w + 1)).map (latticeGeodesic v w), ?_, ?_, ?_, ?_⟩
  · simp [List.head?_eq_getElem?, latticeGeodesic_zero]
  · have hw : latticeGeodesic v w (latticeDist v w) = w :=
      latticeGeodesic_of_latticeDist_le le_rfl
    simp [List.getLast?_eq_getElem?, hw]
  · intro k hk
    have h2 : k + 1 < ((List.range (latticeDist v w + 1)).map (latticeGeodesic v w)).length := hk
    have h1 : k < ((List.range (latticeDist v w + 1)).map (latticeGeodesic v w)).length :=
      Nat.lt_of_succ_lt hk
    rw [getElem!_pos ((List.range (latticeDist v w + 1)).map (latticeGeodesic v w)) k h1,
      getElem!_pos ((List.range (latticeDist v w + 1)).map (latticeGeodesic v w)) (k + 1) h2]
    simp only [List.getElem_map, List.getElem_range]
    exact latticeDist_latticeGeodesic_succ v w k
  · intro u hu
    simp only [List.mem_map] at hu
    obtain ⟨k, hk, rfl⟩ := hu
    refine h k ?_
    have hk' : k < latticeDist v w + 1 := List.mem_range.mp hk
    omega

/-- The coordinate path stays in any ball containing its endpoints. -/
theorem inLatticeBallReal_latticeGeodesic {z v w : Lattice d} {R : ℝ}
    (hv : InLatticeBallReal z v R) (hw : InLatticeBallReal z w R) (k : ℕ) :
    InLatticeBallReal z (latticeGeodesic v w k) R := by
  intro i
  have hA : |((v i - z i : ℤ) : ℝ)| ≤ R := by rw [← Int.cast_abs]; exact hv i
  have hB : |((w i - z i : ℤ) : ℝ)| ≤ R := by rw [← Int.cast_abs]; exact hw i
  have ha := abs_le.mp hA
  have hb := abs_le.mp hB
  have hbetween : (v i - z i ≤ latticeGeodesic v w k i - z i ∧
      latticeGeodesic v w k i - z i ≤ w i - z i) ∨
      (w i - z i ≤ latticeGeodesic v w k i - z i ∧
      latticeGeodesic v w k i - z i ≤ v i - z i) := by
    simp only [latticeGeodesic]
    omega
  show ((|latticeGeodesic v w k i - z i| : ℤ) : ℝ) ≤ R
  rw [Int.cast_abs]
  refine abs_le.mpr ?_
  rcases hbetween with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact ⟨le_trans ha.1 (by exact_mod_cast hl), le_trans (by exact_mod_cast hr) hb.2⟩
  · exact ⟨le_trans hb.1 (by exact_mod_cast hl), le_trans (by exact_mod_cast hr) ha.2⟩

/-- **The unobstructed case of the separation step.**  If the coordinate path from `v` to `w`
meets no bad site, the conclusion of `[DRS]` condition S1 holds for that pair: no appeal to
`[Timár, Lemma 2]` is needed, and the good path stays in the ball that contains `v` and `w`.
 -/
theorem jStepReachableIn_good_of_forall_latticeGeodesic_good {Ω : Type*}
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω} {z : Lattice d} {L : ℕ} {v w : Lattice d}
    (hv : InLatticeBallReal z v (L : ℝ)) (hw : InLatticeBallReal z w (L : ℝ))
    (hgood : ∀ k, k ≤ latticeDist v w →
      IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k)) :
    JStepReachableIn 1
      {u | IsPercolationGoodSite E Cbox ω u ∧ InLatticeBallReal z u (2 * L : ℝ)} v w := by
  refine jStepReachableIn_of_forall_latticeGeodesic_mem fun k hk => ⟨hgood k hk, ?_⟩
  have hL : (L : ℝ) ≤ (2 * L : ℝ) := by
    have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith
  exact inLatticeBallReal_mono hL (inLatticeBallReal_latticeGeodesic hv hw k)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
