module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalConnectivityTail
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingChain

@[expose] public section

/-!
# Confining the good detour to a tube, and the length it costs

bundle P-404, the deterministic half of the **length** residual of
the chemical-distance bound.

`Section9ChemicalTimarSeparation` proves the connectivity half by walking along the `ℓ∞`
geodesic from `v` to `w` and, whenever the walk meets a bad `1`-step component `K`, detouring
along the part of `∂K` visible from `v` (the proved Timár lemma).  That proof throws away a
quantitative fact it establishes on the way: **every site of every detour lies within
`T + 1` of the geodesic**, where `T` bounds the `ℓ∞` diameter of the bad components met.

This file re-runs the walk keeping that fact.  The output is reachability inside

```text
    (good sites) ∩ latticeTubeFinset v w (T + 1) ,
```

a set of at most `(latticeDist v w + 1) * (2 T + 3) ^ d` sites, and hence — after loop erasure
(`exists_nodup_isChain`) — a good path from `v` to `w` with **at most that many vertices**.

## What this buys, and what it does not

At `latticeDist v w ≤ 2 L` the budget is `(2 L + 1) (2 T + 3) ^ d`, which is *linear in `L`*
with a constant `(2 T + 3) ^ d` governed by the largest bad component the geodesic meets.  The
tail of that maximum over `B_{2L}(z)` is `exp (-c q √T)`
(`Section9ChemicalASDDiameterTail.measure_badComponentFailureEvent_le`), so a failure
probability `exp (-c q (log L) ^ 2)` forces `T ≍ (log L) ^ 4` and the budget
`C L (log L) ^ (4 d)`.  **The tube route cannot do better than `L · polylog`**: a constant `T`
has `P[some bad component of diameter > T meets B_{2L}(z)] ≳ L ^ d e^{-c q T}`, which grows in
`L`, so the tube radius must grow.  Getting the frozen anchor's *linear* budget needs the
detour cost charged per component (`≍ diam K`) rather than by the volume of a uniform tube,
i.e. a large-deviation bound on `∑_K diam K` along the geodesic.

## Source

`mfd:in-deterministic` and `s.tightness` (the detour).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The tube around the `ℓ∞` geodesic -/

/-- The `r`-neighbourhood of the `ℓ∞` geodesic from `v` to `w`, as a `Finset`. -/
def latticeTubeFinset (v w : Lattice d) (r : ℕ) : Finset (Lattice d) :=
  (Finset.range (latticeDist v w + 1)).biUnion
    fun k => latticeBallFinset (latticeGeodesic v w k) r

theorem mem_latticeTubeFinset {v w u : Lattice d} {r k : ℕ}
    (hk : k ≤ latticeDist v w) (hu : latticeDist (latticeGeodesic v w k) u ≤ r) :
    u ∈ latticeTubeFinset v w r :=
  Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega),
    mem_latticeBallFinset_iff.mpr hu⟩

theorem latticeGeodesic_mem_latticeTubeFinset {v w : Lattice d} {r k : ℕ}
    (hk : k ≤ latticeDist v w) : latticeGeodesic v w k ∈ latticeTubeFinset v w r :=
  mem_latticeTubeFinset hk (by rw [latticeDist_self]; exact Nat.zero_le r)

/-- The tube has at most `(latticeDist v w + 1) (2 r + 1) ^ d` sites. -/
theorem card_latticeTubeFinset_le (v w : Lattice d) (r : ℕ) :
    (latticeTubeFinset v w r).card ≤ (latticeDist v w + 1) * (2 * r + 1) ^ d := by
  classical
  calc (latticeTubeFinset v w r).card
      ≤ ∑ k ∈ Finset.range (latticeDist v w + 1),
          (latticeBallFinset (latticeGeodesic v w k) r).card := Finset.card_biUnion_le
    _ = (latticeDist v w + 1) * (2 * r + 1) ^ d := by
        simp [card_latticeBallFinset]

/-! ## Loop erasure: reachability inside a finite set is a short path -/

/-- **A path confined to a finite set can be taken with at most that many vertices.**
Loop erasure (`exists_nodup_isChain`) keeps the endpoints and the step bound and makes the
vertex list repetition-free, so its length is the cardinality of a subset of `F`. -/
theorem exists_short_jStepPath {J : ℕ} {S : Set (Lattice d)} {F : Finset (Lattice d)}
    (hSF : S ⊆ (F : Set (Lattice d))) {v w : Lattice d} (h : JStepReachableIn J S v w) :
    ∃ path : List (Lattice d),
      path.head? = some v ∧ path.getLast? = some w ∧ IsJStepListPath J path ∧
        (∀ u ∈ path, u ∈ S) ∧ path.length ≤ F.card := by
  classical
  obtain ⟨p, hhead, hlast, hstep, hmem⟩ := h
  obtain ⟨p', hchain', hsub', hhead', hlast', hnd'⟩ :=
    exists_nodup_isChain p ((isJStepListPath_iff_isChain p).mp hstep)
  refine ⟨p', by rw [hhead', hhead], by rw [hlast', hlast],
    (isJStepListPath_iff_isChain p').mpr hchain',
    fun u hu => hmem u (hsub'.subset hu), ?_⟩
  have hcard : p'.toFinset.card = p'.length := List.toFinset_card_of_nodup hnd'
  have hsubF : p'.toFinset ⊆ F := by
    intro u hu
    exact hSF (hmem u (hsub'.subset (List.mem_toFinset.mp hu)))
  rw [← hcard]
  exact Finset.card_le_card hsubF

/-! ## A diameter bound in lattice-distance form -/

/-- `HasLatticeDiameterAtMost` at a natural threshold is a lattice-distance bound. -/
theorem latticeDist_le_of_hasLatticeDiameterAtMost_nat {S : Set (Lattice d)} {T : ℕ}
    (h : HasLatticeDiameterAtMost S (T : ℝ)) {v w : Lattice d} (hv : v ∈ S) (hw : w ∈ S) :
    latticeDist v w ≤ T := by
  refine latticeDist_le_iff.mpr fun i => ?_
  have hi := h v hv w hw i
  have hz : ((|v i - w i| : ℤ) : ℝ) ≤ ((T : ℤ) : ℝ) := by push_cast at hi ⊢; linarith
  have hz' : (|v i - w i| : ℤ) ≤ (T : ℤ) := by exact_mod_cast hz
  rw [Int.abs_eq_natAbs] at hz'
  omega

/-! ## The tube confinement -/

/-- **The good connection can be confined to a tube around the geodesic.**

Let `v` be good and let `w` be reachable from `v` through good sites.  If every bad `1`-step
component met by the `ℓ∞` geodesic from `v` to `w` has all its sites within `T` of the
geodesic site that meets it, then `v` and `w` are joined by good sites lying within `T + 1` of
the geodesic.

The proof is the walk of
`goodConnectedInDoubleBallAt_of_timarBoundaryComponentConnectivity` with two changes: the
target set is the tube rather than the double ball, and the hypothesis that both endpoints lie
in large good components — used there only to place `w` in the same complementary component as
`v` — is replaced by the reachability hypothesis, which says that directly.  In particular no
dimension restriction is needed: the Timár lemma
(`timarBoundaryComponentConnectivity`) is proved for every `d`. -/
theorem jStepReachableIn_good_tube_of_bad_diameter
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω} {v w : Lattice d} {T : ℕ}
    (hvgood : IsPercolationGoodSite E Cbox ω v)
    (hreach : JStepReachableIn 1 {u | IsPercolationGoodSite E Cbox ω u} v w)
    (hbad : ∀ k, k ≤ latticeDist v w →
      ¬ IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
      ∀ u ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
          (latticeGeodesic v w k),
        latticeDist (latticeGeodesic v w k) u ≤ T) :
    JStepReachableIn 1
      ({u | IsPercolationGoodSite E Cbox ω u} ∩
        (latticeTubeFinset v w (T + 1) : Set (Lattice d))) v w := by
  classical
  have hgm : latticeGeodesic v w (latticeDist v w) = w :=
    latticeGeodesic_of_latticeDist_le le_rfl
  have hg0 : latticeGeodesic v w 0 = v := latticeGeodesic_zero v w
  have key : ∀ n k : ℕ, latticeDist v w - k ≤ n → k ≤ latticeDist v w →
      IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
      JStepReachableIn 1
        ({u | IsPercolationGoodSite E Cbox ω u} ∩
          (latticeTubeFinset v w (T + 1) : Set (Lattice d))) v (latticeGeodesic v w k) →
      JStepReachableIn 1
        ({u | IsPercolationGoodSite E Cbox ω u} ∩
          (latticeTubeFinset v w (T + 1) : Set (Lattice d))) v w := by
    intro n
    induction n with
    | zero =>
      intro k hkn hkm _ hr
      have hk : k = latticeDist v w := by omega
      subst hk
      rwa [hgm] at hr
    | succ n ih =>
      intro k hkn hkm hgood hr
      by_cases hkeq : k = latticeDist v w
      · subst hkeq
        rwa [hgm] at hr
      have hklt : k < latticeDist v w := lt_of_le_of_ne hkm hkeq
      by_cases hnext : IsPercolationGoodSite E Cbox ω (latticeGeodesic v w (k + 1))
      · have hstep : JStepReachableIn 1
            ({u | IsPercolationGoodSite E Cbox ω u} ∩
              (latticeTubeFinset v w (T + 1) : Set (Lattice d)))
            (latticeGeodesic v w k) (latticeGeodesic v w (k + 1)) :=
          jStepReachableIn_of_dist
            ⟨hgood, Finset.mem_coe.mpr (latticeGeodesic_mem_latticeTubeFinset hkm)⟩
            ⟨hnext, Finset.mem_coe.mpr
              (latticeGeodesic_mem_latticeTubeFinset (by omega))⟩
            (latticeDist_latticeGeodesic_succ v w k)
        exact ih (k + 1) (by omega) (by omega) hnext (hr.trans hstep)
      · have hKmem : latticeGeodesic v w (k + 1) ∈
            jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)) := self_mem_jStepComponent hnext
        have hKball : ∀ u ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)),
            latticeDist (latticeGeodesic v w (k + 1)) u ≤ T :=
          hbad (k + 1) (by omega) hnext
        have hgoodK : ∀ {p : Lattice d}, IsPercolationGoodSite E Cbox ω p →
            p ∈ (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)))ᶜ :=
          fun {_} hp hmem => (jStepComponent_subset hmem) hp
        have hvK := hgoodK hvgood
        have hGK : {u | IsPercolationGoodSite E Cbox ω u} ⊆
            (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)))ᶜ := fun _ hu => hgoodK hu
        have hTgtK : ({u | IsPercolationGoodSite E Cbox ω u} ∩
              (latticeTubeFinset v w (T + 1) : Set (Lattice d))) ⊆
            (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)))ᶜ := fun _ hu => hgoodK hu.1
        have hwC : w ∈ jStepComponent 1
            (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)))ᶜ v := jStepReachableIn_mono_set hGK hreach
        have hgkC : latticeGeodesic v w k ∈ jStepComponent 1
            (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)))ᶜ v := jStepReachableIn_mono_set hTgtK hr
        obtain ⟨b, hbk, hbm, hbC, hbmax⟩ :=
          exists_greatest_index
            (fun j => latticeGeodesic v w j ∉ jStepComponent 1
              (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
                (latticeGeodesic v w (k + 1)))ᶜ v)
            (latticeDist v w) (k + 1) (by omega)
            (fun hmem => (jStepComponent_subset hmem) hKmem)
        have hbne : b ≠ latticeDist v w := by
          intro hbeq
          exact hbC (by rw [hbeq, hgm]; exact hwC)
        have hblt : b < latticeDist v w := lt_of_le_of_ne hbm hbne
        have hb1C : latticeGeodesic v w (b + 1) ∈ jStepComponent 1
            (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)))ᶜ v :=
          not_not.mp (hbmax (b + 1) (by omega) (by omega))
        have hbK : latticeGeodesic v w b ∈
            jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)) := by
          by_contra hnotK
          refine hbC (mem_jStepComponent_of_dist_le hb1C hnotK ?_)
          rw [latticeDist_comm]
          exact latticeDist_latticeGeodesic_succ v w b
        have hb1out : latticeGeodesic v w (b + 1) ∈ outerBoundary
            (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1))) :=
          mem_outerBoundary_of_step hbK (jStepComponent_subset hb1C)
            (latticeDist_latticeGeodesic_succ v w b)
        have hgkout : latticeGeodesic v w k ∈ outerBoundary
            (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1))) := by
          refine mem_outerBoundary_of_step hKmem (hgoodK hgood) ?_
          rw [latticeDist_comm]
          exact latticeDist_latticeGeodesic_succ v w k
        have hKfin : (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
            (latticeGeodesic v w (k + 1))).Finite :=
          finite_of_forall_latticeDist_le hKball
        have hKne : (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
            (latticeGeodesic v w (k + 1))).Nonempty := ⟨_, hKmem⟩
        have hKconn : ∀ a ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)),
            ∀ b' ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)),
            JStepReachableIn 1 (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1))) a b' := fun a ha b' hb' =>
          jStepReachableIn_within_jStepComponent ha hb'
        have hpath := timarBoundaryComponentConnectivity d _ hKfin hKne hKconn v hvK
          (latticeGeodesic v w k) ⟨hgkout, hgkC⟩
          (latticeGeodesic v w (b + 1)) ⟨hb1out, hb1C⟩
        have hvisT : visibleBoundary (jStepComponent 1
              {x | ¬ IsPercolationGoodSite E Cbox ω x} (latticeGeodesic v w (k + 1))) v ⊆
            ({u | IsPercolationGoodSite E Cbox ω u} ∩
              (latticeTubeFinset v w (T + 1) : Set (Lattice d))) := by
          intro u hu
          refine ⟨isPercolationGoodSite_of_mem_outerBoundary_badComponent le_rfl hu.1,
            Finset.mem_coe.mpr (mem_latticeTubeFinset (k := k + 1) (by omega) ?_)⟩
          exact latticeDist_le_of_outerBoundary hKball hu.1
        have hdetour := jStepReachableIn_mono_set hvisT hpath
        have hb1good : IsPercolationGoodSite E Cbox ω (latticeGeodesic v w (b + 1)) :=
          (hvisT ⟨hb1out, hb1C⟩).1
        exact ih (b + 1) (by omega) (by omega) hb1good (hr.trans hdetour)
  have hvT : v ∈ ({u | IsPercolationGoodSite E Cbox ω u} ∩
      (latticeTubeFinset v w (T + 1) : Set (Lattice d))) := by
    refine ⟨hvgood, Finset.mem_coe.mpr ?_⟩
    refine mem_latticeTubeFinset (k := 0) (Nat.zero_le _) ?_
    rw [hg0, latticeDist_self]
    exact Nat.zero_le _
  refine key (latticeDist v w) 0 (by omega) (by omega) ?_ ?_
  · rw [hg0]; exact hvgood
  · rw [hg0]
    exact jStepReachableIn_of_dist hvT hvT (by rw [latticeDist_self]; exact Nat.zero_le 1)

/-! ## The length budget the tube costs -/

/-- **The good detour, with its length.**  Under the same hypotheses the connection is
realised by a good `1`-step path with at most `(latticeDist v w + 1) (2 T + 3) ^ d`
vertices. -/
theorem isShortGoodPath_of_bad_diameter
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω} {v w : Lattice d} {T : ℕ}
    (hvgood : IsPercolationGoodSite E Cbox ω v)
    (hreach : JStepReachableIn 1 {u | IsPercolationGoodSite E Cbox ω u} v w)
    (hbad : ∀ k, k ≤ latticeDist v w →
      ¬ IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
      ∀ u ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
          (latticeGeodesic v w k),
        latticeDist (latticeGeodesic v w k) u ≤ T) :
    IsShortGoodPath E Cbox ω
      (((latticeDist v w + 1) * (2 * (T + 1) + 1) ^ d : ℕ) : ℝ) v w := by
  obtain ⟨p, hhead, hlast, hstep, hmem, hlen⟩ :=
    exists_short_jStepPath (F := latticeTubeFinset v w (T + 1)) Set.inter_subset_right
      (jStepReachableIn_good_tube_of_bad_diameter hvgood hreach hbad)
  refine ⟨p, hhead, hlast, ?_, hstep, fun u hu => (hmem u hu).1⟩
  have hle : p.length ≤ (latticeDist v w + 1) * (2 * (T + 1) + 1) ^ d :=
    hlen.trans (card_latticeTubeFinset_le v w (T + 1))
  exact_mod_cast hle

/-! ## The chemical-distance failure event with a free budget -/

/-- `chemicalDistanceFailureEvent` with the length budget left free, so that a budget which is
not a fixed multiple of `L` can be discussed.  The frozen event is the case
`bound = Clen * L`. -/
def chemicalDistanceFailureEventAt (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (bound : ℝ)
    (z : Lattice d) (L : ℕ) : Set Ω :=
  {ω | ∃ v w : Lattice d,
      InLatticeBallReal z v L ∧ InLatticeBallReal z w L ∧
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) v ∧
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω ((L : ℝ) / 20) w ∧
      ¬ IsShortGoodPath E Cbox ω bound v w}

theorem chemicalDistanceFailureEvent_eq_at (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (Clen : ℝ) (z : Lattice d) (L : ℕ) :
    chemicalDistanceFailureEvent E Cbox Clen z L =
      chemicalDistanceFailureEventAt E Cbox (Clen * L) z L := rfl

theorem chemicalDistanceFailureEventAt_mono {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {bound bound' : ℝ} (h : bound ≤ bound') {z : Lattice d} {L : ℕ} :
    chemicalDistanceFailureEventAt E Cbox bound' z L ⊆
      chemicalDistanceFailureEventAt E Cbox bound z L := by
  rintro ω ⟨v, w, hv, hw, hvc, hwc, hshort⟩
  exact ⟨v, w, hv, hw, hvc, hwc, fun hp => hshort (hp.mono h)⟩

/-- **The split of `D_L(z)` used by P-404.**

If the length budget covers the tube of radius `T + 1` around a geodesic of `2 L + 1` sites,
then the chemical-distance failure event at that budget is contained in the union of the
*connectivity* failure — bounded by `exists_connectivity_tail` — and the event that some bad
`1`-step component meeting `B_{2L}(z)` has `ℓ∞` diameter exceeding `T`, whose tail is the
already-proved clause-(ii) estimate.

Contrast `chemicalDistanceFailureEvent_subset_union`, which isolates the length residual
without bounding it: here the residual is *bounded*, at the price of a budget that grows with
the tube radius `T`. -/
theorem chemicalDistanceFailureEventAt_subset_union (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (z : Lattice d) (L T : ℕ) {bound : ℝ}
    (hbound : (((2 * L + 1) * (2 * (T + 1) + 1) ^ d : ℕ) : ℝ) ≤ bound) :
    chemicalDistanceFailureEventAt E Cbox bound z L ⊆
      {ω | ¬ GoodConnectedInDoubleBallAt E Cbox ω z L ((L : ℝ) / 20)} ∪
        badComponentFailureEvent E Cbox 1 z (2 * L : ℝ) (T : ℝ) := by
  rintro ω ⟨v, w, hv, hw, hvc, hwc, hshort⟩
  by_cases hconn : GoodConnectedInDoubleBallAt E Cbox ω z L ((L : ℝ) / 20)
  · refine Or.inr ?_
    by_contra hcon
    refine hshort ?_
    -- no bad component meeting `B_{2L}(z)` has diameter above `T`
    have hdiam : ∀ u : Lattice d, InLatticeBallReal z u (2 * L : ℝ) →
        ¬ IsPercolationGoodSite E Cbox ω u →
        HasLatticeDiameterAtMost
          (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x} u) (T : ℝ) := by
      intro u hu hubad
      by_contra hd
      exact hcon ⟨u, hu, hubad, hd⟩
    -- the endpoints are close
    have hzv : latticeDist z v ≤ L := latticeDist_le_of_inLatticeBallReal_natRadius hv
    have hzw : latticeDist z w ≤ L := latticeDist_le_of_inLatticeBallReal_natRadius hw
    have hvw : latticeDist v w ≤ 2 * L := by
      have := latticeDist_triangle v z w
      rw [latticeDist_comm v z] at this
      omega
    have hL2 : (L : ℝ) ≤ (2 * L : ℝ) := by
      have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      linarith
    -- the geodesic hypothesis
    have hbad : ∀ k, k ≤ latticeDist v w →
        ¬ IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
        ∀ u ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
            (latticeGeodesic v w k),
          latticeDist (latticeGeodesic v w k) u ≤ T := by
      intro k _ hkbad u hu
      have hball : InLatticeBallReal z (latticeGeodesic v w k) (2 * L : ℝ) :=
        inLatticeBallReal_mono hL2 (inLatticeBallReal_latticeGeodesic hv hw k)
      refine latticeDist_le_of_hasLatticeDiameterAtMost_nat
        (hdiam _ hball hkbad) (self_mem_jStepComponent hkbad) hu
    have hreach : JStepReachableIn 1 {u | IsPercolationGoodSite E Cbox ω u} v w :=
      jStepReachableIn_mono_set (fun _ hu => hu.1) (hconn v w hv hw hvc hwc)
    refine IsShortGoodPath.mono ?_
      (isShortGoodPath_of_bad_diameter hvc.1 hreach hbad)
    refine le_trans ?_ hbound
    have hmono : (latticeDist v w + 1) * (2 * (T + 1) + 1) ^ d ≤
        (2 * L + 1) * (2 * (T + 1) + 1) ^ d :=
      Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast hmono
  · exact Or.inl hconn

/-! ## The small-scale regime: an all-good ball needs no detour at all -/

/-- If every site of the `ℓ∞` geodesic from `v` to `w` is good, the geodesic itself is a good
path with `latticeDist v w + 1` vertices. -/
theorem isShortGoodPath_of_forall_latticeGeodesic_good
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω} {v w : Lattice d}
    (h : ∀ k, k ≤ latticeDist v w →
      IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k)) :
    IsShortGoodPath E Cbox ω ((latticeDist v w + 1 : ℕ) : ℝ) v w := by
  obtain ⟨p, hhead, hlast, hstep, hmem, hlen⟩ :=
    exists_short_jStepPath (F := latticeTubeFinset v w 0) Set.inter_subset_right
      (jStepReachableIn_of_forall_latticeGeodesic_mem
        (S := {u | IsPercolationGoodSite E Cbox ω u} ∩
          (latticeTubeFinset v w 0 : Set (Lattice d)))
        (fun k hk => ⟨h k hk,
          Finset.mem_coe.mpr (latticeGeodesic_mem_latticeTubeFinset hk)⟩))
  refine ⟨p, hhead, hlast, ?_, hstep, fun u hu => (hmem u hu).1⟩
  have hcard : p.length ≤ latticeDist v w + 1 := by
    have := hlen.trans (card_latticeTubeFinset_le v w 0)
    simpa using this
  exact_mod_cast hcard

/-- **At small scales the failure event is contained in a union of bad-site events.**

If the length budget is at least `2 L + 1` then the chemical-distance failure event at scale
`L` forces some site of `B_L(z)` to be bad: otherwise the `ℓ∞` geodesic between the two
endpoints, which stays in `B_L(z)`, is itself a good path with at most `2 L + 1` vertices.
This is what carries the bound through the finitely many scales below the threshold of
`exists_connectivity_tail`. -/
theorem chemicalDistanceFailureEventAt_subset_badSite_union (E : ℕ → Lattice d → Set Ω)
    (Cbox : ℕ) (z : Lattice d) (L : ℕ) {bound : ℝ}
    (hbound : ((2 * L + 1 : ℕ) : ℝ) ≤ bound) :
    chemicalDistanceFailureEventAt E Cbox bound z L ⊆
      ⋃ u ∈ latticeBallFinset z L, percolationBadSite E Cbox u := by
  rintro ω ⟨v, w, hv, hw, hvc, hwc, hshort⟩
  by_contra hcon
  refine hshort ?_
  have hgood : ∀ u : Lattice d, latticeDist z u ≤ L → IsPercolationGoodSite E Cbox ω u := by
    intro u hu
    by_contra hbad
    exact hcon (Set.mem_biUnion (mem_latticeBallFinset_iff.mpr hu) hbad)
  have hzv : latticeDist z v ≤ L := latticeDist_le_of_inLatticeBallReal_natRadius hv
  have hzw : latticeDist z w ≤ L := latticeDist_le_of_inLatticeBallReal_natRadius hw
  have hvw : latticeDist v w ≤ 2 * L := by
    have := latticeDist_triangle v z w
    rw [latticeDist_comm v z] at this
    omega
  refine IsShortGoodPath.mono ?_
    (isShortGoodPath_of_forall_latticeGeodesic_good (E := E) (Cbox := Cbox) (ω := ω)
      (fun k _ => hgood _ (latticeDist_le_of_inLatticeBallReal_natRadius
        (inLatticeBallReal_latticeGeodesic hv hw k))))
  refine le_trans ?_ hbound
  have : latticeDist v w + 1 ≤ 2 * L + 1 := by omega
  exact_mod_cast this

/-! ## The trade-off between the frozen linear budget and the tube radius -/



theorem chemicalDistanceFailureEvent_subset_union_of_diameter (E : ℕ → Lattice d → Set Ω)
    (Cbox : ℕ) (Clen : ℝ) (z : Lattice d) (L T : ℕ) (hL : 1 ≤ L)
    (hClen : (3 : ℝ) * (((2 * (T + 1) + 1) ^ d : ℕ) : ℝ) ≤ Clen) :
    chemicalDistanceFailureEvent E Cbox Clen z L ⊆
      {ω | ¬ GoodConnectedInDoubleBallAt E Cbox ω z L ((L : ℝ) / 20)} ∪
        badComponentFailureEvent E Cbox 1 z (2 * L : ℝ) (T : ℝ) := by
  rw [chemicalDistanceFailureEvent_eq_at]
  refine chemicalDistanceFailureEventAt_subset_union E Cbox z L T ?_
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hM : (0 : ℝ) ≤ (((2 * (T + 1) + 1) ^ d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcast : ((((2 * L + 1) * (2 * (T + 1) + 1) ^ d : ℕ)) : ℝ)
      = (2 * (L : ℝ) + 1) * (((2 * (T + 1) + 1) ^ d : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  nlinarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
