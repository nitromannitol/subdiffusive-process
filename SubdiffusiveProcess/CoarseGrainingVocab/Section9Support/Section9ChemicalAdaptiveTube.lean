import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTube




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## The tube with a per-index radius schedule -/

/-- The tube around the `ℓ∞` geodesic from `v` to `w` whose radius at the `k`-th geodesic
site is `r k`. -/
def latticeAdaptiveTubeFinset (v w : Lattice d) (r : ℕ → ℕ) : Finset (Lattice d) :=
  (Finset.range (latticeDist v w + 1)).biUnion
    fun k => latticeBallFinset (latticeGeodesic v w k) (r k)

theorem mem_latticeAdaptiveTubeFinset {v w u : Lattice d} {r : ℕ → ℕ} {k : ℕ}
    (hk : k ≤ latticeDist v w) (hu : latticeDist (latticeGeodesic v w k) u ≤ r k) :
    u ∈ latticeAdaptiveTubeFinset v w r :=
  Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega),
    mem_latticeBallFinset_iff.mpr hu⟩

theorem latticeGeodesic_mem_latticeAdaptiveTubeFinset {v w : Lattice d} {r : ℕ → ℕ} {k : ℕ}
    (hk : k ≤ latticeDist v w) : latticeGeodesic v w k ∈ latticeAdaptiveTubeFinset v w r :=
  mem_latticeAdaptiveTubeFinset hk (by rw [latticeDist_self]; exact Nat.zero_le _)

/-- **The size of the adaptive tube**: the sum of the ball sizes along the geodesic. -/
theorem card_latticeAdaptiveTubeFinset_le (v w : Lattice d) (r : ℕ → ℕ) :
    (latticeAdaptiveTubeFinset v w r).card ≤
      ∑ k ∈ Finset.range (latticeDist v w + 1), (2 * r k + 1) ^ d := by
  classical
  refine le_trans Finset.card_biUnion_le ?_
  exact Finset.sum_le_sum fun k _ => le_of_eq (card_latticeBallFinset _ _)

/-! ## The confinement -/

/-- **The good connection is confined to the adaptive tube.**

Verbatim the walk of `jStepReachableIn_good_tube_of_bad_diameter`, with the uniform radius
`T + 1` replaced by the schedule `fun k => T k + 1`.  The walk leaves the geodesic only at an
index whose site is bad, and only as far as the boundary of the component there, so only the
radius at *that* index is used. -/
theorem jStepReachableIn_good_adaptiveTube_of_bad_diameter
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω} {v w : Lattice d} {T : ℕ → ℕ}
    (hvgood : IsPercolationGoodSite E Cbox ω v)
    (hreach : JStepReachableIn 1 {u | IsPercolationGoodSite E Cbox ω u} v w)
    (hbad : ∀ k, k ≤ latticeDist v w →
      ¬ IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
      ∀ u ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
          (latticeGeodesic v w k),
        latticeDist (latticeGeodesic v w k) u ≤ T k) :
    JStepReachableIn 1
      ({u | IsPercolationGoodSite E Cbox ω u} ∩
        (latticeAdaptiveTubeFinset v w (fun k => T k + 1) : Set (Lattice d))) v w := by
  classical
  set r : ℕ → ℕ := fun k => T k + 1 with hr
  have hgm : latticeGeodesic v w (latticeDist v w) = w :=
    latticeGeodesic_of_latticeDist_le le_rfl
  have hg0 : latticeGeodesic v w 0 = v := latticeGeodesic_zero v w
  have key : ∀ n k : ℕ, latticeDist v w - k ≤ n → k ≤ latticeDist v w →
      IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
      JStepReachableIn 1
        ({u | IsPercolationGoodSite E Cbox ω u} ∩
          (latticeAdaptiveTubeFinset v w r : Set (Lattice d))) v (latticeGeodesic v w k) →
      JStepReachableIn 1
        ({u | IsPercolationGoodSite E Cbox ω u} ∩
          (latticeAdaptiveTubeFinset v w r : Set (Lattice d))) v w := by
    intro n
    induction n with
    | zero =>
      intro k hkn hkm _ hrch
      have hk : k = latticeDist v w := by omega
      subst hk
      rwa [hgm] at hrch
    | succ n ih =>
      intro k hkn hkm hgood hrch
      by_cases hkeq : k = latticeDist v w
      · subst hkeq
        rwa [hgm] at hrch
      have hklt : k < latticeDist v w := lt_of_le_of_ne hkm hkeq
      by_cases hnext : IsPercolationGoodSite E Cbox ω (latticeGeodesic v w (k + 1))
      · have hstep : JStepReachableIn 1
            ({u | IsPercolationGoodSite E Cbox ω u} ∩
              (latticeAdaptiveTubeFinset v w r : Set (Lattice d)))
            (latticeGeodesic v w k) (latticeGeodesic v w (k + 1)) :=
          jStepReachableIn_of_dist
            ⟨hgood, Finset.mem_coe.mpr (latticeGeodesic_mem_latticeAdaptiveTubeFinset hkm)⟩
            ⟨hnext, Finset.mem_coe.mpr
              (latticeGeodesic_mem_latticeAdaptiveTubeFinset (by omega))⟩
            (latticeDist_latticeGeodesic_succ v w k)
        exact ih (k + 1) (by omega) (by omega) hnext (hrch.trans hstep)
      · have hKmem : latticeGeodesic v w (k + 1) ∈
            jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)) := self_mem_jStepComponent hnext
        have hKball : ∀ u ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)),
            latticeDist (latticeGeodesic v w (k + 1)) u ≤ T (k + 1) :=
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
              (latticeAdaptiveTubeFinset v w r : Set (Lattice d))) ⊆
            (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)))ᶜ := fun _ hu => hgoodK hu.1
        have hwC : w ∈ jStepComponent 1
            (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)))ᶜ v := jStepReachableIn_mono_set hGK hreach
        have hgkC : latticeGeodesic v w k ∈ jStepComponent 1
            (jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w (k + 1)))ᶜ v := jStepReachableIn_mono_set hTgtK hrch
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
              (latticeAdaptiveTubeFinset v w r : Set (Lattice d))) := by
          intro u hu
          refine ⟨isPercolationGoodSite_of_mem_outerBoundary_badComponent le_rfl hu.1,
            Finset.mem_coe.mpr (mem_latticeAdaptiveTubeFinset (k := k + 1) (by omega) ?_)⟩
          exact latticeDist_le_of_outerBoundary hKball hu.1
        have hdetour := jStepReachableIn_mono_set hvisT hpath
        have hb1good : IsPercolationGoodSite E Cbox ω (latticeGeodesic v w (b + 1)) :=
          (hvisT ⟨hb1out, hb1C⟩).1
        exact ih (b + 1) (by omega) (by omega) hb1good (hrch.trans hdetour)
  have hvT : v ∈ ({u | IsPercolationGoodSite E Cbox ω u} ∩
      (latticeAdaptiveTubeFinset v w r : Set (Lattice d))) := by
    refine ⟨hvgood, Finset.mem_coe.mpr ?_⟩
    refine mem_latticeAdaptiveTubeFinset (k := 0) (Nat.zero_le _) ?_
    rw [hg0, latticeDist_self]
    exact Nat.zero_le _
  refine key (latticeDist v w) 0 (by omega) (by omega) ?_ ?_
  · rw [hg0]; exact hvgood
  · rw [hg0]
    exact jStepReachableIn_of_dist hvT hvT (by rw [latticeDist_self]; exact Nat.zero_le 1)

/-! ## The length the adaptive tube costs -/

/-- The per-component length budget of a radius schedule along the geodesic. -/
def geodesicTubeCost (dim : ℕ) (v w : Lattice d) (T : ℕ → ℕ) : ℕ :=
  ∑ k ∈ Finset.range (latticeDist v w + 1), (2 * T k + 3) ^ dim

/-- **The good detour, charged per component.**  Under the adaptive confinement the
connection is realised by a good `1`-step path with at most `geodesicTubeCost d v w T`
vertices. -/
theorem isShortGoodPath_of_bad_diameter_adaptive
    {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω} {v w : Lattice d} {T : ℕ → ℕ}
    (hvgood : IsPercolationGoodSite E Cbox ω v)
    (hreach : JStepReachableIn 1 {u | IsPercolationGoodSite E Cbox ω u} v w)
    (hbad : ∀ k, k ≤ latticeDist v w →
      ¬ IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
      ∀ u ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
          (latticeGeodesic v w k),
        latticeDist (latticeGeodesic v w k) u ≤ T k) :
    IsShortGoodPath E Cbox ω ((geodesicTubeCost d v w T : ℕ) : ℝ) v w := by
  classical
  obtain ⟨p, hhead, hlast, hstep, hmem, hlen⟩ :=
    exists_short_jStepPath (F := latticeAdaptiveTubeFinset v w (fun k => T k + 1))
      Set.inter_subset_right
      (jStepReachableIn_good_adaptiveTube_of_bad_diameter hvgood hreach hbad)
  refine ⟨p, hhead, hlast, ?_, hstep, fun u hu => (hmem u hu).1⟩
  have hcard := card_latticeAdaptiveTubeFinset_le v w (fun k => T k + 1)
  have hEq : ∑ k ∈ Finset.range (latticeDist v w + 1), (2 * (T k + 1) + 1) ^ d
      = geodesicTubeCost d v w T := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : 2 * (T k + 1) + 1 = 2 * T k + 3 := by omega
    rw [hk]
  have hle : p.length ≤ geodesicTubeCost d v w T := by
    refine hlen.trans ?_
    rw [← hEq]
    exact hcard
  exact_mod_cast hle

/-! ## The split of the frozen event at the linear budget -/

/-- **The residual of the linear budget.**

A sample lies in this event when, for the two endpoints witnessing the failure, *every*
admissible radius schedule along the geodesic already costs more than the budget.  A schedule
is admissible when it dominates the diameter of the bad component at every bad geodesic site.

This is the exact form of what P-407 owes: the frozen linear clause follows from a tail for
this event at the budget `Clen * L`, with `Clen` fixed before `L`. -/
def adaptiveTubeFailureEvent (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ)
    (z : Lattice d) (L : ℕ) (bud : ℝ) : Set Ω :=
  {ω | ∃ v w : Lattice d,
      InLatticeBallReal z v (L : ℝ) ∧ InLatticeBallReal z w (L : ℝ) ∧
      ∀ T : ℕ → ℕ,
        (∀ k, k ≤ latticeDist v w →
          ¬ IsPercolationGoodSite E Cbox ω (latticeGeodesic v w k) →
          ∀ u ∈ jStepComponent 1 {x | ¬ IsPercolationGoodSite E Cbox ω x}
              (latticeGeodesic v w k),
            latticeDist (latticeGeodesic v w k) u ≤ T k) →
        bud < ((geodesicTubeCost d v w T : ℕ) : ℝ)}

/-- **The P-407 split of `D_L(z)`.**

At *any* budget — in particular at the frozen linear budget `Clen * L` — the
chemical-distance failure event is contained in the union of the connectivity failure, whose
tail is already proved, and the adaptive-tube residual.

Contrast `Section9ChemicalTube.chemicalDistanceFailureEventAt_subset_union`, which needs the
budget to cover a *uniform* tube of radius `T + 1` and therefore cannot be linear: here no
hypothesis relates the budget to a threshold at all, because the residual carries the whole
per-component accounting. -/
theorem chemicalDistanceFailureEventAt_subset_union_adaptive
    (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (z : Lattice d) (L : ℕ) (bud : ℝ) :
    chemicalDistanceFailureEventAt E Cbox bud z L ⊆
      {ω | ¬ GoodConnectedInDoubleBallAt E Cbox ω z L ((L : ℝ) / 20)} ∪
        adaptiveTubeFailureEvent E Cbox z L bud := by
  rintro ω ⟨v, w, hv, hw, hvc, hwc, hshort⟩
  by_cases hconn : GoodConnectedInDoubleBallAt E Cbox ω z L ((L : ℝ) / 20)
  · refine Or.inr ⟨v, w, hv, hw, fun T hT => ?_⟩
    by_contra hcon
    push_neg at hcon
    have hreach : JStepReachableIn 1 {u | IsPercolationGoodSite E Cbox ω u} v w :=
      jStepReachableIn_mono_set (fun _ hu => hu.1) (hconn v w hv hw hvc hwc)
    exact hshort
      (IsShortGoodPath.mono hcon
        (isShortGoodPath_of_bad_diameter_adaptive hvc.1 hreach hT))
  · exact Or.inl hconn

/-- The frozen linear clause, split. -/
theorem chemicalDistanceFailureEvent_subset_union_adaptive
    (E : ℕ → Lattice d → Set Ω) (Cbox : ℕ) (Clen : ℝ) (z : Lattice d) (L : ℕ) :
    chemicalDistanceFailureEvent E Cbox Clen z L ⊆
      {ω | ¬ GoodConnectedInDoubleBallAt E Cbox ω z L ((L : ℝ) / 20)} ∪
        adaptiveTubeFailureEvent E Cbox z L (Clen * L) := by
  rw [chemicalDistanceFailureEvent_eq_at]
  exact chemicalDistanceFailureEventAt_subset_union_adaptive E Cbox z L (Clen * L)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
