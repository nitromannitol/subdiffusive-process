module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingChain
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalASDClauses

@[expose] public section

/-!
# Reading a crossing certificate off a crossing path

Given a `J`-step path that starts in `B_{l/3}(z)` and leaves `B_{2l/3}(z)`, this
file builds a **crossing chain** of cells (`CrossChain`) all of whose event cells
occur, and whose good-vertex cells are good vertices *of the path*.

The walk is the obvious one, run by strong induction on the number of remaining
steps.  At the current vertex `p k`:

* if `p k` is already outside `B_{2l/3}(z)`, one cell covering `p k` finishes the
  chain;
* if `p k` is percolation-good, emit the good cell `p k` and step to `p (k+1)`;
* if `p k` is bad, some `E j u` with `|u - p k| ≤ Cbox 3^j` occurs; emit the
  event cell at the snapped grid point `w` of `u`, whose radius
  `(Cbox + Cdep) 3^j` covers `p k`, and **jump** to the first later vertex
  outside `B_{rad}(w)` — or, if the path never leaves that ball before its end,
  stop, since then the cell itself already reaches outside `B_{2l/3}(z)`.

The jump is what keeps the chain short: a bad vertex costs one cell, not one
cell per step, and the cell's radius is paid for once.  Because the exit vertex
is within one `J`-step of a vertex of `B_{rad}(w)`, consecutive cells are within
reach in the sense of `cellReach`.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-- A bad site carries an occurring event whose snapped cell covers it. -/
theorem exists_cell_of_not_isPercolationGoodSite {E : ℕ → Lattice d → Set Ω}
    {Cbox Cdep : ℕ} {ω : Ω} {v : Lattice d}
    (hbad : ¬ IsPercolationGoodSite E Cbox ω v) :
    ∃ c : CrossCell d, ω ∈ cellOccurs E Cdep c ∧
      latticeDist v (cellCenter Cdep c) ≤ cellRadius Cbox Cdep c ∧
      (∀ w : Lattice d, c ≠ Sum.inr w) := by
  simp only [IsPercolationGoodSite, InInfluenceBox, not_forall, not_not] at hbad
  obtain ⟨j, u, hu, hmem⟩ := hbad
  refine ⟨Sum.inl (j, crossSnap Cdep j u), ?_, ?_, by simp⟩
  · refine Set.mem_iUnion₂.mpr ⟨u, ?_, hmem⟩
    rw [mem_latticeBallFinset_iff, latticeDist_comm]
    exact latticeDist_crossGrid_crossSnap Cdep j u
  · show latticeDist v (crossGrid Cdep j (crossSnap Cdep j u)) ≤ (Cbox + Cdep) * 3 ^ j
    calc latticeDist v (crossGrid Cdep j (crossSnap Cdep j u))
        ≤ latticeDist v u + latticeDist u (crossGrid Cdep j (crossSnap Cdep j u)) :=
          latticeDist_triangle _ _ _
      _ ≤ Cbox * 3 ^ j + Cdep * 3 ^ j := by
          refine Nat.add_le_add ?_ (latticeDist_crossGrid_crossSnap Cdep j u)
          rwa [latticeDist_comm]
      _ = (Cbox + Cdep) * 3 ^ j := by ring

/-- Every vertex is covered by a single cell: the good cell at that vertex, or
an event cell if it is bad. -/
theorem exists_covering_cell (E : ℕ → Lattice d → Set Ω) (Cbox Cdep : ℕ) (ω : Ω)
    (v : Lattice d) :
    ∃ c : CrossCell d, ω ∈ cellOccurs E Cdep c ∧
      latticeDist v (cellCenter Cdep c) ≤ cellRadius Cbox Cdep c ∧
      (∀ w : Lattice d, c = Sum.inr w →
        w = v ∧ IsPercolationGoodSite E Cbox ω v) := by
  by_cases hgood : IsPercolationGoodSite E Cbox ω v
  · refine ⟨Sum.inr v, Set.mem_univ _, ?_, ?_⟩
    · simp [cellCenter, cellRadius]
    · rintro w hw
      exact ⟨(Sum.inr_injective hw).symm, hgood⟩
  · obtain ⟨c, hc1, hc2, hc3⟩ :=
      exists_cell_of_not_isPercolationGoodSite (Cdep := Cdep) hgood
    exact ⟨c, hc1, hc2, fun w hw => absurd hw (hc3 w)⟩

/-- **The walk.**  From any index of a path whose last vertex is outside
`B_{2l/3}(z)`, a crossing chain covering the current vertex is built. -/
theorem exists_chain_from_index (E : ℕ → Lattice d → Set Ω) (Cbox Cdep J : ℕ)
    (ω : Ω) (z : Lattice d) (l : ℕ) (p : ℕ → Lattice d) (b : ℕ)
    (hp : IsJStepPath J p b) (hout : 2 * l < 3 * latticeDist z (p b)) :
    ∀ k, k ≤ b →
      ∃ L : List (CrossCell d), L ≠ [] ∧ L.IsChain (cellReach Cbox Cdep J) ∧
        ω ∈ chainEvent E Cdep L ∧
        (∀ c ∈ L.head?, latticeDist (p k) (cellCenter Cdep c) ≤
          cellRadius Cbox Cdep c) ∧
        (∀ c ∈ L.getLast?, 2 * l ≤
          3 * (latticeDist z (cellCenter Cdep c) + cellRadius Cbox Cdep c)) ∧
        (∀ v : Lattice d, Sum.inr v ∈ L →
          ∃ i, k ≤ i ∧ i ≤ b ∧ v = p i ∧ IsPercolationGoodSite E Cbox ω (p i)) := by
  classical
  intro k
  induction hn : (b - k) using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    intro hk
    obtain ⟨c, hcocc, hccov, hcgood⟩ := exists_covering_cell E Cbox Cdep ω (p k)
    by_cases hcase : 2 * l < 3 * latticeDist z (p k)
    · -- the current vertex is already outside: one cell suffices
      refine ⟨[c], by simp, List.isChain_singleton c, ?_, ?_, ?_, ?_⟩
      · intro c' hc'
        simp only [List.mem_singleton] at hc'
        subst hc'
        exact hcocc
      · intro c' hc'
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
        subst hc'
        exact hccov
      · intro c' hc'
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hc'
        subst hc'
        have hle : latticeDist z (p k) ≤
            latticeDist z (cellCenter Cdep c) + cellRadius Cbox Cdep c := by
          refine le_trans (latticeDist_triangle z (cellCenter Cdep c) (p k)) ?_
          exact Nat.add_le_add_left (by rwa [latticeDist_comm]) _
        omega
      · intro v hv
        simp only [List.mem_singleton] at hv
        obtain ⟨rfl, hg⟩ := hcgood v hv.symm
        exact ⟨k, le_rfl, hk, rfl, hg⟩
    · -- not yet outside, so the path continues
      have hkb : k < b := by
        rcases Nat.lt_or_ge k b with h | h
        · exact h
        · exact absurd (by omega : k = b) (by rintro rfl; exact hcase hout)
      by_cases hgood : IsPercolationGoodSite E Cbox ω (p k)
      · -- a good vertex: step by one
        obtain ⟨L, hne, hchain, hev, hhead, hlast, hgc⟩ :=
          ih (b - (k + 1)) (by omega) (k + 1) rfl (by omega)
        refine ⟨Sum.inr (p k) :: L, by simp, ?_, ?_, ?_, ?_, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, hchain⟩
          intro y hy
          show latticeDist (cellCenter Cdep (Sum.inr (p k))) (cellCenter Cdep y) ≤
            cellRadius Cbox Cdep (Sum.inr (p k)) + cellRadius Cbox Cdep y + J
          have hcov := hhead y hy
          have hstep : latticeDist (p k) (p (k + 1)) ≤ J := hp k hkb
          have := latticeDist_triangle (p k) (p (k + 1)) (cellCenter Cdep y)
          show latticeDist (p k) (cellCenter Cdep y) ≤ 0 + cellRadius Cbox Cdep y + J
          omega
        · intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc'
          · exact Set.mem_univ _
          · exact hev c' hc'
        · intro c' hc'
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
          subst hc'
          simp [cellCenter, cellRadius]
        · intro c' hc'
          rcases L with _ | ⟨e, L'⟩
          · exact absurd rfl hne
          · rw [List.getLast?_cons_cons] at hc'
            exact hlast c' hc'
        · intro v hv
          rcases List.mem_cons.mp hv with hv | hv
          · obtain rfl : v = p k := Sum.inr_injective hv
            exact ⟨k, le_rfl, le_of_lt hkb, rfl, hgood⟩
          · obtain ⟨i, hi1, hi2, hi3, hi4⟩ := hgc v hv
            exact ⟨i, by omega, hi2, hi3, hi4⟩
      · -- a bad vertex: emit its cell and jump out of the cell's ball
        obtain ⟨cb, hbocc, hbcov, hbev⟩ :=
          exists_cell_of_not_isPercolationGoodSite (Cdep := Cdep) (Cbox := Cbox) hgood
        set w : Lattice d := cellCenter Cdep cb with hw
        set rad : ℕ := cellRadius Cbox Cdep cb with hrad
        by_cases hstay : latticeDist w (p b) ≤ rad
        · -- the path never leaves the cell: the cell already reaches outside
          refine ⟨[cb], by simp, List.isChain_singleton cb, ?_, ?_, ?_, ?_⟩
          · intro c' hc'
            simp only [List.mem_singleton] at hc'
            subst hc'
            exact hbocc
          · intro c' hc'
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
            subst hc'
            exact hbcov
          · intro c' hc'
            simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hc'
            subst hc'
            have hle : latticeDist z (p b) ≤ latticeDist z w + rad :=
              le_trans (latticeDist_triangle z w (p b)) (Nat.add_le_add_left hstay _)
            show 2 * l ≤ 3 * (latticeDist z w + rad)
            omega
          · intro v hv
            simp only [List.mem_singleton] at hv
            exact absurd hv.symm (hbev v)
        · -- the path leaves the cell: jump to the first exit
          have hex : ∃ i, k < i ∧ i ≤ b ∧ rad < latticeDist w (p i) :=
            ⟨b, hkb, le_rfl, Nat.lt_of_not_ge hstay⟩
          classical
          set i : ℕ := Nat.find hex with hi
          obtain ⟨hik, hib, hiexit⟩ := Nat.find_spec hex
          have hprev : latticeDist w (p (i - 1)) ≤ rad := by
            rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hik) with heq | hlt
            · have : i - 1 = k := by omega
              rw [this, latticeDist_comm]
              exact hbcov
            · by_contra hcon
              have hlt' : i - 1 < i := by omega
              exact absurd (Nat.find_min hex hlt' ⟨by omega, by omega, Nat.lt_of_not_ge hcon⟩)
                (by simp)
          have hnear : latticeDist w (p i) ≤ rad + J := by
            have hstep : latticeDist (p (i - 1)) (p i) ≤ J := by
              have := hp (i - 1) (by omega)
              rwa [show i - 1 + 1 = i by omega] at this
            calc latticeDist w (p i) ≤ latticeDist w (p (i - 1)) +
                  latticeDist (p (i - 1)) (p i) := latticeDist_triangle _ _ _
              _ ≤ rad + J := Nat.add_le_add hprev hstep
          obtain ⟨L, hne, hchain, hev, hhead, hlast, hgc⟩ :=
            ih (b - i) (by omega) i rfl hib
          refine ⟨cb :: L, by simp, ?_, ?_, ?_, ?_, ?_⟩
          · refine List.isChain_cons.mpr ⟨?_, hchain⟩
            intro y hy
            have hcov := hhead y hy
            have htri := latticeDist_triangle w (p i) (cellCenter Cdep y)
            show latticeDist w (cellCenter Cdep y) ≤ rad + cellRadius Cbox Cdep y + J
            omega
          · intro c' hc'
            rcases List.mem_cons.mp hc' with rfl | hc'
            · exact hbocc
            · exact hev c' hc'
          · intro c' hc'
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
            subst hc'
            exact hbcov
          · intro c' hc'
            rcases L with _ | ⟨e, L'⟩
            · exact absurd rfl hne
            · rw [List.getLast?_cons_cons] at hc'
              exact hlast c' hc'
          · intro v hv
            rcases List.mem_cons.mp hv with hv | hv
            · exact absurd hv.symm (hbev v)
            · obtain ⟨i', hi1, hi2, hi3, hi4⟩ := hgc v hv
              exact ⟨i', by omega, hi2, hi3, hi4⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
