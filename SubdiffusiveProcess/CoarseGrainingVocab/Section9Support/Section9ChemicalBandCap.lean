module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalBadChain
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalTimarSeparation

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## Boxes of bad sites -/

/-- Every site of the influence box of an occurring event is bad. -/
theorem not_isPercolationGoodSite_of_mem_influenceBox {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ}
    {ω : Ω} {j : ℕ} {u y : Lattice d} (hmem : ω ∈ E j u)
    (hy : latticeDist u y ≤ Cbox * 3 ^ j) :
    ¬ IsPercolationGoodSite E Cbox ω y :=
  fun hgood => hgood j u hy hmem

/-- **A box reaches its own radius from every centre.**  Some site of `B_r(u)` is at `ℓ∞`
distance at least `r` from any prescribed site `x`: move the coordinate `i₀` of `u` away from
`x`. -/
theorem exists_far_mem_latticeBall (hd : 1 ≤ d) (x u : Lattice d) (r : ℕ) :
    ∃ y : Lattice d, latticeDist u y ≤ r ∧ r ≤ latticeDist x y := by
  classical
  have hne : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨i₀⟩ := hne
  refine ⟨fun i => if i = i₀ then (if x i₀ ≤ u i₀ then u i₀ + (r : ℤ) else u i₀ - (r : ℤ))
      else u i, ?_, ?_⟩
  · refine latticeDist_le_iff.mpr fun i => ?_
    by_cases hi : i = i₀
    · subst hi
      by_cases hx : x i ≤ u i <;> simp only [hx, if_false, if_pos] <;> omega
    · simp only [if_neg hi]
      omega
  · refine le_trans ?_ (coord_le_latticeDist x _ i₀)
    by_cases hx : x i₀ ≤ u i₀ <;>
      simp only [hx, if_false, if_pos] <;> omega

/-! ## The cap -/

/-- The radius of a cell whose scale is capped by `R`. -/
theorem cellRadius_le_of_scale_le {Cbox Cdep R : ℕ} (hCbox : 1 ≤ Cbox) (c : CrossCell d)
    (h : Cbox * 3 ^ cellScale c ≤ R) : cellRadius Cbox Cdep c ≤ (Cbox + Cdep) * R := by
  cases c with
  | inl q =>
      have h3 : 3 ^ q.1 ≤ R :=
        le_trans (Nat.le_mul_of_pos_left _ (by omega : 0 < Cbox)) h
      exact Nat.mul_le_mul_left _ h3
  | inr v =>
      show 0 ≤ (Cbox + Cdep) * R
      exact Nat.zero_le _

/-- **The scale cap of a bounded bad component.**

At every site `v` of the bad `1`-step component of `x`, the witnessing event can be taken of a
scale `j` with `Cbox 3 ^ j` below the reach `R` of that component: the box `B_{Cbox 3^j}(u)` of
the witnessing event is bad, `1`-step connected and meets the component, hence lies inside it,
and it contains a site at distance at least `Cbox 3 ^ j` from `x`. -/
theorem exists_capped_cell_of_mem_badComponent {E : ℕ → Lattice d → Set Ω} {Cbox Cdep : ℕ}
    {ω : Ω} (hd : 1 ≤ d) {x v : Lattice d} {R : ℕ}
    (hR : ∀ y ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u} x,
      latticeDist x y ≤ R)
    (hv : v ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u} x) :
    ∃ c : CrossCell d, ω ∈ cellOccurs E Cdep c ∧
      latticeDist v (cellCenter Cdep c) ≤ cellRadius Cbox Cdep c ∧
      (∀ w : Lattice d, c ≠ Sum.inr w) ∧ Cbox * 3 ^ cellScale c ≤ R := by
  classical
  have hbad : ¬ IsPercolationGoodSite E Cbox ω v := jStepComponent_subset hv
  simp only [IsPercolationGoodSite, InInfluenceBox, not_forall, not_not] at hbad
  obtain ⟨j, u, hu, hmem⟩ := hbad
  set r : ℕ := Cbox * 3 ^ j with hr
  -- the whole box of the witnessing event lies inside the component of `x`
  have hsub : ∀ y : Lattice d, latticeDist u y ≤ r →
      y ∈ jStepComponent 1 {w | ¬ IsPercolationGoodSite E Cbox ω w} x := by
    intro y hy
    refine hv.trans ?_
    refine jStepReachableIn_of_forall_latticeGeodesic_mem fun k _ => ?_
    refine not_isPercolationGoodSite_of_mem_influenceBox hmem ?_
    refine latticeDist_le_of_inLatticeBallReal_natRadius ?_
    exact inLatticeBallReal_latticeGeodesic
      (inLatticeBallReal_of_latticeDist_le hu le_rfl)
      (inLatticeBallReal_of_latticeDist_le hy le_rfl) k
  obtain ⟨y0, hy0u, hy0x⟩ := exists_far_mem_latticeBall hd x u r
  have hrR : r ≤ R := le_trans hy0x (hR y0 (hsub y0 hy0u))
  refine ⟨Sum.inl (j, crossSnap Cdep j u), ?_, ?_, by simp, hrR⟩
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

/-! ## The walk with a supplied family of covering cells -/

/-- **The certificate walk, driven by a supplied cover.**

This is `Section9ChemicalCrossingExtract.exists_chain_from_index` with the choice of covering
cell taken as a hypothesis rather than made inside the walk.  Because every emitted cell then
comes from `hcov`, an arbitrary property `Q` of the supplied cells is inherited by every cell
of the chain; and because the supplied cells are event cells, the chain has no good-vertex cell
at all.

The walk is also shorter than the original: there is no need to distinguish good from bad
vertices, since the "jump out of the cell's ball, or stop because the ball already reaches
outside" step is correct for cells of radius `0` as well. -/
theorem exists_chain_from_index_of_cover (E : ℕ → Lattice d → Set Ω) (Cbox Cdep J : ℕ)
    (ω : Ω) (z : Lattice d) (l : ℕ) (p : ℕ → Lattice d) (b : ℕ) (Q : CrossCell d → Prop)
    (hp : IsJStepPath J p b) (hout : 2 * l < 3 * latticeDist z (p b))
    (hcov : ∀ i, i ≤ b → ∃ c : CrossCell d, ω ∈ cellOccurs E Cdep c ∧
      latticeDist (p i) (cellCenter Cdep c) ≤ cellRadius Cbox Cdep c ∧
      (∀ w : Lattice d, c ≠ Sum.inr w) ∧ Q c) :
    ∀ k, k ≤ b →
      ∃ L : List (CrossCell d), L ≠ [] ∧ L.IsChain (cellReach Cbox Cdep J) ∧
        ω ∈ chainEvent E Cdep L ∧
        (∀ c ∈ L.head?, latticeDist (p k) (cellCenter Cdep c) ≤
          cellRadius Cbox Cdep c) ∧
        (∀ c ∈ L.getLast?, 2 * l ≤
          3 * (latticeDist z (cellCenter Cdep c) + cellRadius Cbox Cdep c)) ∧
        (∀ c ∈ L, Q c) ∧ (∀ v : Lattice d, Sum.inr v ∉ L) := by
  classical
  intro k
  induction hn : (b - k) using Nat.strong_induction_on generalizing k with
  | _ n ih =>
    intro hk
    obtain ⟨c, hocc, hcovk, hcinr, hQ⟩ := hcov k hk
    by_cases hcase : 2 * l < 3 * latticeDist z (p k)
    · -- the current vertex is already outside: one cell suffices
      refine ⟨[c], by simp, List.isChain_singleton c, ?_, ?_, ?_, ?_, ?_⟩
      · intro c' hc'
        simp only [List.mem_singleton] at hc'
        subst hc'
        exact hocc
      · intro c' hc'
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
        subst hc'
        exact hcovk
      · intro c' hc'
        simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hc'
        subst hc'
        have hle : latticeDist z (p k) ≤
            latticeDist z (cellCenter Cdep c) + cellRadius Cbox Cdep c := by
          refine le_trans (latticeDist_triangle z (cellCenter Cdep c) (p k)) ?_
          exact Nat.add_le_add_left (by rwa [latticeDist_comm]) _
        omega
      · intro c' hc'
        simp only [List.mem_singleton] at hc'
        subst hc'
        exact hQ
      · intro v hv
        simp only [List.mem_singleton] at hv
        exact hcinr v hv.symm
    · have hkb : k < b := by
        rcases Nat.lt_or_ge k b with h | h
        · exact h
        · exact absurd (by omega : k = b) (by rintro rfl; exact hcase hout)
      set w : Lattice d := cellCenter Cdep c with hw
      set rad : ℕ := cellRadius Cbox Cdep c with hrad
      by_cases hstay : latticeDist w (p b) ≤ rad
      · -- the path never leaves the cell: the cell already reaches outside
        refine ⟨[c], by simp, List.isChain_singleton c, ?_, ?_, ?_, ?_, ?_⟩
        · intro c' hc'
          simp only [List.mem_singleton] at hc'
          subst hc'
          exact hocc
        · intro c' hc'
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
          subst hc'
          exact hcovk
        · intro c' hc'
          simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hc'
          subst hc'
          have hle : latticeDist z (p b) ≤ latticeDist z w + rad :=
            le_trans (latticeDist_triangle z w (p b)) (Nat.add_le_add_left hstay _)
          show 2 * l ≤ 3 * (latticeDist z w + rad)
          omega
        · intro c' hc'
          simp only [List.mem_singleton] at hc'
          subst hc'
          exact hQ
        · intro v hv
          simp only [List.mem_singleton] at hv
          exact hcinr v hv.symm
      · -- the path leaves the cell: jump to the first exit
        have hex : ∃ i, k < i ∧ i ≤ b ∧ rad < latticeDist w (p i) :=
          ⟨b, hkb, le_rfl, Nat.lt_of_not_ge hstay⟩
        set i : ℕ := Nat.find hex with hi
        obtain ⟨hik, hib, hiexit⟩ := Nat.find_spec hex
        have hprev : latticeDist w (p (i - 1)) ≤ rad := by
          rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hik) with heq | hlt
          · have hik' : i - 1 = k := by omega
            rw [hik', latticeDist_comm]
            exact hcovk
          · by_contra hcon
            have hlt' : i - 1 < i := by omega
            exact absurd
              (Nat.find_min hex hlt' ⟨by omega, by omega, Nat.lt_of_not_ge hcon⟩) (by simp)
        have hnear : latticeDist w (p i) ≤ rad + J := by
          have hstep : latticeDist (p (i - 1)) (p i) ≤ J := by
            have := hp (i - 1) (by omega)
            rwa [show i - 1 + 1 = i by omega] at this
          calc latticeDist w (p i) ≤ latticeDist w (p (i - 1)) +
                latticeDist (p (i - 1)) (p i) := latticeDist_triangle _ _ _
            _ ≤ rad + J := Nat.add_le_add hprev hstep
        obtain ⟨L, hne, hchain, hev, hhead, hlast, hQL, hinr⟩ :=
          ih (b - i) (by omega) i rfl hib
        refine ⟨c :: L, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, hchain⟩
          intro y hy
          have hcov' := hhead y hy
          have htri := latticeDist_triangle w (p i) (cellCenter Cdep y)
          show latticeDist w (cellCenter Cdep y) ≤ rad + cellRadius Cbox Cdep y + J
          omega
        · intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc'
          · exact hocc
          · exact hev c' hc'
        · intro c' hc'
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
          subst hc'
          exact hcovk
        · intro c' hc'
          rcases L with _ | ⟨e, L'⟩
          · exact absurd rfl hne
          · rw [List.getLast?_cons_cons] at hc'
            exact hlast c' hc'
        · intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc'
          · exact hQ
          · exact hQL c' hc'
        · intro v hv
          rcases List.mem_cons.mp hv with hv | hv
          · exact hcinr v hv.symm
          · exact hinr v hv

/-! ## The certificate of a bad component of bounded reach -/

/-- **The capped certificate.**

A bad `1`-step component reaching `ℓ∞` distance `l` from its root `x`, and of total reach at
most `R`, produces a crossing certificate at scale `l` with distinct cells, *no* good-vertex
cell, and every cell within `(1 + Cbox + Cdep) R` of `x`.

The last conjunct is what the `m`-fold union bound consumes: two such certificates with roots
farther apart than `2 (1 + Cbox + Cdep) R` share no cell. -/
theorem exists_bandCrossChain (E : ℕ → Lattice d → Set Ω) (Cbox Cdep : ℕ)
    (hd : 1 ≤ d) (hCbox : 1 ≤ Cbox) (ω : Ω) (x : Lattice d) (R l : ℕ) (hl : 1 ≤ l)
    (hreach : ∃ y ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u} x,
      l ≤ latticeDist x y)
    (hcap : ∀ y ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u} x,
      latticeDist x y ≤ R) :
    ∃ L : List (CrossCell d), CrossChain Cbox Cdep 1 x l L ∧ L.Nodup ∧
      ω ∈ chainEvent E Cdep L ∧ goodCellCount L = 0 ∧
      ∀ c ∈ L, latticeDist x (cellCenter Cdep c) ≤ (1 + Cbox + Cdep) * R := by
  classical
  obtain ⟨y, hy, hdy⟩ := hreach
  obtain ⟨p, b, hp, hp0, hpb, hpmem⟩ := exists_isJStepPath_of_jStepReachableIn hy
  have hxS : x ∈ {u | ¬ IsPercolationGoodSite E Cbox ω u} :=
    mem_of_jStepReachableIn hy.symm
  have hpK : ∀ i, i ≤ b → p i ∈ jStepComponent 1 {u | ¬ IsPercolationGoodSite E Cbox ω u} x := by
    intro i
    induction i with
    | zero => intro _; rw [hp0]; exact self_mem_jStepComponent hxS
    | succ i ihh =>
        intro hi
        exact mem_jStepComponent_of_dist_le (ihh (by omega)) (hpmem (i + 1) hi)
          (hp i (by omega))
  have hcov : ∀ i, i ≤ b → ∃ c : CrossCell d, ω ∈ cellOccurs E Cdep c ∧
      latticeDist (p i) (cellCenter Cdep c) ≤ cellRadius Cbox Cdep c ∧
      (∀ w : Lattice d, c ≠ Sum.inr w) ∧
      latticeDist x (cellCenter Cdep c) ≤ (1 + Cbox + Cdep) * R := by
    intro i hi
    obtain ⟨c, h1, h2, h3, h4⟩ :=
      exists_capped_cell_of_mem_badComponent (Cdep := Cdep) hd hcap (hpK i hi)
    refine ⟨c, h1, h2, h3, ?_⟩
    have hxi : latticeDist x (p i) ≤ R := hcap _ (hpK i hi)
    have hrad : cellRadius Cbox Cdep c ≤ (Cbox + Cdep) * R :=
      cellRadius_le_of_scale_le hCbox c h4
    have htri := latticeDist_triangle x (p i) (cellCenter Cdep c)
    have hexp : (1 + Cbox + Cdep) * R = R + (Cbox + Cdep) * R := by ring
    omega
  have hout : 2 * l < 3 * latticeDist x (p b) := by
    rw [hpb]
    omega
  obtain ⟨L0, hne0, hchain0, hev0, hhead0, hlast0, hQ0, hinr0⟩ :=
    exists_chain_from_index_of_cover E Cbox Cdep 1 ω x l p b
      (fun c => latticeDist x (cellCenter Cdep c) ≤ (1 + Cbox + Cdep) * R)
      hp hout hcov 0 (Nat.zero_le _)
  obtain ⟨L, hchain, hsub, hhead, hlast, hnd⟩ := exists_nodup_isChain L0 hchain0
  have hne : L ≠ [] := by
    intro hc
    rw [hc] at hhead
    rcases L0 with _ | ⟨e, Lt⟩
    · exact hne0 rfl
    · simp at hhead
  refine ⟨L, ⟨hne, hchain, ?_, ?_⟩, hnd, ?_, ?_, ?_⟩
  · intro c hc
    rw [hhead] at hc
    have hcov' := hhead0 c hc
    rw [hp0] at hcov'
    omega
  · intro c hc
    rw [hlast] at hc
    exact hlast0 c hc
  · intro c hc
    exact hev0 c (hsub.subset hc)
  · have hfilter : L.filter (fun c => c.isRight) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcr
      cases c with
      | inl q => simp at hcr
      | inr v => exact hinr0 v (hsub.subset hc)
    rw [goodCellCount, hfilter]
    simp
  · intro c hc
    exact hQ0 c (hsub.subset hc)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
