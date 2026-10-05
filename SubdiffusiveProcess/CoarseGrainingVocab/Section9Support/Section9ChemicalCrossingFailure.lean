module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingExtract

@[expose] public section

/-!
# The crossing-density failure event is covered by crossing certificates

`CrossingGoodCount E Cbox J ω z l N` asks every `J`-step path from `B_{l/3}(z)`
leaving `B_{2l/3}(z)` to carry at least `N` annulus-good vertices.  This file
shows that its failure produces a **crossing certificate**: a chain of cells with
distinct entries, all of whose event cells occur, whose radial coverage is forced
by `crossChain_le_radius_sum`, and which uses at most `N + 2` good-vertex cells.

Two elementary conversions do most of the bookkeeping:

* the manuscript's real-radius balls are integer conditions
  (`inLatticeBallReal_div_iff`);
* a path vertex strictly between the last visit to `B_{l/3}(z)` and the first
  exit from `B_{2l/3}(z)` has its whole `Cbox`-box inside the middle annulus as
  soon as `12 Cbox ≤ l` (`annulusGoodSite_of_mid`), so a *good* such vertex is
  annulus-good and is therefore counted by the hypothesis.

The two endpoints of that segment are the only good-vertex cells not covered by
the hypothesis, whence the `+ 2`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## Real-radius balls as integer conditions -/

theorem inLatticeBallReal_div_iff {z v : Lattice d} {a b : ℕ} (hb : 0 < b) :
    InLatticeBallReal z v ((a : ℝ) / (b : ℝ)) ↔ b * latticeDist z v ≤ a := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hcoord : ∀ i : Fin d, |(v i - z i : ℤ)| = ((z i - v i).natAbs : ℤ) := by
    intro i
    rw [Int.abs_eq_natAbs, ← Int.natAbs_neg, neg_sub]
  have hiff : ∀ i : Fin d,
      ((|(v i - z i : ℤ)| : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) ↔
        b * (z i - v i).natAbs ≤ a := by
    intro i
    rw [hcoord i, le_div_iff₀' hbR]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  constructor
  · intro h
    have hall : ∀ i : Fin d, b * (z i - v i).natAbs ≤ a := fun i => (hiff i).mp (h i)
    have hsup : latticeDist z v ≤ a / b :=
      Finset.sup_le fun i _ =>
        (Nat.le_div_iff_mul_le hb).mpr (by rw [Nat.mul_comm]; exact hall i)
    calc b * latticeDist z v ≤ b * (a / b) := Nat.mul_le_mul_left _ hsup
      _ = a / b * b := Nat.mul_comm _ _
      _ ≤ a := Nat.div_mul_le_self a b
  · intro h i
    exact (hiff i).mpr
      (le_trans (Nat.mul_le_mul_left _ (coord_le_latticeDist z v i)) h)

theorem inLatticeBallReal_nat_iff {z v : Lattice d} {a : ℕ} :
    InLatticeBallReal z v (a : ℝ) ↔ latticeDist z v ≤ a := by
  have h := inLatticeBallReal_div_iff (z := z) (v := v) (a := a) (b := 1) (by omega)
  simpa using h

/-! ## Middle-annulus vertices -/

/-- A good vertex strictly between the two balls has its whole `Cbox`-box in the
middle annulus, hence is annulus-good. -/
theorem annulusGoodSite_of_mid {E : ℕ → Lattice d → Set Ω} {Cbox : ℕ} {ω : Ω}
    {z v : Lattice d} {l : ℕ} (hCbox : 12 * Cbox ≤ l)
    (hlo : l < 3 * latticeDist z v) (hhi : 3 * latticeDist z v ≤ 2 * l)
    (hgood : IsPercolationGoodSite E Cbox ω v) :
    AnnulusGoodSite E Cbox ω z l v := by
  refine ⟨hgood, ?_⟩
  intro u hu
  have hvu : latticeDist v u ≤ Cbox := inLatticeBallReal_nat_iff.mp hu
  have h1 : latticeDist z u ≤ latticeDist z v + Cbox :=
    le_trans (latticeDist_triangle z v u) (Nat.add_le_add_left hvu _)
  have h2 : latticeDist z v ≤ latticeDist z u + Cbox := by
    refine le_trans (latticeDist_triangle z u v) (Nat.add_le_add_left ?_ _)
    rwa [latticeDist_comm]
  constructor
  · have hin : 4 * latticeDist z u ≤ 3 * l := by omega
    have hcast : (3 * (l : ℝ)) / 4 = ((3 * l : ℕ) : ℝ) / ((4 : ℕ) : ℝ) := by
      push_cast; ring
    show InLatticeBallReal z u ((3 * l : ℝ) / 4)
    rw [hcast]
    exact (inLatticeBallReal_div_iff (by omega)).mpr (by omega)
  · have hout : ¬ (4 * latticeDist z u ≤ l) := by omega
    have hcast : ((l : ℝ)) / 4 = ((l : ℕ) : ℝ) / ((4 : ℕ) : ℝ) := by push_cast; ring
    intro hmem
    have : InLatticeBallReal z u ((l : ℝ) / 4) := hmem
    rw [hcast] at this
    exact hout ((inLatticeBallReal_div_iff (by omega)).mp this)

/-! ## Counting the good-vertex cells -/

theorem goodCellCount_le_card {L : List (CrossCell d)} (hnd : L.Nodup)
    (T : Finset (Lattice d)) (hT : ∀ v : Lattice d, Sum.inr v ∈ L → v ∈ T) :
    goodCellCount L ≤ T.card := by
  classical
  set M : List (CrossCell d) := L.filter (fun c => c.isRight) with hM
  have hMnd : M.Nodup := hnd.filter _
  set f : CrossCell d → Lattice d := fun c => (Sum.getRight? c).getD 0 with hf
  have hmemM : ∀ c ∈ M, ∃ v, c = Sum.inr v := by
    intro c hc
    have hr := (List.mem_filter.mp hc).2
    cases c with
    | inl p => simp at hr
    | inr v => exact ⟨v, rfl⟩
  have hinj : ∀ c₁ ∈ M, ∀ c₂ ∈ M, f c₁ = f c₂ → c₁ = c₂ := by
    intro c₁ h₁ c₂ h₂ heq
    obtain ⟨v₁, rfl⟩ := hmemM c₁ h₁
    obtain ⟨v₂, rfl⟩ := hmemM c₂ h₂
    have : v₁ = v₂ := heq
    rw [this]
  have hmapnd : (M.map f).Nodup := hMnd.map_on hinj
  have hsub : (M.map f).toFinset ⊆ T := by
    intro v hv
    simp only [List.mem_toFinset, List.mem_map] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    obtain ⟨w, rfl⟩ := hmemM c hc
    exact hT w (List.mem_of_mem_filter hc)
  calc goodCellCount L = M.length := rfl
    _ = (M.map f).length := (List.length_map _).symm
    _ = (M.map f).toFinset.card := (List.toFinset_card_of_nodup hmapnd).symm
    _ ≤ T.card := Finset.card_le_card hsub

/-! ## The certificate of a failing crossing path -/

/-- **A crossing path yields a crossing certificate.**

The path is given in indexed form, starting inside `B_{l/3}(z)` and ending
outside `B_{2l/3}(z)`; `AG` is any finite set collecting the good vertices of the
path that lie strictly between the two balls. -/
theorem exists_crossChain_of_indexed
    (E : ℕ → Lattice d → Set Ω) (Cbox Cdep J : ℕ) (ω : Ω) (z : Lattice d) (l : ℕ)
    (AG : Finset (Lattice d)) (p₁ : ℕ → Lattice d) (m : ℕ) (hp : IsJStepPath J p₁ m)
    (hin : 3 * latticeDist z (p₁ 0) ≤ l)
    (hout : 2 * l < 3 * latticeDist z (p₁ m))
    (hAG : ∀ k, k ≤ m → l < 3 * latticeDist z (p₁ k) →
      3 * latticeDist z (p₁ k) ≤ 2 * l →
      IsPercolationGoodSite E Cbox ω (p₁ k) → p₁ k ∈ AG) :
    ∃ L : List (CrossCell d), CrossChain Cbox Cdep J z l L ∧ L.Nodup ∧
      ω ∈ chainEvent E Cdep L ∧ goodCellCount L ≤ AG.card + 2 := by
  classical
  have hexb : ∃ i, i ≤ m ∧ 2 * l < 3 * latticeDist z (p₁ i) := ⟨m, le_rfl, hout⟩
  set b : ℕ := Nat.find hexb with hbdef
  obtain ⟨hbm0, hbout0⟩ := Nat.find_spec hexb
  have hbm : b ≤ m := by rw [hbdef]; exact hbm0
  have hbout : 2 * l < 3 * latticeDist z (p₁ b) := by rw [hbdef]; exact hbout0
  have hbmin : ∀ i, i < b → 3 * latticeDist z (p₁ i) ≤ 2 * l := by
    intro i hi
    by_contra hcon
    exact Nat.find_min hexb hi ⟨by omega, by omega⟩
  have hb0 : 0 < b := by
    by_contra hcon
    have hb : b = 0 := by omega
    rw [hb] at hbout
    omega
  set Pa : ℕ → Prop := fun i => 3 * latticeDist z (p₁ i) ≤ l with hPa
  set a : ℕ := Nat.findGreatest Pa (b - 1) with hadef
  have hale : a ≤ b - 1 := Nat.findGreatest_le _
  have haPa : 3 * latticeDist z (p₁ a) ≤ l := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h]; exact hin
    · have hne0 : Nat.findGreatest Pa (b - 1) ≠ 0 := by rw [← hadef]; omega
      have hres : Pa (Nat.findGreatest Pa (b - 1)) :=
        Nat.findGreatest_of_ne_zero rfl hne0
      rw [← hadef] at hres
      exact hres
  have hamax : ∀ i, a < i → i < b → l < 3 * latticeDist z (p₁ i) := by
    intro i h1 h2
    have hnp := Nat.findGreatest_is_greatest (P := Pa) (n := b - 1) (k := i)
      (by omega) (by omega)
    simp only [hPa] at hnp
    omega
  set p₂ : ℕ → Lattice d := fun k => p₁ (a + k) with hp2
  set b₂ : ℕ := b - a with hb2def
  have hp2path : IsJStepPath J p₂ b₂ := by
    intro i hi
    have hlt : a + i < m := by omega
    have hstep := hp (a + i) hlt
    show latticeDist (p₁ (a + i)) (p₁ (a + (i + 1))) ≤ J
    rw [show a + (i + 1) = a + i + 1 by omega]
    exact hstep
  have hp2b : p₂ b₂ = p₁ b := by
    show p₁ (a + (b - a)) = p₁ b
    congr 1
    omega
  have hp2out : 2 * l < 3 * latticeDist z (p₂ b₂) := by rw [hp2b]; exact hbout
  obtain ⟨L, hne, hchain, hev, hhead, hlast, hgc⟩ :=
    exists_chain_from_index E Cbox Cdep J ω z l p₂ b₂ hp2path hp2out 0 (Nat.zero_le _)
  obtain ⟨L', hchain', hsub', hhead', hlast', hnd'⟩ := exists_nodup_isChain L hchain
  have hne' : L' ≠ [] := by
    intro hcon
    rw [hcon] at hhead'
    rcases L with _ | ⟨e, Lt⟩
    · exact hne rfl
    · simp at hhead'
  refine ⟨L', ⟨hne', hchain', ?_, ?_⟩, hnd', ?_, ?_⟩
  · intro c hc
    rw [hhead'] at hc
    have hcov := hhead c hc
    have htri : latticeDist z (cellCenter Cdep c) ≤
        latticeDist z (p₂ 0) + cellRadius Cbox Cdep c := by
      refine le_trans (latticeDist_triangle z (p₂ 0) (cellCenter Cdep c)) ?_
      exact Nat.add_le_add_left hcov _
    have hz : p₂ 0 = p₁ a := by show p₁ (a + 0) = p₁ a; congr 1
    rw [hz] at htri
    omega
  · intro c hc
    rw [hlast'] at hc
    exact hlast c hc
  · intro c hc
    exact hev c (hsub'.subset hc)
  · refine le_trans (goodCellCount_le_card hnd'
      (insert (p₁ a) (insert (p₁ b) AG)) ?_) ?_
    · intro v hv
      obtain ⟨i, -, hib, rfl, hgood⟩ := hgc v (hsub'.subset hv)
      have hval : p₂ i = p₁ (a + i) := rfl
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · refine Finset.mem_insert.mpr (Or.inl ?_)
        show p₁ (a + 0) = p₁ a
        congr 1
      · rcases Nat.eq_or_lt_of_le hib with heq | hlt
        · refine Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl ?_))
          show p₁ (a + i) = p₁ b
          congr 1
          omega
        · refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
          rw [hval]
          exact hAG (a + i) (by omega) (hamax (a + i) (by omega) (by omega))
            (hbmin (a + i) (by omega)) hgood
    · calc (insert (p₁ a) (insert (p₁ b) AG)).card
          ≤ (insert (p₁ b) AG).card + 1 := Finset.card_insert_le _ _
        _ ≤ (AG.card + 1) + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ = AG.card + 2 := by omega

/-! ## From the failure of the crossing count to a certificate -/

theorem inBall_third_iff {z v : Lattice d} {l : ℕ} :
    InLatticeBallReal z v ((l : ℝ) / 3) ↔ 3 * latticeDist z v ≤ l := by
  have h : ((l : ℝ) / 3) = ((l : ℕ) : ℝ) / ((3 : ℕ) : ℝ) := by push_cast; ring
  rw [h]
  exact inLatticeBallReal_div_iff (by omega)

theorem inBall_twoThirds_iff {z v : Lattice d} {l : ℕ} :
    InLatticeBallReal z v (2 * (l : ℝ) / 3) ↔ 3 * latticeDist z v ≤ 2 * l := by
  have h : (2 * (l : ℝ) / 3) = ((2 * l : ℕ) : ℝ) / ((3 : ℕ) : ℝ) := by push_cast; ring
  rw [h]
  exact inLatticeBallReal_div_iff (by omega)

/-- **The failure of the crossing count produces a crossing certificate.** -/
theorem exists_crossChain_of_not_crossingGoodCount
    (E : ℕ → Lattice d → Set Ω) (Cbox Cdep J : ℕ) (ω : Ω) (z : Lattice d) (l N : ℕ)
    (hCbox : 12 * Cbox ≤ l)
    (hfail : ¬ CrossingGoodCount E Cbox J ω z l N) :
    ∃ L : List (CrossCell d), CrossChain Cbox Cdep J z l L ∧ L.Nodup ∧
      ω ∈ chainEvent E Cdep L ∧ goodCellCount L ≤ N + 2 := by
  classical
  rw [CrossingGoodCount] at hfail
  push Not at hfail
  obtain ⟨path, hpath, hstart, hexit, hnoS⟩ := hfail
  set AG : Finset (Lattice d) :=
    path.toFinset.filter (fun v => AnnulusGoodSite E Cbox ω z l v) with hAGdef
  have hAGcard : AG.card < N := by
    have h1 : ∀ v ∈ AG, v ∈ path := by
      intro v hv
      exact List.mem_toFinset.mp (Finset.mem_filter.mp hv).1
    have h2 : ∀ v ∈ AG, AnnulusGoodSite E Cbox ω z l v := by
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    exact hnoS AG h1 h2
  set p : ℕ → Lattice d := fun k => path[k]! with hpdef
  set n : ℕ := path.length - 1 with hndef
  have hjs : IsJStepPath J p n := by
    intro i hi
    exact hpath i (by omega)
  have hmem : ∀ k, k < path.length → p k ∈ path := by
    intro k hk
    have hg : path[k]! = path[k] := getElem!_pos path k hk
    show path[k]! ∈ path
    rw [hg]
    exact List.getElem_mem hk
  have hidx : ∀ v : Lattice d, v ∈ path → ∃ k, k < path.length ∧ p k = v := by
    intro v hv
    obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hv
    refine ⟨k, hk, ?_⟩
    show path[k]! = v
    rw [getElem!_pos path k hk]
    exact hkv
  obtain ⟨v₀, hv₀mem, hv₀in⟩ := hstart
  obtain ⟨v₁, hv₁mem, hv₁out⟩ := hexit
  obtain ⟨a₀, ha₀lt, rfl⟩ := hidx v₀ hv₀mem
  obtain ⟨b₀, hb₀lt, rfl⟩ := hidx v₁ hv₁mem
  rw [inBall_third_iff] at hv₀in
  rw [inBall_twoThirds_iff] at hv₁out
  have hv₁out' : 2 * l < 3 * latticeDist z (p b₀) := by omega
  -- the annulus-good bookkeeping, phrased for an arbitrary index
  have hAGidx : ∀ k, k < path.length → l < 3 * latticeDist z (p k) →
      3 * latticeDist z (p k) ≤ 2 * l →
      IsPercolationGoodSite E Cbox ω (p k) → p k ∈ AG := by
    intro k hk h1 h2 hgood
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hmem k hk), ?_⟩
    exact annulusGoodSite_of_mid hCbox h1 h2 hgood
  have hane : a₀ ≠ b₀ := by
    intro h
    rw [h] at hv₀in
    omega
  have hmain : ∃ L : List (CrossCell d), CrossChain Cbox Cdep J z l L ∧ L.Nodup ∧
      ω ∈ chainEvent E Cdep L ∧ goodCellCount L ≤ AG.card + 2 := by
    rcases Nat.lt_or_ge a₀ b₀ with hlt | hge
    · refine exists_crossChain_of_indexed E Cbox Cdep J ω z l AG
        (fun k => p (a₀ + k)) (b₀ - a₀) ?_ ?_ ?_ ?_
      · intro i hi
        have hstep := hjs (a₀ + i) (by omega)
        show latticeDist (p (a₀ + i)) (p (a₀ + (i + 1))) ≤ J
        rw [show a₀ + (i + 1) = a₀ + i + 1 by omega]
        exact hstep
      · show 3 * latticeDist z (p (a₀ + 0)) ≤ l
        rw [show a₀ + 0 = a₀ by omega]
        exact hv₀in
      · show 2 * l < 3 * latticeDist z (p (a₀ + (b₀ - a₀)))
        rw [show a₀ + (b₀ - a₀) = b₀ by omega]
        exact hv₁out'
      · intro k hk h1 h2 hgood
        exact hAGidx (a₀ + k) (by omega) h1 h2 hgood
    · have hlt : b₀ < a₀ := by omega
      refine exists_crossChain_of_indexed E Cbox Cdep J ω z l AG
        (fun k => p (a₀ - k)) (a₀ - b₀) ?_ ?_ ?_ ?_
      · intro i hi
        have hstep := hjs (a₀ - i - 1) (by omega)
        show latticeDist (p (a₀ - i)) (p (a₀ - (i + 1))) ≤ J
        rw [show a₀ - (i + 1) = a₀ - i - 1 by omega, latticeDist_comm]
        rw [show a₀ - i - 1 + 1 = a₀ - i by omega] at hstep
        exact hstep
      · show 3 * latticeDist z (p (a₀ - 0)) ≤ l
        rw [show a₀ - 0 = a₀ by omega]
        exact hv₀in
      · show 2 * l < 3 * latticeDist z (p (a₀ - (a₀ - b₀)))
        rw [show a₀ - (a₀ - b₀) = b₀ by omega]
        exact hv₁out'
      · intro k hk h1 h2 hgood
        exact hAGidx (a₀ - k) (by omega) h1 h2 hgood
  obtain ⟨L, hcc, hnd, hev, hgc⟩ := hmain
  exact ⟨L, hcc, hnd, hev, by omega⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
