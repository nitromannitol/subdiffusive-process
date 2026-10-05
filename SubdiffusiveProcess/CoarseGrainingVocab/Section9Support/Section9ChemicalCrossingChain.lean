module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ChemicalCrossingSum

@[expose] public section

/-!
# Crossing chains: their radial coverage, and loop erasure

A **crossing chain** for `z` at scale `l` is a chain of cells whose first cell
meets `B_{l/3}(z)` and whose last cell leaves `B_{2l/3}(z)`.  Two facts about
such a chain are proved here.

* **Radial coverage** (`crossChain_le_radius_sum`): the triangle inequality,
  telescoped along the chain, forces

  `l ≤ 6 ∑ (cell radii) + 3 J (number of cells)`.

  This is the whole point of the certificate: to connect the two balls, the
  chain must either carry a large total radius — which is expensive, since the
  radius of a scale-`j` cell is `(Cbox+Cdep) 3^j` while its probability carries
  `exp(-c q 3^{3j/2})` — or use many cells, and the good-vertex cells are capped
  by the crossing-density assumption.

* **Loop erasure** (`exists_nodup_isChain`): a chain with a repeated cell can be
  shortened *without changing its first and last cells*, because a repetition
  `… a … a …` lets the chain jump directly from the first occurrence's suffix.
  Iterating, every crossing chain contains a crossing chain with **distinct**
  cells, which is what the separated-product bound `measure_chainEvent_le`
  needs.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

noncomputable section

variable {d : ℕ}

/-! ## Loop erasure -/

/-- A chain with a repeated entry can be shortened, keeping its first and last
entries. -/
theorem exists_shorter_isChain {α : Type*} {R : α → α → Prop} :
    ∀ L : List α, L.IsChain R → ¬ L.Nodup →
      ∃ L' : List α, L'.IsChain R ∧ L'.Sublist L ∧ L'.length < L.length ∧
        L'.head? = L.head? ∧ L'.getLast? = L.getLast? := by
  intro L
  induction L with
  | nil => intro _ hnd; exact absurd List.nodup_nil hnd
  | cons a t ih =>
      intro hchain hnd
      by_cases hat : a ∈ t
      · obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem hat
        refine ⟨a :: t₂, ?_, ?_, ?_, rfl, ?_⟩
        · refine hchain.suffix ?_
          exact ⟨a :: t₁, by simp⟩
        · refine List.Sublist.cons_cons a ?_
          exact (List.sublist_cons_self a t₂).trans
            (List.sublist_append_right t₁ (a :: t₂))
        · simp only [List.length_cons, List.length_append]
          omega
        · show (a :: t₂).getLast? = ((a :: t₁) ++ (a :: t₂)).getLast?
          rw [List.getLast?_append_of_ne_nil (a :: t₁) (List.cons_ne_nil a t₂)]
      · have hndt : ¬ t.Nodup := by
          intro h
          exact hnd (List.nodup_cons.mpr ⟨hat, h⟩)
        obtain ⟨t', hch, hsub, hlen, hhead, hlast⟩ := ih hchain.tail hndt
        refine ⟨a :: t', ?_, hsub.cons_cons a, by simpa using hlen, rfl, ?_⟩
        · refine List.isChain_cons.mpr ⟨?_, hch⟩
          intro y hy
          rw [hhead] at hy
          exact (List.isChain_cons.mp hchain).1 y hy
        · rcases t' with _ | ⟨b, t''⟩
          · have : t = [] := by
              rcases t with _ | ⟨c, u⟩
              · rfl
              · simp at hhead
            simp [this]
          · rcases t with _ | ⟨c, u⟩
            · simp at hhead
            · rw [List.getLast?_cons_cons, List.getLast?_cons_cons, hlast]

/-- Every chain contains a chain with distinct entries and the same first and
last entries. -/
theorem exists_nodup_isChain {α : Type*} {R : α → α → Prop} (L : List α)
    (hL : L.IsChain R) :
    ∃ L' : List α, L'.IsChain R ∧ L'.Sublist L ∧
      L'.head? = L.head? ∧ L'.getLast? = L.getLast? ∧ L'.Nodup := by
  classical
  induction hn : L.length using Nat.strong_induction_on generalizing L with
  | _ n ih =>
      by_cases hnd : L.Nodup
      · exact ⟨L, hL, List.Sublist.refl L, rfl, rfl, hnd⟩
      · obtain ⟨L', hch, hsub, hlen, hhead, hlast⟩ := exists_shorter_isChain L hL hnd
        obtain ⟨L'', hch'', hsub'', hhead'', hlast'', hnd''⟩ :=
          ih L'.length (by omega) L' hch rfl
        exact ⟨L'', hch'', hsub''.trans hsub, hhead''.trans hhead,
          hlast''.trans hlast, hnd''⟩

/-! ## Crossing chains and their radial coverage -/

/-- A crossing chain for `z` at scale `l`: a nonempty chain of cells whose first
cell meets `B_{l/3}(z)` and whose last cell reaches outside `B_{2l/3}(z)`. -/
def CrossChain (Cbox Cdep J : ℕ) (z : Lattice d) (l : ℕ) (L : List (CrossCell d)) :
    Prop :=
  L ≠ [] ∧ L.IsChain (cellReach Cbox Cdep J) ∧
    (∀ c ∈ L.head?, 3 * latticeDist z (cellCenter Cdep c) ≤
      l + 3 * cellRadius Cbox Cdep c) ∧
    (∀ c ∈ L.getLast?, 2 * l ≤
      3 * (latticeDist z (cellCenter Cdep c) + cellRadius Cbox Cdep c))

/-- The telescoped triangle inequality along a chain. -/
theorem isChain_dist_le (Cbox Cdep J : ℕ) (z : Lattice d) :
    ∀ (c : CrossCell d) (L : List (CrossCell d)),
      (c :: L).IsChain (cellReach Cbox Cdep J) →
      ∀ cl ∈ (c :: L).getLast?,
        latticeDist z (cellCenter Cdep cl) + cellRadius Cbox Cdep cl +
            cellRadius Cbox Cdep c ≤
          latticeDist z (cellCenter Cdep c) +
            (2 * ((c :: L).map (cellRadius Cbox Cdep)).sum +
              J * (c :: L).length) := by
  intro c L
  induction L generalizing c with
  | nil =>
      intro _ cl hcl
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hcl
      subst hcl
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.length_cons, List.length_nil]
      omega
  | cons c' L' ih =>
      intro hchain cl hcl
      have hrel : cellReach Cbox Cdep J c c' := by
        have := (List.isChain_cons.mp hchain).1
        exact this c' (by simp)
      have htail : (c' :: L').IsChain (cellReach Cbox Cdep J) := hchain.tail
      have hcl' : cl ∈ (c' :: L').getLast? := by
        rwa [List.getLast?_cons_cons] at hcl
      have hIH := ih c' htail cl hcl'
      have hstep : latticeDist z (cellCenter Cdep c') ≤
          latticeDist z (cellCenter Cdep c) + (cellRadius Cbox Cdep c +
            cellRadius Cbox Cdep c' + J) :=
        le_trans (latticeDist_triangle z (cellCenter Cdep c) (cellCenter Cdep c'))
          (Nat.add_le_add_left hrel _)
      simp only [List.map_cons, List.sum_cons, List.length_cons] at hIH ⊢
      have hJ : J * (L'.length + 1 + 1) = J * (L'.length + 1) + J := by ring
      omega

/-- **The radial coverage of a crossing chain.**

To join `B_{l/3}(z)` to the exterior of `B_{2l/3}(z)`, a chain must spend either
total radius or cells. -/
theorem crossChain_le_radius_sum {Cbox Cdep J : ℕ} {z : Lattice d} {l : ℕ}
    {L : List (CrossCell d)} (hL : CrossChain Cbox Cdep J z l L) :
    l ≤ 6 * (L.map (cellRadius Cbox Cdep)).sum + 3 * (J * L.length) := by
  obtain ⟨hne, hchain, hhead, hlast⟩ := hL
  rcases L with _ | ⟨c, L'⟩
  · exact absurd rfl hne
  have hcl : (c :: L').getLast (List.cons_ne_nil c L') ∈ (c :: L').getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil c L')]
    rfl
  set cl : CrossCell d := (c :: L').getLast (List.cons_ne_nil c L') with hcldef
  have hkey := isChain_dist_le Cbox Cdep J z c L' hchain cl hcl
  have h1 := hhead c (by simp)
  have h2 := hlast cl hcl
  omega

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
