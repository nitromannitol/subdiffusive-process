module

public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.Geometry.OddGridPartition
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Lane2.CellAssembly
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import Mathlib
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.Lane3.Interfaces
public import SubdiffusiveProcess.Paper.lem_finite_stopping_crude_cost

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false




open MeasureTheory Filter TopologicalSpace Topology Finset
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper


variable {d : ℕ}

/-- The length-`k` prefix of a word of length `n`. -/
def aux_lem_finite_stopping_partition_wordPrefix {α : Type*} {n : ℕ} (w : Fin n → α) (k : ℕ) (hk : k ≤ n) : Fin k → α :=
  fun i => w (Fin.castLE hk i)

theorem aux_lem_finite_stopping_partition_wordPrefix_self {α : Type*} {n : ℕ} (w : Fin n → α) (hk : n ≤ n) :
    aux_lem_finite_stopping_partition_wordPrefix w n hk = w := by
  funext i
  simp [aux_lem_finite_stopping_partition_wordPrefix]

theorem aux_lem_finite_stopping_partition_wordPrefix_wordPrefix {α : Type*} {n : ℕ} (w : Fin n → α) (k l : ℕ)
    (hk : k ≤ n) (hl : l ≤ k) :
    aux_lem_finite_stopping_partition_wordPrefix (aux_lem_finite_stopping_partition_wordPrefix w k hk) l hl = aux_lem_finite_stopping_partition_wordPrefix w l (hl.trans hk) := by
  funext i
  rfl

theorem aux_lem_finite_stopping_partition_wordPrefix_castSucc {α : Type*} {n : ℕ} (w : Fin (n + 1) → α) (k : ℕ)
    (hk : k ≤ n) :
    aux_lem_finite_stopping_partition_wordPrefix (fun i : Fin n => w i.castSucc) k hk =
      aux_lem_finite_stopping_partition_wordPrefix w k (hk.trans (Nat.le_succ n)) := by
  funext i
  rfl

/-- The one-step identity: a depth-`n+1` cell is the odd-grid child of its parent cell. -/
theorem aux_lem_finite_stopping_partition_descendantCell_succ_eq_oddGridCell (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (n : ℕ) (w : Fin (n + 1) → OddGridIndex d m) :
    (descendantCell m z hr (n + 1) w : Set (SpatialCoordinates d)) =
      oddGridCell (descendantCenter m z r n fun i => w i.castSucc)
        (descendantSide m n r) (descendantSide_pos m n hr) m (w (Fin.last n)) := by
  rw [descendantCell_coe, oddGridCell_coe, descendantSide_succ]
  rfl

theorem aux_lem_finite_stopping_partition_descendantCell_zero (m : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (w : Fin 0 → OddGridIndex d m) :
    (descendantCell m z hr 0 w : Set (SpatialCoordinates d)) = centeredCube z r hr := by
  rw [descendantCell_coe]
  change Metric.ball z (descendantSide m 0 r / 2) = Metric.ball z (r / 2)
  rw [descendantSide_zero]

/-- A cell lies in the cell of each of its prefixes. -/
theorem aux_lem_finite_stopping_partition_descendantCell_subset_prefix (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    ∀ (n : ℕ) (w : Fin n → OddGridIndex d m) (k : ℕ) (hk : k ≤ n),
      (descendantCell m z hr n w : Set (SpatialCoordinates d)) ⊆
        descendantCell m z hr k (aux_lem_finite_stopping_partition_wordPrefix w k hk) := by
  intro n
  induction n with
  | zero =>
    intro w k hk
    obtain rfl : k = 0 := by omega
    rw [aux_lem_finite_stopping_partition_descendantCell_zero, aux_lem_finite_stopping_partition_descendantCell_zero]
  | succ n ih =>
    intro w k hk
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hkn : k ≤ n := by omega
      refine (descendantCell_succ_subset m z hr n w).trans ?_
      have h := ih (fun i => w i.castSucc) k hkn
      rwa [aux_lem_finite_stopping_partition_wordPrefix_castSucc] at h
    · obtain rfl : k = n + 1 := by omega
      rw [aux_lem_finite_stopping_partition_wordPrefix_self]

/-- Every descendant cell lies in the root cube. -/
theorem aux_lem_finite_stopping_partition_descendantCell_subset_root (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (n : ℕ) (w : Fin n → OddGridIndex d m) :
    (descendantCell m z hr n w : Set (SpatialCoordinates d)) ⊆ centeredCube z r hr := by
  have h := aux_lem_finite_stopping_partition_descendantCell_subset_prefix m z hr n w 0 (Nat.zero_le n)
  rwa [aux_lem_finite_stopping_partition_descendantCell_zero] at h

/-- Two cells of the same depth that share a point carry the same word. -/
theorem aux_lem_finite_stopping_partition_descendantCell_word_eq_of_mem (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    ∀ (n : ℕ) (w w' : Fin n → OddGridIndex d m) (x : SpatialCoordinates d),
      x ∈ (descendantCell m z hr n w : Set (SpatialCoordinates d)) →
      x ∈ (descendantCell m z hr n w' : Set (SpatialCoordinates d)) → w = w' := by
  intro n
  induction n with
  | zero =>
    intro w w' _ _ _
    funext i
    exact i.elim0
  | succ n ih =>
    intro w w' x hx hx'
    have hinit : (fun i : Fin n => w i.castSucc) = fun i => w' i.castSucc :=
      ih _ _ x (descendantCell_succ_subset m z hr n w hx)
        (descendantCell_succ_subset m z hr n w' hx')
    have hlast : w (Fin.last n) = w' (Fin.last n) := by
      by_contra hne
      rw [aux_lem_finite_stopping_partition_descendantCell_succ_eq_oddGridCell] at hx hx'
      rw [hinit] at hx
      exact (oddGridCell_pairwiseDisjoint _ (descendantSide_pos m n hr) m hne).le_bot
        ⟨hx, hx'⟩
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact congrFun hinit j
    · exact hlast

/-- The depth-`n` cells cover the root cube up to a null set. -/
theorem aux_lem_finite_stopping_partition_descendantCells_union_ae_eq (m : ℕ) (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) :
    ∀ n : ℕ, (⋃ w : Fin n → OddGridIndex d m,
      (descendantCell m z hr n w : Set (SpatialCoordinates d))) =ᵐ[volume]
        (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  intro n
  induction n with
  | zero =>
    have h : (⋃ w : Fin 0 → OddGridIndex d m,
        (descendantCell m z hr 0 w : Set (SpatialCoordinates d))) =
          centeredCube z r hr := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun w => (aux_lem_finite_stopping_partition_descendantCell_zero m z hr w).le
      · intro x hx
        exact Set.mem_iUnion.2 ⟨Fin.elim0, by rw [aux_lem_finite_stopping_partition_descendantCell_zero]; exact hx⟩
    rw [h]
  | succ n ih =>
    have hset : (⋃ w : Fin (n + 1) → OddGridIndex d m,
        (descendantCell m z hr (n + 1) w : Set (SpatialCoordinates d))) =
        ⋃ v : Fin n → OddGridIndex d m, ⋃ l : OddGridIndex d m,
          (oddGridCell (descendantCenter m z r n v) (descendantSide m n r)
            (descendantSide_pos m n hr) m l : Set (SpatialCoordinates d)) := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨w, hw⟩
        rw [aux_lem_finite_stopping_partition_descendantCell_succ_eq_oddGridCell] at hw
        exact ⟨_, _, hw⟩
      · rintro ⟨v, l, hvl⟩
        refine ⟨Fin.snoc (α := fun _ => OddGridIndex d m) v l, ?_⟩
        rw [aux_lem_finite_stopping_partition_descendantCell_succ_eq_oddGridCell]
        have hv : (fun i : Fin n =>
            (Fin.snoc (α := fun _ => OddGridIndex d m) v l) i.castSucc) = v := by
          funext i
          simp
        rw [hv, Fin.snoc_last]
        exact hvl
    rw [hset]
    refine (EventuallyEq.countable_iUnion fun v => ?_).trans ih
    exact oddGrid_union_ae_eq (descendantCenter m z r n v) (descendantSide_pos m n hr) m

/-! ## Stopping leaves -/

/-- A leaf of the stopping tree: stopped or at the final depth, with no stopped
proper prefix. -/
def aux_lem_finite_stopping_partition_IsLeaf {m : ℕ} (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax n : ℕ)
    (w : Fin n → OddGridIndex d m) : Prop :=
  n ≤ nmax ∧ (stop n w ∨ n = nmax) ∧
    ∀ (k : ℕ) (hk : k < n), ¬ stop k (aux_lem_finite_stopping_partition_wordPrefix w k hk.le)

/-- Distinct leaves have disjoint cells. -/
theorem aux_lem_finite_stopping_partition_leaf_cells_disjoint {m : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax : ℕ)
    {n n' : ℕ} {w : Fin n → OddGridIndex d m} {w' : Fin n' → OddGridIndex d m}
    (hw : aux_lem_finite_stopping_partition_IsLeaf stop nmax n w) (hw' : aux_lem_finite_stopping_partition_IsLeaf stop nmax n' w')
    (hne : (⟨n, w⟩ : Σ k, Fin k → OddGridIndex d m) ≠ ⟨n', w'⟩) :
    Disjoint (descendantCell m z hr n w : Set (SpatialCoordinates d))
      (descendantCell m z hr n' w' : Set (SpatialCoordinates d)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  -- the two words are comparable; the shorter is a prefix of the longer
  have key : ∀ {a b : ℕ} {u : Fin a → OddGridIndex d m} {v : Fin b → OddGridIndex d m},
      aux_lem_finite_stopping_partition_IsLeaf stop nmax a u → aux_lem_finite_stopping_partition_IsLeaf stop nmax b v →
      x ∈ (descendantCell m z hr a u : Set (SpatialCoordinates d)) →
      x ∈ (descendantCell m z hr b v : Set (SpatialCoordinates d)) → a < b → False := by
    intro a b u v hu hv hxu hxv hab
    have hxv' := aux_lem_finite_stopping_partition_descendantCell_subset_prefix m z hr b v a hab.le hxv
    have hpre : u = aux_lem_finite_stopping_partition_wordPrefix v a hab.le :=
      aux_lem_finite_stopping_partition_descendantCell_word_eq_of_mem m z hr a u _ x hxu hxv'
    rcases hu.2.1 with hstop | hmax
    · exact hv.2.2 a hab (hpre ▸ hstop)
    · have := hv.1
      omega
  rcases lt_trichotomy n n' with hlt | heq | hgt
  · exact key hw hw' hx hx' hlt
  · subst heq
    exact hne (by rw [aux_lem_finite_stopping_partition_descendantCell_word_eq_of_mem m z hr n w w' x hx hx'])
  · exact key hw' hw hx' hx hgt

/-- Every point of a depth-`nmax` cell lies in a leaf cell. -/
theorem aux_lem_finite_stopping_partition_exists_leaf_of_mem {m : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax : ℕ)
    (w : Fin nmax → OddGridIndex d m) (x : SpatialCoordinates d)
    (hx : x ∈ (descendantCell m z hr nmax w : Set (SpatialCoordinates d))) :
    ∃ (n : ℕ) (v : Fin n → OddGridIndex d m), aux_lem_finite_stopping_partition_IsLeaf stop nmax n v ∧
      x ∈ (descendantCell m z hr n v : Set (SpatialCoordinates d)) := by
  classical
  let P : ℕ → Prop := fun k => ∃ hk : k ≤ nmax, stop k (aux_lem_finite_stopping_partition_wordPrefix w k hk) ∨ k = nmax
  have hP : ∃ k, P k := ⟨nmax, le_rfl, Or.inr rfl⟩
  let k := Nat.find hP
  obtain ⟨hk, hstop⟩ : P k := Nat.find_spec hP
  refine ⟨k, aux_lem_finite_stopping_partition_wordPrefix w k hk, ⟨hk, hstop, ?_⟩, ?_⟩
  · intro l hl hsl
    have hmin := Nat.find_min hP hl
    apply hmin
    refine ⟨hl.le.trans hk, Or.inl ?_⟩
    rwa [aux_lem_finite_stopping_partition_wordPrefix_wordPrefix] at hsl
  · exact aux_lem_finite_stopping_partition_descendantCell_subset_prefix m z hr nmax w k hk hx

/-- The finite set of leaves, as a finset of the dependent word type. -/
def aux_lem_finite_stopping_partition_leafFinset {m : ℕ} (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop) (nmax : ℕ) :
    Finset (Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m) := by
  classical
  exact Finset.univ.filter fun p => aux_lem_finite_stopping_partition_IsLeaf stop nmax p.1 p.2

theorem aux_lem_finite_stopping_partition_mem_leafFinset {m : ℕ} (stop : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop)
    (nmax : ℕ) (p : Σ n : Fin (nmax + 1), Fin n → OddGridIndex d m) :
    p ∈ aux_lem_finite_stopping_partition_leafFinset stop nmax ↔ aux_lem_finite_stopping_partition_IsLeaf stop nmax p.1 p.2 := by
  classical
  simp [aux_lem_finite_stopping_partition_leafFinset]

variable {d : ℕ}
/-! ## Actual cell energies -/

variable {Q U : Opens (SpatialCoordinates d)}
variable {d : ℕ}
theorem aux_lem_finite_stopping_partition_prod_ite_mem_const {n : ℕ} (I : Finset (Fin n)) (a b : ℕ) :
    (∏ i : Fin n, if i ∈ I then a else b) = a ^ I.card * b ^ (n - I.card) := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (univ.filter fun i : Fin n => i ∈ I).card = I.card := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n))) (fun i => i ∈ I)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  have h3 : (univ.filter fun i : Fin n => ¬ i ∈ I).card = n - I.card := by omega
  rw [h1, h3]

/-- Words with at least `T` letters in `NP`. -/
theorem aux_lem_finite_stopping_partition_card_many_hits_le {α : Type*} [Fintype α] [DecidableEq α] (n T : ℕ)
    (NP : Finset α) :
    (univ.filter (fun w : Fin n → α =>
        T ≤ (univ.filter (fun i => w i ∈ NP)).card)).card ≤
      2 ^ n * NP.card ^ T * Fintype.card α ^ (n - T) := by
  classical
  by_cases hT : T ≤ n
  · have hsub : univ.filter (fun w : Fin n → α =>
          T ≤ (univ.filter fun i => w i ∈ NP).card) ⊆
        (powersetCard T (univ : Finset (Fin n))).biUnion
          (fun I => Fintype.piFinset (fun i => if i ∈ I then NP else univ)) := by
      intro w hw
      rw [mem_filter] at hw
      obtain ⟨I, hIsub, hIcard⟩ := exists_subset_card_eq hw.2
      rw [mem_biUnion]
      refine ⟨I, mem_powersetCard.2 ⟨subset_univ _, hIcard⟩, ?_⟩
      rw [Fintype.mem_piFinset]
      intro i
      split_ifs with hi
      · exact (mem_filter.1 (hIsub hi)).2
      · exact mem_univ _
    calc _ ≤ _ := card_le_card hsub
      _ ≤ ∑ I ∈ powersetCard T (univ : Finset (Fin n)),
            (Fintype.piFinset (fun i => if i ∈ I then NP else univ)).card :=
          card_biUnion_le
      _ = ∑ I ∈ powersetCard T (univ : Finset (Fin n)),
            NP.card ^ T * Fintype.card α ^ (n - T) := by
          refine sum_congr rfl fun I hI => ?_
          rw [Fintype.card_piFinset]
          have hIc := (mem_powersetCard.1 hI).2
          rw [show (∏ i : Fin n, (if i ∈ I then NP else (univ : Finset α)).card) =
              ∏ i : Fin n, (if i ∈ I then NP.card else Fintype.card α) from
            prod_congr rfl fun i _ => by split_ifs <;> simp]
          rw [aux_lem_finite_stopping_partition_prod_ite_mem_const, hIc]
      _ = n.choose T * (NP.card ^ T * Fintype.card α ^ (n - T)) := by
          rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ 2 ^ n * (NP.card ^ T * Fintype.card α ^ (n - T)) :=
          Nat.mul_le_mul_right _ (Nat.choose_le_two_pow n T)
      _ = _ := by ring
  · have hempty : univ.filter (fun w : Fin n → α =>
        T ≤ (univ.filter fun i => w i ∈ NP).card) = ∅ := by
      apply Finset.filter_false_of_mem
      intro w _ h
      have hle : (univ.filter fun i => w i ∈ NP).card ≤ n := by
        calc _ ≤ (univ : Finset (Fin n)).card := card_filter_le _ _
          _ = n := by simp
      omega
    rw [hempty, card_empty]
    exact Nat.zero_le _

/-- Number of strict `L^D` drops along the first `k` steps of a chain. -/
noncomputable def aux_lem_finite_stopping_partition_dropCount (lam : ℕ → ℝ) (LD : ℝ) (k : ℕ) : ℕ :=
  ((range k).filter fun s => LD * lam (s + 1) < lam s).card

/-- **Mass-drop chain.** For a non-increasing nonnegative chain, the drops by the
factor `LD ≥ 1` accumulate multiplicatively. -/
theorem aux_lem_finite_stopping_partition_mass_drop_chain (lam : ℕ → ℝ) (LD : ℝ) (hLD : 1 ≤ LD)
    (hmono : ∀ s, lam (s + 1) ≤ lam s) :
    ∀ k, LD ^ aux_lem_finite_stopping_partition_dropCount lam LD k * lam k ≤ lam 0 := by
  classical
  have hLD0 : 0 ≤ LD := zero_le_one.trans hLD
  intro k
  induction k with
  | zero => simp [aux_lem_finite_stopping_partition_dropCount]
  | succ k ih =>
    unfold aux_lem_finite_stopping_partition_dropCount at ih ⊢
    rw [range_add_one, filter_insert]
    have hnot : k ∉ (range k).filter (fun s => LD * lam (s + 1) < lam s) := by
      simp
    have hpow : 0 ≤ LD ^ ((range k).filter fun s => LD * lam (s + 1) < lam s).card :=
      pow_nonneg hLD0 _
    split_ifs with hdrop
    · rw [card_insert_of_notMem hnot, pow_succ, mul_assoc]
      calc _ ≤ LD ^ ((range k).filter fun s => LD * lam (s + 1) < lam s).card * lam k :=
            mul_le_mul_of_nonneg_left hdrop.le hpow
        _ ≤ lam 0 := ih
    · calc _ ≤ LD ^ ((range k).filter fun s => LD * lam (s + 1) < lam s).card * lam k :=
            mul_le_mul_of_nonneg_left (hmono k) hpow
        _ ≤ lam 0 := ih

/-- If the final mass is at least `fl > 0` and the initial mass is below
`LD^(g+1) fl`, then there are at most `g` drops. -/
theorem aux_lem_finite_stopping_partition_dropCount_le (lam : ℕ → ℝ) (LD fl : ℝ) (hLD : 1 < LD) (hfl : 0 < fl)
    (hmono : ∀ s, lam (s + 1) ≤ lam s) (k g : ℕ)
    (hfinal : fl ≤ lam k) (hinit : lam 0 < LD ^ (g + 1) * fl) :
    aux_lem_finite_stopping_partition_dropCount lam LD k ≤ g := by
  have hchain := aux_lem_finite_stopping_partition_mass_drop_chain lam LD hLD.le hmono k
  have hpow : 0 ≤ LD ^ aux_lem_finite_stopping_partition_dropCount lam LD k := pow_nonneg (by linarith) _
  have h1 : LD ^ aux_lem_finite_stopping_partition_dropCount lam LD k * fl < LD ^ (g + 1) * fl :=
    lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hfinal hpow).trans hchain) hinit
  have h2 : LD ^ aux_lem_finite_stopping_partition_dropCount lam LD k < LD ^ (g + 1) := lt_of_mul_lt_mul_right h1 hfl.le
  have h3 := (pow_lt_pow_iff_right₀ hLD).1 h2
  omega

/-- The selected-step subtraction: a selected unstopped step is bad, non-padded or
a mass drop. -/
theorem aux_lem_finite_stopping_partition_card_filter_le_three {β : Type*} (s : Finset β) (p a b c : β → Prop)
    [DecidablePred p] [DecidablePred a] [DecidablePred b] [DecidablePred c]
    (h : ∀ x ∈ s, p x → a x ∨ b x ∨ c x) :
    (s.filter p).card ≤ (s.filter a).card + (s.filter b).card + (s.filter c).card := by
  classical
  have hsub : s.filter p ⊆ (s.filter a ∪ s.filter b) ∪ s.filter c := by
    intro x hx
    rw [mem_filter] at hx
    rcases h x hx.1 hx.2 with ha | hb | hc
    · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hx.1, ha⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hx.1, hb⟩))
    · exact mem_union_right _ (mem_filter.2 ⟨hx.1, hc⟩)
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (s.filter a ∪ s.filter b).card + (s.filter c).card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (card_union_le _ _) _


variable {d : ℕ}
/-- The source's stopping rule (paper 4231--4233). -/
def aux_lem_finite_stopping_partition_stopRule {mg : ℕ} (Sel : ℕ → Prop)
    (Good : (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
    (Pad : OddGridIndex d mg → Prop) (mass : (n : ℕ) → (Fin n → OddGridIndex d mg) → ℝ)
    (LD : ℝ) : (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop
  | 0, _ => False
  | s + 1, w => Sel (s + 1) ∧ Good (s + 1) w ∧ Pad (w (Fin.last s)) ∧
      mass s (fun i => w i.castSucc) ≤ LD * mass (s + 1) w

theorem aux_lem_finite_stopping_partition_card_filter_fin_eq_range (B : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.univ : Finset (Fin B)).filter (fun i => p i.val)).card =
      ((Finset.range B).filter p).card := by
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨i.isLt, hi⟩
  · intro i _ j _ h
    exact Fin.ext h
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact ⟨⟨n, hn.1⟩, by simp [hn.2], rfl⟩

section Core

open Classical

variable [NeZero d] (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg B : ℕ)
end Core


variable {d : ℕ}

/-- `P`-padded child label. -/
def aux_lem_finite_stopping_partition_padLabel {m : ℕ} (P : ℕ) (k : OddGridIndex d m) : Prop :=
  ∀ i, P ≤ (k i).val ∧ (k i).val + P ≤ 2 * m

/-- The non-padded labels in one coordinate direction. -/
theorem aux_lem_finite_stopping_partition_card_coord_bad_le (m P : ℕ) :
    ((univ : Finset (Fin (2 * m + 1))).filter
      (fun x => ¬ (P ≤ x.val ∧ x.val + P ≤ 2 * m))).card ≤ 2 * P := by
  classical
  have hsub : ((univ : Finset (Fin (2 * m + 1))).filter
      (fun x => ¬ (P ≤ x.val ∧ x.val + P ≤ 2 * m))).image (fun x => x.val) ⊆
      Finset.range P ∪ Finset.Ioc (2 * m - P) (2 * m) := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    have hxlt := x.isLt
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]
    omega
  have hinj : Set.InjOn (fun x : Fin (2 * m + 1) => x.val)
      ↑((univ : Finset (Fin (2 * m + 1))).filter
        (fun x => ¬ (P ≤ x.val ∧ x.val + P ≤ 2 * m))) :=
    fun x _ y _ h => Fin.ext h
  rw [← Finset.card_image_of_injOn hinj]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.range P).card + (Finset.Ioc (2 * m - P) (2 * m)).card :=
        Finset.card_union_le _ _
    _ ≤ 2 * P := by
        rw [Finset.card_range, Nat.card_Ioc]
        omega

open Classical in
/-- Non-padded labels: at most `d (2P) (2m+1)^(d-1)`. -/
theorem aux_lem_finite_stopping_partition_card_not_padLabel_le (m P : ℕ) :
    ((univ : Finset (OddGridIndex d m)).filter (fun k => ¬ aux_lem_finite_stopping_partition_padLabel P k)).card ≤
      d * (2 * P) * (2 * m + 1) ^ (d - 1) := by
  classical
  let bad : Finset (Fin (2 * m + 1)) := (univ : Finset (Fin (2 * m + 1))).filter
    (fun x => ¬ (P ≤ x.val ∧ x.val + P ≤ 2 * m))
  have hsub : (univ : Finset (OddGridIndex d m)).filter (fun k => ¬ aux_lem_finite_stopping_partition_padLabel P k) ⊆
      (univ : Finset (Fin d)).biUnion (fun i =>
        Fintype.piFinset (fun j => if j = i then bad else univ)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, aux_lem_finite_stopping_partition_padLabel, not_forall] at hk
    obtain ⟨i, hi⟩ := hk
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [Fintype.mem_piFinset]
    intro j
    split_ifs with hj
    · subst hj
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    · exact Finset.mem_univ _
  have hcard : ∀ i : Fin d, (Fintype.piFinset (fun j : Fin d =>
      if j = i then bad else (univ : Finset (Fin (2 * m + 1))))).card ≤
      2 * P * (2 * m + 1) ^ (d - 1) := by
    intro i
    rw [Fintype.card_piFinset]
    have hprod : (∏ j : Fin d, (if j = i then bad else
        (univ : Finset (Fin (2 * m + 1)))).card) =
        bad.card * (2 * m + 1) ^ (d - 1) := by
      rw [← Finset.mul_prod_erase (univ : Finset (Fin d)) _ (Finset.mem_univ i)]
      have h2 : (∏ j ∈ (univ : Finset (Fin d)).erase i, (if j = i then bad else
          (univ : Finset (Fin (2 * m + 1)))).card) = (2 * m + 1) ^ (d - 1) := by
        rw [Finset.prod_congr rfl (g := fun _ => 2 * m + 1) (fun j hj => by
          rw [if_neg (Finset.ne_of_mem_erase hj), Finset.card_univ, Fintype.card_fin])]
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
      rw [h2, if_pos rfl]
    rw [hprod]
    exact Nat.mul_le_mul_right _ (aux_lem_finite_stopping_partition_card_coord_bad_le m P)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin d, (Fintype.piFinset (fun j : Fin d =>
          if j = i then bad else (univ : Finset (Fin (2 * m + 1))))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin d, 2 * P * (2 * m + 1) ^ (d - 1) := Finset.sum_le_sum fun i _ => hcard i
    _ = d * (2 * P) * (2 * m + 1) ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring


open Classical in


theorem lem_finite_stopping_partition_tree (m P : ℕ) :
    ((univ : Finset (OddGridIndex d m)).filter (fun k => ¬ aux_lem_finite_stopping_partition_padLabel P k)).card ≤
      d * (2 * P) * (2 * m + 1) ^ (d - 1) :=
  aux_lem_finite_stopping_partition_card_not_padLabel_le m P

end Paper
