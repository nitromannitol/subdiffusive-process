module

public import SubdiffusiveProcess.Paper.lem_finite_stopping_partition

@[expose] public section

/-!
# `lfsc_partition_core` — the deterministic sourced stopping partition

Verbatim adaptation of `aux_lem_finite_stopping_partition_{stopped_leaf_le, stopped_sum_le, core_partition}`
(paper `\label{mfd:lem-finite-stopping}` Steps 1-3, on the actual two-stage tree) to the paper's mass
`λ = Γ_M(u_M) + 3^{-ζN}B² dx` of `\label{mfd:lem-finite-source-comparison}`: the local hypothesis at a stopped cell
carries the source term absorbed in the mass of the PARENT (`massOn aS u fl parent`), and the stopping rule
`mass(parent) ≤ L^D mass(child)` then gives the same stopped-cell budget `c Γ(q) + A c L^D λ(q)`.
The floor `fl` is a parameter, exactly as in the unsourced core; `u` is any weak function (no minimizing property is used).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter TopologicalSpace Topology Finset
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper

variable {d : ℕ}

section Core

open Classical

variable [NeZero d] (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (t0 mg B : ℕ)
  (aT aS : PositiveCoefficient (centeredCube z r hr))
  (u : weakSobolevGraph (centeredCube z r hr)) (fl LD : ℝ)
  (Sel : ℕ → Prop)
  (Good : (Fin t0 → OddGridIndex d 1) → (n : ℕ) → (Fin n → OddGridIndex d mg) → Prop)
  (Pad : OddGridIndex d mg → Prop)

/-- One stopped cell costs at most `c Γ(q) + A c L^D λ(q)`. -/
theorem aux_lfsc_partition_core_stopped_leaf_le (hfl : 0 ≤ fl) (A c : ℝ) (hA : 0 ≤ A) (ρ : ℕ → ℝ)
    (hρ : ∀ s, Sel s → 0 ≤ ρ s ∧ ρ s ≤ c)
    (hcell : ∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg),
      s + 1 ≤ B → Sel (s + 1) → Good w0 (s + 1) w → Pad (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
        ρ (s + 1) * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) +
          A * ρ (s + 1) * aux_lem_finite_stopping_partition_massOn aS u.val fl
            (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc) :
              Set (SpatialCoordinates d)))
    (p : aux_lem_finite_stopping_partition_LeafIdx d t0 mg B)
    (hstop : aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad p.1 p.2.1 p.2.2) :
    aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg p.1 p.2.1 p.2.2)
        (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg p.1 p.2.1 p.2.2) ≤
      c * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg p.1 p.2.1 p.2.2) +
        A * c * LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_cell2 z hr t0 mg p.1 p.2.1 p.2.2) := by
  rcases p with ⟨w0, ⟨⟨s, hs⟩, w⟩⟩
  cases s with
  | zero => exact absurd hstop (by simp [aux_lem_finite_stopping_partition_stop2, aux_lem_finite_stopping_partition_stopRule])
  | succ s =>
    simp only [aux_lem_finite_stopping_partition_stop2, aux_lem_finite_stopping_partition_stopRule] at hstop
    obtain ⟨hSel, hG, hP, hM⟩ := hstop
    have h1 := hcell w0 s w (by omega) hSel hG hP
    obtain ⟨hρ0, hρc⟩ := hρ (s + 1) hSel
    have hq0 : 0 ≤ aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) :=
      aux_lem_finite_stopping_partition_energyOn_nonneg aS u.val (aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg w0 _ _)
    have hp0 : 0 ≤ aux_lem_finite_stopping_partition_massOn aS u.val fl
        (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc) : Set (SpatialCoordinates d)) :=
      add_nonneg (aux_lem_finite_stopping_partition_energyOn_nonneg aS u.val
        (aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg w0 _ _))
        (mul_nonneg hfl measureReal_nonneg)
    have hpm : aux_lem_finite_stopping_partition_massOn aS u.val fl
        (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc) : Set (SpatialCoordinates d)) ≤
        LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) := hM
    have hc0 : 0 ≤ c := hρ0.trans hρc
    calc _ ≤ _ := h1
      _ ≤ c * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) +
            A * c * (LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w)) := by
          gcongr
      _ = _ := by ring

/-- **Stopped-cell budget** (paper 4240--4247). -/
theorem aux_lfsc_partition_core_stopped_sum_le (hfl : 0 ≤ fl) (A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hLD0 : 0 ≤ LD)
    (ρ : ℕ → ℝ) (hρ : ∀ s, Sel s → 0 ≤ ρ s ∧ ρ s ≤ c)
    (hcell : ∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg),
      s + 1 ≤ B → Sel (s + 1) → Good w0 (s + 1) w → Pad (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
        ρ (s + 1) * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) +
          A * ρ (s + 1) * aux_lem_finite_stopping_partition_massOn aS u.val fl
            (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc) :
              Set (SpatialCoordinates d))) :
    (∑ p ∈ (aux_lem_finite_stopping_partition_leaves2 (aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad) B).filter
        (fun p => aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad p.1 p.2.1 p.2.2),
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg p.1 p.2.1 p.2.2)
        (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg p.1 p.2.1 p.2.2)) ≤
      c * aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z r hr : Set (SpatialCoordinates d)) +
        A * c * LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  classical
  set F := (aux_lem_finite_stopping_partition_leaves2 (aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad) B).filter
    (fun p => aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad p.1 p.2.1 p.2.2) with hF
  have hdisj : (F : Set (aux_lem_finite_stopping_partition_LeafIdx d t0 mg B)).PairwiseDisjoint
      (fun p => (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d))) :=
    (aux_lem_finite_stopping_partition_leaves2_pairwiseDisjoint z hr _ B).subset (Finset.coe_subset.2 (Finset.filter_subset _ _))
  have hE := aux_lem_finite_stopping_partition_energyOn_sum_le F aS u.val (fun p => (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)))
    (fun p => (aux_lem_finite_stopping_partition_leafCell z hr p).isOpen.measurableSet)
    (fun p => aux_lem_finite_stopping_partition_cell2_subset_root z hr t0 mg _ _ _) hdisj
  have hM := (aux_lem_finite_stopping_partition_volume_sum_cells_le z hr t0 mg B aS u fl F hdisj).resolve_right (not_lt.2 hfl)
  calc _ ≤ ∑ p ∈ F, (c * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)) +
          A * c * LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d))) := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact aux_lfsc_partition_core_stopped_leaf_le z hr t0 mg B aT aS u fl LD Sel Good Pad hfl A c hA ρ hρ hcell p
          (Finset.mem_filter.1 hp).2
    _ = c * ∑ p ∈ F, aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)) +
          A * c * LD * ∑ p ∈ F, aux_lem_finite_stopping_partition_massOn aS u.val fl (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        have hAcL : 0 ≤ A * c * LD := mul_nonneg (mul_nonneg hA hc) hLD0
        gcongr

/-- **Per-sample finite stopping partition** (paper 4227--4280, one sample).
The conclusion has exactly the partition/sum shape of the frozen parent. -/
theorem lfsc_partition_core (hfl : 0 < fl) (hLD : 1 < LD) (A c Kc : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (ρ : ℕ → ℝ) (hρ : ∀ s, Sel s → 0 ≤ ρ s ∧ ρ s ≤ c)
    (hcell : ∀ (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin (s + 1) → OddGridIndex d mg),
      s + 1 ≤ B → Sel (s + 1) → Good w0 (s + 1) w → Pad (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg w0 (s + 1) w) ≤
        ρ (s + 1) * aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 (s + 1) w) +
          A * ρ (s + 1) * aux_lem_finite_stopping_partition_massOn aS u.val fl
            (aux_lem_finite_stopping_partition_cell2 z hr t0 mg w0 s (fun i => w i.castSucc) :
              Set (SpatialCoordinates d)))
    (nsel nbad g : ℕ)
    (hbad : ∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
      ((Finset.univ : Finset (Fin B)).filter fun i =>
        ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card ≤ nbad)
    (hsel : nsel ≤ ((Finset.univ : Finset (Fin B)).filter fun i => Sel (i.val + 1)).card)
    (hmassQ : aux_lem_finite_stopping_partition_massOn aS u.val fl (centeredCube z r hr : Set (SpatialCoordinates d)) <
      LD ^ (g + 1) * (fl * (descendantSide mg B (descendantSide 1 t0 r)) ^ d))
    (hcrude : ∀ (w0 : Fin t0 → OddGridIndex d 1) (w : Fin B → OddGridIndex d mg),
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg w0 B w) (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg w0 B w) ≤
        Kc) :
    ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
      (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
    let cell := fun i => centeredCube (centers i) (sides i) (hside i)
    ∃ hle : ∀ i, cell i ≤ centeredCube z r hr,
    (∀ i, ∃ s ≤ B, sides i = descendantSide mg s (descendantSide 1 t0 r)) ∧
    Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d))
      (cell j : Set (SpatialCoordinates d))) ∧
    ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
      (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
    ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
      ‖(v : SobolevData (cell i)).1‖ ≤
        K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖,
    let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
      ⟨sobolevDataRestrict (hle i) u.val, sobolevDataRestrict_mem_weak (hle i) u.property⟩
    ∃ R : ℕ, R ≤ (3 ^ d) ^ t0 * (2 ^ B * (Finset.univ.filter fun l => ¬ Pad l).card ^
            (nsel - nbad - g) * ((2 * mg + 1) ^ d) ^ (B - (nsel - nbad - g))) ∧
    (∑ i : Fin ncell,
      @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
        (positiveCoefficientRestrict (hle i) aT) (bcell i)) ≤
      c * aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z r hr : Set (SpatialCoordinates d)) +
        A * c * LD * aux_lem_finite_stopping_partition_massOn aS u.val fl (centeredCube z r hr : Set (SpatialCoordinates d)) +
        (R : ℝ) * Kc := by
  classical
  set stop := aux_lem_finite_stopping_partition_stop2 z hr t0 mg aS u fl LD Sel Good Pad with hstopdef
  set F := aux_lem_finite_stopping_partition_leaves2 stop B with hFdef
  let e : F ≃ Fin F.card := F.equivFin
  let leaf : Fin F.card → aux_lem_finite_stopping_partition_LeafIdx d t0 mg B := fun i => (e.symm i).1
  have hleafmem : ∀ i, leaf i ∈ F := fun i => (e.symm i).2
  have hleaf_e : ∀ (p : aux_lem_finite_stopping_partition_LeafIdx d t0 mg B) (hp : p ∈ F), leaf (e ⟨p, hp⟩) = p := by
    intro p hp
    simp only [leaf]
    rw [e.symm_apply_apply]
  let resp : aux_lem_finite_stopping_partition_LeafIdx d t0 mg B → ℝ := fun p =>
    aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg p.1 p.2.1 p.2.2)
      (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg p.1 p.2.1 p.2.2)
  refine ⟨F.card,
    fun i => descendantCenter mg (descendantCenter 1 z r t0 (leaf i).1)
      (descendantSide 1 t0 r) (leaf i).2.1 (leaf i).2.2,
    fun i => descendantSide mg (leaf i).2.1 (descendantSide 1 t0 r),
    fun i => descendantSide_pos mg _ (descendantSide_pos 1 t0 hr), ?_⟩
  refine ⟨fun i => aux_lem_finite_stopping_partition_cell2_le_root z hr t0 mg (leaf i).1 (leaf i).2.1 (leaf i).2.2,
    ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(leaf i).2.1, Nat.lt_succ_iff.1 (leaf i).2.1.isLt, rfl⟩
  · intro i j hij
    have hne : leaf i ≠ leaf j := fun h => hij (e.symm.injective (Subtype.ext h))
    exact aux_lem_finite_stopping_partition_leaves2_pairwiseDisjoint z hr stop B (hleafmem i) (hleafmem j) hne
  · have hset : (⋃ i, (aux_lem_finite_stopping_partition_leafCell z hr (leaf i) : Set (SpatialCoordinates d))) =
        ⋃ p ∈ F, (aux_lem_finite_stopping_partition_leafCell z hr p : Set (SpatialCoordinates d)) := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hx⟩
        exact ⟨leaf i, hleafmem i, hx⟩
      · rintro ⟨p, hp, hx⟩
        refine ⟨e ⟨p, hp⟩, ?_⟩
        rw [hleaf_e p hp]
        exact hx
    have h := aux_lem_finite_stopping_partition_leaves2_cover z hr stop B
    rw [← hset] at h
    exact h
  · refine ⟨fun i => aux_lem_finite_stopping_partition_cell2_killedPoincare z hr t0 mg (leaf i).1 (leaf i).2.1 (leaf i).2.2,
      (F.filter (fun p => ¬ stop p.1 p.2.1 p.2.2)).card,
      aux_lem_finite_stopping_partition_residual_card_le z hr t0 mg B aS u fl LD Sel Good Pad hfl hLD nsel nbad g hbad hsel hmassQ,
      ?_⟩
    show (∑ i : Fin F.card, resp (leaf i)) ≤ _
    have hsum : (∑ i : Fin F.card, resp (leaf i)) = ∑ p ∈ F, resp p := by
      rw [← Finset.sum_coe_sort F]
      exact Equiv.sum_comp e.symm (fun x : F => resp x.1)
    rw [hsum, ← Finset.sum_filter_add_sum_filter_not F (fun p => stop p.1 p.2.1 p.2.2)]
    have h1 := aux_lfsc_partition_core_stopped_sum_le z hr t0 mg B aT aS u fl LD Sel Good Pad hfl.le A c hA hc
      (by linarith) ρ hρ hcell
    have hres : ∀ p ∈ F.filter (fun p => ¬ stop p.1 p.2.1 p.2.2), resp p ≤ Kc := by
      intro p hp
      rw [Finset.mem_filter, hFdef, aux_lem_finite_stopping_partition_mem_leaves2] at hp
      obtain ⟨hleaf, hnstop⟩ := hp
      rcases p with ⟨w0, ⟨⟨s, hs⟩, w⟩⟩
      have hsB : s = B := hleaf.2.1.resolve_left hnstop
      subst hsB
      exact hcrude w0 w
    have h2 := Finset.sum_le_card_nsmul _ _ Kc hres
    rw [nsmul_eq_mul] at h2
    exact add_le_add h1 h2


end Core

end Paper
