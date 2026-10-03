module

public import SubdiffusiveProcess.Paper.density_based_full_grid
public import SubdiffusiveProcess.Paper.density_based_tree
public import Mathlib.Data.Fin.Tuple.Take
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
open Classical
lemma aux_density_based_energy_bounds_prefix {A : Type} (Good : List A → Prop)
    (theta B : ℝ)
    (h : ∀ J (w : Fin J → A),
      (Set.ncard {i : Fin J | ¬ Good ((List.ofFn w).take (i.val + 1))} : ℝ) ≤ theta * J + B) :
    ∀ J (w : Fin J → A),
      (((Finset.univ : Finset (Fin J)).filter fun i : Fin J =>
        ¬ Good (List.ofFn (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt))).card : ℝ) ≤
          theta * J + B := by
  classical
  intro J w
  have hp : ∀ (k : ℕ) (hk : k ≤ J),
      List.ofFn (aux_lem_finite_stopping_partition_wordPrefix w k hk) = (List.ofFn w).take k :=
    fun k hk => Fin.ofFn_take_eq_take_ofFn hk w
  have heq : (((Finset.univ : Finset (Fin J)).filter fun i : Fin J =>
      ¬ Good (List.ofFn (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt))) : Set (Fin J)) =
      {i : Fin J | ¬ Good ((List.ofFn w).take (i.val + 1))} := by
    ext i
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, hp]
  have hc := h J w
  rw [← heq, Set.ncard_coe_finset] at hc
  exact hc

/-- Transfer actual bank costs, good-cell source absorption and branch counts to
the exact descendant tree of a contained fine base cell. -/
theorem density_based_energy_bounds {d : ℕ} (hd : 1 ≤ d) (H1 base : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (zroot : SpatialCoordinates d) (jroot : Fin d → ℤ)
    (hroot : zroot = fun i => z0 i + (3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ)) * (jroot i : ℝ))
    (hsub : (centeredCube zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ)))
      (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z0 R hR : Set (SpatialCoordinates d))) :
    let m := subdivisionHalfWidth H1
    let r := (3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))
    let Cells := aux_goodext_admissible_grid_cells z0 R hR
    let Bank := aux_density_full_grid_cells z0 R hR
    let active := aux_density_based_tree_active H1 base z0 R hR zroot
    ∀ (embed : Cells → Bank) (hEmbed : ∀ b, (embed b).val = b.val)
      (index : List (OddGridIndex d m) → Cells)
      (hIndex : ∀ w, active w → (index w).val.1 = H1 * (base + w.length) ∧
        aux_goodext_admissible_grid_centre z0 (index w).val = descendantCenter m zroot r w.length w.get)
      (hPad : ∀ n (w : Fin (n + 1) → OddGridIndex d m),
        aux_lem_finite_stopping_partition_padLabel 3 (w (Fin.last n)) →
        (descendantCell m zroot (show 0 < r from zpow_pos (by norm_num) _) n
          (fun i => w i.castSucc) : Set (SpatialCoordinates d)) ⊆ (centeredCube z0 R hR : Set (SpatialCoordinates d)) →
        active (List.ofFn w))
      (Good : Cells → Prop) (theta B : ℝ)
      (hCount : ∀ J (w : Fin J → OddGridIndex d m),
        (Set.ncard {i : Fin J | ¬ (active ((List.ofFn w).take (i.val + 1)) →
          Good (index ((List.ofFn w).take (i.val + 1))))} : ℝ) ≤ theta * J + B)
      (ref cost : Bank → ℝ) (ratio : ℕ → ℝ) (nu : Measure (SpatialCoordinates d))
      (C K s fsup c r0 : ℝ) (hbase : r ≤ r0)
      (hRef : ∀ q, 0 < ref q)
      (hSource : ∀ b, Good b → (3 : ℝ) ^ (-(b.val.1 : ℤ)) ≤ r0 →
        (ref (embed b))⁻¹ * ((3 : ℝ) ^ (-(b.val.1 : ℤ))) ^ ((d : ℝ) + 2) * fsup ^ 2 ≤
          c * ((3 : ℝ) ^ (-(b.val.1 : ℤ))) ^ d)
      (hLocal : ∀ b, Good b → ∀ zP (idx : OddGridIndex d m),
        let side := (3 : ℝ) ^ (-(b.val.1 : ℤ))
        aux_goodext_admissible_grid_centre z0 b.val = oddGridCenter zP ((3 : ℝ) ^ H1 * side) m idx →
        Metric.closedBall (aux_goodext_admissible_grid_centre z0 b.val) (3 * side / 2) ⊆
          Metric.ball zP ((3 : ℝ) ^ H1 * side / 2) →
        Metric.ball zP ((3 : ℝ) ^ H1 * side / 2) ⊆ (centeredCube z0 R hR : Set (SpatialCoordinates d)) →
        cost (embed b) ≤ C * ratio b.val.1 *
          (nu.real (Metric.ball zP ((3 : ℝ) ^ H1 * side / 2)) +
            (ref (embed b))⁻¹ * side ^ ((d : ℝ) + 2) * fsup ^ 2))
      (hCrude : ∀ q, cost q ≤ K * ((3 : ℝ) ^ (-(q.val.1 : ℤ))) ^ s),
    ∃ fullIndex : (n : ℕ) → (Fin n → OddGridIndex d m) → Bank,
      (∀ n w, (fullIndex n w).val.1 = H1 * (base + n) ∧
        aux_goodext_admissible_grid_centre z0 (fullIndex n w).val = descendantCenter m zroot r n w ∧
        (3 : ℝ) ^ (-((fullIndex n w).val.1 : ℤ)) = descendantSide m n r ∧
        centeredCube (aux_goodext_admissible_grid_centre z0 (fullIndex n w).val)
          ((3 : ℝ) ^ (-((fullIndex n w).val.1 : ℤ))) (zpow_pos (by norm_num) _) =
            descendantCell m zroot (show 0 < r from zpow_pos (by norm_num) _) n w) ∧
      let TreeGood := fun n (w : Fin n → OddGridIndex d m) => active (List.ofFn w) → Good (index (List.ofFn w))
      (∀ J (w : Fin J → OddGridIndex d m),
        (((Finset.univ : Finset (Fin J)).filter fun i : Fin J =>
          ¬ TreeGood (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card : ℝ) ≤
            theta * J + B) ∧
      (∀ n w, 0 < ref (fullIndex n w)) ∧
      (∀ n (w : Fin (n + 1) → OddGridIndex d m), TreeGood (n + 1) w →
        aux_lem_finite_stopping_partition_padLabel 3 (w (Fin.last n)) →
        (ref (fullIndex (n + 1) w))⁻¹ * (descendantSide m (n + 1) r) ^ ((d : ℝ) + 2) * fsup ^ 2 ≤
          c * (descendantSide m (n + 1) r) ^ d) ∧
      (∀ n (w : Fin (n + 1) → OddGridIndex d m), TreeGood (n + 1) w →
        aux_lem_finite_stopping_partition_padLabel 3 (w (Fin.last n)) →
        cost (fullIndex (n + 1) w) ≤ C * ratio (H1 * (base + (n + 1))) *
          (nu.real (descendantCell m zroot (show 0 < r from zpow_pos (by norm_num) _) n
            (fun i => w i.castSucc) : Set (SpatialCoordinates d)) +
            (ref (fullIndex (n + 1) w))⁻¹ * (descendantSide m (n + 1) r) ^ ((d : ℝ) + 2) * fsup ^ 2)) ∧
      (∀ n w, cost (fullIndex n w) ≤ K * (descendantSide m n r) ^ s) := by
  classical
  intro m r Cells Bank active embed hEmbed index hIndex hPad Good theta B hCount
    ref cost ratio nu C K s fsup c r0 hbase hRef hSource hLocal hCrude
  have hr : 0 < r := zpow_pos (by norm_num) _
  obtain ⟨fullIndex, hFull⟩ := density_based_full_grid H1 base z0 R hR zroot jroot hroot hsub
  have hI : ∀ n (w : Fin n → OddGridIndex d m), active (List.ofFn w) →
      (index (List.ofFn w)).val.1 = H1 * (base + n) ∧
      aux_goodext_admissible_grid_centre z0 (index (List.ofFn w)).val = descendantCenter m zroot r n w := by
    intro n w hw
    have h := hIndex (List.ofFn w) hw
    have hc := aux_gcat_mass_grid_chain_prefix (fun n w => descendantCenter m zroot r n w) n n le_rfl w
    rw [List.take_of_length_le (by simp only [List.length_ofFn, le_refl])] at hc
    exact ⟨by simpa only [List.length_ofFn] using h.1, h.2.trans hc⟩
  have hMatch : ∀ n (w : Fin n → OddGridIndex d m), active (List.ofFn w) →
      fullIndex n w = embed (index (List.ofFn w)) := by
    intro n w hw
    exact Subtype.ext (((hFull n w).2.2.2.2 _ (hI n w hw).1 (hI n w hw).2).trans (hEmbed _).symm)
  have hRad : ∀ n (w : Fin n → OddGridIndex d m), active (List.ofFn w) →
      (3 : ℝ) ^ (-((index (List.ofFn w)).val.1 : ℤ)) = descendantSide m n r := by
    intro n w hw
    have h := (hFull n w).2.2.1
    rw [hMatch n w hw, hEmbed] at h
    exact h
  have hParent : ∀ n (w : Fin (n + 1) → OddGridIndex d m),
      (descendantCell m zroot hr n (fun i => w i.castSucc) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z0 R hR : Set (SpatialCoordinates d)) :=
    fun n w => (aux_lem_finite_stopping_partition_descendantCell_subset_root m zroot hr n _).trans hsub
  refine ⟨fullIndex, fun n w => ⟨(hFull n w).1, (hFull n w).2.1,
    (hFull n w).2.2.1, (hFull n w).2.2.2.1⟩, ?_⟩
  intro TreeGood
  refine ⟨?_, fun n w => hRef _, ?_, ?_, ?_⟩
  · intro J w
    have hc := aux_density_based_energy_bounds_prefix (fun w => active w → Good (index w)) theta B hCount J w
    convert hc using 1
    congr 2
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, TreeGood]
  · intro n w hg hp
    have ha := hPad n w hp (hParent n w)
    have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hwidthOne : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by linarith only [hmR]
    have hsmall : descendantSide m (n + 1) r ≤ r0 :=
      (div_le_self hr.le (one_le_pow₀ hwidthOne)).trans hbase
    have h := hSource (index (List.ofFn w)) (hg ha) ((hRad _ _ ha).trans_le hsmall)
    rw [← hMatch _ _ ha, hRad _ _ ha] at h
    exact h
  · intro n w hg hp
    have ha := hPad n w hp (hParent n w)
    let b := index (List.ofFn w)
    let side := (3 : ℝ) ^ (-(b.val.1 : ℤ))
    let zP := descendantCenter m zroot r n (fun i => w i.castSucc)
    have hs : descendantSide m n r = (3 : ℝ) ^ H1 * side := by
      rw [FiniteStopping.cell2_parent_side_eq H1 r n, ← hRad _ _ ha]
    have hc : aux_goodext_admissible_grid_centre z0 b.val =
        oddGridCenter zP ((3 : ℝ) ^ H1 * side) m (w (Fin.last n)) := by
      rw [(hI _ _ ha).2]
      change oddGridCenter zP (descendantSide m n r) m _ = _
      rw [hs]
    have hpar : Metric.ball zP ((3 : ℝ) ^ H1 * side / 2) ⊆
        (centeredCube z0 R hR : Set (SpatialCoordinates d)) := by
      rw [← hs]
      exact hParent n w
    have hwidth : 2 * (m : ℝ) + 1 = (3 : ℝ) ^ H1 := by exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
    have hpad := ((goodext_fixed_padding d hd m).2 zP side (zpow_pos (by norm_num) _) b.val.1 rfl
      (w (Fin.last n)) hp).1
    rw [hwidth, ← hc] at hpad
    have h := hLocal b (hg ha) zP (w (Fin.last n)) hc hpad hpar
    rw [← hs] at h
    rw [← hMatch _ _ ha, hRad _ _ ha, (hI _ _ ha).1] at h
    exact h
  · intro n w
    have h := hCrude (fullIndex n w)
    rw [(hFull n w).2.2.1] at h
    exact h
end Paper
