module

public import SubdiffusiveProcess.Paper.density_grid_descendants
public import SubdiffusiveProcess.Paper.gcat_mass_grid_prefix
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- A vertex below a fine base cell is active when its fixed enlargement lies in Q. -/
def aux_density_based_tree_active {d : ℕ} (H1 base : ℕ)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (zroot : SpatialCoordinates d)
    (w : List (OddGridIndex d (subdivisionHalfWidth H1))) : Prop :=
  1 ≤ H1 * (base + w.length) ∧ ∀ U : Fin 3 × (Fin d → Fin 3),
    closure (centeredCube
      (gcat_rootCentre 1 (H1 * (base + w.length))
        (descendantCenter (subdivisionHalfWidth H1) zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) w.length w.get) U)
      (gcat_rootSide 1 (H1 * (base + w.length)) U) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z0 R hR : Set (SpatialCoordinates d))

/-- Starting at an arbitrary absolute observation base cell, every active
descendant has the exact admissible-bank index and every padded child of a
contained parent is active. This supplies the direct shifted-count interface. -/
theorem density_based_tree {d : ℕ} (hd : 1 ≤ d) (H1 base : ℕ) (hH1 : 0 < H1)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (zroot : SpatialCoordinates d) (jroot : Fin d → ℤ)
    (hroot : zroot = fun i => z0 i + (3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ)) * (jroot i : ℝ)) :
    ∃ index : List (OddGridIndex d (subdivisionHalfWidth H1)) →
        aux_goodext_admissible_grid_cells z0 R hR,
      (∀ w, aux_density_based_tree_active H1 base z0 R hR zroot w →
        (index w).val.1 = H1 * (base + w.length) ∧
        aux_goodext_admissible_grid_centre z0 (index w).val =
          descendantCenter (subdivisionHalfWidth H1) zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) w.length w.get) ∧
      ∀ (n : ℕ) (w : Fin (n + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
        aux_lem_finite_stopping_partition_padLabel 3 (w (Fin.last n)) →
        (descendantCell (subdivisionHalfWidth H1) zroot (zpow_pos (by norm_num : (0 : ℝ) < 3) (-((H1 * base : ℕ) : ℤ)))
          n (fun i => w i.castSucc) : Set (SpatialCoordinates d)) ⊆
            (centeredCube z0 R hR : Set (SpatialCoordinates d)) →
        aux_density_based_tree_active H1 base z0 R hR zroot (List.ofFn w) := by
  classical
  obtain ⟨first⟩ := (goodext_admissible_grid d hd z0 R hR).2.1
  have hex : ∀ w, aux_density_based_tree_active H1 base z0 R hR zroot w →
      ∃ b : aux_goodext_admissible_grid_cells z0 R hR,
        b.val.1 = H1 * (base + w.length) ∧ aux_goodext_admissible_grid_centre z0 b.val =
          descendantCenter (subdivisionHalfWidth H1) zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) w.length w.get := by
    intro w hw
    obtain ⟨j, hj⟩ := density_grid_descendants H1 (H1 * base) z0 zroot jroot hroot w.length w.get
    rw [← Nat.mul_add] at hj
    refine ⟨⟨(H1 * (base + w.length), j), hw.1, ?_⟩, rfl, hj.symm⟩
    intro U
    rw [← hj]
    exact hw.2 U
  let index := fun w => if hw : aux_density_based_tree_active H1 base z0 R hR zroot w
    then Classical.choose (hex w hw) else first
  refine ⟨index, ?_, ?_⟩
  · intro w hw
    simpa only [index, dif_pos hw] using Classical.choose_spec (hex w hw)
  · intro n w hpad hparent
    let m := subdivisionHalfWidth H1
    let k := H1 * (base + (n + 1))
    let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
    let zP := descendantCenter m zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) n (fun i => w i.castSucc)
    have hL : 2 * (m : ℝ) + 1 = (3 : ℝ) ^ H1 := by
      exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
    have hchild : descendantSide m (n + 1) ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) = r := by
      have h := FiniteStopping.descendantSide_zpow H1 m
        (two_mul_subdivisionHalfWidth_add_one H1) (-((H1 * base : ℕ) : ℤ)) (n + 1)
      exact h.trans (by dsimp only [r, k]; congr 1; push_cast; ring)
    have hside : descendantSide m n ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) = (2 * (m : ℝ) + 1) * r := by
      rw [FiniteStopping.cell2_parent_side_eq H1 ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) n, hchild, hL]
    have hcentre : descendantCenter m zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) (n + 1) w =
        oddGridCenter zP ((2 * (m : ℝ) + 1) * r) m (w (Fin.last n)) := by
      change oddGridCenter zP (descendantSide m n ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ)))) m (w (Fin.last n)) = _
      rw [hside]
    have hparent' : Metric.ball zP ((2 * (m : ℝ) + 1) * r / 2) ⊆
        (centeredCube z0 R hR : Set (SpatialCoordinates d)) := by
      change Metric.ball zP (descendantSide m n ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) / 2) ⊆ _ at hparent
      rwa [hside] at hparent
    have hroots := (goodext_fixed_padding d hd m).2 zP r (zpow_pos (by norm_num) _)
      k rfl (w (Fin.last n)) hpad
    have hfull : 1 ≤ k ∧ ∀ U : Fin 3 × (Fin d → Fin 3),
      closure (centeredCube (gcat_rootCentre 1 k (descendantCenter m zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) (n + 1) w) U)
        (gcat_rootSide 1 k U) (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
          (centeredCube z0 R hR : Set (SpatialCoordinates d)) := by
      refine ⟨by dsimp [k]; exact Nat.mul_pos hH1 (by omega), ?_⟩
      intro U
      rw [hcentre]
      exact (hroots.2 U).trans hparent'
    have hctr : descendantCenter m zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) (List.ofFn w).length (List.ofFn w).get =
        descendantCenter m zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) (n + 1) w := by
      have h := aux_gcat_mass_grid_chain_prefix (fun j v => descendantCenter m zroot ((3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))) j v)
        (n + 1) (n + 1) le_rfl w
      have htake : (List.ofFn w).take (n + 1) = List.ofFn w :=
        List.take_of_length_le (by simp only [List.length_ofFn, le_refl])
      rw [htake] at h
      exact h
    unfold aux_density_based_tree_active
    rw [hctr]
    simpa only [List.length_ofFn] using hfull
end Paper
