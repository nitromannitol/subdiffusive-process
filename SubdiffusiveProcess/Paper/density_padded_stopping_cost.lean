module

public import SubdiffusiveProcess.Paper.density_stopping_cost
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
open Classical

/-- Source absorption is needed only on good padded cells, the cells eligible
for stopping. This allows inactive catalogue vertices to count as good without
requiring a fictitious source bound there. The final cost bound is unchanged. -/
theorem density_padded_stopping_cost
    (d m : ℕ) (hm : 0 < m) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (c D eta theta Bbad Cd s C a K fsup : ℝ)
    (hc : 0 < c) (hD : 0 < D) (heta : 0 < eta) (heta3 : eta ≤ 3)
    (hDim : (d : ℝ) / D ≤ eta / 8) (htheta : theta ≤ eta / 8)
    (hCd : 0 < Cd) (hs : (d : ℝ) - eta / 8 < s) (hC : 0 ≤ C) (ha : 0 < a) (hK : 0 ≤ K)
    (Sel : ℕ → Prop) (hSel : eta ≤ upperDensity Sel) (base : ℕ)
    (ratio : ℕ → ℝ) (hratio : ∀ n, Sel n → ratio n ≤ a)
    (Good : (n : ℕ) → (Fin n → OddGridIndex d m) → Prop)
    (Pad : OddGridIndex d m → Prop)
    (hbad : ∀ (J : ℕ) (w : Fin J → OddGridIndex d m),
      (((Finset.univ : Finset (Fin J)).filter fun i =>
        ¬ Good (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card : ℝ) ≤
          theta * (J : ℝ) + Bbad)
    (ref cost : (n : ℕ) → (Fin n → OddGridIndex d m) → ℝ)
    (href : ∀ n w, 0 < ref n w)
    (hsource : ∀ n (w : Fin (n + 1) → OddGridIndex d m),
      Good (n + 1) w → Pad (w (Fin.last n)) →
      (ref (n + 1) w)⁻¹ * (descendantSide m (n + 1) r) ^ ((d : ℝ) + 2) * fsup ^ 2 ≤
        c * (descendantSide m (n + 1) r) ^ d)
    (hlocal : ∀ n (w : Fin (n + 1) → OddGridIndex d m), Good (n + 1) w → Pad (w (Fin.last n)) →
      cost (n + 1) w ≤ C * ratio (base + (n + 1)) *
        (nu.real (descendantCell m z hr n (fun i => w i.castSucc) : Set (SpatialCoordinates d)) +
          (ref (n + 1) w)⁻¹ * (descendantSide m (n + 1) r) ^ ((d : ℝ) + 2) * fsup ^ 2))
    (hcrude : ∀ n w, cost n w ≤ K * (descendantSide m n r) ^ s) :
    let mu := nu + ENNReal.ofReal c • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
    let mass := fun n w => mu.real (descendantCell m z hr n w : Set (SpatialCoordinates d))
    let L : ℝ := 2 * (m : ℝ) + 1
    let stop := aux_lem_finite_stopping_partition_stopRule (fun n => Sel (base + n)) Good Pad mass (L ^ D)
    (((Finset.univ : Finset (OddGridIndex d m)).filter fun l => ¬ Pad l).card : ℝ) ≤
      Cd * L ^ ((d : ℝ) - 1) →
    2 * Cd ^ (eta / 3) ≤ L ^ (eta / 3 - eta / 8) →
    ∀ eps : ℝ, 0 < eps → ∃ᶠ J : ℕ in atTop,
      (∑ p ∈ aux_lem_finite_stopping_partition_leafFinset stop J, cost p.1 p.2) ≤
        (C * a * L ^ D) * mu.real (centeredCube z r hr : Set (SpatialCoordinates d)) + eps := by
  intro mu mass L stop hNP hLarge eps heps
  have hvolQ : volume (centeredCube z r hr : Set (SpatialCoordinates d)) < ⊤ := by
    rw [centeredCube_volume]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hvolQ⟩
  haveI : IsFiniteMeasure (ENNReal.ofReal c • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hmass : ∀ n w, mass n w =
      nu.real (descendantCell m z hr n w : Set (SpatialCoordinates d)) +
        c * volume.real (descendantCell m z hr n w : Set (SpatialCoordinates d)) := by
    intro n w
    dsimp only [mass, mu]
    rw [measureReal_add_apply, measureReal_ennreal_smul_apply,
      ENNReal.toReal_ofReal hc.le,
      measureReal_restrict_apply (descendantCell m z hr n w).isOpen.measurableSet,
      Set.inter_eq_left.mpr (aux_lem_finite_stopping_partition_descendantCell_subset_root m z hr n w)]
  have hcost : ∀ n w, stop n w → cost n w ≤ (C * a * L ^ D) * mass n w := by
    intro n w hstop
    cases n with
    | zero => exact False.elim hstop
    | succ n =>
      rcases hstop with ⟨hselected, hgood, hpadded, hdrop⟩
      have hchildSub := aux_lem_finite_stopping_partition_descendantCell_subset_prefix m z hr
        (n + 1) w n (Nat.le_succ n)
      have hparentFinite : volume (descendantCell m z hr n (fun i => w i.castSucc) : Set (SpatialCoordinates d)) ≠ ⊤ := by
        change volume (centeredCube (descendantCenter m z r n (fun i => w i.castSucc))
          (descendantSide m n r) (descendantSide_pos m n hr) : Set (SpatialCoordinates d)) ≠ ⊤
        rw [centeredCube_volume]
        exact ENNReal.ofReal_ne_top
      have hvol : volume.real (descendantCell m z hr (n + 1) w : Set (SpatialCoordinates d)) ≤
          volume.real (descendantCell m z hr n (fun i => w i.castSucc) : Set (SpatialCoordinates d)) :=
        measureReal_mono hchildSub hparentFinite
      have hsmall := hsource n w hgood hpadded
      have hvolChild : volume.real (descendantCell m z hr (n + 1) w : Set (SpatialCoordinates d)) =
          (descendantSide m (n + 1) r) ^ d := by
        change (volume (centeredCube (descendantCenter m z r (n + 1) w)
          (descendantSide m (n + 1) r) (descendantSide_pos m (n + 1) hr) : Set (SpatialCoordinates d))).toReal = _
        rw [centeredCube_volume, ENNReal.toReal_ofReal (pow_nonneg (descendantSide_pos m (n + 1) hr).le _)]
      have hparent :
          nu.real (descendantCell m z hr n (fun i => w i.castSucc) : Set (SpatialCoordinates d)) +
          (ref (n + 1) w)⁻¹ * (descendantSide m (n + 1) r) ^ ((d : ℝ) + 2) * fsup ^ 2 ≤
          mass n (fun i => w i.castSucc) := by
        rw [hmass]
        apply add_le_add_right
        exact hsmall.trans (by rw [← hvolChild]; exact mul_le_mul_of_nonneg_left hvol hc.le)
      have hnonneg : 0 ≤
          nu.real (descendantCell m z hr n (fun i => w i.castSucc) : Set (SpatialCoordinates d)) +
          (ref (n + 1) w)⁻¹ * (descendantSide m (n + 1) r) ^ ((d : ℝ) + 2) * fsup ^ 2 := by
        have hrefPos := href (n + 1) w
        have hrPos := descendantSide_pos m (n + 1) hr
        positivity
      calc
        cost (n + 1) w ≤ _ := hlocal n w hgood hpadded
        _ ≤ C * a * mass n (fun i => w i.castSucc) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hratio _ hselected) hC)
            hparent hnonneg (mul_nonneg hC ha.le)
        _ ≤ C * a * (L ^ D * mass (n + 1) w) :=
          mul_le_mul_of_nonneg_left hdrop (mul_nonneg hC ha.le)
        _ = (C * a * L ^ D) * mass (n + 1) w := by ring
  exact density_stopping_cost d m hm z r hr nu c D eta theta Bbad Cd s (C * a * L ^ D) K
    hc hD heta heta3 hDim htheta hCd hs (by dsimp [L]; positivity) hK
    Sel hSel base Good Pad hbad hNP hLarge cost hcost hcrude eps heps

end Paper
