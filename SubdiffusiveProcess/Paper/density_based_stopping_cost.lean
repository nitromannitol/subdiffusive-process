import SubdiffusiveProcess.Paper.density_based_energy_bounds
import SubdiffusiveProcess.Paper.density_padded_stopping_cost
open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
open Classical
/-- Stop the actual bank costs below a fine base, bounding leaf sums by the
common ambient source measure evaluated on the base root. -/
theorem density_based_stopping_cost {d : ℕ} (hd : 1 ≤ d) (H1 base : ℕ) (hH1 : 0 < H1)
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
      (ref cost : Bank → ℝ) (ratio : ℕ → ℝ) (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
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
      (hCrude : ∀ q, cost q ≤ K * ((3 : ℝ) ^ (-(q.val.1 : ℤ))) ^ s)
      (D eta a : ℝ) (hc : 0 < c) (hD : 0 < D) (heta : 0 < eta) (heta3 : eta ≤ 3)
      (hDim : (d : ℝ) / D ≤ eta / 8) (htheta : theta ≤ eta / 8)
      (hs : (d : ℝ) - eta / 8 < s) (hC : 0 ≤ C) (ha : 0 < a) (hK : 0 ≤ K)
      (Sel : ℕ → Prop) (hSel : eta ≤ upperDensity Sel)
      (hRatio : ∀ n, Sel n → ratio (H1 * n) ≤ a)
      (hLarge : 2 * (6 * (d : ℝ)) ^ (eta / 3) ≤
        ((3 : ℝ) ^ H1) ^ (eta / 3 - eta / 8)),
    ∃ fullIndex : (n : ℕ) → (Fin n → OddGridIndex d m) → Bank,
      (∀ n w, (fullIndex n w).val.1 = H1 * (base + n) ∧
        aux_goodext_admissible_grid_centre z0 (fullIndex n w).val = descendantCenter m zroot r n w ∧
        (3 : ℝ) ^ (-((fullIndex n w).val.1 : ℤ)) = descendantSide m n r ∧
        centeredCube (aux_goodext_admissible_grid_centre z0 (fullIndex n w).val)
          ((3 : ℝ) ^ (-((fullIndex n w).val.1 : ℤ))) (zpow_pos (by norm_num) _) =
            descendantCell m zroot (show 0 < r from zpow_pos (by norm_num) _) n w) ∧
      let TreeGood := fun n (w : Fin n → OddGridIndex d m) => active (List.ofFn w) → Good (index (List.ofFn w))
      let mu := nu + ENNReal.ofReal c • volume.restrict (centeredCube zroot r (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))
      let mass := fun n w => mu.real (descendantCell m zroot (show 0 < r from zpow_pos (by norm_num) _) n w : Set (SpatialCoordinates d))
      let stop := aux_lem_finite_stopping_partition_stopRule (fun n => Sel (base + n)) TreeGood
        (aux_lem_finite_stopping_partition_padLabel 3) mass (((3 : ℝ) ^ H1) ^ D)
      ∀ eps : ℝ, 0 < eps → ∃ᶠ J : ℕ in atTop,
        (∑ p ∈ aux_lem_finite_stopping_partition_leafFinset stop J, cost (fullIndex p.1 p.2)) ≤
          (C * a * ((3 : ℝ) ^ H1) ^ D) *
            (nu + ENNReal.ofReal c • volume.restrict (centeredCube z0 R hR : Set (SpatialCoordinates d))).real
              (centeredCube zroot r (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) + eps := by
  classical
  intro m r Cells Bank active embed hEmbed index hIndex hPad Good theta B hCount
    ref cost ratio nu _ C K s fsup c r0 hbase hRef hSource hLocal hCrude
    D eta a hc hD heta heta3 hDim htheta hs hC ha hK Sel hSel hRatio hLarge
  have hr : 0 < r := zpow_pos (by norm_num) _
  have hBounds := density_based_energy_bounds hd H1 base z0 R hR zroot jroot hroot hsub
    embed hEmbed index hIndex hPad Good theta B hCount ref cost ratio nu C K s fsup c r0
    hbase hRef hSource hLocal hCrude
  obtain ⟨fullIndex, hGeometry, hBad, hRefTree, hSourceTree, hLocalTree, hCrudeTree⟩ := hBounds
  refine ⟨fullIndex, hGeometry, ?_⟩
  intro TreeGood mu mass stop
  have hwidth : 2 * (m : ℝ) + 1 = (3 : ℝ) ^ H1 := by exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
  have hm : 0 < m := by
    have hp : 3 ≤ 3 ^ H1 := by simpa only [pow_one] using (pow_le_pow_right₀ (by decide : 1 ≤ (3 : ℕ)) hH1)
    have h := two_mul_subdivisionHalfWidth_add_one H1
    dsimp only [m]
    omega
  have hCd : 0 < 6 * (d : ℝ) := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hAll := density_padded_stopping_cost d m hm zroot r hr nu c D eta theta B (6 * d) s C a K fsup
    hc hD heta heta3 hDim htheta hCd hs hC ha hK Sel hSel base
    (fun n => ratio (H1 * n)) hRatio TreeGood (aux_lem_finite_stopping_partition_padLabel 3)
    (by
      intro J w
      convert hBad J w using 1
      congr 2
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, TreeGood, active])
    (fun n w => ref (fullIndex n w)) (fun n w => cost (fullIndex n w))
    hRefTree hSourceTree hLocalTree hCrudeTree (goodext_fixed_padding d hd m).1
    (by simpa only [hwidth] using hLarge)
  have hInter : (centeredCube zroot r hr : Set (SpatialCoordinates d)) ∩
      (centeredCube z0 R hR : Set (SpatialCoordinates d)) =
        (centeredCube zroot r hr : Set (SpatialCoordinates d)) := Set.inter_eq_left.mpr hsub
  have hMass : (nu + ENNReal.ofReal c • volume.restrict (centeredCube zroot r hr : Set (SpatialCoordinates d))).real
      (centeredCube zroot r hr : Set (SpatialCoordinates d)) =
      (nu + ENNReal.ofReal c • volume.restrict (centeredCube z0 R hR : Set (SpatialCoordinates d))).real
        (centeredCube zroot r hr : Set (SpatialCoordinates d)) := by
    change ((nu + ENNReal.ofReal c • volume.restrict (centeredCube zroot r hr : Set (SpatialCoordinates d)))
      (centeredCube zroot r hr : Set (SpatialCoordinates d))).toReal = _
    congr 1
    simp only [Measure.add_apply, Measure.smul_apply, Measure.restrict_apply (centeredCube zroot r hr).isOpen.measurableSet,
      Set.inter_self, hInter]
  intro eps heps
  have h := hAll eps heps
  simpa only [hwidth, hMass] using h
end Paper
