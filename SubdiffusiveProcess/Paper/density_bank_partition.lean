module

public import SubdiffusiveProcess.Paper.density_based_stopping_cost
public import SubdiffusiveProcess.Paper.density_base_partition
public import SubdiffusiveProcess.Paper.density_forest_cost
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
open Classical
/-- A fine absolute mesh and actual bank estimates produce a finite partition
of the killed cube, with controlled mesh and total harmonic cost. -/
theorem density_bank_partition {d : ℕ} (hd : 1 ≤ d) (H1 base : ℕ) (hH1 : 0 < H1)
    (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (ell : ℤ) (hscale : R = (3 : ℝ) ^ ell) (hmesh : 0 ≤ ell + ((H1 * base : ℕ) : ℤ)) :
    let m := subdivisionHalfWidth H1
    let r := (3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ))
    let Cells := aux_goodext_admissible_grid_cells z0 R hR
    let Bank := aux_density_full_grid_cells z0 R hR
    let zroot := fun j : Fin d → ℤ => fun i => z0 i + r * (j i : ℝ)
    let active := fun j => aux_density_based_tree_active H1 base z0 R hR (zroot j)
    ∀ (embed : Cells → Bank) (hEmbed : ∀ b, (embed b).val = b.val)
      (index : (Fin d → ℤ) → List (OddGridIndex d m) → Cells)
      (hIndex : ∀ j w, active j w → (index j w).val.1 = H1 * (base + w.length) ∧
        aux_goodext_admissible_grid_centre z0 (index j w).val = descendantCenter m (zroot j) r w.length w.get)
      (hPad : ∀ j n (w : Fin (n + 1) → OddGridIndex d m),
        aux_lem_finite_stopping_partition_padLabel 3 (w (Fin.last n)) →
        (descendantCell m (zroot j) (show 0 < r from zpow_pos (by norm_num) _) n
          (fun i => w i.castSucc) : Set (SpatialCoordinates d)) ⊆ (centeredCube z0 R hR : Set (SpatialCoordinates d)) →
        active j (List.ofFn w))
      (Good : Cells → Prop) (theta : ℝ) (B : (Fin d → ℤ) → ℝ)
      (hCount : ∀ j J (w : Fin J → OddGridIndex d m),
        (Set.ncard {i : Fin J | ¬ (active j ((List.ofFn w).take (i.val + 1)) →
          Good (index j ((List.ofFn w).take (i.val + 1))))} : ℝ) ≤ theta * J + B j)
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
    ∀ eps : ℝ, 0 < eps → ∃ (total : ℕ) (q : Fin total → Bank),
      let cell := fun i => centeredCube (aux_goodext_admissible_grid_centre z0 (q i).val)
        ((3 : ℝ) ^ (-((q i).val.1 : ℤ))) (zpow_pos (by norm_num) _)
      (∀ i, (3 : ℝ) ^ (-((q i).val.1 : ℤ)) ≤ r) ∧
      Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d)) (cell j : Set (SpatialCoordinates d))) ∧
      (⋃ i, closure (cell i : Set (SpatialCoordinates d))) = closure (centeredCube z0 R hR : Set (SpatialCoordinates d)) ∧
      ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume] (centeredCube z0 R hR : Set (SpatialCoordinates d))) ∧
      (∑ i, cost (q i)) ≤ (C * a * ((3 : ℝ) ^ H1) ^ D) *
        (nu + ENNReal.ofReal c • volume.restrict (centeredCube z0 R hR : Set (SpatialCoordinates d))).real
          (centeredCube z0 R hR : Set (SpatialCoordinates d)) + eps := by
  classical
  intro m r Cells Bank zroot active embed hEmbed index hIndex hPad Good theta B hCount
    ref cost ratio nu _ C K s fsup c r0 hbase hRef hSource hLocal hCrude
    D eta a hc hD heta heta3 hDim htheta hs hC ha hK Sel hSel hRatio hLarge eps heps
  have hr : 0 < r := zpow_pos (by norm_num) _
  obtain ⟨depth, _hdepth, hCentre, _hCell, hSub, hDisj, hCover, hAE⟩ :=
    density_base_partition z0 R hR ell hscale (H1 * base) hmesh
  let T := OddGridIndex d (triadicHalf depth)
  let nb := Fintype.card T
  let e : Fin nb ≃ T := (Fintype.equivFin T).symm
  let jroot := fun b : Fin nb => fun i => ((e b i).val : ℤ) - (triadicHalf depth : ℤ)
  let zc := fun b : Fin nb => zroot (jroot b)
  have hzc : ∀ b : Fin nb, zc b = triadicGridCenter z0 R ⟨depth, e b⟩ := by
    intro b
    simpa only [zc, zroot, jroot, Int.cast_sub] using (hCentre (e b)).symm
  have hBaseSub : ∀ b, (centeredCube (zc b) r hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube z0 R hR : Set (SpatialCoordinates d)) := by
    intro b
    rw [hzc]
    exact hSub (e b)
  have hBaseDisj : Pairwise (fun i j : Fin nb => Disjoint
      (centeredCube (zc i) r hr : Set (SpatialCoordinates d))
      (centeredCube (zc j) r hr : Set (SpatialCoordinates d))) := by
    intro i j hij
    rw [hzc, hzc]
    exact hDisj (fun heq => hij (e.injective heq))
  have hBaseCover : (⋃ b : Fin nb, closure (centeredCube (zc b) r hr : Set (SpatialCoordinates d))) =
      closure (centeredCube z0 R hR : Set (SpatialCoordinates d)) := by
    simp_rw [hzc]
    rw [e.surjective.iUnion_comp (fun q : T => closure
      (centeredCube (triadicGridCenter z0 R ⟨depth, q⟩) r hr : Set (SpatialCoordinates d)))]
    exact hCover
  have hBaseAE : (⋃ b : Fin nb, (centeredCube (zc b) r hr : Set (SpatialCoordinates d)))
      =ᵐ[volume] (centeredCube z0 R hR : Set (SpatialCoordinates d)) := by
    simp_rw [hzc]
    rw [e.surjective.iUnion_comp (fun q : T =>
      (centeredCube (triadicGridCenter z0 R ⟨depth, q⟩) r hr : Set (SpatialCoordinates d)))]
    exact hAE
  have hStopped := fun b : Fin nb => density_based_stopping_cost hd H1 base hH1
    z0 R hR (zc b) (jroot b) rfl (hBaseSub b)
    embed hEmbed (index (jroot b)) (hIndex (jroot b)) (hPad (jroot b)) Good theta (B (jroot b))
    (hCount (jroot b)) ref cost ratio nu C K s fsup c r0 hbase hRef hSource hLocal hCrude
    D eta a hc hD heta heta3 hDim htheta hs hC ha hK Sel hSel hRatio hLarge
  choose fullIndex hGeometry hCheap using hStopped
  let mu := nu + ENNReal.ofReal c • volume.restrict (centeredCube z0 R hR : Set (SpatialCoordinates d))
  letI : IsFiniteMeasure (volume.restrict (centeredCube z0 R hR : Set (SpatialCoordinates d))) :=
    isFiniteMeasure_restrict.mpr (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top)
  letI : IsFiniteMeasure (ENNReal.ofReal c • volume.restrict (centeredCube z0 R hR : Set (SpatialCoordinates d))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure mu := by dsimp only [mu]; infer_instance
  let stop := fun b : Fin nb => aux_lem_finite_stopping_partition_stopRule (fun n => Sel (base + n))
    (fun n (w : Fin n → OddGridIndex d m) => active (jroot b) (List.ofFn w) → Good (index (jroot b) (List.ofFn w)))
    (aux_lem_finite_stopping_partition_padLabel 3)
    (fun n w => (nu + ENNReal.ofReal c • volume.restrict (centeredCube (zc b) r hr : Set (SpatialCoordinates d))).real
      (descendantCell m (zc b) hr n w : Set (SpatialCoordinates d))) (((3 : ℝ) ^ H1) ^ D)
  have hCglobal : 0 ≤ C * a * ((3 : ℝ) ^ H1) ^ D := by positivity
  obtain ⟨nmax, total, root, dep, word, _hLeaf, _hBase, _hSub, hDisjF, hCoverF, hAEF, _hSum, hCost⟩ :=
    density_forest_cost z0 R hR nb m zc (fun _ => r) (fun _ => hr) hBaseSub hBaseDisj
      hBaseCover hBaseAE stop mu (C * a * ((3 : ℝ) ^ H1) ^ D) hCglobal
      (fun b n w => cost (fullIndex b n w)) hCheap eps heps
  let q := fun i : Fin total => fullIndex (root i) (dep i) (word i)
  refine ⟨total, q, ?_⟩
  intro cell
  have hCells : ∀ i, cell i = descendantCell m (zc (root i)) hr (dep i) (word i) :=
    fun i => (hGeometry (root i) (dep i) (word i)).2.2.2
  refine ⟨?_, ?_, ?_, ?_, hCost⟩
  · intro i
    rw [(hGeometry (root i) (dep i) (word i)).2.2.1]
    have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    exact div_le_self hr.le (one_le_pow₀ (by linarith only [hmR] : (1 : ℝ) ≤ 2 * m + 1))
  · intro i j hij
    rw [hCells, hCells]
    exact hDisjF hij
  · simp_rw [hCells]
    exact hCoverF
  · simp_rw [hCells]
    exact hAEF
end Paper
