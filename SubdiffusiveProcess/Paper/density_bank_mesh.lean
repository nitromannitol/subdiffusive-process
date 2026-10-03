module

public import SubdiffusiveProcess.Paper.density_bank_partition
public import SubdiffusiveProcess.Paper.density_based_counts

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
open Classical

/-- Sufficiently fine absolute observation levels: the triadic scale condition and the mesh bound. -/
theorem aux_density_bank_mesh_base_choice (ell : ℤ) (H1 : ℕ) (hH1 : 0 < H1) (m : ℝ) (hm : 0 < m) :
    ∃ base0 : ℕ, ∀ base : ℕ, base0 ≤ base →
      0 ≤ ell + ((H1 * base : ℕ) : ℤ) ∧ (3 : ℝ) ^ (-((H1 * base : ℕ) : ℤ)) ≤ m := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hm (by norm_num : (1/3:ℝ) < 1)
  refine ⟨max n ell.natAbs, ?_⟩
  intro base hbase
  constructor
  · have hb1 : ell.natAbs ≤ base := le_trans (le_max_right _ _) hbase
    have hb2 : base ≤ H1 * base := Nat.le_mul_of_pos_left base hH1
    have hk : ell.natAbs ≤ H1 * base := le_trans hb1 hb2
    have hkz : ((ell.natAbs : ℤ)) ≤ ((H1*base : ℕ) : ℤ) := by exact_mod_cast hk
    have hneg : -(ell:ℤ) ≤ (ell.natAbs : ℤ) := by omega
    push_cast
    omega
  · have hb1 : n ≤ base := le_trans (le_max_left _ _) hbase
    have hb2 : base ≤ H1 * base := Nat.le_mul_of_pos_left base hH1
    have hk : n ≤ H1 * base := le_trans hb1 hb2
    have hpow : (1/3 : ℝ) ^ (H1*base) ≤ (1/3)^n := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    have heq : (3:ℝ) ^ (-((H1*base : ℕ) : ℤ)) = (1/3)^(H1*base) := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [heq]
    linarith

/-- At every mesh and tolerance the bank admits a finite partition of the killed cube by absolute-grid cells of side
at most the mesh, with total cost at most `C a L^D (nu + c dx)(Q) + eps` (the deterministic stopping construction
at a sufficiently fine base, from the branch counts, the source absorption and the local and crude cost bounds). -/
theorem density_bank_mesh {d : ℕ} (hd : 1 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (ell : ℤ) (hell : r = (3 : ℝ) ^ ell) (H1 : ℕ) (hH1 : 0 < H1) (theta : ℝ)
    (embed : aux_goodext_admissible_grid_cells z r hr → aux_density_full_grid_cells z r hr)
    (hEmbed : ∀ b, (embed b).val = b.val) :
    let zroot := fun b : ℕ × (Fin d → ℤ) => fun i => z i + (3 : ℝ) ^ (-((H1 * b.1 : ℕ) : ℤ)) * (b.2 i : ℝ)
    ∀ (index : ℕ × (Fin d → ℤ) → List (OddGridIndex d (subdivisionHalfWidth H1)) →
        aux_goodext_admissible_grid_cells z r hr)
      (hIndex : ∀ (b : ℕ × (Fin d → ℤ)) (w : List (OddGridIndex d (subdivisionHalfWidth H1))),
        aux_density_based_tree_active H1 b.1 z r hr (zroot b) w →
        (index b w).val.1 = H1 * (b.1 + w.length) ∧
        aux_goodext_admissible_grid_centre z (index b w).val =
          descendantCenter (subdivisionHalfWidth H1) (zroot b) ((3 : ℝ) ^ (-((H1 * b.1 : ℕ) : ℤ))) w.length w.get)
      (hPad : ∀ (b : ℕ × (Fin d → ℤ)) (n : ℕ) (w : Fin (n + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
        aux_lem_finite_stopping_partition_padLabel 3 (w (Fin.last n)) →
        (descendantCell (subdivisionHalfWidth H1) (zroot b)
          (zpow_pos (by norm_num : (0 : ℝ) < 3) (-((H1 * b.1 : ℕ) : ℤ))) n (fun i => w i.castSucc) :
            Set (SpatialCoordinates d)) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        aux_density_based_tree_active H1 b.1 z r hr (zroot b) (List.ofFn w))
      (Good : aux_goodext_admissible_grid_cells z r hr → Prop) (B : ℕ × (Fin d → ℤ) → ℝ)
      (hCount : ∀ (b : ℕ × (Fin d → ℤ)) (J : ℕ) (w : Fin J → OddGridIndex d (subdivisionHalfWidth H1)),
        (Set.ncard {i : Fin J | ¬ (aux_density_based_tree_active H1 b.1 z r hr (zroot b)
          ((List.ofFn w).take (i.val + 1)) → Good (index b ((List.ofFn w).take (i.val + 1))))} : ℝ) ≤
            theta * J + B b)
      (ref cost : aux_density_full_grid_cells z r hr → ℝ) (ratio : ℕ → ℝ)
      (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
      (C K s fsup c r0 : ℝ) (hr0 : 0 < r0)
      (hRef : ∀ q, 0 < ref q)
      (hSource : ∀ b, Good b → (3 : ℝ) ^ (-(b.val.1 : ℤ)) ≤ r0 →
        (ref (embed b))⁻¹ * ((3 : ℝ) ^ (-(b.val.1 : ℤ))) ^ ((d : ℝ) + 2) * fsup ^ 2 ≤
          c * ((3 : ℝ) ^ (-(b.val.1 : ℤ))) ^ d)
      (hLocal : ∀ b, Good b → ∀ zP (idx : OddGridIndex d (subdivisionHalfWidth H1)),
        let side := (3 : ℝ) ^ (-(b.val.1 : ℤ))
        aux_goodext_admissible_grid_centre z b.val = oddGridCenter zP ((3 : ℝ) ^ H1 * side) (subdivisionHalfWidth H1) idx →
        Metric.closedBall (aux_goodext_admissible_grid_centre z b.val) (3 * side / 2) ⊆
          Metric.ball zP ((3 : ℝ) ^ H1 * side / 2) →
        Metric.ball zP ((3 : ℝ) ^ H1 * side / 2) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        cost (embed b) ≤ C * ratio b.val.1 *
          (nu.real (Metric.ball zP ((3 : ℝ) ^ H1 * side / 2)) +
            (ref (embed b))⁻¹ * side ^ ((d : ℝ) + 2) * fsup ^ 2))
      (hCrude : ∀ q, cost q ≤ K * ((3 : ℝ) ^ (-(q.val.1 : ℤ))) ^ s)
      (D eta0 a : ℝ) (hc : 0 < c) (hD : 0 < D) (heta0 : 0 < eta0) (heta03 : eta0 ≤ 3)
      (hDim : (d : ℝ) / D ≤ eta0 / 8) (htheta : theta ≤ eta0 / 8)
      (hs : (d : ℝ) - eta0 / 8 < s) (hC : 0 ≤ C) (haPos : 0 < a) (hK : 0 ≤ K)
      (Sel : ℕ → Prop) (hSel : eta0 ≤ upperDensity Sel)
      (hRatio : ∀ n, Sel n → ratio (H1 * n) ≤ a)
      (hLarge : 2 * (6 * (d : ℝ)) ^ (eta0 / 3) ≤ ((3 : ℝ) ^ H1) ^ (eta0 / 3 - eta0 / 8))
      (mesh : ℝ) (hmesh : 0 < mesh) (eps : ℝ) (heps : 0 < eps),
    ∃ (total : ℕ) (q : Fin total → aux_density_full_grid_cells z r hr),
      (∀ i, (3 : ℝ) ^ (-((q i).val.1 : ℤ)) ≤ mesh) ∧
      Pairwise (fun i j => Disjoint
        (centeredCube (aux_goodext_admissible_grid_centre z (q i).val) ((3 : ℝ) ^ (-((q i).val.1 : ℤ)))
          (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))
        (centeredCube (aux_goodext_admissible_grid_centre z (q j).val) ((3 : ℝ) ^ (-((q j).val.1 : ℤ)))
          (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))) ∧
      (⋃ i, closure (centeredCube (aux_goodext_admissible_grid_centre z (q i).val) ((3 : ℝ) ^ (-((q i).val.1 : ℤ)))
          (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))) =
        closure (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      ((⋃ i, (centeredCube (aux_goodext_admissible_grid_centre z (q i).val) ((3 : ℝ) ^ (-((q i).val.1 : ℤ)))
          (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d))) =ᵐ[volume]
        (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
      ∑ i, cost (q i) ≤ ((C * a * ((3 : ℝ) ^ H1) ^ D) *
        (nu + ENNReal.ofReal c • volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).real
          (centeredCube z r hr : Set (SpatialCoordinates d))) + eps := by
  intro zroot index hIndex hPad Good B hCount ref cost ratio nu hnu C K s fsup c r0 hr0 hRef hSource hLocal
    hCrude D eta0 a hc hD heta0 heta03 hDim htheta hs hC haPos hK Sel hSel hRatio hLarge mesh hmesh eps heps
  obtain ⟨base0, hb0⟩ := aux_density_bank_mesh_base_choice ell H1 hH1 (min r0 mesh) (lt_min hr0 hmesh)
  obtain ⟨hb1, hb2⟩ := hb0 base0 le_rfl
  obtain ⟨total, q, h1, h2, h3, h4, h5⟩ := density_bank_partition hd H1 base0 hH1 z r hr
    ell hell hb1 embed hEmbed (fun j => index (base0, j)) (fun j w hw => hIndex (base0, j) w hw)
    (fun j n w hw hsub => hPad (base0, j) n w hw hsub) Good theta (fun j => B (base0, j))
    (fun j J w => hCount (base0, j) J w) ref cost ratio nu C K s fsup c r0
    (hb2.trans (min_le_left _ _)) hRef hSource hLocal hCrude D eta0 a hc hD heta0 heta03 hDim htheta hs
    hC haPos hK Sel hSel hRatio hLarge eps heps
  exact ⟨total, q, fun i' => (h1 i').trans (hb2.trans (min_le_right _ _)), h2, h3, h4, h5⟩

end Paper
