module

public import SubdiffusiveProcess.Paper.lem_15
public import SubdiffusiveProcess.Geometry.Cube
public import Mathlib.Tactic

@[expose] public section

/-! The grid of boxes, cores and strips at level `k` (box side `ell ≤ s`, strip width `w ≤ ell`, anchor `0`)
for the fine-layer step of `prop-conc`, and the grid weight `Σ_k 1_{core_k} T_k` of a family of pieces `T_k`.
Only the deterministic geometry is treated here: the finite index set of boxes meeting the cell, the
disjoint cores, the covering of the cell off the strips, the enlarged compact set carrying all clamping
boxes, and the deletion/replacement identities of the grid weight. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

variable {d : ℕ}

/-- The geometric package of a grid on the cell `centeredCube z s`: the boxes `idx k` have pairwise disjoint
cores that cover the cell off the strips, and all clamping boxes lie in `closedBall z (3 s / 2)`. -/
def aux_prop_conc_fine_grid_Grid (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (ell w : ℝ) {m : ℕ}
    (idx : Fin m → (Fin d → ℤ)) : Prop :=
  0 < w ∧ w ≤ ell ∧ ell ≤ s ∧ Function.Injective idx ∧
    (∀ x ∈ (centeredCube z s hs : Set (SpatialCoordinates d)),
      x ∉ aux_lem_15_u_stripSet 0 ell w → ∃ k, x ∈ aux_lem_15_u_core 0 ell w (idx k)) ∧
    (∀ k, aux_lem_15_u_kbox 0 ell w (idx k) ⊆ Metric.closedBall z (3 * s / 2))

/-- Boxes of the index set lie in the closed cube `closedBall z (s/2 + ell)`. -/
theorem aux_prop_conc_fine_grid_kbox_subset (a z : SpatialCoordinates d) {s ell w : ℝ}
    (hs0 : 0 ≤ s) (hell : 0 < ell) (hw : 0 ≤ w) {idx : Fin d → ℤ}
    (hidx : idx ∈ aux_lem_15_u_index a z s ell) :
    aux_lem_15_u_kbox a ell w idx ⊆ Metric.closedBall z (s / 2 + ell) := by
  intro x hx
  rw [aux_lem_15_u_index, Fintype.mem_piFinset] at hidx
  rw [mem_closedBall_iff_norm]
  have hbd : ∀ c, |x c - z c| ≤ s / 2 + ell := by
    intro c
    obtain ⟨h1, h2⟩ := hx c
    have hc := Finset.mem_Icc.mp (hidx c)
    have hlo1 : ((z c - s / 2 - a c) / ell) - 1 < (idx c : ℝ) := by
      have := Int.lt_floor_add_one ((z c - s / 2 - a c) / ell)
      have h' : (⌊(z c - s / 2 - a c) / ell⌋ : ℝ) ≤ (idx c : ℝ) := by exact_mod_cast hc.1
      linarith
    have hhi1 : (idx c : ℝ) ≤ (z c + s / 2 - a c) / ell := by
      have := Int.floor_le ((z c + s / 2 - a c) / ell)
      have h' : (idx c : ℝ) ≤ (⌊(z c + s / 2 - a c) / ell⌋ : ℝ) := by exact_mod_cast hc.2
      linarith
    have hlo2 : z c - s / 2 - a c - ell < (idx c : ℝ) * ell := by
      have := mul_lt_mul_of_pos_right hlo1 hell
      rw [sub_mul, div_mul_cancel₀ _ hell.ne', one_mul] at this
      exact this
    have hhi2 : (idx c : ℝ) * ell ≤ z c + s / 2 - a c := by
      have := mul_le_mul_of_nonneg_right hhi1 hell.le
      rwa [div_mul_cancel₀ _ hell.ne'] at this
    rw [abs_le]
    constructor <;> nlinarith
  have hnn : 0 ≤ s / 2 + ell := by linarith
  exact (pi_norm_le_iff_of_nonneg hnn).2 fun c => by
    rw [Real.norm_eq_abs]; exact hbd c

/-- **Grid existence.**  For a box side `ell ≤ s` and a strip width `0 < w ≤ ell` there is a finite family of
boxes covering the cell, with the geometric package `aux_prop_conc_fine_grid_Grid`. -/
theorem prop_conc_fine_grid (z : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (ell w : ℝ) (hw : 0 < w)
    (hwl : w ≤ ell) (hls : ell ≤ s) :
    ∃ (m : ℕ) (idx : Fin m → (Fin d → ℤ)), aux_prop_conc_fine_grid_Grid z s hs ell w idx := by
  set I := aux_lem_15_u_index 0 z s ell with hI
  have hell : 0 < ell := hw.trans_le hwl
  refine ⟨I.card, fun k => (I.equivFin.symm k).1, hw, hwl, hls, ?_, ?_, ?_⟩
  · intro k k' h
    exact I.equivFin.symm.injective (Subtype.ext h)
  · intro x hx hxs
    have hmem := aux_lem_15_u_floorIdx_mem_index 0 z (s := s) hell hx
    refine ⟨I.equivFin ⟨_, hmem⟩, ?_⟩
    have : (fun k => (I.equivFin.symm k).1) (I.equivFin ⟨_, hmem⟩) = aux_lem_15_u_floorIdx 0 ell x := by
      simp
    rw [this]
    exact aux_lem_15_u_mem_core_of_not_strip 0 hell hxs
  · intro k
    exact (aux_prop_conc_fine_grid_kbox_subset 0 z hs.le hell hw.le (I.equivFin.symm k).2).trans
      (Metric.closedBall_subset_closedBall (by linarith))

/-- The grid weight `Σ_k 1_{core_k} T_k` of a family of pieces. -/
def aux_prop_conc_fine_grid_wt (ell w : ℝ) {m : ℕ} (idx : Fin m → (Fin d → ℤ))
    (T : Fin m → C(SpatialCoordinates d, ℝ)) : SpatialCoordinates d → ℝ :=
  fun x => ∑ k, (aux_lem_15_u_core 0 ell w (idx k)).indicator (fun y => T k y) x

theorem aux_prop_conc_fine_grid_wt_measurable (ell w : ℝ) {m : ℕ} (idx : Fin m → (Fin d → ℤ))
    (T : Fin m → C(SpatialCoordinates d, ℝ)) :
    Measurable (aux_prop_conc_fine_grid_wt ell w idx T) := by
  unfold aux_prop_conc_fine_grid_wt
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (T k).continuous.measurable.indicator (aux_lem_15_u_core_isOpen 0 ell w (idx k)).measurableSet

/-- Replacing one piece changes the grid weight only on its core. -/
theorem aux_prop_conc_fine_grid_wt_update (ell w : ℝ) {m : ℕ} (idx : Fin m → (Fin d → ℤ))
    (T : Fin m → C(SpatialCoordinates d, ℝ)) (i : Fin m) (v : C(SpatialCoordinates d, ℝ)) :
    aux_prop_conc_fine_grid_wt ell w idx (Function.update T i v) =
      aux_prop_conc_fine_grid_wt ell w idx T +
        (aux_lem_15_u_core 0 ell w (idx i)).indicator (fun y => v y - T i y) := by
  classical
  funext x
  unfold aux_prop_conc_fine_grid_wt
  have hterm : ∀ k : Fin m,
      (aux_lem_15_u_core 0 ell w (idx k)).indicator (fun y => (Function.update T i v k) y) x =
        (aux_lem_15_u_core 0 ell w (idx k)).indicator (fun y => T k y) x +
          (if k = i then (aux_lem_15_u_core 0 ell w (idx i)).indicator (fun y => v y - T i y) x else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self, ↓reduceIte]
      by_cases hx : x ∈ aux_lem_15_u_core 0 ell w (idx k)
      · simp only [Set.indicator_of_mem hx]; ring
      · simp only [Set.indicator_of_notMem hx]; ring
    · simp [hk]
  simp only [Pi.add_apply]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

/-- At the pieces of a field `y`, the grid weight is `y` off the strips (on the cell). -/
theorem aux_prop_conc_fine_grid_wt_pieces {z : SpatialCoordinates d} {s : ℝ} {hs : 0 < s} {ell w : ℝ}
    {m : ℕ} {idx : Fin m → (Fin d → ℤ)} (hg : aux_prop_conc_fine_grid_Grid z s hs ell w idx)
    (y : C(SpatialCoordinates d, ℝ)) {x : SpatialCoordinates d}
    (hx : x ∈ (centeredCube z s hs : Set (SpatialCoordinates d))) :
    aux_prop_conc_fine_grid_wt ell w idx (fun k => aux_lem_15_u_localize 0 ell w (idx k) y) x =
      (aux_lem_15_u_stripSet 0 ell w)ᶜ.indicator (fun y' => y y') x := by
  obtain ⟨hw, hwl, hls, hinj, hcover, hkbox⟩ := hg
  have hell : 0 < ell := hw.trans_le hwl
  unfold aux_prop_conc_fine_grid_wt
  by_cases hxs : x ∈ aux_lem_15_u_stripSet 0 ell w
  · rw [Set.indicator_of_notMem (by simpa using hxs)]
    refine Finset.sum_eq_zero fun k _ => ?_
    exact Set.indicator_of_notMem (fun hxc => aux_lem_15_u_core_not_strip 0 hell.le (idx k) hxc hxs) _
  · rw [Set.indicator_of_mem (show x ∈ (aux_lem_15_u_stripSet 0 ell w)ᶜ from hxs)]
    obtain ⟨k, hk⟩ := hcover x hx hxs
    rw [Finset.sum_eq_single k]
    · rw [Set.indicator_of_mem hk]
      show y (aux_lem_15_u_clamp 0 ell w (idx k) x) = y x
      rw [aux_lem_15_u_clamp_of_mem 0 ell w (idx k) (aux_lem_15_u_core_subset_kbox 0 hw.le (idx k) hk)]
    · intro k' _ hne
      refine Set.indicator_of_notMem (fun hxc => ?_) _
      exact Set.disjoint_left.mp
        (aux_lem_15_u_core_disjoint 0 hell.le hw (fun h => hne (hinj h))) hxc hk
    · intro h; exact absurd (Finset.mem_univ k) h

/-- The grid weight of pieces is bounded by the sums of the `Qt`-sup norms. -/
theorem aux_prop_conc_fine_grid_wt_abs_le {z : SpatialCoordinates d} {s : ℝ} {hs : 0 < s} {ell w : ℝ}
    {m : ℕ} {idx : Fin m → (Fin d → ℤ)} (hg : aux_prop_conc_fine_grid_Grid z s hs ell w idx)
    (T T' : Fin m → C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) :
    |aux_prop_conc_fine_grid_wt ell w idx T x - aux_prop_conc_fine_grid_wt ell w idx T' x| ≤
      ∑ k, aux_lem_15_u_supn (Metric.closedBall z (3 * s / 2)) (isCompact_closedBall _ _)
        (T k - T' k) := by
  obtain ⟨hw, hwl, hls, hinj, hcover, hkbox⟩ := hg
  unfold aux_prop_conc_fine_grid_wt
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  by_cases hx : x ∈ aux_lem_15_u_core 0 ell w (idx k)
  · simp only [Set.indicator_of_mem hx]
    haveI : CompactSpace (Metric.closedBall z (3 * s / 2)) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    have hxQ : x ∈ Metric.closedBall z (3 * s / 2) :=
      hkbox k (aux_lem_15_u_core_subset_kbox 0 hw.le (idx k) hx)
    have := ContinuousMap.norm_coe_le_norm ((T k - T' k).restrict (Metric.closedBall z (3 * s / 2)))
      ⟨x, hxQ⟩
    simpa [aux_lem_15_u_supn, Real.norm_eq_abs] using this
  · simp only [Set.indicator_of_notMem hx, sub_self, abs_zero]
    exact aux_lem_15_u_supn_nonneg _ _ _

end
end Paper
