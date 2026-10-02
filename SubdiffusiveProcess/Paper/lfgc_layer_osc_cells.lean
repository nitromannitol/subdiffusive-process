import SubdiffusiveProcess.Paper.lfgc_layer_tail

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# A layer oscillation on a cube of side at most 27 forces a large unit-cell observable

The `57^d` unit cells centred at `w + (v - 28)/2`, `v : Fin d → Fin 57`, cover the closed
cube of centre `w` and side `r ≤ 27`.  If every cell observable of a potential sample is
at most `t` at level `i`, the layer `i` oscillates by at most `(r/2) t / (3^i d)` on the cube
(mean value inequality).
-/

open MeasureTheory Filter Topology SubdiffusiveProcess SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

namespace Paper
variable {d : ℕ}

/-- The centres of the covering unit cells. -/
noncomputable def aux_lfgc_layer_osc_cells_cellCenters (w : Vec d) : Finset (Vec d) :=
  Finset.univ.image (fun v : Fin d → Fin 57 => w + fun j => ((v j : ℕ) - 28 : ℝ) / 2)

theorem aux_lfgc_layer_osc_cells_card_cellCenters_le (w : Vec d) : ((aux_lfgc_layer_osc_cells_cellCenters w).card : ℝ) ≤ 57 ^ d := by
  have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin d → Fin 57)))
    (f := fun v : Fin d → Fin 57 => w + fun j => ((v j : ℕ) - 28 : ℝ) / 2)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  have h' : (aux_lfgc_layer_osc_cells_cellCenters w).card ≤ 57 ^ d := h
  exact_mod_cast h'

theorem aux_lfgc_layer_osc_cells_mem_cube_zero_iff' (x : Vec d) : x ∈ cube d 0 ↔ ∀ j, |x j| < 1 / 2 := by
  have h := Lane4.centeredCube_zero_eq_openCubeSet_originCube (d := d) 0 (by norm_num)
  simp only [zpow_zero] at h
  unfold cube
  rw [← h, centeredCube_eq_pi]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo, Pi.zero_apply, zero_sub,
    zero_add, abs_lt]

theorem aux_lfgc_layer_osc_cells_exists_cell (w : Vec d) {r : ℝ} (hr : 0 < r) (hr27 : r ≤ 27) (x : Vec d)
    (hx : x ∈ (closedCube w r hr : Set (Vec d))) :
    ∃ y ∈ aux_lfgc_layer_osc_cells_cellCenters w, x - y ∈ cube d 0 := by
  have hxj : ∀ j, |x j - w j| ≤ 27 / 2 := by
    intro j
    have : dist x w ≤ r / 2 := hx
    have h2 := dist_le_pi_dist x w j
    rw [Real.dist_eq] at h2
    linarith
  choose v hv using fun j => (show ∃ v : Fin 57, |x j - w j - ((v : ℕ) - 28 : ℝ) / 2| < 1 / 2 by
    set u := x j - w j
    have hu := abs_le.mp (hxj j)
    set k : ℤ := round (2 * u) with hk
    have hk1 := abs_sub_round (2 * u)
    have hklo : -27 ≤ k := by
      have : (-27 : ℝ) - 1/2 ≤ (k : ℝ) := by
        have := abs_le.mp hk1; rw [← hk] at this; linarith [this.1, this.2]
      have : (-28 : ℝ) < (k : ℝ) := by linarith
      have : (-28 : ℤ) < k := by exact_mod_cast this
      omega
    have hkhi : k ≤ 27 := by
      have : (k : ℝ) ≤ 27 + 1/2 := by
        have := abs_le.mp hk1; rw [← hk] at this; linarith [this.1, this.2]
      have : (k : ℝ) < 28 := by linarith
      have : k < (28 : ℤ) := by exact_mod_cast this
      omega
    refine ⟨⟨(k + 28).toNat, by omega⟩, ?_⟩
    have hcast : (((k + 28).toNat : ℕ) : ℝ) = (k : ℝ) + 28 := by
      have : ((k + 28).toNat : ℤ) = k + 28 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    simp only [hcast, add_sub_cancel_right]
    rw [show u - (k : ℝ) / 2 = (2 * u - k) / 2 by ring, abs_div, abs_two]
    have : |2 * u - k| ≤ 1 / 2 := by rw [hk]; exact hk1
    have hlt : |2 * u - k| < 1 := by linarith
    linarith)
  refine ⟨w + fun j => ((v j : ℕ) - 28 : ℝ) / 2, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩, ?_⟩
  rw [aux_lfgc_layer_osc_cells_mem_cube_zero_iff']
  intro j
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [show x j - (w j + ((v j : ℕ) - 28 : ℝ) / 2) = x j - w j - ((v j : ℕ) - 28 : ℝ) / 2 by ring]
  exact hv j

/-- Cell observables bound the derivative on the cell. -/
theorem aux_lfgc_layer_osc_cells_norm_deriv_le_cellObs (i : ℕ) (y x : Vec d) (omega : PotentialSample d)
    (hx : x - y ∈ cube d 0) (hd : 0 < d) :
    ‖PotentialField.deriv (omega i) x‖ ≤ Paper.aux_psf_cellObs i y omega / ((3 : ℝ) ^ i * d) := by
  have h := PotentialField.norm_deriv_le_unitCubeDerivNorm (PotentialField.translate y (omega i)) hx
  rw [Paper.aux_psf_deriv_translate, sub_add_cancel] at h
  have hv := PotentialField.unitCubeValueNorm_nonneg (PotentialField.translate y (omega i))
  have hpos : (0 : ℝ) < (3 : ℝ) ^ i * d := by positivity
  rw [le_div_iff₀ hpos]
  unfold Paper.aux_psf_cellObs
  nlinarith

/-- Mean value inequality on the cube from bounded cell observables. -/
theorem lfgc_layer_osc_cells (hd : 0 < d) (i : ℕ) (omega : PotentialSample d) (w : Vec d) {r : ℝ}
    (hr : 0 < r) (hr27 : r ≤ 27) {t : ℝ}
    (ht : ∀ y ∈ aux_lfgc_layer_osc_cells_cellCenters w, Paper.aux_psf_cellObs i y omega ≤ t) :
    ∀ x ∈ (closedCube w r hr : Set (Vec d)),
      |(omega i : Vec d → ℝ) x - (omega i : Vec d → ℝ) w| ≤ r / 2 * (t / ((3 : ℝ) ^ i * d)) := by
  intro x hx
  set K := (closedCube w r hr : Set (Vec d))
  have hconv : Convex ℝ K := convex_closedBall w (r / 2)
  have hw : w ∈ K := Metric.mem_closedBall_self (by positivity)
  have hbound : ∀ z ∈ K, ‖PotentialField.deriv (omega i) z‖ ≤ t / ((3 : ℝ) ^ i * d) := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := aux_lfgc_layer_osc_cells_exists_cell w hr hr27 z hz
    refine (aux_lfgc_layer_osc_cells_norm_deriv_le_cellObs i y z omega hzy hd).trans ?_
    exact div_le_div_of_nonneg_right (ht y hy) (by positivity)
  have hmvt := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => ((omega i).hasFDerivAt z).hasFDerivWithinAt) hbound hw hx
  rw [Real.norm_eq_abs] at hmvt
  refine hmvt.trans ?_
  have hxw : ‖x - w‖ ≤ r / 2 := by rw [← dist_eq_norm]; exact hx
  have ht0 : 0 ≤ t / ((3 : ℝ) ^ i * d) := (norm_nonneg _).trans (hbound w hw)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hxw ht0

end Paper
