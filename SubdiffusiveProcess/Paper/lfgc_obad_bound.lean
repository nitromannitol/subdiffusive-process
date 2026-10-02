import SubdiffusiveProcess.Paper.lfgc_chain_bound

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# Total probability of the tail cell events

`P(⋃_{i, l ≥ L, y} aux_lfgc_single_cover1_cellEvent) ≤ e^{-R (L+1+k)} / (8 (1 - e^{-R}))` at small disorder.
-/

open MeasureTheory Filter Topology SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem lfgc_obad_bound (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {T : ℕ}
    (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (k : ℕ)
    (z : SpatialCoordinates d) (hoff : ∀ i, -3 ≤ offset i) {ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 < R)
    (L : ℕ) (hC1 : R ≤ (2 * ε * d / 27 / Paper.aux_psf_sigma M) ^ 2)
    (hC2 : 16 * T * 57 ^ d * Real.exp (-(2 * ε * d / 27 / Paper.aux_psf_sigma M) ^ 2) ≤ 1) :
    (chaosSampleLaw M).toMeasure (⋃ (i : Fin T) (l : ℕ) (_ : L ≤ l)
        (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
        aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y) ≤
      ENNReal.ofReal (Real.exp (-R * ((L + 1 + k : ℕ) : ℝ)) / (8 * (1 - Real.exp (-R)))) := by
  classical
  set C := 2 * ε * d / 27 / Paper.aux_psf_sigma M
  set P := (chaosSampleLaw M).toMeasure
  -- per-layer bound
  have hlayer : ∀ l : ℕ, P (⋃ (i : Fin T) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
      aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y) ≤
      ENNReal.ofReal (Real.exp (-R * ((l + 1 + k : ℕ) : ℝ)) / 8) := by
    intro l
    have hc : ∀ (i : Fin T) (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d),
        P (aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y) ≤
          2 * ENNReal.ofReal (Real.exp (-C ^ 2) * Real.exp (-R * ((l + 1 + k : ℕ) : ℝ))) :=
      fun i y => aux_lfgc_family_cover_cellEvent_prob M offset k hoff hε hC1 i l y
    set x := Real.exp (-C ^ 2) * Real.exp (-R * ((l + 1 + k : ℕ) : ℝ))
    have hxle : 2 * ((T : ℝ) * 57 ^ d * x) ≤ Real.exp (-R * ((l + 1 + k : ℕ) : ℝ)) / 8 := by
      have he := Real.exp_pos (-R * ((l + 1 + k : ℕ) : ℝ))
      have : 2 * ((T : ℝ) * 57 ^ d * Real.exp (-C ^ 2)) ≤ 1 / 8 := by linarith
      simp only [x]; nlinarith [he, this]
    have hx : 0 ≤ x := by positivity
    clear_value x
    calc P (⋃ (i : Fin T) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
          aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y)
        ≤ ∑ i : Fin T, P (⋃ (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
          aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : Fin T, (57 ^ d : ℝ≥0∞) * (2 * ENNReal.ofReal x) := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (measure_biUnion_finset_le _ _).trans ?_
          refine (Finset.sum_le_sum fun y _ => hc i y).trans ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast aux_lfgc_family_cover_card_cellCenters_le_nat _
      _ = ENNReal.ofReal ((T : ℝ) * 57 ^ d * (2 * x)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by norm_num),
            ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (Real.exp (-R * ((l + 1 + k : ℕ) : ℝ)) / 8) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  -- sum over the layers
  have hunion : (⋃ (i : Fin T) (l : ℕ) (_ : L ≤ l)
      (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
      aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i l y) ⊆
      ⋃ j : ℕ, ⋃ (i : Fin T) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
        aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i (L + j) y := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨i, l, hl, y, hy, h⟩ := hω
    exact ⟨l - L, i, y, hy, by rwa [Nat.add_sub_cancel' hl]⟩
  refine (measure_mono hunion).trans ((measure_iUnion_le _).trans ?_)
  have hq : Real.exp (-R) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq0 : 0 ≤ Real.exp (-R) := (Real.exp_pos _).le
  calc ∑' j : ℕ, P (⋃ (i : Fin T) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-(k : ℤ))) • shift i)),
        aux_lfgc_single_cover1_cellEvent T offset (k : ℤ) ε i (L + j) y)
      ≤ ∑' j : ℕ, ENNReal.ofReal (Real.exp (-R * ((L + 1 + k : ℕ) : ℝ)) / 8) *
          ENNReal.ofReal (Real.exp (-R)) ^ j := by
        refine ENNReal.tsum_le_tsum fun j => (hlayer (L + j)).trans (le_of_eq ?_)
        rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (by positivity), ← Real.exp_nat_mul]
        congr 1
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        congr 2; push_cast; ring
    _ = ENNReal.ofReal (Real.exp (-R * ((L + 1 + k : ℕ) : ℝ)) / 8) *
          (1 - ENNReal.ofReal (Real.exp (-R)))⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (Real.exp (-R * ((L + 1 + k : ℕ) : ℝ)) / (8 * (1 - Real.exp (-R)))) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0,
          ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

end Paper
