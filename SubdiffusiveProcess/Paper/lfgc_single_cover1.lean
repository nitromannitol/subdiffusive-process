module

public import SubdiffusiveProcess.Paper.lfgc_endpoint_meas
public import SubdiffusiveProcess.Paper.lfgc_layer_osc_cells
public import SubdiffusiveProcess.Lfgc.Cover

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc

/-!
# The single-point tests: deterministic cover inclusion

On a carrier where the infrared partial sums converge and the canonical sample has the
canonical formula, failure of the near-unit property for the infrared field `H` or for the
zero field forces: a chain event of any finite chain ending at the truncated statistic
`aux_lfgc_root_impl_rootX (S_L)`, or a large unit-cell observable of an infrared layer (`n ≥ 0` at tolerance
`ε₁ 2^{-(n+1)}`, or `n ≥ L` at tolerance `ε₂ 2^{-(n+1)}`).
-/

open MeasureTheory Filter Topology Homogenization.Book.Ch02 SubdiffusiveProcess
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- The unit-cell event attached to layer `n + 1`, root `i`, cell `y`, tolerance `ε`. -/
def aux_lfgc_single_cover1_cellEvent (T : ℕ) (offset : Fin T → ℤ) (n : ℤ) (ε : ℝ) (i : Fin T) (l : ℕ)
    (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d) : Set (BilateralField d) :=
  {omega | 2 * (ε / 2 ^ (l + 1)) / (3 : ℝ) ^ (-(n + offset i)) * ((3 : ℝ) ^ (l + 1) * d) <
    Paper.aux_psf_cellObs (l + 1) y (aux_lfgc_layer_tail_canonEta 0 omega)}

theorem aux_lfgc_single_cover1_layerOsc_subset_cellEvent (hd : 0 < d) (T : ℕ) (offset : Fin T → ℤ)
    (shift : Fin T → SpatialCoordinates d) (n : ℤ) (z : SpatialCoordinates d)
    (hr27 : ∀ i, (3 : ℝ) ^ (-(n + offset i)) ≤ 27) (ε : ℝ) (i : Fin T) (l : ℕ)
    (omega : BilateralField d)
    (hcanon : ∀ (j : ℕ) (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d),
      (aux_lfgc_layer_tail_canonEta 0 omega j : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ) y = omega (j : ℤ) y)
    (hosc : omega ∈ aux_lfgc_infrared_osc_layerOsc (Int.ofNat (l + 1)) (z + ((3 : ℝ) ^ (-n)) • shift i)
      ((3 : ℝ) ^ (-(n + offset i))) (by positivity) (ε / 2 ^ (l + 1))) :
    ∃ y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-n)) • shift i),
      omega ∈ aux_lfgc_single_cover1_cellEvent T offset n ε i l y := by
  by_contra hno
  push_neg at hno
  simp only [aux_lfgc_single_cover1_cellEvent, Set.mem_setOf_eq, not_lt] at hno
  obtain ⟨x, hx, hlt⟩ := hosc
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-(n + offset i)) := by positivity
  have hb := lfgc_layer_osc_cells hd (l + 1) (aux_lfgc_layer_tail_canonEta 0 omega) (z + ((3 : ℝ) ^ (-n)) • shift i) hr
    (hr27 i) hno x hx
  rw [hcanon, hcanon] at hb
  have hcast : ((Int.ofNat (l + 1)) : ℤ) = ((l + 1 : ℕ) : ℤ) := rfl
  rw [hcast] at hlt
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (l + 1) * d := by positivity
  have : (3 : ℝ) ^ (-(n + offset i)) / 2 *
      (2 * (ε / 2 ^ (l + 1)) / (3 : ℝ) ^ (-(n + offset i)) * ((3 : ℝ) ^ (l + 1) * d) /
        ((3 : ℝ) ^ (l + 1) * d)) = ε / 2 ^ (l + 1) := by
    field_simp
  rw [this] at hb
  linarith

end Paper
namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- From an oscillation of the infrared tail to a unit-cell event of some tail layer. -/
theorem aux_lfgc_single_cover1_tail_osc_to_cell (hd : 0 < d) (T : ℕ) (offset : Fin T → ℤ)
    (shift : Fin T → SpatialCoordinates d) (n : ℤ) (z : SpatialCoordinates d)
    (hr27 : ∀ i, (3 : ℝ) ^ (-(n + offset i)) ≤ 27)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (hconv : Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (hcanon : ∀ (j : ℕ) (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d),
      (aux_lfgc_layer_tail_canonEta 0 omega j : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ) y = omega (j : ℤ) y)
    (L₀ : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (i : Fin T)
    (hosc : ¬ aux_lfgc_root_near_OscLe (fun y => H omega y - infraredPartialSum omega L₀ y)
      (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i))) (by positivity) ε) :
    ∃ l, L₀ ≤ l ∧ ∃ y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-n)) • shift i),
      omega ∈ aux_lfgc_single_cover1_cellEvent T offset n ε i l y := by
  by_contra hno
  push_neg at hno
  apply hosc
  refine lfgc_infrared_osc H omega hconv L₀ _ (by positivity) hε fun l hl hmem => ?_
  obtain ⟨y, hy, hyev⟩ := aux_lfgc_single_cover1_layerOsc_subset_cellEvent hd T offset shift n z hr27 ε i l omega hcanon hmem
  exact hno l hl y hy hyev

theorem lfgc_single_cover1 (hd2 : 2 ≤ d) [NeZero d] (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (T : ℕ) (offset : Fin T → ℤ) (shift : Fin T → SpatialCoordinates d) (N : ℕ) (n : ℤ)
    (z : SpatialCoordinates d) {θ₀ ε₁ ε₂ : ℝ} (hθ₀ : 0 < θ₀) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (htol1 : aux_lfgc_near_tests_tolTransfer ε₁ (θ₀ / 4) ≤ θ₀) (htol2 : aux_lfgc_near_tests_tolTransfer ε₂ (θ₀ / 8) < θ₀ / 4)
    (hr27 : ∀ i, (3 : ℝ) ^ (-(n + offset i)) ≤ 27)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (L ℓs : ℕ)
    (Y : ℕ → BilateralField d → ℝ)
    (hYend : Y ℓs = aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀)
      (fun omega => infraredPartialSum omega L))
    (θ : ℕ → ℝ) (hθ : ∑ ℓ ∈ Finset.range (ℓs + 1), θ ℓ ≤ 3 / 16)
    (Carrier : Set (BilateralField d))
    (hconv : ∀ omega ∈ Carrier, Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (hcanon : ∀ omega ∈ Carrier, ∀ (j : ℕ) (y : SubdiffusiveProcess.CoarseGrainingVocab.Vec d),
      (aux_lfgc_layer_tail_canonEta 0 omega j : SubdiffusiveProcess.CoarseGrainingVocab.Vec d → ℝ) y = omega (j : ℤ) y) :
    Carrier ∩ ({omega | ¬ aux_lfgc_root_stat_nearAll I M H sigma T offset shift N n z θ₀ omega} ∪
        {omega | ¬ aux_lfgc_root_stat_nearAll I M 0 sigma T offset shift N n z θ₀ omega}) ⊆
      (⋃ ℓ ∈ Finset.range (ℓs + 1), chainEvent Y θ ℓ) ∪
      (⋃ (i : Fin T) (l : ℕ) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-n)) • shift i)),
        aux_lfgc_single_cover1_cellEvent T offset n ε₁ i l y) ∪
      (⋃ (i : Fin T) (l : ℕ) (_ : L ≤ l) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-n)) • shift i)),
        aux_lfgc_single_cover1_cellEvent T offset n ε₂ i l y) := by
  have hd : 0 < d := by omega
  rintro omega ⟨hC, hbad⟩
  -- the family-A escape
  have escA : ∀ i : Fin T, ¬ aux_lfgc_root_near_OscLe (fun y => (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
      omega y - H omega y) (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i)))
      (by positivity) ε₁ →
      omega ∈ (⋃ (i : Fin T) (l : ℕ) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-n)) • shift i)),
        aux_lfgc_single_cover1_cellEvent T offset n ε₁ i l y) := by
    intro i hosc
    have hosc' : ¬ aux_lfgc_root_near_OscLe (fun y => H omega y - infraredPartialSum omega 0 y)
        (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i))) (by positivity) ε₁ := by
      intro h
      apply hosc
      have h0 : infraredPartialSum omega 0 = 0 := by simp [infraredPartialSum]
      have := aux_lfgc_root_near_OscLe.symm (f := fun y => H omega y)
        (g := fun y => (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega y)
        (by simpa [h0] using h)
      simpa using this
    obtain ⟨l, -, y, hy, hev⟩ := aux_lfgc_single_cover1_tail_osc_to_cell hd T offset shift n z hr27 H omega (hconv omega hC)
      (hcanon omega hC) 0 hε₁ i hosc'
    simp only [Set.mem_iUnion]
    exact ⟨i, l, y, hy, hev⟩
  -- the endpoint escape
  have escB : ∀ i : Fin T, ¬ aux_lfgc_root_near_OscLe (fun y => H omega y - infraredPartialSum omega L y)
      (z + ((3 : ℝ) ^ (-n)) • shift i) ((3 : ℝ) ^ (-(n + offset i))) (by positivity) ε₂ →
      omega ∈ (⋃ (i : Fin T) (l : ℕ) (_ : L ≤ l) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-n)) • shift i)),
        aux_lfgc_single_cover1_cellEvent T offset n ε₂ i l y) := by
    intro i hosc
    obtain ⟨l, hl, y, hy, hev⟩ := aux_lfgc_single_cover1_tail_osc_to_cell hd T offset shift n z hr27 H omega (hconv omega hC)
      (hcanon omega hC) L hε₂ i hosc
    simp only [Set.mem_iUnion]
    exact ⟨i, l, hl, y, hy, hev⟩
  -- the statistic is large
  have hX : 1 / 2 ≤ aux_lfgc_root_impl_rootX I M sigma T offset shift N n z (2 / θ₀) H omega ∨
      omega ∈ (⋃ (i : Fin T) (l : ℕ) (y ∈ aux_lfgc_layer_osc_cells_cellCenters (z + ((3 : ℝ) ^ (-n)) • shift i)),
        aux_lfgc_single_cover1_cellEvent T offset n ε₁ i l y) := by
    rcases hbad with hb | hb
    · exact Or.inl (aux_lfgc_root_impl_not_nearAll_imp hsigma hθ₀ H omega hb)
    · rcases aux_lfgc_root_impl_not_nearAll_imp' hsigma hθ₀ hε₁ htol1 H 0 omega hb with h | h
      · exact Or.inl h
      · right
        simp only [aux_lfgc_root_impl_allOscLe, not_forall] at h
        obtain ⟨i, hi⟩ := h
        exact escA i hi
  rcases hX with hX | hX
  · rcases aux_lfgc_root_impl_half_le_imp hsigma hθ₀ hε₂ htol2 H (fun omega => infraredPartialSum omega L) omega hX
      with hZ | hZ
    · -- chain
      left; left
      have hlt : 3 / 16 < Y ℓs omega := by rw [hYend]; linarith
      exact chain_cover Y θ ℓs (3 / 16) hθ hlt
    · right
      simp only [aux_lfgc_root_impl_allOscLe, not_forall] at hZ
      obtain ⟨i, hi⟩ := hZ
      exact escB i hi
  · left; right; exact hX

end Paper
