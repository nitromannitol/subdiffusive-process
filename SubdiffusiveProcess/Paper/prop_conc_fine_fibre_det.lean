module

public import SubdiffusiveProcess.Paper.prop_conc_fine_psi
public import SubdiffusiveProcess.Paper.prop_conc_fine_geometry

@[expose] public section

/-! Deterministic estimates along one fibre of the fine-layer step: for one pair `X`, a reference layer `x0` and
one layer sample `y` whose masked pair has the growth constant `Ky`, the deletion error
`|θ_X(y - x0) - Ψ(T y)|` and the data of the conditional Efron--Stein variance (masses of the doubly masked
pair on the cores, and the piece-replacement variations) are bounded through `prop_conc_fine_pair_step`,
the masked mass bounds and the level-`k` strip and core masses. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

section defs
variable {d : ℕ}

/-- The weight `1_q (y - x0)` of the layer sample `y` relative to the reference `x0`. -/
def aux_prop_conc_fine_fibre_det_wY (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (x0 y : C(SpatialCoordinates d, ℝ)) : SpatialCoordinates d → ℝ :=
  (centeredCube z r hr : Set (SpatialCoordinates d)).indicator (fun x => y x - x0 x)

/-- The deletion weight `-1_{q ∩ strips} y`. -/
def aux_prop_conc_fine_fibre_det_uY (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (ell w : ℝ)
    (y : C(SpatialCoordinates d, ℝ)) : SpatialCoordinates d → ℝ :=
  ((centeredCube z r hr : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_stripSet 0 ell w).indicator
    (fun x => - y x)

/-- The enlarged compact set. -/
def aux_prop_conc_fine_fibre_det_Qt (z : SpatialCoordinates d) (r : ℝ) : Set (SpatialCoordinates d) :=
  Metric.closedBall z (3 * r / 2)

/-- The sup norm of a field on the enlarged cell. -/
def aux_prop_conc_fine_fibre_det_S (z : SpatialCoordinates d) (r : ℝ)
    (y : C(SpatialCoordinates d, ℝ)) : ℝ :=
  aux_lem_15_u_supn (aux_prop_conc_fine_fibre_det_Qt z r) (isCompact_closedBall _ _) y

theorem aux_prop_conc_fine_fibre_det_S_nonneg (z : SpatialCoordinates d) (r : ℝ)
    (y : C(SpatialCoordinates d, ℝ)) : 0 ≤ aux_prop_conc_fine_fibre_det_S z r y :=
  aux_lem_15_u_supn_nonneg _ _ _

theorem aux_prop_conc_fine_fibre_det_cell_subset (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ aux_prop_conc_fine_fibre_det_Qt z r := by
  intro x hx
  have : dist x z < r / 2 := hx
  rw [aux_prop_conc_fine_fibre_det_Qt, Metric.mem_closedBall]
  linarith

theorem aux_prop_conc_fine_fibre_det_abs_le_S (z : SpatialCoordinates d) (r : ℝ)
    (y : C(SpatialCoordinates d, ℝ)) {x : SpatialCoordinates d}
    (hx : x ∈ aux_prop_conc_fine_fibre_det_Qt z r) :
    |y x| ≤ aux_prop_conc_fine_fibre_det_S z r y := by
  haveI : CompactSpace (aux_prop_conc_fine_fibre_det_Qt z r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have := ContinuousMap.norm_coe_le_norm (y.restrict (aux_prop_conc_fine_fibre_det_Qt z r)) ⟨x, hx⟩
  simpa [aux_prop_conc_fine_fibre_det_S, aux_lem_15_u_supn, Real.norm_eq_abs] using this

theorem aux_prop_conc_fine_fibre_det_wY_measurable (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (x0 y : C(SpatialCoordinates d, ℝ)) :
    Measurable (aux_prop_conc_fine_fibre_det_wY z r hr x0 y) :=
  (y.continuous.measurable.sub x0.continuous.measurable).indicator
    (centeredCube z r hr).isOpen.measurableSet

theorem aux_prop_conc_fine_fibre_det_wY_bound (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (x0 y : C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) :
    |aux_prop_conc_fine_fibre_det_wY z r hr x0 y x| ≤
      aux_prop_conc_fine_fibre_det_S z r y + aux_prop_conc_fine_fibre_det_S z r x0 := by
  have h1 := aux_prop_conc_fine_fibre_det_S_nonneg z r y
  have h2 := aux_prop_conc_fine_fibre_det_S_nonneg z r x0
  by_cases hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
  · simp only [aux_prop_conc_fine_fibre_det_wY, Set.indicator_of_mem hx]
    have hxQ := aux_prop_conc_fine_fibre_det_cell_subset z hr hx
    exact (abs_sub _ _).trans (add_le_add (aux_prop_conc_fine_fibre_det_abs_le_S z r y hxQ)
      (aux_prop_conc_fine_fibre_det_abs_le_S z r x0 hxQ))
  · simp only [aux_prop_conc_fine_fibre_det_wY, Set.indicator_of_notMem hx, abs_zero]
    linarith

theorem aux_prop_conc_fine_fibre_det_uY_measurable (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (ell w : ℝ) (y : C(SpatialCoordinates d, ℝ)) :
    Measurable (aux_prop_conc_fine_fibre_det_uY z r hr ell w y) :=
  (y.continuous.measurable.neg).indicator
    ((centeredCube z r hr).isOpen.measurableSet.inter (aux_lem_15_u_stripSet_measurable 0 ell w))

theorem aux_prop_conc_fine_fibre_det_uY_bound (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (ell w : ℝ) (y : C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d) :
    |aux_prop_conc_fine_fibre_det_uY z r hr ell w y x| ≤ aux_prop_conc_fine_fibre_det_S z r y := by
  have h1 := aux_prop_conc_fine_fibre_det_S_nonneg z r y
  by_cases hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_stripSet 0 ell w
  · simp only [aux_prop_conc_fine_fibre_det_uY, Set.indicator_of_mem hx, abs_neg]
    exact aux_prop_conc_fine_fibre_det_abs_le_S z r y
      (aux_prop_conc_fine_fibre_det_cell_subset z hr hx.1)
  · simp only [aux_prop_conc_fine_fibre_det_uY, Set.indicator_of_notMem hx, abs_zero]
    exact h1

theorem aux_prop_conc_fine_fibre_det_uY_supp (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (ell w : ℝ) (y : C(SpatialCoordinates d, ℝ)) (x : SpatialCoordinates d)
    (hx : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_stripSet 0 ell w) :
    aux_prop_conc_fine_fibre_det_uY z r hr ell w y x = 0 :=
  Set.indicator_of_notMem hx _

end defs

section pairs
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
  {C0 m M : ℝ}

/-- The normalized measure `ν` of a pair is finite. -/
theorem aux_prop_conc_fine_fibre_det_nu_finite (Y : prop_conc_pair_data Q z r hr C0 m M) :
    IsFiniteMeasure (aux_prop_conc_pair_data_nu Y (aux_prop_conc_pair_data_slopes d)) := by
  refine ⟨?_⟩
  unfold aux_prop_conc_pair_data_nu
  rw [Measure.smul_apply, Measure.finset_sum_apply, smul_eq_mul]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun p _ => ?_)
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.mpr
    ⟨Y.GammaE.measure_univ_lt_top _ (Y.P.boundary p).property,
      Y.GammaE.measure_univ_lt_top _ (Y.P.domain_eq ▸ Y.P.memF p)⟩

/-- The growth bound of a pair, in the form used for the strip and core masses. -/
theorem aux_prop_conc_fine_fibre_det_growth_enn (Y : prop_conc_pair_data Q z r hr C0 m M)
    (t K : ℝ)
    (hgr : aux_prop_conc_pair_data_growth Y (aux_prop_conc_pair_data_slopes d) t K) :
    ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rho : ℝ, 0 < rho → rho ≤ r →
      aux_prop_conc_pair_data_nu Y (aux_prop_conc_pair_data_slopes d)
          (Metric.ball x rho ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) ≤
        ENNReal.ofReal (K * (rho / r) ^ t) := by
  intro x _ rho hrho hrr
  haveI := aux_prop_conc_fine_fibre_det_nu_finite Y
  have h := hgr x rho hrho hrr
  calc _ = ENNReal.ofReal (_ : ℝ≥0∞).toReal := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal h

/-- The normalized difference measure `ζ` of a pair is finite. -/
theorem aux_prop_conc_fine_fibre_det_zeta_finite (Y : prop_conc_pair_data Q z r hr C0 m M) :
    IsFiniteMeasure (aux_prop_conc_pair_data_zeta Y (aux_prop_conc_pair_data_slopes d)) := by
  refine ⟨?_⟩
  unfold aux_prop_conc_pair_data_zeta
  rw [Measure.smul_apply, Measure.finset_sum_apply, smul_eq_mul]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun p _ => ?_)
  exact Y.GammaE.measure_univ_lt_top _ (Y.E.domain.sub_mem (Y.P.domain_eq ▸ Y.P.memF p)
    (Y.P.boundary p).property)

/-- Strip and core masses of a pair with the cell-normalized growth. -/
theorem aux_prop_conc_fine_fibre_det_masses (Y : prop_conc_pair_data Q z r hr C0 m M)
    (t K : ℝ) (hK : 0 ≤ K)
    (hgr : aux_prop_conc_pair_data_growth Y (aux_prop_conc_pair_data_slopes d) t K)
    (ell w Astrip Acore : ℝ) (hAs : 0 ≤ Astrip) (hAc : 0 ≤ Acore)
    (hcb : aux_prop_conc_fine_geometry_CellBound z r hr t ell w Astrip Acore) :
    aux_prop_conc_fine_pair_step_nu Y
        ((centeredCube z r hr : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_stripSet 0 ell w) ≤
        Astrip * K ∧
      ∀ idx : Fin d → ℤ, aux_prop_conc_fine_pair_step_nu Y
        ((centeredCube z r hr : Set (SpatialCoordinates d)) ∩
          {x | ∀ i : Fin d, (0 : SpatialCoordinates d) i + (idx i : ℝ) * ell ≤ x i ∧
            x i < (0 : SpatialCoordinates d) i + ((idx i : ℝ) + 1) * ell}) ≤ Acore * K := by
  haveI := aux_prop_conc_fine_fibre_det_nu_finite Y
  obtain ⟨h1, h2⟩ := hcb _ K hK (aux_prop_conc_fine_fibre_det_growth_enn Y t K hgr)
  refine ⟨?_, fun idx => ?_⟩
  · exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hAs hK) h1
  · exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hAc hK) (h2 idx)

end pairs

section pieces
variable {d : ℕ}

/-- The pieces of a layer sample on the grid. -/
def aux_prop_conc_fine_fibre_det_T (ell w : ℝ) {n : ℕ} (idx : Fin n → (Fin d → ℤ))
    (y : C(SpatialCoordinates d, ℝ)) : Fin n → C(SpatialCoordinates d, ℝ) :=
  fun k => aux_lem_15_u_localize 0 ell w (idx k) y

theorem aux_prop_conc_fine_fibre_det_localize_bound {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {ell w : ℝ} {n : ℕ} {idx : Fin n → (Fin d → ℤ)}
    (hg : aux_prop_conc_fine_grid_Grid z r hr ell w idx) (y : C(SpatialCoordinates d, ℝ)) (k : Fin n)
    (x : SpatialCoordinates d) :
    |aux_lem_15_u_localize 0 ell w (idx k) y x| ≤ aux_prop_conc_fine_fibre_det_S z r y := by
  obtain ⟨hw, hwl, hls, hinj, hcover, hkbox⟩ := hg
  have hmem : aux_lem_15_u_clamp 0 ell w (idx k) x ∈ aux_prop_conc_fine_fibre_det_Qt z r :=
    hkbox k (aux_lem_15_u_clamp_mem 0 hwl (idx k) x)
  exact aux_prop_conc_fine_fibre_det_abs_le_S z r y hmem

/-- The piece-replaced response as the response of the weight `g_T + h`. -/
theorem aux_prop_conc_fine_fibre_det_psi_update {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ) (p : Fin d → ℝ) (x0 : C(SpatialCoordinates d, ℝ))
    (ell w : ℝ) {n : ℕ} (idx : Fin n → (Fin d → ℤ)) (T : Fin n → C(SpatialCoordinates d, ℝ))
    (i : Fin n) (v : C(SpatialCoordinates d, ℝ)) :
    aux_prop_conc_fine_psi_Psi X c p x0 ell w idx (Function.update T i v) =
      aux_prop_conc_pair_data_theta X c p
        ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator
            (fun x => aux_prop_conc_fine_grid_wt ell w idx T x - x0 x) +
          ((centeredCube z r hr : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_core 0 ell w (idx i)).indicator
            (fun x => v x - T i x)) := by
  unfold aux_prop_conc_fine_psi_Psi
  congr 1
  funext x
  rw [aux_prop_conc_fine_grid_wt_update]
  by_cases hxq : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
  · by_cases hxc : x ∈ aux_lem_15_u_core 0 ell w (idx i)
    · simp [Set.indicator_of_mem hxq, Set.indicator_of_mem hxc, Set.indicator_of_mem (show x ∈ _ ∩ _ from ⟨hxq, hxc⟩)]
      ring
    · simp [Set.indicator_of_mem hxq, Set.indicator_of_notMem hxc,
        Set.indicator_of_notMem (show x ∉ _ ∩ _ from fun h => hxc h.2)]
  · simp [Set.indicator_of_notMem hxq, Set.indicator_of_notMem (show x ∉ _ ∩ _ from fun h => hxq h.1)]

/-- On the cell, the grid weight of the pieces of `y` minus `x0` is `wY + uY`. -/
theorem aux_prop_conc_fine_fibre_det_gridwt_eq {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    (x0 y : C(SpatialCoordinates d, ℝ)) {ell w : ℝ} {n : ℕ} {idx : Fin n → (Fin d → ℤ)}
    (hg : aux_prop_conc_fine_grid_Grid z r hr ell w idx) {x : SpatialCoordinates d}
    (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    aux_prop_conc_fine_grid_wt ell w idx (aux_prop_conc_fine_fibre_det_T ell w idx y) x - x0 x =
      (aux_prop_conc_fine_fibre_det_wY z r hr x0 y + aux_prop_conc_fine_fibre_det_uY z r hr ell w y) x := by
  have h1 : aux_prop_conc_fine_grid_wt ell w idx (aux_prop_conc_fine_fibre_det_T ell w idx y) x =
      (aux_lem_15_u_stripSet 0 ell w)ᶜ.indicator (fun y' => y y') x :=
    aux_prop_conc_fine_grid_wt_pieces hg y hx
  rw [h1]
  simp only [Pi.add_apply, aux_prop_conc_fine_fibre_det_wY, aux_prop_conc_fine_fibre_det_uY,
    Set.indicator_of_mem hx]
  by_cases hxs : x ∈ aux_lem_15_u_stripSet 0 ell w
  · rw [Set.indicator_of_notMem (show x ∉ (aux_lem_15_u_stripSet 0 ell w)ᶜ from fun h => h hxs),
      Set.indicator_of_mem (show x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) ∩ _ from ⟨hx, hxs⟩)]
    ring
  · rw [Set.indicator_of_mem (show x ∈ (aux_lem_15_u_stripSet 0 ell w)ᶜ from hxs),
      Set.indicator_of_notMem (show x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) ∩ _ from
        fun h => hxs h.2)]
    ring

/-- `Ψ (T y) = θ_X (wY + uY)`: the response of the pieces of `y` is the response of the layer with the strips
deleted. -/
theorem aux_prop_conc_fine_fibre_det_psi_eq {Q : Opens (SpatialCoordinates d)}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {C0 m M : ℝ}
    (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ) (p : Fin d → ℝ) (x0 y : C(SpatialCoordinates d, ℝ))
    {ell w : ℝ} {n : ℕ} {idx : Fin n → (Fin d → ℤ)}
    (hg : aux_prop_conc_fine_grid_Grid z r hr ell w idx) :
    aux_prop_conc_fine_psi_Psi X c p x0 ell w idx (aux_prop_conc_fine_fibre_det_T ell w idx y) =
      aux_prop_conc_pair_data_theta X c p
        (aux_prop_conc_fine_fibre_det_wY z r hr x0 y + aux_prop_conc_fine_fibre_det_uY z r hr ell w y) := by
  unfold aux_prop_conc_fine_psi_Psi
  refine aux_prop_conc_fine_pair_step_theta_congr X c p _ _ (fun x hx => ?_)
  rw [Set.indicator_of_mem hx]
  exact aux_prop_conc_fine_fibre_det_gridwt_eq x0 y hg hx

/-- Finite measures: a sum over pairwise disjoint measurable pieces of a set is at most the mass of the set. -/
theorem aux_prop_conc_fine_fibre_det_sum_le {n : ℕ} (nu : Measure (SpatialCoordinates d))
    [IsFiniteMeasure nu] (B : Fin n → Set (SpatialCoordinates d)) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Function.onFun Disjoint B)) (q : Set (SpatialCoordinates d))
    (hBq : ∀ i, B i ⊆ q) :
    ∑ i, (nu (B i)).toReal ≤ (nu q).toReal := by
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top nu _)]
  refine ENNReal.toReal_mono (measure_ne_top nu _) ?_
  have h := measure_iUnion (μ := nu) hdisj hB
  rw [tsum_fintype] at h
  rw [← h]
  exact measure_mono (Set.iUnion_subset hBq)

end pieces

section main
variable {d : ℕ}

/-- **Deterministic estimates along one fibre.**  For a reference `x0`, a layer sample `y` whose masked pair has
the growth constant `Ky`: the deletion error, and the data `(ν_i, ζ_i, max ν)` of the conditional variance of
the pieces response, all with one constant `Cex(C0, d)`. -/
theorem prop_conc_fine_fibre_det (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    ∃ Cex : ℝ, 0 < Cex ∧
    ∀ {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {m M : ℝ}
      (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Set.Icc m M →
      ∀ p ∈ aux_prop_conc_pair_data_slopes d,
      ∀ (x0 : C(SpatialCoordinates d, ℝ)) (ell w : ℝ) {n : ℕ} (idx : Fin n → (Fin d → ℤ)),
        aux_prop_conc_fine_grid_Grid z r hr ell w idx →
      ∀ (t Astrip Acore : ℝ), 0 ≤ Astrip → 0 ≤ Acore →
        aux_prop_conc_fine_geometry_CellBound z r hr t ell w Astrip Acore →
      ∀ (y : C(SpatialCoordinates d, ℝ)) (Ky : ℝ), 0 ≤ Ky →
        (∀ (hw : Measurable (aux_prop_conc_fine_fibre_det_wY z r hr x0 y)) (Kw : ℝ)
          (hKw : ∀ x, |aux_prop_conc_fine_fibre_det_wY z r hr x0 y x| ≤ Kw),
          aux_prop_conc_pair_data_growth
            (aux_prop_conc_pair_mask_pair X (aux_prop_conc_fine_fibre_det_wY z r hr x0 y) hw Kw hKw)
            (aux_prop_conc_pair_data_slopes d) t Ky) →
        |aux_prop_conc_pair_data_theta X c p (fun x => y x - x0 x) -
            aux_prop_conc_fine_psi_Psi X c p x0 ell w idx
              (aux_prop_conc_fine_fibre_det_T ell w idx y)| ≤
          Cex * aux_prop_conc_fine_fibre_det_S z r y *
            Real.exp (Cex * aux_prop_conc_fine_fibre_det_S z r y) * (M - m) *
            (Ky * Astrip + Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
                ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)) *
              Real.sqrt Ky * Real.sqrt Astrip) ∧
        ∃ (nu zeta : Fin n → ℝ) (mx : ℝ), 0 ≤ mx ∧ (∀ i, 0 ≤ nu i) ∧ (∀ i, 0 ≤ zeta i) ∧
          (∀ i, nu i ≤ mx) ∧ (∑ i, nu i ≤ Cex) ∧ (∑ i, zeta i ≤ Cex * (M - m) ^ 2) ∧
          mx ≤ Cex * Real.exp (Cex * aux_prop_conc_fine_fibre_det_S z r y) * ((Acore + Astrip) * Ky) ∧
          ∀ (y' : C(SpatialCoordinates d, ℝ)) (i : Fin n),
            |aux_prop_conc_fine_psi_Psi X c p x0 ell w idx
                (Function.update (aux_prop_conc_fine_fibre_det_T ell w idx y) i
                  (aux_prop_conc_fine_fibre_det_T ell w idx y' i)) -
              aux_prop_conc_fine_psi_Psi X c p x0 ell w idx (aux_prop_conc_fine_fibre_det_T ell w idx y)| ≤
            Cex * (aux_prop_conc_fine_fibre_det_S z r y + aux_prop_conc_fine_fibre_det_S z r y') *
              Real.exp (Cex * (aux_prop_conc_fine_fibre_det_S z r y +
                aux_prop_conc_fine_fibre_det_S z r y')) *
              ((M - m) * nu i + Real.sqrt (nu i * zeta i)) := by
  obtain ⟨-, -, ⟨Cdel, hCdel, hdel⟩, ⟨Cpc, hCpc, hpc⟩⟩ := prop_conc_fine_pair_step C0 hC0 d
  obtain ⟨Cmb, hCmb, hmb⟩ := prop_conc_masked_delta_bounds C0 hC0 d
  set Cex : ℝ := max (max Cdel Cpc) Cmb with hCexdef
  have hCex_pos : 0 < Cex := lt_max_of_lt_right hCmb
  have hdel_le : Cdel ≤ Cex := (le_max_left _ _).trans (le_max_left _ _)
  have hpc_le : Cpc ≤ Cex := (le_max_right _ _).trans (le_max_left _ _)
  have hmb_le : Cmb ≤ Cex := le_max_right _ _
  refine ⟨Cex, hCex_pos, ?_⟩
  intro Q z r hr m M X c hc p hp x0 ell w n idx hg t Astrip Acore hAs hAc hcb y Ky hKy hgr
  have hgap : 0 ≤ M - m := sub_nonneg.mpr X.hmM
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  set S : ℝ := aux_prop_conc_fine_fibre_det_S z r y with hSdef
  set S0 : ℝ := aux_prop_conc_fine_fibre_det_S z r x0 with hS0def
  have hS0 : 0 ≤ S := aux_prop_conc_fine_fibre_det_S_nonneg z r y
  have hS00 : 0 ≤ S0 := aux_prop_conc_fine_fibre_det_S_nonneg z r x0
  set wY := aux_prop_conc_fine_fibre_det_wY z r hr x0 y with hwYdef
  have hwm : Measurable wY := aux_prop_conc_fine_fibre_det_wY_measurable z r hr x0 y
  have hKw : ∀ x, |wY x| ≤ S + S0 := aux_prop_conc_fine_fibre_det_wY_bound z r hr x0 y
  set uY := aux_prop_conc_fine_fibre_det_uY z r hr ell w y with huYdef
  have hum : Measurable uY := aux_prop_conc_fine_fibre_det_uY_measurable z r hr ell w y
  have hKu : ∀ x, |uY x| ≤ S := aux_prop_conc_fine_fibre_det_uY_bound z r hr ell w y
  set Bs : Set (SpatialCoordinates d) :=
    (centeredCube z r hr : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_stripSet 0 ell w with hBs
  have hBsm : MeasurableSet Bs := hq.inter (aux_lem_15_u_stripSet_measurable 0 ell w)
  have hBsq : Bs ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := Set.inter_subset_left
  have hsuppu : ∀ x, x ∉ Bs → uY x = 0 :=
    fun x hx => aux_prop_conc_fine_fibre_det_uY_supp z r hr ell w y x hx
  set Y' := aux_prop_conc_pair_mask_pair X wY hwm (S + S0) hKw with hY'
  have hg' := hgr hwm (S + S0) hKw
  obtain ⟨hstrip, hcore⟩ := aux_prop_conc_fine_fibre_det_masses Y' t Ky hKy hg' ell w Astrip Acore hAs hAc hcb
  have hΔ : ∀ (C : ℝ), Cdel ≤ C → 0 ≤ Cdel → Cdel * S * Real.exp (Cdel * S) ≤ C * S * Real.exp (C * S) := by
    intro C hC h0
    have := aux_prop_conc_deletion_cost_mono hC h0 hS0 le_rfl
    simpa [mul_assoc] using this
  refine ⟨?_, ?_⟩
  · -- the deletion error
    have hθ1 : aux_prop_conc_pair_data_theta X c p (fun x => y x - x0 x) =
        aux_prop_conc_pair_data_theta X c p wY := by
      refine aux_prop_conc_fine_pair_step_theta_congr X c p _ _ (fun x hx => ?_)
      simp [hwYdef, aux_prop_conc_fine_fibre_det_wY, Set.indicator_of_mem hx]
    have h1 := hdel X c hc p hp wY uY hwm (S + S0) hKw hum Bs hBsm hBsq hsuppu S hS0 hKu Ky Astrip hKy hAs
      (by rw [mul_comm]; exact hstrip)
    rw [← aux_prop_conc_fine_fibre_det_psi_eq X c p x0 y hg, ← hθ1, abs_sub_comm] at h1
    refine h1.trans ?_
    have hA : 0 ≤ Ky * Astrip + Real.sqrt (C0 ^ 2 * ((2 : ℝ) ^ d *
        ∑ v ∈ aux_prop_conc_pair_data_slopes d, ∑ i : Fin d, (v i) ^ 2)) * Real.sqrt Ky *
        Real.sqrt Astrip := by positivity
    have := hΔ Cex hdel_le hCdel.le
    calc Cdel * S * Real.exp (Cdel * S) * (M - m) * _ ≤ Cex * S * Real.exp (Cex * S) * (M - m) * _ := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hgap) hA
      _ = _ := rfl
  · -- the data of the conditional variance
    set Z' := aux_prop_conc_pair_mask_pair Y' uY hum S hKu with hZ'
    haveI hfinZ := aux_prop_conc_fine_fibre_det_nu_finite Z'
    haveI hfinZ2 := aux_prop_conc_fine_fibre_det_zeta_finite Z'
    haveI hfinY := aux_prop_conc_fine_fibre_det_nu_finite Y'
    obtain ⟨hw', hwl, hls, hinj, hcover, hkbox⟩ := hg
    have hg : aux_prop_conc_fine_grid_Grid z r hr ell w idx := ⟨hw', hwl, hls, hinj, hcover, hkbox⟩
    set B : Fin n → Set (SpatialCoordinates d) := fun i =>
      (centeredCube z r hr : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_core 0 ell w (idx i) with hB
    have hBm : ∀ i, MeasurableSet (B i) := fun i =>
      hq.inter (aux_lem_15_u_core_isOpen 0 ell w (idx i)).measurableSet
    have hBq : ∀ i, B i ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := fun i =>
      Set.inter_subset_left
    have hdisj : Pairwise (Function.onFun Disjoint B) := by
      intro i j hij
      refine Set.disjoint_left.mpr (fun x hxi hxj => ?_)
      exact Set.disjoint_left.mp (aux_lem_15_u_core_disjoint 0 (hw'.trans_le hwl).le hw'
        (fun h => hij (hinj h))) hxi.2 hxj.2
    obtain ⟨hmb1, hmb2⟩ := hmb Y'
    have hexp : Cmb * Real.exp (Cmb * S) ≤ Cex * Real.exp (Cex * S) :=
      mul_le_mul hmb_le (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hmb_le hS0))
        (Real.exp_pos _).le hCex_pos.le
    have hnu_le : ∀ i, aux_prop_conc_fine_pair_step_nu Z' (B i) ≤
        Cex * Real.exp (Cex * S) * ((Acore + Astrip) * Ky) := by
      intro i
      have h2 := hmb2 uY hum S hKu Bs hBsm hBsq hsuppu S hS0 hKu (B i) (hBm i) (hBq i)
      have hbox : B i ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∩
          {x | ∀ c : Fin d, (0 : SpatialCoordinates d) c + (idx i c : ℝ) * ell ≤ x c ∧
            x c < (0 : SpatialCoordinates d) c + ((idx i c : ℝ) + 1) * ell} := by
        intro x hx
        refine ⟨hx.1, fun c => ?_⟩
        have := hx.2 c
        simp only [Pi.zero_apply, zero_add] at this ⊢
        constructor <;> linarith [this.1, this.2]
      have h3 : aux_prop_conc_fine_pair_step_nu Y' (B i) ≤ Acore * Ky :=
        (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hbox)).trans (hcore (idx i))
      have h4 : aux_prop_conc_fine_pair_step_nu Y' Bs ≤ Astrip * Ky := hstrip
      have h5 : aux_prop_conc_fine_pair_step_nu Z' (B i) ≤
          Cmb * Real.exp (Cmb * S) * ((Acore + Astrip) * Ky) := by
        refine h2.trans ?_
        have h3' : (aux_prop_conc_pair_data_nu Y' (aux_prop_conc_pair_data_slopes d) (B i)).toReal ≤
            Acore * Ky := h3
        have h4' : (aux_prop_conc_pair_data_nu Y' (aux_prop_conc_pair_data_slopes d) Bs).toReal ≤
            Astrip * Ky := h4
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      refine h5.trans ?_
      exact mul_le_mul_of_nonneg_right hexp (by positivity)
    refine ⟨fun i => aux_prop_conc_fine_pair_step_nu Z' (B i),
      fun i => aux_prop_conc_fine_pair_step_zeta Z' (B i),
      Cex * Real.exp (Cex * S) * ((Acore + Astrip) * Ky), by positivity,
      fun i => ENNReal.toReal_nonneg, fun i => ENNReal.toReal_nonneg, hnu_le, ?_, ?_, le_rfl, ?_⟩
    · exact (aux_prop_conc_fine_fibre_det_sum_le (aux_prop_conc_pair_data_nu Z' (aux_prop_conc_pair_data_slopes d))
        B hBm hdisj _ hBq).trans (((hmb1 Z').1).trans hmb_le)
    · exact (aux_prop_conc_fine_fibre_det_sum_le (aux_prop_conc_pair_data_zeta Z' (aux_prop_conc_pair_data_slopes d))
        B hBm hdisj _ hBq).trans (((hmb1 Z').2).trans
          (mul_le_mul_of_nonneg_right hmb_le (sq_nonneg _)))
    · intro y' i
      set v := aux_prop_conc_fine_fibre_det_T ell w idx y' i with hv
      set hp' : SpatialCoordinates d → ℝ := (B i).indicator
        (fun x => v x - aux_prop_conc_fine_fibre_det_T ell w idx y i x) with hhp
      have hhm : Measurable hp' := by
        refine Measurable.indicator ?_ (hBm i)
        exact v.continuous.measurable.sub (aux_prop_conc_fine_fibre_det_T ell w idx y i).continuous.measurable
      have hsupp' : ∀ x, x ∉ B i → hp' x = 0 := fun x hx => Set.indicator_of_notMem hx _
      set S' : ℝ := aux_prop_conc_fine_fibre_det_S z r y' with hS'
      have hS'0 : 0 ≤ S' := aux_prop_conc_fine_fibre_det_S_nonneg z r y'
      have hbd : ∀ x, |hp' x| ≤ S + S' := by
        intro x
        by_cases hx : x ∈ B i
        · simp only [hhp, Set.indicator_of_mem hx]
          exact (abs_sub _ _).trans (add_le_add
            (aux_prop_conc_fine_fibre_det_localize_bound hg y' i x)
            (aux_prop_conc_fine_fibre_det_localize_bound hg y i x) |>.trans_eq (add_comm _ _))
        · simp only [hhp, Set.indicator_of_notMem hx, abs_zero]; linarith
      rw [aux_prop_conc_fine_fibre_det_psi_update X c p x0 ell w idx _ i v,
        aux_prop_conc_fine_fibre_det_psi_eq X c p x0 y hg]
      have hcongr : aux_prop_conc_pair_data_theta X c p
          ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator
            (fun x => aux_prop_conc_fine_grid_wt ell w idx (aux_prop_conc_fine_fibre_det_T ell w idx y) x - x0 x) +
          ((centeredCube z r hr : Set (SpatialCoordinates d)) ∩ aux_lem_15_u_core 0 ell w (idx i)).indicator
            (fun x => v x - aux_prop_conc_fine_fibre_det_T ell w idx y i x)) =
          aux_prop_conc_pair_data_theta X c p (wY + uY + hp') := by
        refine aux_prop_conc_fine_pair_step_theta_congr X c p _ _ (fun x hx => ?_)
        simp only [Pi.add_apply]
        rw [Set.indicator_of_mem hx, aux_prop_conc_fine_fibre_det_gridwt_eq x0 y hg hx]
        rfl
      rw [hcongr]
      have h1 := hpc X c hc p hp wY uY hp' hwm (S + S0) hKw hum S hKu hhm (B i) (hBm i) (hBq i) hsupp'
        (S + S') (by positivity) hbd
      refine h1.trans ?_
      have hGe : Cpc * (S + S') * Real.exp (Cpc * (S + S')) ≤ Cex * (S + S') * Real.exp (Cex * (S + S')) := by
        have := aux_prop_conc_deletion_cost_mono hpc_le hCpc.le (by positivity : 0 ≤ S + S') le_rfl
        simpa [mul_assoc] using this
      refine mul_le_mul_of_nonneg_right hGe ?_
      exact add_nonneg (mul_nonneg hgap ENNReal.toReal_nonneg) (Real.sqrt_nonneg _)

end main

end
end Paper
