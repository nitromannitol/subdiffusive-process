module

public import SubdiffusiveProcess.Paper.prop_conc_fine_grid
public import SubdiffusiveProcess.Paper.prop_conc_fine_pair_step

@[expose] public section

/-! The relative response of the pieces-masked configuration as a function of the pieces, for a fixed pair
`X`: `Ψ(T) = θ_X(1_q (Σ_k 1_{core_k} T_k - x0))`.  It is bounded by `C (M - m)` and continuous for the product
of the compact-open topologies, hence measurable, so the Efron--Stein inequality applies to it for the
fixed pair. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

variable {d : ℕ}

/-- `Ψ(T) = θ_X (1_q (grid weight of T - x0))`. -/
def aux_prop_conc_fine_psi_Psi {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ}
    {hr : 0 < r} {C0 m M : ℝ} (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ) (p : Fin d → ℝ)
    (x0 : C(SpatialCoordinates d, ℝ)) (ell w : ℝ) {n : ℕ} (idx : Fin n → (Fin d → ℤ))
    (T : Fin n → C(SpatialCoordinates d, ℝ)) : ℝ :=
  aux_prop_conc_pair_data_theta X c p
    ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator
      (fun x => aux_prop_conc_fine_grid_wt ell w idx T x - x0 x))

theorem aux_prop_conc_fine_psi_supn_zero (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt) :
    aux_lem_15_u_supn Qt hQt (0 : C(SpatialCoordinates d, ℝ)) = 0 := by
  haveI : CompactSpace Qt := isCompact_iff_compactSpace.mp hQt
  have h : (0 : C(SpatialCoordinates d, ℝ)).restrict Qt = 0 := ContinuousMap.ext fun _ => rfl
  show ‖(0 : C(SpatialCoordinates d, ℝ)).restrict Qt‖ = 0
  rw [h, norm_zero]

/-- The weight `1_q (grid weight - x0)` is a measurable function bounded by the sup norms. -/
theorem aux_prop_conc_fine_psi_weight_bound {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {ell w : ℝ}
    {n : ℕ} {idx : Fin n → (Fin d → ℤ)} (hg : aux_prop_conc_fine_grid_Grid z r hr ell w idx)
    (x0 : C(SpatialCoordinates d, ℝ)) (T : Fin n → C(SpatialCoordinates d, ℝ)) :
    Measurable ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator
      (fun x => aux_prop_conc_fine_grid_wt ell w idx T x - x0 x)) ∧
    ∀ x, |(centeredCube z r hr : Set (SpatialCoordinates d)).indicator
      (fun x => aux_prop_conc_fine_grid_wt ell w idx T x - x0 x) x| ≤
      (∑ k, aux_lem_15_u_supn (Metric.closedBall z (3 * r / 2)) (isCompact_closedBall _ _) (T k)) +
        aux_lem_15_u_supn (Metric.closedBall z (3 * r / 2)) (isCompact_closedBall _ _) x0 := by
  have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  refine ⟨((aux_prop_conc_fine_grid_wt_measurable ell w idx T).sub
    x0.continuous.measurable).indicator hq, fun x => ?_⟩
  have hnn : 0 ≤ (∑ k, aux_lem_15_u_supn (Metric.closedBall z (3 * r / 2)) (isCompact_closedBall _ _) (T k)) +
        aux_lem_15_u_supn (Metric.closedBall z (3 * r / 2)) (isCompact_closedBall _ _) x0 :=
    add_nonneg (Finset.sum_nonneg fun k _ => aux_lem_15_u_supn_nonneg _ _ _)
      (aux_lem_15_u_supn_nonneg _ _ _)
  by_cases hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hx]
    have h1 := aux_prop_conc_fine_grid_wt_abs_le hg T (fun _ => 0) x
    have h0 : aux_prop_conc_fine_grid_wt ell w idx (fun _ => (0 : C(SpatialCoordinates d, ℝ))) x = 0 := by
      simp [aux_prop_conc_fine_grid_wt]
    rw [h0, sub_zero] at h1
    have h2 : |x0 x| ≤ aux_lem_15_u_supn (Metric.closedBall z (3 * r / 2)) (isCompact_closedBall _ _) x0 := by
      haveI : CompactSpace (Metric.closedBall z (3 * r / 2)) :=
        isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
      have hxQ : x ∈ Metric.closedBall z (3 * r / 2) := by
        have : dist x z < r / 2 := hx
        rw [Metric.mem_closedBall]
        have := hr
        linarith
      have := ContinuousMap.norm_coe_le_norm (x0.restrict (Metric.closedBall z (3 * r / 2))) ⟨x, hxQ⟩
      simpa [aux_lem_15_u_supn, Real.norm_eq_abs] using this
    have h3 : ∀ k, aux_lem_15_u_supn (Metric.closedBall z (3 * r / 2)) (isCompact_closedBall _ _)
        (T k - (fun _ => (0 : C(SpatialCoordinates d, ℝ))) k) =
        aux_lem_15_u_supn (Metric.closedBall z (3 * r / 2)) (isCompact_closedBall _ _) (T k) := by
      intro k; simp
    simp only [h3] at h1
    calc |aux_prop_conc_fine_grid_wt ell w idx T x - x0 x|
        ≤ |aux_prop_conc_fine_grid_wt ell w idx T x| + |x0 x| := abs_sub _ _
      _ ≤ _ := add_le_add h1 h2
  · rw [Set.indicator_of_notMem hx, abs_zero]; exact hnn

/-- **The pieces response.**  `Ψ` is bounded by `C (M - m)` and continuous. -/
theorem prop_conc_fine_psi (C0 : ℝ) (hC0 : 1 ≤ C0) (d : ℕ) :
    ∃ CB : ℝ, 0 < CB ∧
      ∀ {Q : Opens (SpatialCoordinates d)} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r} {m M : ℝ}
        (X : prop_conc_pair_data Q z r hr C0 m M) (c : ℝ), c ∈ Set.Icc m M →
        ∀ p ∈ aux_prop_conc_pair_data_slopes d,
        ∀ (x0 : C(SpatialCoordinates d, ℝ)) (ell w : ℝ) {n : ℕ} (idx : Fin n → (Fin d → ℤ)),
          aux_prop_conc_fine_grid_Grid z r hr ell w idx →
          Continuous (aux_prop_conc_fine_psi_Psi X c p x0 ell w idx) ∧
          ∀ T, |aux_prop_conc_fine_psi_Psi X c p x0 ell w idx T| ≤ CB * (M - m) := by
  obtain ⟨⟨CB, hCB, hbd⟩, ⟨CL, hCL, hlip⟩, -, -⟩ := prop_conc_fine_pair_step C0 hC0 d
  refine ⟨CB, hCB, ?_⟩
  intro Q z r hr m M X c hc p hp x0 ell w n idx hg
  have hgap : 0 ≤ M - m := sub_nonneg.mpr X.hmM
  set Qt : Set (SpatialCoordinates d) := Metric.closedBall z (3 * r / 2) with hQt
  refine ⟨?_, fun T => ?_⟩
  · -- continuity through the Lipschitz estimate
    refine continuous_iff_continuousAt.mpr fun T0 => ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    -- the size of the perturbation
    have hsmall : ∃ δ : ℝ, 0 < δ ∧ ∀ G : ℝ, 0 ≤ G → G < δ → CL * G * Real.exp (CL * G) * (M - m) < ε := by
      -- continuity at `0` of `G ↦ CL * G * exp (CL * G) * (M - m)`
      have hcont : Continuous (fun G : ℝ => CL * G * Real.exp (CL * G) * (M - m)) := by fun_prop
      have h0 : (fun G : ℝ => CL * G * Real.exp (CL * G) * (M - m)) 0 < ε := by simpa using hε
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ε hε
      refine ⟨δ, hδ, fun G hG0 hGδ => ?_⟩
      have h1 := hδ' (show dist G 0 < δ by simpa [Real.dist_eq, abs_of_nonneg hG0] using hGδ)
      have hfG : 0 ≤ CL * G * Real.exp (CL * G) * (M - m) := by positivity
      rw [Real.dist_eq, show CL * (0 : ℝ) * Real.exp (CL * 0) * (M - m) = 0 by simp, sub_zero,
        abs_of_nonneg hfG] at h1
      exact h1
    obtain ⟨δ, hδ, hδε⟩ := hsmall
    -- neighbourhood: the sum of sup-norm distances is small
    have hcontG : Continuous (fun T : Fin n → C(SpatialCoordinates d, ℝ) =>
        ∑ k, aux_lem_15_u_supn Qt (isCompact_closedBall _ _) (T k - T0 k)) := by
      refine continuous_finset_sum _ fun k _ => ?_
      exact (aux_lem_15_u_supn_continuous Qt _).comp
        (((continuous_apply k).sub continuous_const))
    have hev : ∀ᶠ T in nhds T0, ∑ k, aux_lem_15_u_supn Qt (isCompact_closedBall _ _) (T k - T0 k) < δ := by
      have h0 : ∑ k, aux_lem_15_u_supn Qt (isCompact_closedBall _ _) (T0 k - T0 k) < δ := by
        have h00 : ∀ k, aux_lem_15_u_supn Qt (isCompact_closedBall _ _) (T0 k - T0 k) = 0 := by
          intro k; rw [sub_self]; exact aux_prop_conc_fine_psi_supn_zero _ _
        simp only [h00, Finset.sum_const_zero]; exact hδ
      exact hcontG.continuousAt.eventually (gt_mem_nhds h0)
    filter_upwards [hev] with T hT
    rw [Real.dist_eq]
    set G := ∑ k, aux_lem_15_u_supn Qt (isCompact_closedBall _ _) (T k - T0 k) with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun k _ => aux_lem_15_u_supn_nonneg _ _ _
    obtain ⟨hm1, hb1⟩ := aux_prop_conc_fine_psi_weight_bound hg x0 T
    obtain ⟨hm2, hb2⟩ := aux_prop_conc_fine_psi_weight_bound hg x0 T0
    have hq : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
      (centeredCube z r hr).isOpen.measurableSet
    have := hlip X c hc p hp _ _ hm1 hm2
      (Real.sqrt 0 + ((∑ k, aux_lem_15_u_supn Qt (isCompact_closedBall _ _) (T k)) +
        aux_lem_15_u_supn Qt (isCompact_closedBall _ _) x0) +
        ((∑ k, aux_lem_15_u_supn Qt (isCompact_closedBall _ _) (T0 k)) +
        aux_lem_15_u_supn Qt (isCompact_closedBall _ _) x0))
      (fun x => by
        refine (hb1 x).trans ?_
        have : 0 ≤ ∑ k, aux_lem_15_u_supn Qt (isCompact_closedBall _ _) (T0 k) + aux_lem_15_u_supn Qt (isCompact_closedBall _ _) x0 :=
          add_nonneg (Finset.sum_nonneg fun k _ => aux_lem_15_u_supn_nonneg _ _ _) (aux_lem_15_u_supn_nonneg _ _ _)
        simp; linarith)
      (fun x => by
        refine (hb2 x).trans ?_
        have : 0 ≤ ∑ k, aux_lem_15_u_supn Qt (isCompact_closedBall _ _) (T k) + aux_lem_15_u_supn Qt (isCompact_closedBall _ _) x0 :=
          add_nonneg (Finset.sum_nonneg fun k _ => aux_lem_15_u_supn_nonneg _ _ _) (aux_lem_15_u_supn_nonneg _ _ _)
        simp; linarith)
      G hG0 (fun x hx => by
        have h1 := aux_prop_conc_fine_grid_wt_abs_le hg T T0 x
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
        have : (fun x => aux_prop_conc_fine_grid_wt ell w idx T x - x0 x) x -
            (fun x => aux_prop_conc_fine_grid_wt ell w idx T0 x - x0 x) x =
            aux_prop_conc_fine_grid_wt ell w idx T x - aux_prop_conc_fine_grid_wt ell w idx T0 x := by ring
        rw [this]; exact h1)
    exact lt_of_le_of_lt this (hδε G hG0 hT)
  · obtain ⟨hm1, hb1⟩ := aux_prop_conc_fine_psi_weight_bound hg x0 T
    exact hbd X c hc p hp _ hm1 _ hb1

end
end Paper
