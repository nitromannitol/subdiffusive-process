module

public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.WeakGradient
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-!
# Holder representatives of killed L² limits

This module proves that an `L²` limit of functions with uniformly bounded continuous Holder
representatives on a closed cube has a continuous Holder representative that vanishes on the
frontier when each approximating representative does. It does not produce the approximating
sequence or transfer local response energies.
-/

open Filter MeasureTheory Set Topology
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace Paper

/-- Euclidean length (the metric of `Lane4.holderRatioSet`) is at most `√d` times the sup
distance of `SpatialCoordinates d`. -/
theorem aux_lem_goodext_euclid_le {d : ℕ} (x y : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt d * dist x y := by
  have h : ∀ j, (x j - y j) ^ 2 ≤ dist x y ^ 2 := by
    intro j
    have h1 := dist_le_pi_dist x y j
    rw [Real.dist_eq] at h1
    calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
      _ ≤ dist x y ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hsum : ∑ j : Fin d, (x j - y j) ^ 2 ≤ (d : ℝ) * dist x y ^ 2 := by
    calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, dist x y ^ 2 :=
          Finset.sum_le_sum (fun j _ => h j)
      _ = (d : ℝ) * dist x y ^ 2 := by simp
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * dist x y ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * dist x y := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq dist_nonneg]

/-- On a bounded set, a first-difference Holder bound at exponent `alpha`
also gives one at every smaller nonnegative exponent. -/
theorem aux_lem_goodext_holder_drop {d : ℕ} {S : Set (SpatialCoordinates d)}
    {f : SpatialCoordinates d → ℝ} {alpha beta D : ℝ}
    (hBA : beta < alpha)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S,
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ D)
    (hf : Lane4.IsHolderOn alpha S f) : Lane4.IsHolderOn beta S f := by
  rcases hf with ⟨C, hC⟩
  let C' : ℝ := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hCle : C ≤ C' := le_max_left _ _
  refine ⟨C' * D ^ (alpha - beta), ?_⟩
  rintro v ⟨x, hx, y, hy, hxy, rfl⟩
  let e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)
  have hepos : 0 < e := by
    dsimp [e]
    have hne : ∃ j : Fin d, x j ≠ y j := by
      by_contra! h
      apply hxy
      ext j
      exact h j
    rcases hne with ⟨j, hj⟩
    have hsq : 0 < (x j - y j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
    have hsum : (x j - y j) ^ 2 ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
      Finset.single_le_sum (f := fun i : Fin d => (x i - y i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    exact Real.sqrt_pos.mpr (lt_of_lt_of_le hsq hsum)
  have hsource : |f x - f y| ≤ C' * e ^ alpha := by
    have hratio := hC ⟨x, hx, y, hy, hxy, rfl⟩
    have hden : 0 < e ^ alpha := Real.rpow_pos_of_pos hepos alpha
    have hquot := (div_le_iff₀ hden).mp (le_trans hratio hCle)
    simpa [e, mul_comm] using hquot
  have hquotient : |f x - f y| / e ^ beta ≤ C' * D ^ (alpha - beta) := by
    have hpow : e ^ alpha / e ^ beta = e ^ (alpha - beta) := by
      rw [← Real.rpow_sub hepos alpha beta]
    calc
      |f x - f y| / e ^ beta ≤ (C' * e ^ alpha) / e ^ beta :=
        div_le_div_of_nonneg_right hsource (Real.rpow_nonneg (le_of_lt hepos) beta)
      _ = C' * (e ^ alpha / e ^ beta) := by ring
      _ = C' * e ^ (alpha - beta) := by rw [hpow]
      _ ≤ C' * D ^ (alpha - beta) := by
        apply mul_le_mul_of_nonneg_left _ hC'
        exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (hdiam x hx y hy) (by linarith)
  simpa [e] using hquotient

/-- `L²` convergence gives an almost-everywhere convergent subsequence. -/
theorem aux_lem_goodext_L2_subseq_ae {d : ℕ} (Q : TopologicalSpace.Opens (SpatialCoordinates d))
    (un : ℕ → DomainL2 Q) (u : DomainL2 Q) (hconv : Tendsto un atTop (𝓝 u)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        Tendsto (fun i => (un (ns i) : SpatialCoordinates d → ℝ) x) atTop
          (𝓝 ((u : SpatialCoordinates d → ℝ) x)) :=
  (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae

/-- Hole 1. Pointwise content of `IsHolderOn` plus a `C^α`-norm bound on a compact set. -/
theorem aux_lem_goodext_pointwise_of_cAlpha {d : ℕ} (alpha K : ℝ) (halpha : 0 < alpha)
    (S : Set (SpatialCoordinates d)) (hS : IsCompact S)
    (f : SpatialCoordinates d → ℝ) (hf : ContinuousOn f S)
    (hhol : Lane4.IsHolderOn alpha S f)
    (hnorm : Lane4.cAlphaNorm alpha S f ≤ K) :
    0 ≤ K ∧ (∀ x ∈ S, |f x| ≤ K) ∧
      ∀ x ∈ S, ∀ y ∈ S,
        |f x - f y| ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
  have hK_nonneg : 0 ≤ K := by
    have h_sup_nonneg : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} :=
      Real.sSup_nonneg (fun v hv => by
        rcases hv with ⟨x, hx, rfl⟩
        exact abs_nonneg _)
    have h_holder_nonneg : 0 ≤ holderSeminorm alpha S f :=
      Real.sSup_nonneg (fun v hv => by
        rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
        have hsum_pos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
          have h_ne : ∃ j, x j ≠ y j := by
            contrapose! hxy
            ext j; exact hxy j
          rcases h_ne with ⟨j, hj⟩
          have h_sq_pos : 0 < (x j - y j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
          have h_nonneg : ∀ i, 0 ≤ (x i - y i) ^ 2 := fun i => pow_two_nonneg _
          have h_le : (x j - y j) ^ 2 ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
            Finset.single_le_sum (f := fun i : Fin d => (x i - y i) ^ 2)
              (fun i hi => h_nonneg i) (Finset.mem_univ j)
          linarith
        have he_pos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) :=
          Real.sqrt_pos.mpr hsum_pos
        have hden_pos : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
          Real.rpow_pos_of_pos he_pos alpha
        have hnum_nonneg : 0 ≤ |f x - f y| := abs_nonneg _
        exact div_nonneg hnum_nonneg hden_pos.le)
    have h_cAlphaNorm : Lane4.cAlphaNorm alpha S f = sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + holderSeminorm alpha S f := rfl
    linarith
  have h_bdd_norm : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|} := by
    rcases hS.exists_bound_of_continuousOn hf with ⟨C, hC⟩
    refine ⟨C, fun v hv => ?_⟩
    rcases hv with ⟨x, hx, rfl⟩
    have h := hC x hx
    -- hC gives ‖f x‖ ≤ C, and for ℝ, ‖·‖ = |·|
    simpa [Real.norm_eq_abs] using h
  have h_sup_nonneg : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} :=
    Real.sSup_nonneg (fun v hv => by
      rcases hv with ⟨x, hx, rfl⟩
      exact abs_nonneg _)
  have h_holder_nonneg : 0 ≤ holderSeminorm alpha S f :=
    Real.sSup_nonneg (fun v hv => by
      rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
      have hsum_pos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
        have h_ne : ∃ j, x j ≠ y j := by
          contrapose! hxy
          ext j; exact hxy j
        rcases h_ne with ⟨j, hj⟩
        have h_sq_pos : 0 < (x j - y j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
        have h_nonneg : ∀ i, 0 ≤ (x i - y i) ^ 2 := fun i => pow_two_nonneg _
        have h_le : (x j - y j) ^ 2 ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin d => (x i - y i) ^ 2)
            (fun i hi => h_nonneg i) (Finset.mem_univ j)
        linarith
      have he_pos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := Real.sqrt_pos.mpr hsum_pos
      exact div_nonneg (abs_nonneg _) (Real.rpow_pos_of_pos he_pos alpha).le)
  have h_sup_le_K : sSup {v : ℝ | ∃ x ∈ S, v = |f x|} ≤ K := by
    have : Lane4.cAlphaNorm alpha S f = sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + holderSeminorm alpha S f := rfl
    linarith [hnorm, h_holder_nonneg]
  have h_pointwise : ∀ x ∈ S, |f x| ≤ K := by
    intro x hx
    have h_le_sup : |f x| ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} :=
      le_csSup h_bdd_norm ⟨x, hx, rfl⟩
    linarith
  have h_diff_bound : ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy
      simp [Real.zero_rpow (ne_of_gt halpha)]
    · have he_pos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
        refine Real.sqrt_pos.mpr ?_
        have hsum_pos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
          have h_ne : ∃ j, x j ≠ y j := by
            contrapose! hxy
            ext j; exact hxy j
          rcases h_ne with ⟨j, hj⟩
          have h_sq_pos : 0 < (x j - y j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
          have h_nonneg : ∀ i, 0 ≤ (x i - y i) ^ 2 := fun i => pow_two_nonneg _
          have h_le : (x j - y j) ^ 2 ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
            Finset.single_le_sum (f := fun i : Fin d => (x i - y i) ^ 2)
              (fun i hi => h_nonneg i) (Finset.mem_univ j)
          linarith
        exact hsum_pos
      have he_rpow_pos : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
        Real.rpow_pos_of_pos he_pos alpha
      have h_holder_le : holderSeminorm alpha S f ≤ K := by
        have : Lane4.cAlphaNorm alpha S f = sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + holderSeminorm alpha S f := rfl
        linarith [hnorm, h_sup_nonneg]
      have h_ratio_le : |f x - f y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤
          holderSeminorm alpha S f := by
        have : |f x - f y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ∈
            holderRatioSet alpha S f := by
          refine ⟨x, hx, y, hy, hxy, rfl⟩
        have h_bdd : BddAbove (holderRatioSet alpha S f) := hhol
        exact le_csSup h_bdd this
      calc
        |f x - f y| = (|f x - f y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) *
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
          field_simp [he_rpow_pos.ne']
        _ ≤ holderSeminorm alpha S f * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
          mul_le_mul_of_nonneg_right h_ratio_le (by positivity)
        _ ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
          mul_le_mul_of_nonneg_right h_holder_le (by positivity)
  exact ⟨hK_nonneg, h_pointwise, h_diff_bound⟩

/-- Hole 2. Pointwise bounds give the Hölder class and a `C^α`-norm bound. -/
theorem aux_lem_goodext_cAlpha_of_pointwise {d : ℕ} (alpha K : ℝ) (hK : 0 ≤ K)
    (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ)
    (hsup : ∀ x ∈ S, |f x| ≤ K)
    (hdiff : ∀ x ∈ S, ∀ y ∈ S,
        |f x - f y| ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) :
    Lane4.IsHolderOn alpha S f ∧ Lane4.cAlphaNorm alpha S f ≤ 2 * K := by
  have h_holder_bdd : BddAbove (holderRatioSet alpha S f) := by
    refine ⟨K, fun v hv => ?_⟩
    rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
    have he_pos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      refine Real.sqrt_pos.mpr ?_
      have hsum_pos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
        have h_ne : ∃ j, x j ≠ y j := by
          contrapose! hxy
          ext j; exact hxy j
        rcases h_ne with ⟨j, hj⟩
        have h_sq_pos : 0 < (x j - y j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
        have h_nonneg : ∀ i, 0 ≤ (x i - y i) ^ 2 := fun i => pow_two_nonneg _
        have h_le : (x j - y j) ^ 2 ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin d => (x i - y i) ^ 2)
            (fun i hi => h_nonneg i) (Finset.mem_univ j)
        linarith
      exact hsum_pos
    have he_rpow_pos : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.rpow_pos_of_pos he_pos alpha
    rw [div_le_iff₀ he_rpow_pos]
    exact hdiff x hx y hy
  have h_holder_le : holderSeminorm alpha S f ≤ K := by
    rw [Lane4.holderSeminorm]
    refine Real.sSup_le (fun v hv => ?_) hK
    rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
    have he_pos : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      refine Real.sqrt_pos.mpr ?_
      have hsum_pos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
        have h_ne : ∃ j, x j ≠ y j := by
          contrapose! hxy
          ext j; exact hxy j
        rcases h_ne with ⟨j, hj⟩
        have h_sq_pos : 0 < (x j - y j) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hj)
        have h_nonneg : ∀ i, 0 ≤ (x i - y i) ^ 2 := fun i => pow_two_nonneg _
        have h_le : (x j - y j) ^ 2 ≤ ∑ i : Fin d, (x i - y i) ^ 2 :=
          Finset.single_le_sum (f := fun i : Fin d => (x i - y i) ^ 2)
            (fun i hi => h_nonneg i) (Finset.mem_univ j)
        linarith
      exact hsum_pos
    have he_rpow_pos : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.rpow_pos_of_pos he_pos alpha
    have h := hdiff x hx y hy
    exact (div_le_iff₀ he_rpow_pos).2 h
  have h_normSet_bdd : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|} := by
    refine ⟨K, fun v hv => ?_⟩
    rcases hv with ⟨x, hx, rfl⟩
    exact hsup x hx
  have h_normSet_sup_le : sSup {v : ℝ | ∃ x ∈ S, v = |f x|} ≤ K :=
    Real.sSup_le (fun v hv => by
      rcases hv with ⟨x, hx, rfl⟩
      exact hsup x hx) hK
  have h_cAlphaNorm_le : Lane4.cAlphaNorm alpha S f ≤ 2 * K := by
    rw [Lane4.cAlphaNorm]
    linarith
  exact ⟨h_holder_bdd, h_cAlphaNorm_le⟩

/-- Hole 3. A pointwise Hölder bound with positive exponent gives continuity on the set. -/
theorem aux_lem_goodext_continuousOn_of_holder {d : ℕ} (alpha K : ℝ) (halpha : 0 < alpha)
    (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ)
    (hdiff : ∀ x ∈ S, ∀ y ∈ S,
        |f x - f y| ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha) :
    ContinuousOn f S := by
  set K' := max K 0 with hK'
  have hK'_nonneg : 0 ≤ K' := le_max_right _ _
  have hK'_bound : ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ K' * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
    intro x hx y hy
    have h := hdiff x hx y hy
    have hK : K ≤ K' := le_max_left _ _
    have he_nonneg : 0 ≤ (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    calc
      |f x - f y| ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := h
      _ ≤ K' * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
        mul_le_mul_of_nonneg_right hK he_nonneg
  have h_bound' : ∀ x ∈ S, ∀ y ∈ S,
      |f x - f y| ≤ K' * (Real.sqrt d * dist x y) ^ alpha := by
    intro x hx y hy
    have heucl := aux_lem_goodext_euclid_le x y
    have hrpow : (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤
        (Real.sqrt d * dist x y) ^ alpha :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) heucl halpha.le
    exact (hK'_bound x hx y hy).trans
      (mul_le_mul_of_nonneg_left hrpow hK'_nonneg)
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  have h_tendsto_zero : Tendsto (fun (t : ℝ) => K' * (Real.sqrt d * t) ^ alpha)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h_inner_cont : ContinuousAt (fun t : ℝ => (Real.sqrt d : ℝ) * t) (0 : ℝ) := by
      have hc : ContinuousAt (fun _ : ℝ => (Real.sqrt d : ℝ)) 0 := continuous_const.continuousAt
      exact hc.mul continuousAt_id
    have h_inner : Tendsto (fun t : ℝ => Real.sqrt d * t) (𝓝 0) (𝓝 0) := by
      simpa using h_inner_cont.tendsto
    have h_power : Tendsto (fun t : ℝ => t ^ alpha) (𝓝 0) (𝓝 (0 ^ alpha)) :=
      (Real.continuousAt_rpow_const 0 alpha (Or.inr halpha.le)).tendsto
    have h_comp := h_power.comp h_inner
    have h_scaled := Tendsto.const_mul K' h_comp
    simpa [Real.zero_rpow (ne_of_gt halpha)] using h_scaled
  have h_event : ∀ᶠ t in 𝓝 (0 : ℝ), K' * (Real.sqrt d * t) ^ alpha < ε :=
    h_tendsto_zero.eventually (gt_mem_nhds hε)
  rcases Metric.mem_nhds_iff.mp h_event with ⟨η, hη, hball⟩
  refine ⟨η, hη, fun y hy hdist => ?_⟩
  have h_bound_y : |f y - f b| ≤ K' * (Real.sqrt d * dist y b) ^ alpha := h_bound' y hy b hb
  have h_eps : K' * (Real.sqrt d * dist y b) ^ alpha < ε := by
    have h_nonneg : 0 ≤ K' * (Real.sqrt d * dist y b) ^ alpha := by
      have h_sqrt_nonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
      have h_dist_nonneg : 0 ≤ dist y b := dist_nonneg
      have h_prod_nonneg : 0 ≤ Real.sqrt d * dist y b := mul_nonneg h_sqrt_nonneg h_dist_nonneg
      exact mul_nonneg hK'_nonneg (Real.rpow_nonneg h_prod_nonneg _)
    have h_mem_ball : dist y b ∈ Metric.ball (0 : ℝ) η := by
      rw [Metric.mem_ball, Real.dist_eq]
      simpa [abs_of_nonneg dist_nonneg] using hdist
    have h_ball_val := hball h_mem_ball
    simpa using h_ball_val
  calc
    dist (f y) (f b) = |f y - f b| := Real.dist_eq _ _
    _ ≤ K' * (Real.sqrt d * dist y b) ^ alpha := h_bound_y
    _ < ε := h_eps

/-- Hole 4. A subset of full measure in an open set is dense in its closure. -/
theorem aux_lem_goodext_closure_subset_of_ae {d : ℕ} (Q : Set (SpatialCoordinates d))
    (hQ : IsOpen Q) (A : Set (SpatialCoordinates d))
    (hA : ∀ᵐ x ∂(volume.restrict Q), x ∈ A) :
    closure Q ⊆ closure (A ∩ Q) := by
  intro x hx
  rw [Metric.mem_closure_iff] at hx ⊢
  intro ε hε
  have hball_nonempty : (Metric.ball x ε ∩ Q).Nonempty := by
    rcases hx ε hε with ⟨y, hyQ, hyball⟩
    refine ⟨y, ?_⟩
    constructor
    · exact Metric.mem_ball.mpr (by simpa [dist_comm] using hyball)
    · exact hyQ
  have hball_open : IsOpen (Metric.ball x ε ∩ Q) :=
    IsOpen.inter Metric.isOpen_ball hQ
  by_cases h_empty : (Metric.ball x ε ∩ Q) ∩ A = ∅
  · have h_sub : Metric.ball x ε ∩ Q ⊆ {x | x ∉ A} := by
      intro y hy
      intro hyA
      have hy_inter : y ∈ (Metric.ball x ε ∩ Q) ∩ A := ⟨hy, hyA⟩
      rw [h_empty] at hy_inter
      exact Set.notMem_empty _ hy_inter
    have h_vol_zero : (volume.restrict Q) (Metric.ball x ε ∩ Q) = 0 := by
      have hout : (volume.restrict Q) {x | x ∉ A} = 0 := ae_iff.mp hA
      exact le_antisymm ((measure_mono h_sub).trans_eq hout) bot_le
    have h_vol_pos : 0 < (volume.restrict Q) (Metric.ball x ε ∩ Q) := by
      have h_meas : MeasurableSet (Metric.ball x ε ∩ Q) := hball_open.measurableSet
      rw [Measure.restrict_apply h_meas]
      have h_inter_eq : (Metric.ball x ε ∩ Q) ∩ Q = Metric.ball x ε ∩ Q :=
        Set.inter_eq_left.mpr (by intro y hy; exact hy.2)
      rw [h_inter_eq]
      exact hball_open.measure_pos volume hball_nonempty
    rw [h_vol_zero] at h_vol_pos
    exact (lt_irrefl 0 h_vol_pos).elim
  · have h_nonempty : ((Metric.ball x ε ∩ Q) ∩ A).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr h_empty
    rcases h_nonempty with ⟨y, hy⟩
    refine ⟨y, ⟨hy.2, hy.1.2⟩, ?_⟩
    simpa [dist_comm] using (Metric.mem_ball.mp hy.1.1)

/-- Hole 5. Equi-Hölder functions converging on a dense subset converge at every point. -/
theorem aux_lem_goodext_tendsto_of_dense {d : ℕ} (alpha K : ℝ) (halpha : 0 < alpha)
    (S A : Set (SpatialCoordinates d)) (hAS : S ⊆ closure A) (hA : A ⊆ S)
    (Un : ℕ → SpatialCoordinates d → ℝ)
    (hdiff : ∀ n, ∀ x ∈ S, ∀ y ∈ S,
        |Un n x - Un n y| ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha)
    (hAconv : ∀ a ∈ A, ∃ l : ℝ, Tendsto (fun n => Un n a) atTop (𝓝 l)) :
    ∀ x ∈ S, ∃ l : ℝ, Tendsto (fun n => Un n x) atTop (𝓝 l) := by
  intro x hx
  set K' := max K 0 with hK'
  have hK'_nonneg : 0 ≤ K' := le_max_right _ _
  have hK'_bound : ∀ n, ∀ x ∈ S, ∀ y ∈ S,
      |Un n x - Un n y| ≤ K' * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
    intro n x' hx' y' hy'
    have h := hdiff n x' hx' y' hy'
    have hK : K ≤ K' := le_max_left _ _
    have he_nonneg : 0 ≤ (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ alpha :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    calc
      |Un n x' - Un n y'| ≤ K * (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ alpha := h
      _ ≤ K' * (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ alpha :=
        mul_le_mul_of_nonneg_right hK he_nonneg
  have h_bound' : ∀ n, ∀ x ∈ S, ∀ y ∈ S,
      |Un n x - Un n y| ≤ K' * (Real.sqrt d * dist x y) ^ alpha := by
    intro n x' hx' y' hy'
    have h := hK'_bound n x' hx' y' hy'
    have h_euclid : Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2) ≤ Real.sqrt d * dist x' y' :=
      aux_lem_goodext_euclid_le x' y'
    have h_rpow : (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ alpha ≤
        (Real.sqrt d * dist x' y') ^ alpha :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) h_euclid halpha.le
    calc
      |Un n x' - Un n y'| ≤ K' * (Real.sqrt (∑ j : Fin d, (x' j - y' j) ^ 2)) ^ alpha := h
      _ ≤ K' * (Real.sqrt d * dist x' y') ^ alpha :=
        mul_le_mul_of_nonneg_left h_rpow hK'_nonneg
  have h_cauchy : CauchySeq (fun n => Un n x) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have h_tendsto_zero : Tendsto (fun (t : ℝ) => K' * (Real.sqrt d * t) ^ alpha) (𝓝 (0 : ℝ)) (𝓝 0) := by
      have h_inner_cont : ContinuousAt (fun t : ℝ => (Real.sqrt d : ℝ) * t) (0 : ℝ) := by
        have hc : ContinuousAt (fun _ : ℝ => (Real.sqrt d : ℝ)) 0 := continuous_const.continuousAt
        exact hc.mul continuousAt_id
      have h_inner : Tendsto (fun t : ℝ => Real.sqrt d * t) (𝓝 0) (𝓝 0) := by
        simpa using h_inner_cont.tendsto
      have h_power : Tendsto (fun t : ℝ => t ^ alpha) (𝓝 0) (𝓝 (0 ^ alpha)) :=
        (Real.continuousAt_rpow_const 0 alpha (Or.inr halpha.le)).tendsto
      have h_comp := h_power.comp h_inner
      have h_scaled := Tendsto.const_mul K' h_comp
      simpa [Real.zero_rpow (ne_of_gt halpha)] using h_scaled
    have h_eta : ∃ η > 0, K' * (Real.sqrt d * η) ^ alpha < ε / 3 := by
      have h_event : ∀ᶠ t in 𝓝 (0 : ℝ), K' * (Real.sqrt d * t) ^ alpha < ε / 3 :=
        h_tendsto_zero.eventually (gt_mem_nhds (by linarith : 0 < ε / 3))
      rcases Metric.mem_nhds_iff.mp h_event with ⟨δ, hδ, hball⟩
      refine ⟨δ / 2, half_pos hδ, ?_⟩
      have h_mem_ball : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
        apply Metric.mem_ball.mpr
        simpa [Real.dist_eq, abs_of_pos hδ] using (half_lt_self hδ)
      exact hball h_mem_ball
    rcases h_eta with ⟨η, hη, hη_bound⟩
    have hx_closure : x ∈ closure A := hAS hx
    rw [Metric.mem_closure_iff] at hx_closure
    rcases hx_closure η hη with ⟨a, haA, hadist⟩
    have haS : a ∈ S := hA haA
    have h_triangle : ∀ m n, |Un m x - Un n x| ≤ |Un m x - Un m a| + |Un m a - Un n a| + |Un n a - Un n x| := by
      intro m n
      calc
        |Un m x - Un n x| = |(Un m x - Un m a) + (Un m a - Un n a) + (Un n a - Un n x)| := by ring
        _ ≤ |(Un m x - Un m a) + (Un m a - Un n a)| + |Un n a - Un n x| := abs_add_le _ _
        _ ≤ (|Un m x - Un m a| + |Un m a - Un n a|) + |Un n a - Un n x| := by
          nlinarith [abs_add_le (Un m x - Un m a) (Un m a - Un n a)]
        _ = |Un m x - Un m a| + |Un m a - Un n a| + |Un n a - Un n x| := by ring
    have h_bound_xa : ∀ n, |Un n x - Un n a| < ε / 3 := by
      intro n
      have h_le := h_bound' n x hx a haS
      have h_lt : K' * (Real.sqrt d * dist x a) ^ alpha < ε / 3 := by
        have h_base_nonneg : 0 ≤ Real.sqrt d * dist x a :=
          mul_nonneg (Real.sqrt_nonneg _) dist_nonneg
        have h_base_le : Real.sqrt d * dist x a ≤ Real.sqrt d * η :=
          mul_le_mul_of_nonneg_left (le_of_lt hadist) (Real.sqrt_nonneg _)
        have h_rpow_le : (Real.sqrt d * dist x a) ^ alpha ≤ (Real.sqrt d * η) ^ alpha :=
          Real.rpow_le_rpow h_base_nonneg h_base_le halpha.le
        have h_mul_le : K' * (Real.sqrt d * dist x a) ^ alpha ≤ K' * (Real.sqrt d * η) ^ alpha :=
          mul_le_mul_of_nonneg_left h_rpow_le hK'_nonneg
        linarith
      linarith
    rcases hAconv a haA with ⟨la, hla⟩
    have h_cauchy_a : CauchySeq (fun n => Un n a) := hla.cauchySeq
    rw [Metric.cauchySeq_iff] at h_cauchy_a
    rcases h_cauchy_a (ε / 3) (by linarith) with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    calc
      |Un m x - Un n x| ≤ |Un m x - Un m a| + |Un m a - Un n a| + |Un n a - Un n x| := h_triangle m n
      _ < ε / 3 + ε / 3 + ε / 3 := by
        have hNabs : |Un m a - Un n a| < ε / 3 := by
          simpa [Real.dist_eq] using hN m hm n hn
        have h_last : |Un n a - Un n x| < ε / 3 := by
          simpa [abs_sub_comm] using h_bound_xa n
        nlinarith [h_bound_xa m, h_last, hNabs]
      _ = ε := by ring
  rcases cauchySeq_tendsto_of_complete h_cauchy with ⟨l, hl⟩
  exact ⟨l, hl⟩

/-- Consumer (compiled from the holes): passage of uniform global `C^α` bounds of continuous
representatives to the `L²` limit on the killed cube. -/
theorem aux_lem_goodext_holder_limit {d : ℕ} (Qc : SpatialCoordinates d) {Qs : ℝ}
    (hQs : 0 < Qs) (alpha K : ℝ) (halpha : 0 < alpha)
    (un : ℕ → DomainL2 (centeredCube Qc Qs hQs)) (u : DomainL2 (centeredCube Qc Qs hQs))
    (hconv : Tendsto un atTop (𝓝 u))
    (Un : ℕ → SpatialCoordinates d → ℝ)
    (hcont : ∀ n, ContinuousOn (Un n)
      (closure (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))))
    (hae : ∀ n, (un n : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))] Un n)
    (hzero : ∀ n, ∀ x ∈ frontier (centeredCube Qc Qs hQs : Set (SpatialCoordinates d)),
      Un n x = 0)
    (hhol : ∀ n, Lane4.IsHolderOn alpha
      (closure (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))) (Un n))
    (hnorm : ∀ n, Lane4.cAlphaNorm alpha
      (closure (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))) (Un n) ≤ K) :
    ∃ U : SpatialCoordinates d → ℝ,
      ContinuousOn U (closure (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))) ∧
      ((u : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))] U) ∧
      (∀ x ∈ frontier (centeredCube Qc Qs hQs : Set (SpatialCoordinates d)), U x = 0) ∧
      Lane4.IsHolderOn alpha
        (closure (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))) U ∧
      Lane4.cAlphaNorm alpha
        (closure (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))) U ≤ 2 * K := by
  set Q : Set (SpatialCoordinates d) := (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))
    with hQdef
  set S : Set (SpatialCoordinates d) := closure Q with hSdef
  have hQopen : IsOpen Q := (centeredCube Qc Qs hQs).isOpen
  have hQball : Q = Metric.ball Qc (Qs / 2) := rfl
  have hScpt : IsCompact S := by
    rw [hSdef, hQball]
    exact Metric.isBounded_ball.isCompact_closure
  have hpt : ∀ n, 0 ≤ K ∧ (∀ x ∈ S, |Un n x| ≤ K) ∧
      ∀ x ∈ S, ∀ y ∈ S,
        |Un n x - Un n y| ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
    fun n => aux_lem_goodext_pointwise_of_cAlpha alpha K halpha S hScpt (Un n) (hcont n)
      (hhol n) (hnorm n)
  have hK0 : 0 ≤ K := (hpt 0).1
  obtain ⟨ns, -, hns⟩ := aux_lem_goodext_L2_subseq_ae (centeredCube Qc Qs hQs) un u hconv
  have haeall : ∀ᵐ x ∂(volume.restrict Q), ∀ n,
      (un n : SpatialCoordinates d → ℝ) x = Un n x := ae_all_iff.2 hae
  set A : Set (SpatialCoordinates d) :=
    {x | (∀ n, (un n : SpatialCoordinates d → ℝ) x = Un n x) ∧
      Tendsto (fun i => (un (ns i) : SpatialCoordinates d → ℝ) x) atTop
        (𝓝 ((u : SpatialCoordinates d → ℝ) x))} with hAdef
  have hAae : ∀ᵐ x ∂(volume.restrict Q), x ∈ A := by
    filter_upwards [haeall, hns] with x hx1 hx2
    exact ⟨hx1, hx2⟩
  have hAconv : ∀ a ∈ A, Tendsto (fun i => Un (ns i) a) atTop
      (𝓝 ((u : SpatialCoordinates d → ℝ) a)) := by
    intro a ha
    have hfun : (fun i => (un (ns i) : SpatialCoordinates d → ℝ) a) =
        (fun i => Un (ns i) a) := funext fun i => ha.1 (ns i)
    rw [← hfun]
    exact ha.2
  have hclos : S ⊆ closure (A ∩ Q) :=
    aux_lem_goodext_closure_subset_of_ae Q hQopen A hAae
  have hAQS : A ∩ Q ⊆ S := fun x hx => subset_closure hx.2
  have hlim : ∀ x ∈ S, ∃ l : ℝ, Tendsto (fun i => Un (ns i) x) atTop (𝓝 l) :=
    aux_lem_goodext_tendsto_of_dense alpha K halpha S (A ∩ Q) hclos hAQS
      (fun i => Un (ns i)) (fun i => (hpt (ns i)).2.2)
      (fun a ha => ⟨_, hAconv a ha.1⟩)
  set U : SpatialCoordinates d → ℝ := fun x => limUnder atTop (fun i => Un (ns i) x) with hUdef
  have hUlim : ∀ x ∈ S, Tendsto (fun i => Un (ns i) x) atTop (𝓝 (U x)) :=
    fun x hx => tendsto_nhds_limUnder (hlim x hx)
  have hUsup : ∀ x ∈ S, |U x| ≤ K := by
    intro x hx
    exact le_of_tendsto ((hUlim x hx).abs) (Eventually.of_forall fun i => (hpt (ns i)).2.1 x hx)
  have hUdiff : ∀ x ∈ S, ∀ y ∈ S,
      |U x - U y| ≤ K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
    intro x hx y hy
    exact le_of_tendsto (((hUlim x hx).sub (hUlim y hy)).abs)
      (Eventually.of_forall fun i => (hpt (ns i)).2.2 x hx y hy)
  obtain ⟨hUhol, hUnorm⟩ := aux_lem_goodext_cAlpha_of_pointwise alpha K hK0 S U hUsup hUdiff
  refine ⟨U, aux_lem_goodext_continuousOn_of_holder alpha K halpha S U hUdiff, ?_, ?_,
    hUhol, hUnorm⟩
  · filter_upwards [hAae, ae_restrict_mem hQopen.measurableSet] with x hx hxQ
    exact tendsto_nhds_unique (hAconv x hx) (hUlim x (subset_closure hxQ))
  · intro x hx
    have hxS : x ∈ S := frontier_subset_closure hx
    have h0 : Tendsto (fun i => Un (ns i) x) atTop (𝓝 0) := by
      have hfun : (fun i => Un (ns i) x) = fun _ => (0 : ℝ) :=
        funext fun i => hzero (ns i) x hx
      rw [hfun]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hUlim x hxS) h0

end Paper
