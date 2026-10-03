module

public import SubdiffusiveProcess.Lane2.BoundaryResponse

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess

namespace Paper

lemma aux_lem_finite_trace_holder_beta_bound_holderRatio_const_sub
    {d : ℕ} (gamma : ℝ) (S : Set (SpatialCoordinates d))
    (G : SpatialCoordinates d → ℝ) (c : ℝ) :
    Lane4.holderRatioSet gamma S (fun x => G x - c) =
      Lane4.holderRatioSet gamma S G := by
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    congr 1
    ring_nf
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    congr 1
    ring_nf

lemma aux_lem_finite_trace_holder_beta_bound_cAlphaNorm_nonneg
    {d : ℕ} (gamma : ℝ) (S : Set (SpatialCoordinates d))
    (F : SpatialCoordinates d → ℝ) :
    0 ≤ Lane4.cAlphaNorm gamma S F := by
  unfold Lane4.cAlphaNorm
  apply add_nonneg
  · apply Real.sSup_nonneg
    intro v hv
    rcases hv with ⟨x, hx, rfl⟩
    exact abs_nonneg _
  · apply Real.sSup_nonneg
    intro v hv
    rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
    exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

lemma aux_lem_finite_trace_holder_beta_bound_diameter
    (d : ℕ) (S : Set (SpatialCoordinates d))
    (hS : ∀ x ∈ S, ‖x‖ ≤ (1 / 2 : ℝ))
    {x y : SpatialCoordinates d} (hx : x ∈ S) (hy : y ∈ S) :
    Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤ Real.sqrt (d : ℝ) := by
  have hcoord : ∀ i : Fin d, |x i - y i| ≤ (1 : ℝ) := by
    intro i
    have hxi : |x i| ≤ (1 / 2 : ℝ) := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans (hS x hx)
    have hyi : |y i| ≤ (1 / 2 : ℝ) := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y i).trans (hS y hy)
    calc
      |x i - y i| ≤ |x i - 0| + |0 - y i| := abs_sub_le (x i) 0 (y i)
      _ = |x i| + |y i| := by simp
      _ ≤ 1 := by linarith
  have hsum : (∑ i : Fin d, (x i - y i) ^ 2) ≤ (d : ℝ) := by
    calc
      (∑ i : Fin d, (x i - y i) ^ 2) ≤
          ∑ i : Fin d, (1 : ℝ) ^ 2 := by
        exact Finset.sum_le_sum fun i _ => by
          have hi := hcoord i
          simpa only [sq_abs, one_pow] using
            (sq_le_sq₀ (abs_nonneg (x i - y i)) (by norm_num)).2 hi
      _ = (d : ℝ) := by simp
  exact Real.sqrt_le_sqrt hsum

lemma aux_lem_finite_trace_holder_beta_bound_holder_mono
    (d : ℕ) (hd : 2 ≤ d) (beta alpha : ℝ) (hba : beta < alpha)
    (S : Set (SpatialCoordinates d)) (G : SpatialCoordinates d → ℝ)
    (hS : ∀ x ∈ S, ‖x‖ ≤ (1 / 2 : ℝ))
    (hholder : BddAbove (Lane4.holderRatioSet alpha S G))
    (hsemi : Lane4.holderSeminorm alpha S G < 2) :
    BddAbove (Lane4.holderRatioSet beta S G) ∧
      Lane4.holderSeminorm beta S G ≤
        2 * (Real.sqrt (d : ℝ)) ^ (alpha - beta) := by
  have hdelta : 0 ≤ alpha - beta := by linarith
  let D : ℝ := Real.sqrt (d : ℝ)
  let K : ℝ := 2 * D ^ (alpha - beta)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Real.sqrt_nonneg _
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hsemi_nonneg : 0 ≤ Lane4.holderSeminorm alpha S G := by
    unfold Lane4.holderSeminorm
    apply Real.sSup_nonneg
    intro v hv
    rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
    exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  have hpoint : ∀ v ∈ Lane4.holderRatioSet beta S G, v ≤ K := by
    intro v hv
    rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
    let r : ℝ := Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)
    have hr : 0 < r := by
      dsimp [r]
      apply Real.sqrt_pos.mpr
      have hne : ∃ i : Fin d, x i - y i ≠ 0 := by
        by_contra h
        apply hxy
        funext i
        have hi : x i - y i = 0 := by
          by_contra hi
          exact h ⟨i, hi⟩
        linarith
      rcases hne with ⟨i, hi⟩
      have hnonneg : ∀ j : Fin d, 0 ≤ (x j - y j) ^ 2 := fun j => sq_nonneg _
      have hpos : 0 < (x i - y i) ^ 2 := sq_pos_of_ne_zero hi
      have hsumpos : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
        apply (Finset.sum_pos_iff_of_nonneg (fun j _ => hnonneg j)).2
        exact ⟨i, Finset.mem_univ _, hpos⟩
      exact hsumpos
    have hrD : r ≤ D := by
      dsimp [r, D]
      exact aux_lem_finite_trace_holder_beta_bound_diameter d S hS hx hy
    have hralpha :
        |G x - G y| / r ^ alpha ≤ Lane4.holderSeminorm alpha S G := by
      apply le_csSup hholder
      exact ⟨x, hx, y, hy, hxy, rfl⟩
    have hpow : r ^ (alpha - beta) ≤ D ^ (alpha - beta) := by
      exact Real.rpow_le_rpow (le_of_lt hr) hrD hdelta
    have hidentity :
        |G x - G y| / r ^ beta =
          (|G x - G y| / r ^ alpha) * r ^ (alpha - beta) := by
      rw [Real.rpow_sub hr alpha beta]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hr alpha),
        ne_of_gt (Real.rpow_pos_of_pos hr beta)]
    rw [hidentity]
    have hprod := mul_le_mul hralpha hpow (Real.rpow_nonneg (le_of_lt hr) _)
      hsemi_nonneg
    have hprod' := hprod.trans (mul_le_mul_of_nonneg_right hsemi.le
      (Real.rpow_nonneg hD (alpha - beta)))
    exact hprod'
  have hBdd : BddAbove (Lane4.holderRatioSet beta S G) := ⟨K, hpoint⟩
  refine ⟨hBdd, ?_⟩
  unfold Lane4.holderSeminorm
  exact Real.sSup_le hpoint hK



theorem lem_finite_trace_holder_beta_bound
    (d : ℕ) (hd : 2 ≤ d)
    (beta alpha : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧
      (∀ g : SpatialCoordinates d → ℝ,
        IsCellBoundaryClass alpha 0 1 g → cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 →
    IsCellBoundaryClass beta 0 1 g ∧ cellBoundaryQuotientNorm beta 0 1 g ≤ C) := by
  classical
  let S : Set (SpatialCoordinates d) :=
    frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))
  let D : ℝ := Real.sqrt (d : ℝ)
  let C : ℝ := 2 + 2 * D ^ (alpha - beta)
  have hdelta : 0 ≤ alpha - beta := by linarith
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Real.sqrt_nonneg _
  have hC : 0 < C := by
    dsimp [C]
    have : 0 ≤ (Real.sqrt (d : ℝ)) ^ (alpha - beta) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    linarith
  refine ⟨C, hC, ?_⟩
  intro g hgα hgNorm
  let G : SpatialCoordinates d → ℝ := rescaledDatum 0 1 g
  have hSsub : S ⊆ (closedCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) := by
    dsimp [S]
    have hclosed : IsClosed (closedCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) :=
      (closedCube (0 : SpatialCoordinates d) 1 one_pos).isCompact.isClosed
    exact frontier_subset_closure.trans
      (hclosed.closure_subset_iff.mpr (centeredCube_subset_closedCube 0 one_pos))
  have hSbound : ∀ x ∈ S, ‖x‖ ≤ (1 / 2 : ℝ) := by
    intro x hx
    have hx' := hSsub hx
    change dist x (0 : SpatialCoordinates d) ≤ (1 : ℝ) / 2 at hx'
    simpa only [dist_zero_right] using hx'
  have hgα' :
      Lane4.IsHolderOn alpha S G ∧
        BddAbove {v : ℝ | ∃ x ∈ S, v = |G x|} := by
    simpa only [S, G, IsCellBoundaryClass] using hgα
  have hqαset :
      ({v : ℝ | ∃ c : ℝ, v = Lane4.cAlphaNorm alpha S
        (fun x => G x - c)} : Set ℝ).Nonempty := by
    exact ⟨Lane4.cAlphaNorm alpha S (fun x => G x - 0), 0, rfl⟩
  have hqαlt :
      SubdiffusiveProcess.quotientCBetaNorm alpha S G < 2 := by
    have hnorm' : SubdiffusiveProcess.quotientCBetaNorm alpha S G ≤ 1 := by
      simpa only [cellBoundaryQuotientNorm, quotientCBetaNorm, S, G] using hgNorm
    have hlt : SubdiffusiveProcess.quotientCBetaNorm alpha S G < 2 :=
      lt_of_le_of_lt hnorm' (by norm_num)
    exact hlt
  have hchoose : ∃ c : ℝ,
      Lane4.cAlphaNorm alpha S (fun x => G x - c) < 2 := by
    unfold SubdiffusiveProcess.quotientCBetaNorm at hqαlt
    obtain ⟨v, ⟨c, rfl⟩, hv⟩ :=
      exists_lt_of_csInf_lt hqαset hqαlt
    exact ⟨c, hv⟩
  obtain ⟨c, hc⟩ := hchoose
  have hratioShiftα :
      Lane4.holderRatioSet alpha S (fun x => G x - c) =
        Lane4.holderRatioSet alpha S G :=
    aux_lem_finite_trace_holder_beta_bound_holderRatio_const_sub alpha S G c
  have hholderα : BddAbove (Lane4.holderRatioSet alpha S G) := hgα'.1
  have hsemiShiftα :
      Lane4.holderSeminorm alpha S (fun x => G x - c) < 2 := by
    have hnonneg :
        0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |G x - c|} := by
      apply Real.sSup_nonneg
      intro v hv
      rcases hv with ⟨x, hx, rfl⟩
      exact abs_nonneg _
    have hnonneg' :
        0 ≤ Lane4.holderSeminorm alpha S (fun x => G x - c) := by
      unfold Lane4.holderSeminorm
      apply Real.sSup_nonneg
      intro v hv
      rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
      exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    have : sSup {v : ℝ | ∃ x ∈ S, v = |G x - c|} +
        Lane4.holderSeminorm alpha S (fun x => G x - c) < 2 := by
      simpa only [Lane4.cAlphaNorm] using hc
    linarith
  have hsemiα : Lane4.holderSeminorm alpha S G < 2 := by
    simpa only [Lane4.holderSeminorm, hratioShiftα] using hsemiShiftα
  obtain ⟨hholderβ, hsemiβ⟩ :=
    aux_lem_finite_trace_holder_beta_bound_holder_mono d hd beta alpha hba S G
      hSbound hholderα hsemiα
  have hratioShiftβ :
      Lane4.holderRatioSet beta S (fun x => G x - c) =
        Lane4.holderRatioSet beta S G :=
    aux_lem_finite_trace_holder_beta_bound_holderRatio_const_sub beta S G c
  have hsemiShiftβ :
      Lane4.holderSeminorm beta S (fun x => G x - c) ≤
        2 * D ^ (alpha - beta) := by
    simpa only [Lane4.holderSeminorm, hratioShiftβ, D] using hsemiβ
  have hamp : sSup {v : ℝ | ∃ x ∈ S, v = |G x - c|} < 2 := by
    have hnonneg :
        0 ≤ Lane4.holderSeminorm alpha S (fun x => G x - c) := by
      unfold Lane4.holderSeminorm
      apply Real.sSup_nonneg
      intro v hv
      rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
      exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    have : sSup {v : ℝ | ∃ x ∈ S, v = |G x - c|} +
        Lane4.holderSeminorm alpha S (fun x => G x - c) < 2 := by
      simpa only [Lane4.cAlphaNorm] using hc
    linarith
  have hcbeta : Lane4.cAlphaNorm beta S (fun x => G x - c) ≤ C := by
    unfold Lane4.cAlphaNorm
    dsimp [C]
    exact add_le_add hamp.le hsemiShiftβ
  have hqβbdd : BddBelow
      ({v : ℝ | ∃ c : ℝ, v = Lane4.cAlphaNorm beta S
        (fun x => G x - c)} : Set ℝ) := by
    refine ⟨0, ?_⟩
    intro v hv
    rcases hv with ⟨c', rfl⟩
    exact aux_lem_finite_trace_holder_beta_bound_cAlphaNorm_nonneg beta S
      (fun x => G x - c')
  have hqβ : SubdiffusiveProcess.quotientCBetaNorm beta S G ≤ C := by
    unfold SubdiffusiveProcess.quotientCBetaNorm
    exact (csInf_le hqβbdd ⟨c, rfl⟩).trans hcbeta
  refine ⟨?_, ?_⟩
  · constructor
    · exact hholderβ
    · exact hgα'.2
  · simpa only [cellBoundaryQuotientNorm, quotientCBetaNorm, S, G] using hqβ

end Paper
