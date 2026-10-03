module

public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess

namespace Paper

open Set Metric Filter

private def boundarySet (d : ℕ) : Set (SpatialCoordinates d) :=
  frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))

private abbrev boundaryBCF (d : ℕ) :=
  BoundedContinuousFunction (boundarySet d) ℝ

private lemma aux_lem_finite_trace_holder_finite_net_frontier_nonempty
    (d : ℕ) (hd : 2 ≤ d) : (boundarySet d).Nonempty := by
  have hdn : 0 < d := lt_of_lt_of_le (by norm_num) hd
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hdn
  refine ⟨fun _ : Fin d => (1 / 2 : ℝ), ?_⟩
  change (fun _ : Fin d => (1 / 2 : ℝ)) ∈
    frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
  rw [frontier_ball (0 : SpatialCoordinates d) (by norm_num)]
  rw [Metric.mem_sphere]
  simp +instances [dist_pi_const]

private lemma aux_lem_finite_trace_holder_finite_net_frontier_compact
    (d : ℕ) : IsCompact (boundarySet d) := by
  change IsCompact (frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2)))
  rw [frontier_ball (0 : SpatialCoordinates d) (by norm_num)]
  exact isCompact_sphere 0 (1 / 2)

private lemma aux_lem_finite_trace_holder_finite_net_boundary_dist_le_one
    (d : ℕ) {x : SpatialCoordinates d} (hx : x ∈ boundarySet d) :
    dist x 0 ≤ 1 := by
  change x ∈ frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) at hx
  rw [frontier_ball (0 : SpatialCoordinates d) (by norm_num), Metric.mem_sphere] at hx
  linarith

private lemma aux_lem_finite_trace_holder_finite_net_euclidean_le
    (d : ℕ) (x y : SpatialCoordinates d) :
    Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤ (d : ℝ) * dist x y := by
  have hsq :
      (∑ i : Fin d, |x i - y i| ^ 2) ≤ (∑ i : Fin d, |x i - y i|) ^ 2 := by
    simpa using!
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i : Fin d => |x i - y i|)
        (by intro i hi; exact abs_nonneg _))
  have hsqrt :
      Real.sqrt (∑ i : Fin d, |x i - y i| ^ 2) ≤
        Real.sqrt ((∑ i : Fin d, |x i - y i|) ^ 2) :=
    Real.sqrt_le_sqrt hsq
  have hsum : 0 ≤ ∑ i : Fin d, |x i - y i| :=
    Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
  have hnorm := Pi.sum_norm_apply_le_norm
    (G := fun _ : Fin d => ℝ) (x - y : SpatialCoordinates d)
  have hnorm' : ∑ i : Fin d, |x i - y i| ≤ (d : ℝ) * ‖x - y‖ := by
    calc
      ∑ i : Fin d, |x i - y i| = ∑ i : Fin d, ‖x i - y i‖ := by
        simp +instances only [Real.norm_eq_abs]
      _ = ∑ i : Fin d, ‖(x - y) i‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ ≤ (d : ℝ) * ‖x - y‖ := by
        simpa only [Fintype.card_fin, nsmul_eq_mul] using! hnorm
  calc
    Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) =
        Real.sqrt (∑ i : Fin d, |x i - y i| ^ 2) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [sq_abs]
    _ ≤ Real.sqrt ((∑ i : Fin d, |x i - y i|) ^ 2) := hsqrt
    _ = ∑ i : Fin d, |x i - y i| := Real.sqrt_sq hsum
    _ ≤ (d : ℝ) * dist x y := by
      simpa only [dist_eq_norm] using! hnorm'

private lemma aux_lem_finite_trace_holder_finite_net_bddAbove_abs_sub_const
    {d : ℕ} {S : Set (SpatialCoordinates d)} {g : SpatialCoordinates d → ℝ}
    (hg : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|}) (c : ℝ) :
    BddAbove {v : ℝ | ∃ x ∈ S, v = |g x - c|} := by
  rcases hg with ⟨M, hM⟩
  refine ⟨M + |c|, ?_⟩
  intro v hv
  rcases hv with ⟨x, hx, rfl⟩
  exact (abs_sub _ _).trans (add_le_add (hM ⟨x, hx, rfl⟩) le_rfl)

private lemma aux_lem_finite_trace_holder_finite_net_bddAbove_abs_sub
    {d : ℕ} {S : Set (SpatialCoordinates d)}
    {g h : SpatialCoordinates d → ℝ}
    (hg : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|})
    (hh : BddAbove {v : ℝ | ∃ x ∈ S, v = |h x|}) :
    BddAbove {v : ℝ | ∃ x ∈ S, v = |g x - h x|} := by
  rcases hg with ⟨M, hM⟩
  rcases hh with ⟨N, hN⟩
  refine ⟨M + N, ?_⟩
  intro v hv
  rcases hv with ⟨x, hx, rfl⟩
  exact (abs_sub _ _).trans (add_le_add (hM ⟨x, hx, rfl⟩) (hN ⟨x, hx, rfl⟩))

private lemma aux_lem_finite_trace_holder_finite_net_sSup_nonneg
    {s : Set ℝ} (hs : BddAbove s) (hpos : ∀ x ∈ s, 0 ≤ x) : 0 ≤ sSup s := by
  by_cases hne : s.Nonempty
  · rcases hne with ⟨x, hx⟩
    exact (hpos x hx).trans (le_csSup hs hx)
  · simpa [Set.not_nonempty_iff_eq_empty.mp hne]

private lemma aux_lem_finite_trace_holder_finite_net_sSup_le
    {s : Set ℝ} {a : ℝ} (hs : BddAbove s)
    (ha : ∀ x ∈ s, x ≤ a) (ha0 : 0 ≤ a) : sSup s ≤ a := by
  by_cases hne : s.Nonempty
  · exact csSup_le hne ha
  · simpa [Set.not_nonempty_iff_eq_empty.mp hne] using! ha0

private lemma aux_lem_finite_trace_holder_finite_net_cAlpha_nonneg
    {d : ℕ} {alpha : ℝ} {S : Set (SpatialCoordinates d)}
    (hS : S.Nonempty) (g : SpatialCoordinates d → ℝ)
    (hgb : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|})
    (hgh : BddAbove (Lane4.holderRatioSet alpha S g)) :
    0 ≤ Lane4.cAlphaNorm alpha S g := by
  unfold Lane4.cAlphaNorm
  have h₁ : 0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |g x|} := by
    rcases hS with ⟨x, hx⟩
    exact (abs_nonneg (g x)).trans (le_csSup hgb ⟨x, hx, rfl⟩)
  have h₂ : 0 ≤ Lane4.holderSeminorm alpha S g := by
    unfold Lane4.holderSeminorm
    exact aux_lem_finite_trace_holder_finite_net_sSup_nonneg hgh
      (by
        intro v hv
        rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
        exact div_nonneg (abs_nonneg _)
          (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
  linarith

private lemma aux_lem_finite_trace_holder_finite_net_holderSeminorm_sub_const
    {d : ℕ} {alpha : ℝ} {S : Set (SpatialCoordinates d)}
    (g : SpatialCoordinates d → ℝ) (c : ℝ) :
    Lane4.holderSeminorm alpha S (fun x => g x - c) =
      Lane4.holderSeminorm alpha S g := by
  unfold Lane4.holderSeminorm Lane4.holderRatioSet
  congr 1
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hv⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    rw [show (g x - c) - (g y - c) = g x - g y by ring] at hv
    exact hv
  · rintro ⟨x, hx, y, hy, hxy, hv⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    rw [show (g x - c) - (g y - c) = g x - g y by ring]
    exact hv

private lemma aux_lem_finite_trace_holder_finite_net_holderRatioSet_sub_const
    {d : ℕ} {alpha : ℝ} {S : Set (SpatialCoordinates d)}
    (g : SpatialCoordinates d → ℝ) (c : ℝ) :
    Lane4.holderRatioSet alpha S (fun x => g x - c) =
      Lane4.holderRatioSet alpha S g := by
  unfold Lane4.holderRatioSet
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, hxy, hv⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    rw [show (g x - c) - (g y - c) = g x - g y by ring] at hv
    exact hv
  · rintro ⟨x, hx, y, hy, hxy, hv⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    rw [show (g x - c) - (g y - c) = g x - g y by ring]
    exact hv

private lemma aux_lem_finite_trace_holder_finite_net_sSup_abs_nonneg
    {d : ℕ} {S : Set (SpatialCoordinates d)} (hS : S.Nonempty)
    {f : SpatialCoordinates d → ℝ}
    (hf : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|}) :
    0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} := by
  rcases hS with ⟨x, hx⟩
  exact (abs_nonneg (f x)).trans (le_csSup hf ⟨x, hx, rfl⟩)

private lemma aux_lem_finite_trace_holder_finite_net_holder_le_quotient
    (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (g : SpatialCoordinates d → ℝ)
    (hg : IsCellBoundaryClass alpha 0 1 g) :
    Lane4.holderSeminorm alpha (boundarySet d) g ≤
      cellBoundaryQuotientNorm alpha 0 1 g := by
  have hS : (boundarySet d).Nonempty :=
    aux_lem_finite_trace_holder_finite_net_frontier_nonempty d hd
  have hres : rescaledDatum (0 : SpatialCoordinates d) 1 g = g := by
    funext x
    simp +instances [rescaledDatum]
  have hg' : Lane4.IsHolderOn alpha (boundarySet d) g ∧
      BddAbove {v : ℝ | ∃ x ∈ boundarySet d, v = |g x|} := by
    have hg0 := hg
    unfold IsCellBoundaryClass at hg0
    rw [hres] at hg0
    simpa only [boundarySet] using! hg0
  let T : Set ℝ := {v : ℝ | ∃ c : ℝ,
    v = Lane4.cAlphaNorm alpha (boundarySet d) (fun x => g x - c)}
  have hT : T.Nonempty := by
    refine ⟨Lane4.cAlphaNorm alpha (boundarySet d) g, ?_⟩
    exact ⟨0, by simp⟩
  have hlower : ∀ v ∈ T, Lane4.holderSeminorm alpha (boundarySet d) g ≤ v := by
    intro v hv
    rcases hv with ⟨c, rfl⟩
    have habs : 0 ≤ sSup {v : ℝ | ∃ x ∈ boundarySet d, v = |g x - c|} :=
      aux_lem_finite_trace_holder_finite_net_sSup_abs_nonneg hS
        (aux_lem_finite_trace_holder_finite_net_bddAbove_abs_sub_const hg'.2 c)
    rw [← aux_lem_finite_trace_holder_finite_net_holderSeminorm_sub_const g c]
    unfold Lane4.cAlphaNorm
    linarith
  have hq : Lane4.holderSeminorm alpha (boundarySet d) g ≤ sInf T :=
    le_csInf hT hlower
  simpa [T, cellBoundaryQuotientNorm, quotientCBetaNorm, rescaledDatum] using! hq

private lemma aux_lem_finite_trace_holder_finite_net_ratio_le_one
    (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (g : SpatialCoordinates d → ℝ)
    (hg : IsCellBoundaryClass alpha 0 1 g)
    (hgn : cellBoundaryQuotientNorm alpha 0 1 g ≤ 1) :
    ∀ x ∈ boundarySet d, ∀ y ∈ boundarySet d,
      |g x - g y| /
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha ≤ 1 := by
  have hres : rescaledDatum (0 : SpatialCoordinates d) 1 g = g := by
    funext x
    simp +instances [rescaledDatum]
  have hg' := hg
  unfold IsCellBoundaryClass at hg'
  rw [hres] at hg'
  have hH := aux_lem_finite_trace_holder_finite_net_holder_le_quotient d hd alpha g hg
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simp +instances only [sub_self, abs_zero, zero_div]
    norm_num
  · exact (le_csSup hg'.1 ⟨x, hx, y, hy, hxy, rfl⟩).trans (hH.trans hgn)

private lemma aux_lem_finite_trace_holder_finite_net_euclidean_holder
    (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (g : SpatialCoordinates d → ℝ)
    (hg : IsCellBoundaryClass alpha 0 1 g)
    (hgn : cellBoundaryQuotientNorm alpha 0 1 g ≤ 1) :
    ∀ x ∈ boundarySet d, ∀ y ∈ boundarySet d,
      |g x - g y| ≤
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
  have hratio := aux_lem_finite_trace_holder_finite_net_ratio_le_one d hd alpha g hg hgn
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simp +instances only [sub_self, abs_zero]
    exact Real.rpow_nonneg (by positivity) alpha
  · have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
      apply Finset.sum_pos'
      · intro j hj
        exact sq_nonneg _
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
        exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩
    have hden : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.rpow_pos_of_pos (Real.sqrt_pos.2 hsum) alpha
    simpa using! (div_le_iff₀ hden).mp (hratio x hx y hy)

private lemma aux_lem_finite_trace_holder_finite_net_choose_scale
    {q e : ℝ} (hq : 0 < q) (he : 0 < e) :
    ∃ t : ℝ, 0 < t ∧ 2 * t ^ q < e := by
  have hlim : Tendsto (fun t : ℝ => 2 * |t| ^ q) (nhds 0) (nhds 0) := by
    have hpow : Tendsto (fun t : ℝ => |t| ^ q) (nhds 0) (nhds 0) := by
      have h := (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto
      have habs : Tendsto abs (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
        simpa using! (continuous_abs.continuousAt.tendsto :
          Tendsto abs (nhds (0 : ℝ)) (nhds (abs (0 : ℝ))))
      simpa [Real.zero_rpow hq.ne'] using! h.comp habs
    simpa using! tendsto_const_nhds.mul hpow
  rcases Metric.mem_nhds_iff.mp (hlim (Iio_mem_nhds he)) with ⟨δ, hδ, hδsub⟩
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  have hmem : δ / 2 ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  have := hδsub hmem
  simpa [abs_of_pos (half_pos hδ)] using! this

private lemma aux_lem_finite_trace_holder_finite_net_holder_bound
    (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (halpha : 0 < alpha)
    (g : SpatialCoordinates d → ℝ)
    (hg : IsCellBoundaryClass alpha 0 1 g)
    (hgn : cellBoundaryQuotientNorm alpha 0 1 g ≤ 1) :
    ∀ x ∈ boundarySet d, ∀ y ∈ boundarySet d,
      |g x - g y| ≤ (d : ℝ) ^ alpha * (dist x y) ^ alpha := by
  have hratio := aux_lem_finite_trace_holder_finite_net_ratio_le_one
    d hd alpha g hg hgn
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simp +instances [halpha.ne']
  · have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
      apply Finset.sum_pos'
      · intro j hj
        exact sq_nonneg _
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
        exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩
    have hden : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.rpow_pos_of_pos (Real.sqrt_pos.2 hsum) alpha
    have hnum : |g x - g y| ≤
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
      simpa using! (div_le_iff₀ hden).mp (hratio x hx y hy)
    have hdist := aux_lem_finite_trace_holder_finite_net_euclidean_le d x y
    have hpow := Real.rpow_le_rpow (Real.sqrt_nonneg _) hdist halpha.le
    calc
      |g x - g y| ≤
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := hnum
      _ ≤ ((d : ℝ) * dist x y) ^ alpha := hpow
      _ = (d : ℝ) ^ alpha * (dist x y) ^ alpha := by
        rw [Real.mul_rpow (Nat.cast_nonneg d) (dist_nonneg)]

private lemma aux_lem_finite_trace_holder_finite_net_holderOnWith
    (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (halpha : 0 < alpha)
    (g : SpatialCoordinates d → ℝ)
    (hg : IsCellBoundaryClass alpha 0 1 g)
    (hgn : cellBoundaryQuotientNorm alpha 0 1 g ≤ 1) :
    HolderOnWith ⟨(d : ℝ) ^ alpha, Real.rpow_nonneg (Nat.cast_nonneg d) alpha⟩
      ⟨alpha, halpha.le⟩ g (boundarySet d) := by
  suffices hout : HolderOnWith (NNReal.mk ((d : ℝ)^alpha) (Real.rpow_nonneg (Nat.cast_nonneg d) alpha)) (NNReal.mk alpha halpha.le) g (boundarySet d) by exact hout
  intro x hx y hy
  have hb := aux_lem_finite_trace_holder_finite_net_holder_bound
    d hd alpha halpha g hg hgn x hx y hy
  rw [edist_dist, edist_dist]
  have hc : (↑(NNReal.mk ((d : ℝ)^alpha) (Real.rpow_nonneg (Nat.cast_nonneg d) alpha)) : ENNReal) = ENNReal.ofReal ((d : ℝ)^alpha) := by
    exact ENNReal.coe_nnreal_eq _
  have hr : (↑(NNReal.mk alpha halpha.le) : ℝ) = alpha := rfl
  rw [hc, hr, Real.dist_eq]
  rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) halpha.le]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg d) alpha)]
  exact ENNReal.ofReal_le_ofReal hb

private lemma aux_lem_finite_trace_holder_finite_net_uniform_net
    (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (halpha : 0 < alpha)
    (x₀ : boundarySet d) (eta : ℝ) (heta : 0 < eta) :
    ∃ Gs : Finset (SpatialCoordinates d → ℝ),
      (∀ h ∈ Gs, IsCellBoundaryClass alpha 0 1 h ∧
        cellBoundaryQuotientNorm alpha 0 1 h ≤ 1) ∧
      (∀ g : SpatialCoordinates d → ℝ,
        IsCellBoundaryClass alpha 0 1 g → cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 →
          ∃ h ∈ Gs, ∀ x : boundarySet d,
            |(g x - g x₀) - (h x - h x₀)| < eta) := by
  classical
  letI : CompactSpace (boundarySet d) :=
    isCompact_iff_compactSpace.mp
      (aux_lem_finite_trace_holder_finite_net_frontier_compact d)
  let A : Set (boundaryBCF d) := {f | ∃ g : SpatialCoordinates d → ℝ,
    IsCellBoundaryClass alpha 0 1 g ∧
      cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 ∧
      ∀ x : boundarySet d, f x = g x - g x₀}
  let B : ℝ := (d : ℝ) ^ alpha * (2 : ℝ) ^ alpha
  have hpoint : ∀ (f : boundaryBCF d) (x : boundarySet d), f ∈ A → f x ∈ Set.Icc (-B) B := by
    intro f x hf
    rcases hf with ⟨g, hg, hgn, hfg⟩
    have hb := aux_lem_finite_trace_holder_finite_net_holder_bound
      d hd alpha halpha g hg hgn x x.property x₀ x₀.property
    have hdist : dist (x : SpatialCoordinates d) (x₀ : SpatialCoordinates d) ≤ 2 := by
      calc
        dist (x : SpatialCoordinates d) (x₀ : SpatialCoordinates d) ≤
            dist (x : SpatialCoordinates d) 0 + dist 0 (x₀ : SpatialCoordinates d) :=
          dist_triangle _ _ _
        _ = dist (x : SpatialCoordinates d) 0 + dist (x₀ : SpatialCoordinates d) 0 := by
          rw [dist_comm 0]
        _ ≤ 2 := by
          have hx' := aux_lem_finite_trace_holder_finite_net_boundary_dist_le_one d x.property
          have hx₀' := aux_lem_finite_trace_holder_finite_net_boundary_dist_le_one d x₀.property
          linarith
    have hpow := Real.rpow_le_rpow (dist_nonneg) hdist halpha.le
    have habs : |f x| ≤ B := by
      rw [hfg x]
      calc
        |g (x : SpatialCoordinates d) - g x₀| ≤
            (d : ℝ) ^ alpha * dist (x : SpatialCoordinates d) (x₀ : SpatialCoordinates d) ^ alpha := hb
        _ ≤ (d : ℝ) ^ alpha * (2 : ℝ) ^ alpha := by gcongr
    exact abs_le.mp habs
  have hmod_lim : Tendsto (fun t : ℝ => (d : ℝ) ^ alpha * |t| ^ alpha)
      (nhds 0) (nhds 0) := by
    have hpow_lim : Tendsto (fun t : ℝ => |t| ^ alpha) (nhds 0) (nhds 0) := by
      have h := (Real.continuousAt_rpow_const 0 alpha (Or.inr halpha.le)).tendsto
      have habs : Tendsto abs (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
        simpa using! (continuous_abs.continuousAt.tendsto :
          Tendsto abs (nhds (0 : ℝ)) (nhds (abs (0 : ℝ))))
      simpa [Real.zero_rpow halpha.ne'] using! h.comp habs
    simpa using! tendsto_const_nhds.mul hpow_lim
  have heq : UniformEquicontinuous (fun f : A => (f : boundarySet d → ℝ)) := by
    apply Metric.uniformEquicontinuous_of_continuity_modulus
      (fun t : ℝ => (d : ℝ) ^ alpha * |t| ^ alpha) hmod_lim
    intro x y f
    rcases f.property with ⟨g, hg, hgn, hfg⟩
    have hb := aux_lem_finite_trace_holder_finite_net_holder_bound
      d hd alpha halpha g hg hgn x x.property y y.property
    calc
      dist ((f : boundaryBCF d) x) ((f : boundaryBCF d) y) =
          |(g x - g x₀) - (g y - g x₀)| := by
        rw [Real.dist_eq, hfg x, hfg y]
      _ = |g x - g y| := by congr 1 <;> ring
      _ ≤ (d : ℝ) ^ alpha * dist x y ^ alpha := hb
      _ = (d : ℝ) ^ alpha * |dist x y| ^ alpha := by
        rw [abs_of_nonneg (dist_nonneg)]
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Set.Icc (-B) B) isCompact_Icc A hpoint heq.equicontinuous
  have hcover : closure A ⊆ ⋃ f ∈ A, Metric.ball f eta := by
    intro f hf
    rcases Metric.mem_closure_iff.1 hf eta heta with ⟨g, hg, hfg⟩
    exact mem_iUnion.2 ⟨g, mem_iUnion.2 ⟨hg, hfg⟩⟩
  obtain ⟨b', hbsub, hbfin, hbcover⟩ :=
    hcompact.elim_finite_subcover_image (b := A) (c := fun f => Metric.ball f eta)
      (fun f hf => isOpen_ball) hcover
  have hchoose : ∀ f : A, ∃ g : SpatialCoordinates d → ℝ,
      IsCellBoundaryClass alpha 0 1 g ∧
        cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 ∧
        ∀ x : boundarySet d, (f : boundaryBCF d) x = g x - g x₀ := by
    intro f
    exact f.property
  choose chooseG hchooseG using hchoose
  let Gs : Finset (SpatialCoordinates d → ℝ) :=
    hbfin.toFinset.attach.image (fun f : ↥hbfin.toFinset =>
      chooseG ⟨f.1, hbsub (hbfin.mem_toFinset.mp f.2)⟩)
  refine ⟨Gs, ?_, ?_⟩
  · intro h hh
    change h ∈ hbfin.toFinset.attach.image (fun f : ↥hbfin.toFinset =>
      chooseG ⟨f.1, hbsub (hbfin.mem_toFinset.mp f.2)⟩) at hh
    rcases Finset.mem_image.mp hh with ⟨f, hf, rfl⟩
    exact ⟨(hchooseG ⟨f.1, hbsub (hbfin.mem_toFinset.mp f.2)⟩).1,
      (hchooseG ⟨f.1, hbsub (hbfin.mem_toFinset.mp f.2)⟩).2.1⟩
  · intro g hg hgn
    let fg : boundaryBCF d :=
      BoundedContinuousFunction.mkOfCompact
        { toFun := (boundarySet d).restrict (fun x => g x - g x₀)
          continuous_toFun := by
            have hH := aux_lem_finite_trace_holder_finite_net_holderOnWith
              d hd alpha halpha g hg hgn
            exact (hH.continuousOn (by exact_mod_cast halpha)).sub continuousOn_const |>.restrict }
    have hfgA : fg ∈ A := by
      refine ⟨g, hg, hgn, ?_⟩
      intro x
      rfl
    have hfgcl : fg ∈ closure A := subset_closure hfgA
    rcases Set.mem_iUnion.mp (hbcover hfgcl) with ⟨f, hf⟩
    rcases Set.mem_iUnion.mp hf with ⟨hfmem, hball⟩
    let h := chooseG ⟨f, hbsub hfmem⟩
    have hh : h ∈ Gs := by
      change h ∈ hbfin.toFinset.attach.image (fun q : ↥hbfin.toFinset =>
        chooseG ⟨q.1, hbsub (hbfin.mem_toFinset.mp q.2)⟩)
      exact Finset.mem_image.mpr ⟨⟨f, hbfin.mem_toFinset.mpr hfmem⟩,
        Finset.mem_attach _ _, rfl⟩
    refine ⟨h, hh, ?_⟩
    rcases hchooseG ⟨f, hbsub hfmem⟩ with ⟨_, _, hfcenter⟩
    intro x
    have hdist :=
      (BoundedContinuousFunction.dist_coe_le_dist (f := fg) (g := f) x).trans_lt hball
    have hfgx : fg x = g x - g x₀ := rfl
    have hfx : (f : boundaryBCF d) x = h x - h x₀ := by simpa [h] using! hfcenter x
    calc
      |(g x - g x₀) - (h x - h x₀)| =
          |fg x - (f : boundaryBCF d) x| := by
            rw [hfgx, hfx]
      _ = dist (fg x) ((f : boundaryBCF d) x) := (Real.dist_eq _ _).symm
      _ < eta := hdist



theorem lem_finite_trace_holder_finite_net
    (d : ℕ) (hd : 2 ≤ d)
    (beta alpha : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ Gs : Finset (SpatialCoordinates d → ℝ),
        (∀ h ∈ Gs, IsCellBoundaryClass alpha 0 1 h ∧
          cellBoundaryQuotientNorm alpha 0 1 h ≤ 1) ∧
        (∀ g : SpatialCoordinates d → ℝ,
          IsCellBoundaryClass alpha 0 1 g → cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 →
            ∃ h ∈ Gs,
              IsCellBoundaryClass beta 0 1 (fun x => g x - h x) ∧
              cellBoundaryQuotientNorm beta 0 1 (fun x => g x - h x) ≤ epsilon) := by
  intro epsilon hepsilon
  have hbeta0 : 0 < beta := lt_trans (by norm_num) hbeta
  have halpha0 : 0 < alpha := lt_trans hbeta0 hba
  have hq : 0 < alpha - beta := sub_pos.mpr hba
  obtain ⟨t, ht, ht_small⟩ :=
    aux_lem_finite_trace_holder_finite_net_choose_scale hq
      (by linarith : 0 < epsilon / 4)
  let eta : ℝ := min (epsilon / 4) (epsilon * t ^ beta / 8)
  have ht_beta : 0 < t ^ beta := Real.rpow_pos_of_pos ht beta
  have heta : 0 < eta := by
    dsimp +instances [eta]
    exact lt_min (by linarith) (div_pos (mul_pos hepsilon ht_beta) (by norm_num))
  have heta_eps : eta ≤ epsilon / 4 := min_le_left _ _
  have heta_tail : eta ≤ epsilon * t ^ beta / 8 := min_le_right _ _
  have hS : (boundarySet d).Nonempty :=
    aux_lem_finite_trace_holder_finite_net_frontier_nonempty d hd
  let x₀ : boundarySet d := ⟨Classical.choose hS, Classical.choose_spec hS⟩
  obtain ⟨Gs, hGs, hnet⟩ :=
    aux_lem_finite_trace_holder_finite_net_uniform_net d hd alpha halpha0 x₀ eta heta
  refine ⟨Gs, hGs, ?_⟩
  intro g hg hgn
  obtain ⟨h, hh, happrox⟩ := hnet g hg hgn
  let k : SpatialCoordinates d → ℝ := fun x => g x - h x
  let c : ℝ := g x₀ - h x₀
  have hnorm : ∀ x : boundarySet d, |k x - c| < eta := by
    intro x
    dsimp +instances [k, c]
    convert happrox x using 1 <;> ring
  have hhc := hGs h hh
  have hratio_beta :
      ∀ x ∈ boundarySet d, ∀ y ∈ boundarySet d,
        |k x - k y| /
            (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤ epsilon / 2 := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      simp +instances [k]
      linarith
    · let r : ℝ := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)
      have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
        apply Finset.sum_pos'
        · intro j hj
          exact sq_nonneg _
        · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
          exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩
      have hr : 0 < r := by
        dsimp +instances [r]
        exact Real.sqrt_pos.2 hsum
      have hrpow_beta : 0 < r ^ beta := Real.rpow_pos_of_pos hr beta
      have hgr := aux_lem_finite_trace_holder_finite_net_euclidean_holder
        d hd alpha g hg hgn x hx y hy
      have hhr := aux_lem_finite_trace_holder_finite_net_euclidean_holder
        d hd alpha h hhc.1 hhc.2 x hx y hy
      have hgr' : |g x - g y| ≤ r ^ alpha := by simpa [r] using! hgr
      have hhr' : |h x - h y| ≤ r ^ alpha := by simpa [r] using! hhr
      have hdiff_alpha : |k x - k y| ≤ 2 * r ^ alpha := by
        dsimp +instances [k]
        calc
          |(g x - h x) - (g y - h y)| =
              |(g x - g y) - (h x - h y)| := by congr 1 <;> ring
          _ ≤ |g x - g y| + |h x - h y| := by
            calc
              |(g x - g y) - (h x - h y)| ≤
                  |(g x - g y) - 0| + |0 - (h x - h y)| :=
                abs_sub_le _ _ _
              _ = |g x - g y| + |h x - h y| := by
                simp +instances [abs_sub_comm]
          _ ≤ 2 * r ^ alpha := by linarith
      have hdiff_eta : |k x - k y| < 2 * eta := by
        have hrewrite : k x - k y = (k x - c) - (k y - c) := by ring
        rw [hrewrite]
        calc
          |(k x - c) - (k y - c)| ≤ |k x - c| + |k y - c| := by
            calc
              |(k x - c) - (k y - c)| ≤
                  |(k x - c) - 0| + |0 - (k y - c)| :=
                abs_sub_le _ _ _
              _ = |k x - c| + |k y - c| := by
                simp +instances [abs_sub_comm]
          _ < eta + eta := add_lt_add (hnorm ⟨x, hx⟩) (hnorm ⟨y, hy⟩)
          _ = 2 * eta := by ring
      change |k x - k y| / r ^ beta ≤ epsilon / 2
      by_cases hrt : r ≤ t
      · have hpow : r ^ (alpha - beta) ≤ t ^ (alpha - beta) :=
          Real.rpow_le_rpow hr.le hrt hq.le
        have hsmall : 2 * r ^ (alpha - beta) < epsilon / 4 := by
          exact (mul_le_mul_of_nonneg_left hpow (by norm_num)).trans_lt ht_small
        have hratio_small : |k x - k y| / r ^ beta ≤
            2 * r ^ (alpha - beta) := by
          apply (div_le_iff₀ hrpow_beta).2
          calc
            |k x - k y| ≤ 2 * r ^ alpha := hdiff_alpha
            _ = (2 * r ^ (alpha - beta)) * r ^ beta := by
              calc
                2 * r ^ alpha = 2 * (r ^ (alpha - beta) * r ^ beta) := by
                  rw [← Real.rpow_add hr]
                  congr 1
                  ring
                _ = (2 * r ^ (alpha - beta)) * r ^ beta := by ring
        exact hratio_small.trans (by linarith)
      · have htr : t < r := lt_of_not_ge hrt
        have hpow : t ^ beta ≤ r ^ beta :=
          Real.rpow_le_rpow ht.le htr.le hbeta0.le
        have hprod : 2 * eta ≤ epsilon * t ^ beta / 4 := by
          linarith
        have hprod' : epsilon * t ^ beta / 4 ≤ epsilon * r ^ beta / 4 := by
          gcongr
        have hbound : 2 * eta ≤ (epsilon / 4) * r ^ beta := by
          calc
            2 * eta ≤ epsilon * t ^ beta / 4 := hprod
            _ ≤ epsilon * r ^ beta / 4 := hprod'
            _ = (epsilon / 4) * r ^ beta := by ring
        have hratio_large : |k x - k y| / r ^ beta ≤ epsilon / 4 := by
          apply (div_le_iff₀ hrpow_beta).2
          exact (le_of_lt hdiff_eta).trans hbound
        exact hratio_large.trans (by linarith)
  have hholder : Lane4.IsHolderOn beta (boundarySet d) k := by
    refine ⟨epsilon / 2, ?_⟩
    intro v hv
    rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
    exact hratio_beta x hx y hy
  have hresg : rescaledDatum (0 : SpatialCoordinates d) 1 g = g := by
    funext x
    simp +instances [rescaledDatum]
  have hg' : Lane4.IsHolderOn alpha (boundarySet d) g ∧
      BddAbove {v : ℝ | ∃ x ∈ boundarySet d, v = |g x|} := by
    have hg0 := hg
    unfold IsCellBoundaryClass at hg0
    rw [hresg] at hg0
    simpa only [boundarySet] using! hg0
  have hresh : rescaledDatum (0 : SpatialCoordinates d) 1 h = h := by
    funext x
    simp +instances [rescaledDatum]
  have hh' : Lane4.IsHolderOn alpha (boundarySet d) h ∧
      BddAbove {v : ℝ | ∃ x ∈ boundarySet d, v = |h x|} := by
    have hh0 := hhc.1
    unfold IsCellBoundaryClass at hh0
    rw [hresh] at hh0
    simpa only [boundarySet] using! hh0
  have hkabs : BddAbove {v : ℝ | ∃ x ∈ boundarySet d, v = |k x|} := by
    dsimp +instances [k]
    exact aux_lem_finite_trace_holder_finite_net_bddAbove_abs_sub hg'.2 hh'.2
  have hcb : IsCellBoundaryClass beta 0 1 k := by
    have htmp : Lane4.IsHolderOn beta (boundarySet d) k ∧
        BddAbove {v : ℝ | ∃ x ∈ boundarySet d, v = |k x|} := ⟨hholder, hkabs⟩
    have hresk : rescaledDatum (0 : SpatialCoordinates d) 1 k = k := by
      funext x
      simp +instances [rescaledDatum]
    unfold IsCellBoundaryClass
    rw [hresk]
    simpa only [boundarySet] using! htmp
  have habs_bound : BddAbove {v : ℝ | ∃ x ∈ boundarySet d, v = |k x - c|} := by
    refine ⟨eta, ?_⟩
    intro v hv
    rcases hv with ⟨x, hx, rfl⟩
    exact le_of_lt (hnorm ⟨x, hx⟩)
  have hsabs : sSup {v : ℝ | ∃ x ∈ boundarySet d, v = |k x - c|} ≤ eta := by
    refine aux_lem_finite_trace_holder_finite_net_sSup_le habs_bound ?_ (le_of_lt heta)
    intro v hv
    rcases hv with ⟨x, hx, rfl⟩
    exact le_of_lt (hnorm ⟨x, hx⟩)
  have hsHolder : Lane4.holderSeminorm beta (boundarySet d)
      (fun x => k x - c) ≤ epsilon / 2 := by
    unfold Lane4.holderSeminorm
    rw [aux_lem_finite_trace_holder_finite_net_holderRatioSet_sub_const k c]
    refine aux_lem_finite_trace_holder_finite_net_sSup_le hholder ?_ (by linarith)
    intro v hv
    rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
    exact hratio_beta x hx y hy
  have hcAlpha_bound : Lane4.cAlphaNorm beta (boundarySet d)
      (fun x => k x - c) ≤ epsilon := by
    unfold Lane4.cAlphaNorm
    linarith
  let Q : Set ℝ := {v : ℝ | ∃ a : ℝ,
    v = Lane4.cAlphaNorm beta (boundarySet d) (fun x => k x - a)}
  have hQbelow : BddBelow Q := by
    refine ⟨0, ?_⟩
    intro v hv
    rcases hv with ⟨a, rfl⟩
    have hshift_holder : Lane4.IsHolderOn beta (boundarySet d)
        (fun x => k x - a) := by
      unfold Lane4.IsHolderOn
      rw [aux_lem_finite_trace_holder_finite_net_holderRatioSet_sub_const k a]
      exact hholder
    exact aux_lem_finite_trace_holder_finite_net_cAlpha_nonneg hS
      (fun x => k x - a)
      (aux_lem_finite_trace_holder_finite_net_bddAbove_abs_sub_const hkabs a)
      hshift_holder
  have hqnorm : cellBoundaryQuotientNorm beta 0 1 k ≤
      Lane4.cAlphaNorm beta (boundarySet d) (fun x => k x - c) := by
    have hQmem : Lane4.cAlphaNorm beta (boundarySet d)
        (fun x => k x - c) ∈ Q := ⟨c, rfl⟩
    have hq' := csInf_le hQbelow hQmem
    simpa [Q, cellBoundaryQuotientNorm, quotientCBetaNorm, rescaledDatum,
      boundarySet] using! hq'
  exact ⟨h, hh, hcb, hqnorm.trans hcAlpha_bound⟩

end Paper
