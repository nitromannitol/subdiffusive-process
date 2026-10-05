module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshError
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Paper.prop_boundary
public import SubdiffusiveProcess.Paper.catalog_cutoff_existence
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_truncation
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.cor_energy_measures
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.mesh_interpolator
public import SubdiffusiveProcess.Paper.cell_boundary_continuity
public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Paper.conv_energy_measure_normalization
public import SubdiffusiveProcess.Paper.prop_gluing_smooth_mesh

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper


/-! ## (GlueBase) -/


theorem aux_prop_gluing_limit_le (Lam Uq : ℕ → ℝ) (L C UStar R M : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hUq : ∀ n : ℕ, Uq n ≤ UStar) (hL : Tendsto Lam atTop (𝓝 L)) (hB : ∀ n : ℕ, Lam n ≤ C * Uq n * R * M ^ 2) : L ≤ C * UStar * R * M ^ 2 := by
  refine le_of_tendsto' hL ?_
  intro n
  calc Lam n ≤ C * Uq n * R * M ^ 2 := hB n
    _ ≤ C * UStar * R * M ^ 2 := by
        have h1 : C * Uq n ≤ C * UStar := mul_le_mul_of_nonneg_left (hUq n) hC
        have h2 : C * Uq n * R ≤ C * UStar * R := mul_le_mul_of_nonneg_right h1 hR
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg M)


theorem aux_prop_gluing_three_eps (a : ℕ → ℝ) (ak : ℕ → ℕ → ℝ) (eps : ℕ → ℝ) (hconv : ∀ k : ℕ, ∃ l : ℝ, Tendsto (ak k) atTop (𝓝 l)) (heps : Tendsto eps atTop (𝓝 0)) (hclose : ∀ k N : ℕ, |a N - ak k N| ≤ eps k) : ∃ L : ℝ, Tendsto a atTop (𝓝 L) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨k, hk⟩ := (heps.eventually_lt tendsto_const_nhds hε3).exists
  obtain ⟨l, hl⟩ := hconv k
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hl.cauchySeq) (ε / 3) hε3
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [Real.dist_eq]
  have h1 : |a m - ak k m| ≤ eps k := hclose k m
  have h2 : |ak k n - a n| ≤ eps k := by
    rw [abs_sub_comm]; exact hclose k n
  have h3 : |ak k m - ak k n| < ε / 3 := by
    rw [← Real.dist_eq]; exact hN m hm n hn
  calc |a m - a n| ≤ |a m - ak k m| + |ak k m - a n| := abs_sub_le _ _ _
    _ ≤ |a m - ak k m| + (|ak k m - ak k n| + |ak k n - a n|) := by
          have h4 := abs_sub_le (ak k m) (ak k n) (a n)
          linarith
    _ ≤ eps k + (ε / 3 + eps k) := by linarith
    _ < ε := by linarith

/-! ### Auxiliary gluing constructions. -/



theorem aux_prop_gluing_central_cell {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r) : ((oddGridCell z (3 * r) h3r (triadicHalf 1) (fun _ => ⟨triadicHalf 1, by omega⟩) : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) = (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have hm : triadicHalf 1 = 1 := by decide
  show Metric.ball (oddGridCenter z (3 * r) (triadicHalf 1) (fun _ => ⟨triadicHalf 1, by omega⟩)) (((3 * r) / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)) / 2) = Metric.ball z (r / 2)
  congr 1
  · funext i
    simp only [oddGridCenter]
    rw [hm]
    simp
  · rw [hm]
    push_cast
    ring





theorem aux_prop_gluing_isHolderOn_congr {d : ℕ} (S : Set (SpatialCoordinates d)) (f g : SpatialCoordinates d → ℝ) (beta : ℝ) (hfg : ∀ x ∈ S, f x = g x) (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f) : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S g := by
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn at *
    refine BddAbove.mono ?_ hf
    intro v hv
    obtain ⟨x, hx, y, hy, hxy, rfl⟩ := hv
    exact ⟨x, hx, y, hy, hxy, by rw [hfg x hx, hfg y hy]⟩





theorem aux_prop_gluing_quotientCBetaNorm_congr {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d)) (f g : SpatialCoordinates d → ℝ) (hfg : ∀ x ∈ S, f x = g x) : quotientCBetaNorm beta S f = quotientCBetaNorm beta S g := by
  have key : ∀ c : ℝ, _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S (fun x => f x - c) = _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S (fun x => g x - c) := by
    intro c
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet
    congr 1
    · congr 1
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by beta_reduce; rw [hfg x hx]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by beta_reduce; rw [hfg x hx]⟩
    · congr 1
      ext v
      constructor
      · rintro ⟨x, hx, y, hy, hxy, rfl⟩
        exact ⟨x, hx, y, hy, hxy, by beta_reduce; rw [hfg x hx, hfg y hy]⟩
      · rintro ⟨x, hx, y, hy, hxy, rfl⟩
        exact ⟨x, hx, y, hy, hxy, by beta_reduce; rw [hfg x hx, hfg y hy]⟩
  unfold quotientCBetaNorm
  simp_rw [key]




/-! ### Elementary geometry and Hölder helpers (paper label `mfd:prop-gluing`). -/

theorem aux_prop_gluing_euclid_pos {d : ℕ} (x y : SpatialCoordinates d) (hne : x ≠ y) :
    0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra h
    push Not at h
    exact hne (funext h)
  apply Real.sqrt_pos.mpr
  have hsq : 0 < (x j - y j) ^ 2 := by
    have : x j - y j ≠ 0 := sub_ne_zero.mpr hj
    positivity
  exact lt_of_lt_of_le hsq (Finset.single_le_sum (f := fun k => (x k - y k) ^ 2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ j))

theorem aux_prop_gluing_euclid_le_of_mem_closure {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (x y : SpatialCoordinates d)
    (hx : x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hy : y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d))) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt (d : ℝ) * r := by
  have hx_closed : x ∈ Metric.closedBall z (r / 2) :=
    Metric.closure_ball_subset_closedBall hx
  have hy_closed : y ∈ Metric.closedBall z (r / 2) :=
    Metric.closure_ball_subset_closedBall hy
  have hbound : ∀ w ∈ Metric.closedBall z (r / 2), ∀ j, |w j - z j| ≤ r / 2 := by
    intro w hw j
    have hdist : dist w z ≤ r / 2 := by simpa [Metric.mem_closedBall] using hw
    have hcomp : dist (w j) (z j) ≤ dist w z := dist_le_pi_dist w z j
    rw [Real.dist_eq] at hcomp
    linarith
  have h_diff_bound : ∀ j, |x j - y j| ≤ r := by
    intro j
    have h1 := hbound x hx_closed j
    have h2 := hbound y hy_closed j
    calc
      |x j - y j| = |(x j - z j) + (z j - y j)| := by ring_nf
      _ ≤ |x j - z j| + |z j - y j| := abs_add_le _ _
      _ = |x j - z j| + |y j - z j| := by rw [abs_sub_comm (z j) (y j)]
      _ ≤ r / 2 + r / 2 := add_le_add h1 h2
      _ = r := by ring
  have h_sq_bound : ∀ j, (x j - y j) ^ 2 ≤ r ^ 2 := by
    intro j
    have h_abs' : -r ≤ x j - y j ∧ x j - y j ≤ r := abs_le.mp (h_diff_bound j)
    nlinarith
  have h_sum : ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, r ^ 2 :=
    Finset.sum_le_sum fun j _ => h_sq_bound j
  have h_sum_r : ∑ _j : Fin d, r ^ 2 = (d : ℝ) * r ^ 2 := by simp
  rw [h_sum_r] at h_sum
  calc
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d : ℝ) * r ^ 2) :=
      Real.sqrt_le_sqrt h_sum
    _ = Real.sqrt (d : ℝ) * Real.sqrt (r ^ 2) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d)]
    _ = Real.sqrt (d : ℝ) * r := by rw [Real.sqrt_sq hr.le]

theorem aux_prop_gluing_rescale_mem_frontier {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (y : SpatialCoordinates d)
    (hy : y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) :
    (fun i => z i + r * y i) ∈
      frontier (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  have h1 : (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
      Metric.ball 0 (1 / 2) := rfl
  have h2 : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  rw [h1, frontier_ball _ (by norm_num)] at hy
  rw [h2, frontier_ball _ (ne_of_gt (by positivity))]
  have hpt : (fun i => z i + r * y i) = z + r • y := by
    funext i
    simp [smul_eq_mul]
  rw [mem_sphere_iff_norm, sub_zero] at hy
  rw [hpt, mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, hy]
  ring

theorem aux_prop_gluing_isHolderOn_mono {d : ℕ}
    (S : Set (SpatialCoordinates d)) (G : SpatialCoordinates d → ℝ)
    (D beta alpha : ℝ) (_hD0 : 0 ≤ D)
    (hD : ∀ x ∈ S, ∀ y ∈ S, Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ D)
    (_hbeta0 : 0 ≤ beta) (hba : beta ≤ alpha)
    (hG : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S G) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S G := by
  obtain ⟨M, hM⟩ := hG
  refine ⟨max M 0 * D ^ (alpha - beta), ?_⟩
  rintro v ⟨x, hx, y, hy, hne, rfl⟩
  have hepos := aux_prop_gluing_euclid_pos x y hne
  set e := Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) with he_def
  have hmem : |G x - G y| / e ^ alpha ∈ _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet alpha S G :=
    ⟨x, hx, y, hy, hne, rfl⟩
  have hle := hM hmem
  have heapos : 0 < e ^ alpha := Real.rpow_pos_of_pos hepos alpha
  have hebpos : 0 < e ^ beta := Real.rpow_pos_of_pos hepos beta
  have h1 : |G x - G y| ≤ M * e ^ alpha := (div_le_iff₀ heapos).mp hle
  have hsplit : e ^ alpha = e ^ beta * e ^ (alpha - beta) := by
    rw [← Real.rpow_add hepos]
    congr 1
    ring
  have h2 : e ^ (alpha - beta) ≤ D ^ (alpha - beta) :=
    Real.rpow_le_rpow hepos.le (hD x hx y hy) (by linarith)
  rw [div_le_iff₀ hebpos]
  calc |G x - G y| ≤ M * e ^ alpha := h1
    _ ≤ max M 0 * e ^ alpha := mul_le_mul_of_nonneg_right (le_max_left _ _) heapos.le
    _ = max M 0 * e ^ (alpha - beta) * e ^ beta := by rw [hsplit]; ring
    _ ≤ max M 0 * D ^ (alpha - beta) * e ^ beta := by
        apply mul_le_mul_of_nonneg_right _ hebpos.le
        exact mul_le_mul_of_nonneg_left h2 (le_max_right _ _)

theorem aux_prop_gluing_euclid_rescale {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (y y' : SpatialCoordinates d) :
    Real.sqrt (∑ j : Fin d, ((z j + r * y j) - (z j + r * y' j)) ^ 2) =
      r * Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2) := by
  have hsum : (∑ j : Fin d, ((z j + r * y j) - (z j + r * y' j)) ^ 2) =
      r ^ 2 * (∑ j : Fin d, (y j - y' j) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum, Real.sqrt_mul (pow_two_nonneg r), Real.sqrt_sq hr.le]

theorem aux_prop_gluing_isHolderOn_rescale {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (beta : ℝ) (_hbeta0 : 0 ≤ beta)
    (g : SpatialCoordinates d → ℝ)
    (hg : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) (rescaledDatum z r g) := by
  obtain ⟨M, hM⟩ := hg
  refine ⟨r ^ beta * M, ?_⟩
  rintro v ⟨y, hy, y', hy', hne, rfl⟩
  have hx := aux_prop_gluing_rescale_mem_frontier z r hr y hy
  have hx' := aux_prop_gluing_rescale_mem_frontier z r hr y' hy'
  have hxne : (fun i => z i + r * y i) ≠ (fun i => z i + r * y' i) := by
    intro h
    apply hne
    funext i
    have h1 := congr_fun h i
    have h2 : r * y i = r * y' i := by linarith
    exact mul_left_cancel₀ (ne_of_gt hr) h2
  have hmem : |g (fun i => z i + r * y i) - g (fun i => z i + r * y' i)| /
      (Real.sqrt (∑ j : Fin d, ((fun i => z i + r * y i) j -
        (fun i => z i + r * y' i) j) ^ 2)) ^ beta
      ∈ _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) g :=
    ⟨_, hx, _, hx', hxne, rfl⟩
  have hle := hM hmem
  have hdist := aux_prop_gluing_euclid_rescale z r hr y y'
  simp only at hle
  rw [hdist, Real.mul_rpow hr.le (Real.sqrt_nonneg _)] at hle
  have hepos := aux_prop_gluing_euclid_pos y y' hne
  have hrb : 0 < r ^ beta := Real.rpow_pos_of_pos hr beta
  have he : 0 < (Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2)) ^ beta :=
    Real.rpow_pos_of_pos hepos beta
  change |g (fun i => z i + r * y i) - g (fun i => z i + r * y' i)| /
      (Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2)) ^ beta ≤ r ^ beta * M
  rw [div_le_iff₀ he]
  rw [div_le_iff₀ (mul_pos hrb he)] at hle
  calc _ ≤ M * (r ^ beta * (Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2)) ^ beta) := hle
    _ = r ^ beta * M * (Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2)) ^ beta := by ring

theorem aux_prop_gluing_bddAbove_abs_of_isHolderOn {d : ℕ}
    (S : Set (SpatialCoordinates d)) (G : SpatialCoordinates d → ℝ)
    (D beta : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ x ∈ S, ∀ y ∈ S, Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ D)
    (hbeta0 : 0 ≤ beta) (hG : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S G) :
    BddAbove {v : ℝ | ∃ x ∈ S, v = |G x|} := by
  obtain ⟨M, hM⟩ := hG
  rcases S.eq_empty_or_nonempty with hS | ⟨x0, hx0⟩
  · refine ⟨0, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    simp [hS] at hx
  · refine ⟨|G x0| + max M 0 * D ^ beta, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    have hDb : 0 ≤ max M 0 * D ^ beta :=
      mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hD0 _)
    by_cases hxx : x = x0
    · subst hxx
      linarith
    · have hepos := aux_prop_gluing_euclid_pos x x0 hxx
      set e := Real.sqrt (∑ j : Fin d, (x j - x0 j) ^ 2) with he_def
      have hmem : |G x - G x0| / e ^ beta ∈ _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S G :=
        ⟨x, hx, x0, hx0, hxx, rfl⟩
      have hle := hM hmem
      have hebpos : 0 < e ^ beta := Real.rpow_pos_of_pos hepos beta
      have h1 : |G x - G x0| ≤ M * e ^ beta := (div_le_iff₀ hebpos).mp hle
      have h2 : e ^ beta ≤ D ^ beta := Real.rpow_le_rpow hepos.le (hD x hx x0 hx0) hbeta0
      have h3 : M * e ^ beta ≤ max M 0 * D ^ beta :=
        calc M * e ^ beta ≤ max M 0 * e ^ beta :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hebpos.le
          _ ≤ max M 0 * D ^ beta := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      have h4 : |G x| ≤ |G x - G x0| + |G x0| := by
        have := abs_add_le (G x - G x0) (G x0)
        simpa using this
      linarith

/-! ### Energy-measure triangle inequality (paper label `mfd:prop-gluing`). -/

theorem aux_prop_gluing_sqrt_gamma_add_le {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] {m : Measure X} {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m}
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) {B : Set X}
    (hB : MeasurableSet B) :
    Real.sqrt (Γ.measure (u + v) B).toReal ≤
      Real.sqrt (Γ.measure u B).toReal + Real.sqrt (Γ.measure v B).toReal := by
  have huv := E.domain.add_mem hu hv
  have hexp := Γ.cross_add_self_apply hu hv B
  rw [Γ.cross_self _ huv B hB, Γ.cross_self _ hu B hB, Γ.cross_self _ hv B hB] at hexp
  have hcs := Γ.abs_cross_le u hu v hv B hB
  have ha : 0 ≤ (Γ.measure u B).toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ (Γ.measure v B).toReal := ENNReal.toReal_nonneg
  have hle : (Γ.measure (u + v) B).toReal ≤
      (Real.sqrt (Γ.measure u B).toReal + Real.sqrt (Γ.measure v B).toReal) ^ 2 := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb, hexp]
    have := le_abs_self (Γ.cross u v B)
    nlinarith
  calc Real.sqrt (Γ.measure (u + v) B).toReal ≤
        Real.sqrt ((Real.sqrt (Γ.measure u B).toReal +
          Real.sqrt (Γ.measure v B).toReal) ^ 2) := Real.sqrt_le_sqrt hle
    _ = _ := Real.sqrt_sq (by positivity)

/-! ### `L²` convergence from uniform convergence on a finite-volume domain. -/

theorem aux_prop_gluing_tendsto_L2_of_uniform {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (hfin : volume (Ω : Set (SpatialCoordinates d)) ≠ ⊤)
    (f : ℕ → DomainL2 Ω) (F : ℕ → SpatialCoordinates d → ℝ) (g : DomainL2 Ω)
    (G : SpatialCoordinates d → ℝ)
    (hf : ∀ n, (f n : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] F n)
    (hg : (g : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] G)
    (hFG : TendstoUniformlyOn F G atTop (Ω : Set (SpatialCoordinates d))) :
    Tendsto f atTop (𝓝 g) := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
    isFiniteMeasure_restrict.mpr hfin
  set M : ℝ := ((measureUnivNNReal (volume.restrict (Ω : Set (SpatialCoordinates d))) : ℝ≥0) :
    ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) with hM
  have hM0 : 0 ≤ M := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (2 * (M + 1)) := by positivity
  have hev := (Metric.tendstoUniformlyOn_iff.mp hFG) _ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hbound : ∀ᵐ x ∂(volume.restrict (Ω : Set (SpatialCoordinates d))),
      ‖(f n - g : DomainL2 Ω) x‖ ≤ ε / (2 * (M + 1)) := by
    filter_upwards [Lp.coeFn_sub (f n) g, hf n, hg,
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx1 hx2 hx3 hx4
    rw [hx1, Pi.sub_apply, hx2, hx3, Real.norm_eq_abs, abs_sub_comm]
    have := hN n hn x hx4
    rw [Real.dist_eq] at this
    exact this.le
  have hnorm := Lp.norm_le_of_ae_bound hδ.le hbound
  have hlt : M * (ε / (2 * (M + 1))) < ε := by
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  calc ‖f n - g‖ ≤ _ := hnorm
    _ < ε := by simpa [hM] using hlt


/-- Consumer 1: an `alpha`-Hölder trace on `∂q` is in the `beta` boundary class
of `eq:mfd-2` (first conjunct of `prop_gluing`). -/
theorem aux_prop_gluing_cellBoundaryClass {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (beta alpha : ℝ)
    (hbeta0 : 0 ≤ beta) (hba : beta ≤ alpha) (b : SpatialCoordinates d → ℝ)
    (hb : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b) :
    IsCellBoundaryClass beta z r b := by
  have hDq : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt (d : ℝ) * r :=
    fun x hx y hy => aux_prop_gluing_euclid_le_of_mem_closure z r hr x y
      (frontier_subset_closure hx) (frontier_subset_closure hy)
  have hD1 : ∀ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)),
      ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)),
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt (d : ℝ) * 1 :=
    fun x hx y hy => aux_prop_gluing_euclid_le_of_mem_closure 0 1 one_pos x y
      (frontier_subset_closure hx) (frontier_subset_closure hy)
  have hDr : 0 ≤ Real.sqrt (d : ℝ) * r := mul_nonneg (Real.sqrt_nonneg _) hr.le
  have hD1' : 0 ≤ Real.sqrt (d : ℝ) * 1 := mul_nonneg (Real.sqrt_nonneg _) zero_le_one
  have hbeta : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b :=
    aux_prop_gluing_isHolderOn_mono _ b _ beta alpha hDr hDq hbeta0 hba hb
  have hresc := aux_prop_gluing_isHolderOn_rescale z r hr beta hbeta0 b hbeta
  exact ⟨hresc, aux_prop_gluing_bddAbove_abs_of_isHolderOn _ _ _ beta hD1' hD1
    hbeta0 hresc⟩

/-- Consumer 2: the boundary-datum block of the `prop_gluing` conclusion with
`B := Ext b` (paper label `mfd:prop-gluing` and ). -/
theorem aux_prop_gluing_datum_block {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (beta alpha : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha)
    (Ext : (SpatialCoordinates d → ℝ) →ₗ[ℝ] (SpatialCoordinates d → ℝ))
    (hExtTrace : ∀ b0, ∀ x ∈ frontier
      (centeredCube z r hr : Set (SpatialCoordinates d)), Ext b0 x = b0 x)
    (hExtRegular : ∀ b0 : SpatialCoordinates d → ℝ,
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b0 →
      ContinuousOn (Ext b0)
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      HasCompactSupport (Ext b0) ∧
      tsupport (Ext b0) ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) (Ext b0))
    (b : SpatialCoordinates d → ℝ)
    (hb : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b) :
    IsCellBoundaryClass beta z r b ∧
      ContinuousOn (Ext b)
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      HasCompactSupport (Ext b) ∧
      tsupport (Ext b) ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) (Ext b) ∧
      Ext b = Ext b ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
        Ext b x = b x) := by
  obtain ⟨h1, h2, h3, h4⟩ := hExtRegular b hb
  exact ⟨aux_prop_gluing_cellBoundaryClass z r hr beta alpha (by linarith) hba.le b hb,
    h1, h2, h3, h4, rfl, hExtTrace b⟩

/-! ### Assembled here: face values on `q` and the bound on `L` (paper label `mfd:prop-gluing`). -/

/-- The middle cell of the triadic `3^d` grid of the enlarged cube is `q`
(`aux_prop_gluing_central_cell`), so the patch face values give
`UN n = Ext b = b` on `∂q`. -/
theorem aux_prop_gluing_face_values_central {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (Ext : (SpatialCoordinates d → ℝ) →ₗ[ℝ] (SpatialCoordinates d → ℝ))
    (b : SpatialCoordinates d → ℝ)
    (hExtTrace : ∀ b0, ∀ x ∈ frontier
        (centeredCube z r hr : Set (SpatialCoordinates d)), Ext b0 x = b0 x)
    {S : ResponseSpace (centeredCube z (3 * r) h3r)}
    (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (UNS : ℕ → S.space)
    (hpatch :
      (∀ n : ℕ,
          (UNS n).val = sobolevDataOfH1 (UN n) ∧
          ContinuousOn (UN n).toFun
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            (UN n).toFun x = 0) ∧
          ∀ k : OddGridIndex d (triadicHalf 1),
            IsWeaklyHarmonicOn (A n)
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
                ((UN n).restrict
                  (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)) ∧
            ∀ x ∈ frontier
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
              (UN n).toFun x = Ext b x)) :
    ∀ n : ℕ, ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (UN n).toFun x = b x := by
  intro n x hx
  have hcell := aux_prop_gluing_central_cell z r hr h3r
  have hx' : x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1)
      (fun _ => ⟨triadicHalf 1, by omega⟩) : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) := by
    rw [hcell]; exact hx
  have hk := ((hpatch n).2.2.2 (fun _ => ⟨triadicHalf 1, by omega⟩)).2 x hx'
  rw [hk, hExtTrace b x hx]

/-- : `Λ_q(b) ≤ C U* r^(d-2) ‖b‖²` passes to the limit from `hBound`
applied to the restricted patches, whose trace on `∂q` is `b`. -/
theorem aux_prop_gluing_bound {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta : ℝ)
    (A : ℕ → SpatialCoordinates d → ℝ)
    (C UStar : ℝ) (hC : 0 ≤ C)
    (Uq : ℕ → ℝ) (hUq : ∀ n : ℕ, 0 ≤ Uq n ∧ Uq n ≤ UStar)
    (hBound : ∀ n : ℕ, ∀ e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
        ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta z r e.toFun →
        cellDirichletInfimum (A n) (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
          C * Uq n * r ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta z r e.toFun ^ 2)
    (b : SpatialCoordinates d → ℝ)
    (hcls : IsCellBoundaryClass beta z r b)
    (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNcont : ∀ n : ℕ, ContinuousOn (UN n).toFun
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hUNq : ∀ n : ℕ, ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (UN n).toFun x = b x)
    (L : ℝ)
    (hL : Tendsto (fun n => cellDirichletInfimum (A n)
          (centeredCube z r hr : Set (SpatialCoordinates d))
          ((UN n).restrict (centeredCube z r hr).isOpen hqQ))
        atTop (𝓝 L)) :
    L ≤ C * UStar * r ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta z r b ^ 2 := by
  refine aux_prop_gluing_limit_le _ Uq L C UStar (r ^ ((d : ℝ) - 2))
    (cellBoundaryQuotientNorm beta z r b) hC (Real.rpow_nonneg hr.le _)
    (fun n => (hUq n).2) hL ?_
  intro n
  have hresc : ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      rescaledDatum z r (UN n).toFun y = rescaledDatum z r b y :=
    fun y hy => hUNq n _ (aux_prop_gluing_rescale_mem_frontier z r hr y hy)
  have hcls' : IsCellBoundaryClass beta z r (UN n).toFun := by
    refine ⟨aux_prop_gluing_isHolderOn_congr _ _ _ beta
      (fun y hy => (hresc y hy).symm) hcls.1, ?_⟩
    obtain ⟨M, hM⟩ := hcls.2
    refine ⟨M, ?_⟩
    rintro v ⟨y, hy, rfl⟩
    rw [hresc y hy]
    exact hM ⟨y, hy, rfl⟩
  have hnorm : cellBoundaryQuotientNorm beta z r (UN n).toFun =
      cellBoundaryQuotientNorm beta z r b :=
    aux_prop_gluing_quotientCBetaNorm_congr beta _ _ _ hresc
  have h := hBound n ((UN n).restrict (centeredCube z r hr).isOpen hqQ)
    ((hUNcont n).mono (closure_mono hqQ)) hcls'
  rw [← hnorm]
  exact h




/-! ### `Λ_{N,q}^{1/2}` is a seminorm on traces (paper label `mfd:prop-gluing`). -/

theorem aux_prop_gluing_zeroTrace_refl {d : ℕ} (W : Set (SpatialCoordinates d))
    (beta : H1Function W) : HasZeroTraceDifferenceOn W beta beta := by
  refine ⟨0, fun x => ?_, fun x => ?_⟩
  · show beta.toFun x = beta.toFun x + 0
    ring
  · show beta.grad x = beta.grad x + 0
    simp

theorem aux_prop_gluing_zeroTrace_add {d : ℕ} (W : Set (SpatialCoordinates d))
    (u1 u2 beta1 beta2 : H1Function W)
    (h1 : HasZeroTraceDifferenceOn W u1 beta1)
    (h2 : HasZeroTraceDifferenceOn W u2 beta2) :
    HasZeroTraceDifferenceOn W (u1 + u2) (beta1 + beta2) := by
  rcases h1 with ⟨w1, hw1_val, hw1_grad⟩
  rcases h2 with ⟨w2, hw2_val, hw2_grad⟩
  refine ⟨w1 + w2, fun x => ?_, fun x => ?_⟩
  · show u1.toFun x + u2.toFun x = (beta1.toFun x + beta2.toFun x) +
      (w1.toH1Function.toFun x + w2.toH1Function.toFun x)
    rw [hw1_val x, hw2_val x]
    ring
  · show u1.grad x + u2.grad x = (beta1.grad x + beta2.grad x) +
      (w1.toH1Function.grad x + w2.toH1Function.grad x)
    rw [hw1_grad x, hw2_grad x]
    abel

theorem aux_prop_gluing_energy_nonneg {d : ℕ} (W : Set (SpatialCoordinates d))
    (hW : MeasurableSet W) (a : SpatialCoordinates d → ℝ) (ha0 : ∀ x ∈ W, 0 ≤ a x)
    (u : H1Function W) : 0 ≤ energy a W u := by
  unfold energy
  refine setIntegral_nonneg hW fun x hx => mul_nonneg (ha0 x hx) ?_
  unfold vecDot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem aux_prop_gluing_weighted_integrable {d : ℕ} (W : Set (SpatialCoordinates d))
    (hW : MeasurableSet W) (a : SpatialCoordinates d → ℝ) (Lam : ℝ)
    (ha0 : ∀ x ∈ W, 0 ≤ a x) (haLam : ∀ x ∈ W, a x ≤ Lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W)) (u v : H1Function W) :
    IntegrableOn (fun x => a x * vecDot (u.grad x) (v.grad x)) W := by
  have h := integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 v.grad_memVectorL2
  refine Integrable.bdd_mul (c := Lam) h hameas ?_
  filter_upwards [ae_restrict_mem hW] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (ha0 x hx)]
  exact haLam x hx

theorem aux_prop_gluing_energy_add_smul {d : ℕ} (W : Set (SpatialCoordinates d))
    (hW : MeasurableSet W) (a : SpatialCoordinates d → ℝ) (Lam : ℝ)
    (ha0 : ∀ x ∈ W, 0 ≤ a x) (haLam : ∀ x ∈ W, a x ≤ Lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W)) (u v : H1Function W) (s : ℝ) :
    energy a W (u + s • v) = energy a W u +
      2 * s * (∫ x in W, a x * vecDot (u.grad x) (v.grad x)) + s ^ 2 * energy a W v := by
  unfold energy
  have h1 := aux_prop_gluing_weighted_integrable W hW a Lam ha0 haLam hameas u u
  have h2 := aux_prop_gluing_weighted_integrable W hW a Lam ha0 haLam hameas u v
  have h3 := aux_prop_gluing_weighted_integrable W hW a Lam ha0 haLam hameas v v
  have hpt : (fun x => a x * vecDot ((u + s • v).grad x) ((u + s • v).grad x)) =
      fun x => a x * vecDot (u.grad x) (u.grad x) +
        2 * s * (a x * vecDot (u.grad x) (v.grad x)) +
        s ^ 2 * (a x * vecDot (v.grad x) (v.grad x)) := by
    funext x
    simp only [H1Function.add_grad, H1Function.smul_grad, vecDot, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hpt, integral_add, integral_add, integral_const_mul, integral_const_mul]
  all_goals first
    | exact h1
    | exact h2.const_mul _
    | exact h3.const_mul _
    | exact h1.add (h2.const_mul _)

theorem aux_prop_gluing_sqrt_energy_add {d : ℕ} (W : Set (SpatialCoordinates d))
    (hW : MeasurableSet W) (a : SpatialCoordinates d → ℝ) (Lam : ℝ)
    (ha0 : ∀ x ∈ W, 0 ≤ a x) (haLam : ∀ x ∈ W, a x ≤ Lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W)) (u v : H1Function W) :
    Real.sqrt (energy a W (u + v)) ≤
      Real.sqrt (energy a W u) + Real.sqrt (energy a W v) := by
  set B := ∫ x in W, a x * vecDot (u.grad x) (v.grad x) with hB
  have hEu := aux_prop_gluing_energy_nonneg W hW a ha0 u
  have hEv := aux_prop_gluing_energy_nonneg W hW a ha0 v
  have hq : ∀ s : ℝ, 0 ≤ energy a W v * (s * s) + (2 * B) * s + energy a W u := by
    intro s
    have h := aux_prop_gluing_energy_nonneg W hW a ha0 (u + s • v)
    rw [aux_prop_gluing_energy_add_smul W hW a Lam ha0 haLam hameas u v s] at h
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have hB2 : B ^ 2 ≤ energy a W u * energy a W v := by nlinarith
  have hBle : B ≤ Real.sqrt (energy a W u) * Real.sqrt (energy a W v) := by
    calc B ≤ |B| := le_abs_self B
      _ = Real.sqrt (B ^ 2) := (Real.sqrt_sq_eq_abs B).symm
      _ ≤ Real.sqrt (energy a W u * energy a W v) := Real.sqrt_le_sqrt hB2
      _ = _ := Real.sqrt_mul hEu _
  have h1 : energy a W (u + v) = energy a W u + 2 * B + energy a W v := by
    have := aux_prop_gluing_energy_add_smul W hW a Lam ha0 haLam hameas u v 1
    rw [one_smul] at this
    rw [this]
    ring
  have hle : energy a W (u + v) ≤
      (Real.sqrt (energy a W u) + Real.sqrt (energy a W v)) ^ 2 := by
    rw [add_sq, Real.sq_sqrt hEu, Real.sq_sqrt hEv, h1]
    nlinarith
  calc Real.sqrt (energy a W (u + v)) ≤
        Real.sqrt ((Real.sqrt (energy a W u) + Real.sqrt (energy a W v)) ^ 2) :=
      Real.sqrt_le_sqrt hle
    _ = _ := Real.sqrt_sq (by positivity)

theorem aux_prop_gluing_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hle : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
    have := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
    nlinarith
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
      Real.sqrt_le_sqrt hle
    _ = _ := Real.sqrt_sq (by positivity)

theorem aux_prop_gluing_infimum_set_bdd {d : ℕ} (W : Set (SpatialCoordinates d))
    (hW : MeasurableSet W) (a : SpatialCoordinates d → ℝ) (ha0 : ∀ x ∈ W, 0 ≤ a x)
    (beta : H1Function W) :
    BddBelow {e : ℝ | ∃ u : H1Function W,
      HasZeroTraceDifferenceOn W u beta ∧ e = energy a W u} ∧
    ({e : ℝ | ∃ u : H1Function W,
      HasZeroTraceDifferenceOn W u beta ∧ e = energy a W u}).Nonempty := by
  refine ⟨⟨0, ?_⟩, ⟨energy a W beta, beta, aux_prop_gluing_zeroTrace_refl W beta, rfl⟩⟩
  rintro e ⟨u, -, rfl⟩
  exact aux_prop_gluing_energy_nonneg W hW a ha0 u

theorem aux_prop_gluing_infimum_nonneg {d : ℕ} (W : Set (SpatialCoordinates d))
    (hW : MeasurableSet W) (a : SpatialCoordinates d → ℝ) (ha0 : ∀ x ∈ W, 0 ≤ a x)
    (beta : H1Function W) : 0 ≤ cellDirichletInfimum a W beta := by
  obtain ⟨-, hne⟩ := aux_prop_gluing_infimum_set_bdd W hW a ha0 beta
  unfold cellDirichletInfimum
  apply le_csInf hne
  rintro e ⟨u, -, rfl⟩
  exact aux_prop_gluing_energy_nonneg W hW a ha0 u

theorem aux_prop_gluing_sqrt_infimum_add {d : ℕ} (W : Set (SpatialCoordinates d))
    (hW : MeasurableSet W) (a : SpatialCoordinates d → ℝ) (Lam : ℝ)
    (ha0 : ∀ x ∈ W, 0 ≤ a x) (haLam : ∀ x ∈ W, a x ≤ Lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W)) (beta1 beta2 : H1Function W) :
    Real.sqrt (cellDirichletInfimum a W (beta1 + beta2)) ≤
      Real.sqrt (cellDirichletInfimum a W beta1) +
        Real.sqrt (cellDirichletInfimum a W beta2) := by
  obtain ⟨hb1, hn1⟩ := aux_prop_gluing_infimum_set_bdd W hW a ha0 beta1
  obtain ⟨hb2, hn2⟩ := aux_prop_gluing_infimum_set_bdd W hW a ha0 beta2
  obtain ⟨hb12, hn12⟩ := aux_prop_gluing_infimum_set_bdd W hW a ha0 (beta1 + beta2)
  have hL1 := aux_prop_gluing_infimum_nonneg W hW a ha0 beta1
  have hL2 := aux_prop_gluing_infimum_nonneg W hW a ha0 beta2
  apply le_of_forall_pos_le_add
  intro δ hδ
  set ε := (δ / 2) ^ 2 with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨e1, ⟨u1, hu1, rfl⟩, he1⟩ :=
    exists_lt_of_csInf_lt hn1 (lt_add_of_pos_right (cellDirichletInfimum a W beta1) hεpos)
  obtain ⟨e2, ⟨u2, hu2, rfl⟩, he2⟩ :=
    exists_lt_of_csInf_lt hn2 (lt_add_of_pos_right (cellDirichletInfimum a W beta2) hεpos)
  have h12 : cellDirichletInfimum a W (beta1 + beta2) ≤ energy a W (u1 + u2) :=
    csInf_le hb12 ⟨u1 + u2, aux_prop_gluing_zeroTrace_add W u1 u2 beta1 beta2 hu1 hu2, rfl⟩
  have hs := aux_prop_gluing_sqrt_energy_add W hW a Lam ha0 haLam hameas u1 u2
  have hsq1 : Real.sqrt (energy a W u1) ≤ Real.sqrt (cellDirichletInfimum a W beta1) + δ / 2 := by
    calc Real.sqrt (energy a W u1) ≤ Real.sqrt (cellDirichletInfimum a W beta1 + ε) :=
          Real.sqrt_le_sqrt he1.le
      _ ≤ Real.sqrt (cellDirichletInfimum a W beta1) + Real.sqrt ε :=
          aux_prop_gluing_sqrt_add_le _ _ hL1 hεpos.le
      _ = _ := by rw [hε, Real.sqrt_sq (by positivity)]
  have hsq2 : Real.sqrt (energy a W u2) ≤ Real.sqrt (cellDirichletInfimum a W beta2) + δ / 2 := by
    calc Real.sqrt (energy a W u2) ≤ Real.sqrt (cellDirichletInfimum a W beta2 + ε) :=
          Real.sqrt_le_sqrt he2.le
      _ ≤ Real.sqrt (cellDirichletInfimum a W beta2) + Real.sqrt ε :=
          aux_prop_gluing_sqrt_add_le _ _ hL2 hεpos.le
      _ = _ := by rw [hε, Real.sqrt_sq (by positivity)]
  calc Real.sqrt (cellDirichletInfimum a W (beta1 + beta2)) ≤
        Real.sqrt (energy a W (u1 + u2)) := Real.sqrt_le_sqrt h12
    _ ≤ _ := hs
    _ ≤ _ := by linarith

theorem aux_prop_gluing_sqrt_infimum_sub_le {d : ℕ} (W : Set (SpatialCoordinates d))
    (hW : MeasurableSet W) (a : SpatialCoordinates d → ℝ) (Lam : ℝ)
    (ha0 : ∀ x ∈ W, 0 ≤ a x) (haLam : ∀ x ∈ W, a x ≤ Lam)
    (hameas : AEStronglyMeasurable a (volume.restrict W)) (beta betak : H1Function W) :
    Real.sqrt (cellDirichletInfimum a W beta) ≤
      Real.sqrt (cellDirichletInfimum a W betak) +
        Real.sqrt (cellDirichletInfimum a W (beta - betak)) := by
  have h := aux_prop_gluing_sqrt_infimum_add W hW a Lam ha0 haLam hameas betak
    (beta - betak)
  rwa [add_sub_cancel] at h

/-! ### Rescaled `C^β` quotient norms (paper `eq:mfd-2`). -/

theorem aux_prop_gluing_rescale_ratio {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (beta : ℝ) (g : SpatialCoordinates d → ℝ) (y y' : SpatialCoordinates d)
    (hne : y ≠ y') :
    |rescaledDatum z r g y - rescaledDatum z r g y'| /
        (Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2)) ^ beta =
      r ^ beta * (|g (fun i => z i + r * y i) - g (fun i => z i + r * y' i)| /
        (Real.sqrt (∑ j : Fin d, ((fun i => z i + r * y i) j -
          (fun i => z i + r * y' i) j) ^ 2)) ^ beta) := by
  have hdist := aux_prop_gluing_euclid_rescale z r hr y y'
  have hepos := aux_prop_gluing_euclid_pos y y' hne
  have hrb : 0 < r ^ beta := Real.rpow_pos_of_pos hr beta
  have he : 0 < (Real.sqrt (∑ j : Fin d, (y j - y' j) ^ 2)) ^ beta :=
    Real.rpow_pos_of_pos hepos beta
  simp only [rescaledDatum]
  rw [hdist, Real.mul_rpow hr.le (Real.sqrt_nonneg _)]
  field_simp

theorem aux_prop_gluing_rescale_ne {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (y y' : SpatialCoordinates d) (hne : y ≠ y') :
    (fun i => z i + r * y i) ≠ (fun i => z i + r * y' i) := by
  intro h
  apply hne
  funext i
  have h1 := congr_fun h i
  have h2 : r * y i = r * y' i := by linarith
  exact mul_left_cancel₀ (ne_of_gt hr) h2

theorem aux_prop_gluing_holderSeminorm_nonneg {d : ℕ} (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (g : SpatialCoordinates d → ℝ) :
    0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S g := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  apply Real.sSup_nonneg
  rintro v ⟨x, -, y, -, -, rfl⟩
  exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

theorem aux_prop_gluing_supAbs_nonneg {d : ℕ} (S : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d → ℝ) :
    0 ≤ sSup {v : ℝ | ∃ x ∈ S, v = |g x|} := by
  apply Real.sSup_nonneg
  rintro v ⟨x, -, rfl⟩
  exact abs_nonneg _

theorem aux_prop_gluing_cAlphaNorm_nonneg {d : ℕ} (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (g : SpatialCoordinates d → ℝ) :
    0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S g :=
  add_nonneg (aux_prop_gluing_supAbs_nonneg S g) (aux_prop_gluing_holderSeminorm_nonneg beta S g)

theorem aux_prop_gluing_quotientNorm_nonneg {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d)
    (r : ℝ) (g : SpatialCoordinates d → ℝ) :
    0 ≤ cellBoundaryQuotientNorm beta z r g := by
  unfold cellBoundaryQuotientNorm quotientCBetaNorm
  apply Real.sInf_nonneg
  rintro v ⟨c, rfl⟩
  exact aux_prop_gluing_cAlphaNorm_nonneg _ _ _

theorem aux_prop_gluing_holderSeminorm_rescale_le {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (S : Set (SpatialCoordinates d))
    (hS : ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), (fun i => z i + r * y i) ∈ S)
    (beta : ℝ) (g : SpatialCoordinates d → ℝ)
    (hg : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S g) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) (rescaledDatum z r g) ≤
      r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S g := by
  have hH0 := aux_prop_gluing_holderSeminorm_nonneg beta S g
  have hrb : 0 < r ^ beta := Real.rpow_pos_of_pos hr beta
  rcases (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) (rescaledDatum z r g)).eq_empty_or_nonempty with h | h
  · unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
    rw [h, Real.sSup_empty]
    positivity
  · unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
    apply csSup_le h
    rintro v ⟨y, hy, y', hy', hne, rfl⟩
    rw [aux_prop_gluing_rescale_ratio z r hr beta g y y' hne]
    apply mul_le_mul_of_nonneg_left _ hrb.le
    exact le_csSup hg ⟨_, hS y hy, _, hS y' hy', aux_prop_gluing_rescale_ne z r hr y y' hne, rfl⟩

theorem aux_prop_gluing_isHolderOn_rescale_gen {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (S : Set (SpatialCoordinates d))
    (hS : ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), (fun i => z i + r * y i) ∈ S)
    (beta : ℝ) (g : SpatialCoordinates d → ℝ)
    (hg : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S g) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) (rescaledDatum z r g) := by
  have hrb : 0 < r ^ beta := Real.rpow_pos_of_pos hr beta
  obtain ⟨M, hM⟩ := hg
  refine ⟨r ^ beta * M, ?_⟩
  rintro v ⟨y, hy, y', hy', hne, rfl⟩
  rw [aux_prop_gluing_rescale_ratio z r hr beta g y y' hne]
  exact mul_le_mul_of_nonneg_left
    (hM ⟨_, hS y hy, _, hS y' hy', aux_prop_gluing_rescale_ne z r hr y y' hne, rfl⟩) hrb.le

theorem aux_prop_gluing_bddAbove_rescale {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (S : Set (SpatialCoordinates d))
    (hS : ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), (fun i => z i + r * y i) ∈ S)
    (g : SpatialCoordinates d → ℝ)
    (hgb : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|}) :
    BddAbove {v : ℝ | ∃ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), v = |rescaledDatum z r g y|} := by
  obtain ⟨M, hM⟩ := hgb
  refine ⟨M, ?_⟩
  rintro v ⟨y, hy, rfl⟩
  exact hM ⟨_, hS y hy, rfl⟩

theorem aux_prop_gluing_sSup_abs_rescale_le {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (S : Set (SpatialCoordinates d))
    (hS : ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), (fun i => z i + r * y i) ∈ S)
    (g : SpatialCoordinates d → ℝ)
    (hgb : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|}) :
    sSup {v : ℝ | ∃ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)), v = |rescaledDatum z r g y|} ≤
      sSup {v : ℝ | ∃ x ∈ S, v = |g x|} := by
  rcases ({v : ℝ | ∃ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), v = |rescaledDatum z r g y|}).eq_empty_or_nonempty
    with h | h
  · rw [h, Real.sSup_empty]
    exact aux_prop_gluing_supAbs_nonneg S g
  · apply csSup_le h
    rintro v ⟨y, hy, rfl⟩
    exact le_csSup hgb ⟨_, hS y hy, rfl⟩

/-- The `C^β/ℝ` boundary norm of `eq:mfd-2` of a cell `z + r Q₀` is controlled by
the `C^β` norm on any set containing the cell frontier. -/
theorem aux_prop_gluing_quotientNorm_le {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (S : Set (SpatialCoordinates d))
    (hS : ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), (fun i => z i + r * y i) ∈ S)
    (beta : ℝ) (g : SpatialCoordinates d → ℝ)
    (hg : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S g)
    (hgb : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|}) :
    cellBoundaryQuotientNorm beta z r g ≤
      max 1 (r ^ beta) * _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S g := by
  have h1 : cellBoundaryQuotientNorm beta z r g ≤
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) (rescaledDatum z r g) := by
    unfold cellBoundaryQuotientNorm quotientCBetaNorm
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro v ⟨c, rfl⟩
      exact aux_prop_gluing_cAlphaNorm_nonneg _ _ _
    · exact ⟨0, by simp⟩
  have h2 := aux_prop_gluing_sSup_abs_rescale_le z r S hS g hgb
  have h3 := aux_prop_gluing_holderSeminorm_rescale_le z r hr S hS beta g hg
  have hA := aux_prop_gluing_supAbs_nonneg S g
  have hH := aux_prop_gluing_holderSeminorm_nonneg beta S g
  have hm1 : (1 : ℝ) ≤ max 1 (r ^ beta) := le_max_left _ _
  have hm2 : r ^ beta ≤ max 1 (r ^ beta) := le_max_right _ _
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm at h1 ⊢
  calc cellBoundaryQuotientNorm beta z r g ≤ _ := h1
    _ ≤ sSup {v : ℝ | ∃ x ∈ S, v = |g x|} + r ^ beta * _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S g :=
        add_le_add h2 h3
    _ ≤ max 1 (r ^ beta) * (sSup {v : ℝ | ∃ x ∈ S, v = |g x|} +
        _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S g) := by
        nlinarith [mul_le_mul_of_nonneg_right hm1 hA, mul_le_mul_of_nonneg_right hm2 hH]




/-! ### : the `C^β`/`C^α` seminorm is subadditive.

 (proof of `prop_gluing` (i)): "`Λ_{N,q}^{1/2}` is a seminorm on
traces.. so `|Λ_{N,q}(b_k)^{1/2}-Λ_{N,q}(b_l)^{1/2}| ≤ Λ_{N,q}(b_k-b_l)^{1/2}`".
The three-epsilon argument needs `‖b_k - b_l‖_{C^β}` small when `b_k, b_l` are
both close to the limit datum in `‖·‖_{C^β}`; that needs the triangle
inequality for `SubdiffusiveProcess.EllipticRegularity.cAlphaNorm`, which is a raw `sSup` (Carriers.lean )
and carries no seminorm lemmas yet. These four lemmas supply it. -/

/-- The sup-of-`|·|` summand of `cAlphaNorm` is subadditive under a pointwise
difference (elementary `sSup` triangle inequality; no Hölder structure used). -/
theorem aux_prop_gluing_sSupAbs_sub_le {d : ℕ} (S : Set (SpatialCoordinates d))
    (f g : SpatialCoordinates d → ℝ) (hS : S.Nonempty)
    (hf : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|})
    (hg : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|}) :
    sSup {v : ℝ | ∃ x ∈ S, v = |f x - g x|} ≤
      sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + sSup {v : ℝ | ∃ x ∈ S, v = |g x|} := by
  have hne : {v : ℝ | ∃ x ∈ S, v = |f x - g x|}.Nonempty := by
    rcases hS with ⟨x, hx⟩
    exact ⟨|f x - g x|, x, hx, rfl⟩
  apply csSup_le hne
  intro v hv
  rcases hv with ⟨x, hx, rfl⟩
  have h1 : |f x| ≤ sSup {v : ℝ | ∃ x ∈ S, v = |f x|} := le_csSup hf ⟨x, hx, rfl⟩
  have h2 : |g x| ≤ sSup {v : ℝ | ∃ x ∈ S, v = |g x|} := le_csSup hg ⟨x, hx, rfl⟩
  have hsub : |f x - g x| ≤ |f x| + |g x| := by
    calc
      |f x - g x| = |f x + (-g x)| := by rw [sub_eq_add_neg]
      _ ≤ |f x| + |-g x| := abs_add_le _ _
      _ = |f x| + |g x| := by rw [abs_neg]
  linarith

/-- On a set with two distinct points, the Hölder difference-quotient set
(`SubdiffusiveProcess.EllipticRegularity.holderRatioSet`) is nonempty — needed so `csSup_le` can be applied to
`SubdiffusiveProcess.EllipticRegularity.holderSeminorm` without hitting the junk `sSup ∅ = 0` case. -/
theorem aux_prop_gluing_holderRatioSet_nonempty {d : ℕ} (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ)
    (hS : S.Nontrivial) :
    (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S f).Nonempty := by
  rcases hS with ⟨x, hx, y, hy, hxy⟩
  refine ⟨|f x - f y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta, x, hx, y, hy, hxy, ?_⟩
  rfl

/-- `SubdiffusiveProcess.EllipticRegularity.holderSeminorm` is subadditive under a pointwise difference, given
both summands are Hölder (`SubdiffusiveProcess.EllipticRegularity.IsHolderOn`, i.e. `BddAbove` of the ratio
set — Carriers.lean : this hypothesis is required of every consumer). -/
theorem aux_prop_gluing_holderSeminorm_sub_le {d : ℕ} (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (f g : SpatialCoordinates d → ℝ)
    (hS : S.Nontrivial)
    (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f) (hg : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S g) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S (fun x => f x - g x) ≤
      _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S f + _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm beta S g := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  have hne := aux_prop_gluing_holderRatioSet_nonempty beta S (fun x => f x - g x) hS
  apply csSup_le hne
  intro v hv
  rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
  have hnum : |(f x - g x) - (f y - g y)| ≤ |f x - f y| + |g x - g y| := by
    have h_eq : (f x - g x) - (f y - g y) = (f x - f y) - (g x - g y) := by ring
    rw [h_eq]
    calc
      |(f x - f y) - (g x - g y)| = |(f x - f y) + (-(g x - g y))| := by rw [sub_eq_add_neg]
      _ ≤ |f x - f y| + |-(g x - g y)| := abs_add_le _ _
      _ = |f x - f y| + |g x - g y| := by rw [abs_neg]
  have hDnonneg : 0 ≤ (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hdiv1 : |(f x - g x) - (f y - g y)| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤
      (|f x - f y| + |g x - g y|) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta :=
    div_le_div_of_nonneg_right hnum hDnonneg
  have hdiv2 : (|f x - f y| + |g x - g y|) / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta =
      |f x - f y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta +
      |g x - g y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta := by
    rw [add_div]
  rw [hdiv2] at hdiv1
  have hf_bound : |f x - f y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤
      sSup (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S f) := by
    apply le_csSup hf
    exact ⟨x, hx, y, hy, hxy, rfl⟩
  have hg_bound : |g x - g y| / (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta ≤
      sSup (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S g) := by
    apply le_csSup hg
    exact ⟨x, hx, y, hy, hxy, rfl⟩
  linarith

/-! ### Consumer: `SubdiffusiveProcess.EllipticRegularity.cAlphaNorm` is subadditive (paper label `mfd:prop-gluing`). -/

/-- `‖f-g‖_{C^α(S)} ≤ ‖f‖_{C^α(S)} + ‖g‖_{C^α(S)}`: the seminorm-on-traces claim
used to run the three-epsilon argument on `b_k → b`. Assembled from the three
results above; no new analysis. -/
theorem aux_prop_gluing_cAlphaNorm_sub_le {d : ℕ} (alpha : ℝ)
    (S : Set (SpatialCoordinates d)) (f g : SpatialCoordinates d → ℝ)
    (hS : S.Nontrivial)
    (hfAbs : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|})
    (hgAbs : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|})
    (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S f) (hg : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha S g) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S (fun x => f x - g x) ≤
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S f + _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha S g := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm
  have h1 := aux_prop_gluing_sSupAbs_sub_le S f g hS.nonempty hfAbs hgAbs
  have h2 := aux_prop_gluing_holderSeminorm_sub_le alpha S f g hS hf hg
  calc sSup {v : ℝ | ∃ x ∈ S, v = |f x - g x|} + _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S (fun x => f x - g x)
      ≤ (sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + sSup {v : ℝ | ∃ x ∈ S, v = |g x|}) +
          (_root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f + _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S g) := by
        gcongr
    _ = (sSup {v : ℝ | ∃ x ∈ S, v = |f x|} + _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S f) +
          (sSup {v : ℝ | ∃ x ∈ S, v = |g x|} + _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm alpha S g) := by ring


section
open Classical


/-! ### : envelope-Cauchy and uniform-Cauchy-domination.

 (proof of `prop_gluing` (i)): "the finite-cutoff extensions
satisfy `E_N^Q(U_N^{(k)}-U_N^{(l)}) ≤ C‖β_k-β_l‖_{C^β}^2`.. and
`‖U_N^{(k)}-U_N^{(l)}‖_∞ ≤ ‖β_k-β_l‖_∞`.. so the limits `U^{(k)}` are Cauchy
in `E^Q`-norm.. and uniformly; the limit `U` is continuous". This file
supplies the two generic real-analysis facts that make that step precise:
a sequence dominated by an envelope tending to `0` is Cauchy (already proved
once for `ℝ` in `aux_prop_gluing_three_eps` above the core section; this
generalizes it to any complete metric space, e.g. the `E^Q`-norm side), and a
uniformly-dominated family of continuous functions inherits a continuous
uniform limit from the dominating family's (e.g. `Bk`'s, `hCatalogDense`'s
`TendstoUniformlyOn`) uniform convergence — the `U_N^{(k)} → U` step. -/

/-- A sequence in a complete pseudometric space whose pairwise distance is
controlled by an envelope `C * (f k + f l)` with `f → 0` converges. Same
ε/3-style proof as `aux_prop_gluing_three_eps`, generalized from `ℝ` to any
`CompleteSpace`. -/
theorem aux_prop_gluing_cauchySeq_of_envelope {X : Type*} [PseudoMetricSpace X]
    [CompleteSpace X] (x : ℕ → X) (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Tendsto f atTop (𝓝 0))
    (hbound : ∀ k l : ℕ, dist (x k) (x l) ≤ C * (f k + f l)) :
    ∃ y : X, Tendsto x atTop (𝓝 y) := by
  by_cases hCzero : C = 0
  · subst hCzero
    simp only [zero_mul] at hbound
    have h_cauchy : CauchySeq x := by
      rw [Metric.cauchySeq_iff]
      intro ε' hε'
      refine ⟨0, fun m hm n hn => ?_⟩
      have h := hbound m n
      have hdist0 : dist (x m) (x n) = 0 := le_antisymm h dist_nonneg
      rw [hdist0]
      exact hε'
    exact cauchySeq_tendsto_of_complete h_cauchy
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hf_nonneg : ∀ k, 0 ≤ f k := by
      intro k
      have h := hbound k k
      simp only [dist_self, mul_add] at h
      nlinarith
    have hball : Metric.ball (0 : ℝ) (ε / (2 * (C + 1))) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds 0 (div_pos hε (by nlinarith))
    have hf_event : ∀ᶠ n in atTop, f n ∈ Metric.ball (0 : ℝ) (ε / (2 * (C + 1))) := hf hball
    have hf_bound : ∀ᶠ n in atTop, |f n| < ε / (2 * (C + 1)) := by
      filter_upwards [hf_event] with n hn
      rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hn
    rw [eventually_atTop] at hf_bound
    rcases hf_bound with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    have hfm : |f m| < ε / (2 * (C + 1)) := hN m hm
    have hfn : |f n| < ε / (2 * (C + 1)) := hN n hn
    have hfm_le : f m ≤ ε / (2 * (C + 1)) := le_trans (le_abs_self _) hfm.le
    have hfn_le : f n ≤ ε / (2 * (C + 1)) := le_trans (le_abs_self _) hfn.le
    calc
      dist (x m) (x n) ≤ C * (f m + f n) := hbound m n
      _ ≤ C * ((ε / (2 * (C + 1))) + (ε / (2 * (C + 1)))) := by
        nlinarith
      _ = C * (ε / (C + 1)) := by
        field_simp
        ring
      _ < ε := by
        have h : C / (C + 1) < 1 := by
          refine (div_lt_one ?_).mpr ?_
          · nlinarith
          · nlinarith
        calc
          C * (ε / (C + 1)) = (C / (C + 1)) * ε := by ring
          _ < 1 * ε := mul_lt_mul_of_pos_right h hε
          _ = ε := by simp

/-- If `F` is uniformly Cauchy on `s` and `G` is pointwise dominated by `F`'s
increments on `s`, `G` is uniformly Cauchy on `s` too (`Metric.uniformCauchySeqOn_iff`,
already used by `mathlib`'s own `UniformCauchySeqOn` API). -/
theorem aux_prop_gluing_uniformCauchySeqOn_of_le {γ : Type*} {s : Set γ}
    (F G : ℕ → γ → ℝ) (hF : UniformCauchySeqOn F atTop s)
    (hle : ∀ k l : ℕ, ∀ x ∈ s, dist (G k x) (G l x) ≤ dist (F k x) (F l x)) :
    UniformCauchySeqOn G atTop s := by
  rw [Metric.uniformCauchySeqOn_iff] at hF ⊢
  intro ε hε
  rcases hF ε hε with ⟨N, hN⟩
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  calc
    dist (G m x) (G n x) ≤ dist (F m x) (F n x) := hle m n x hx
    _ < ε := hN m hm n hn x hx

/-- A uniformly Cauchy sequence of functions `γ → ℝ`, each continuous on `s`,
converges uniformly on `s` to a function continuous on `s` (build the pointwise
limit from completeness of `ℝ`, then `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto`
and `TendstoUniformlyOn.continuousOn`). -/
theorem aux_prop_gluing_uniformCauchySeqOn_continuousOn_limit {γ : Type*}
    [TopologicalSpace γ] (F : ℕ → γ → ℝ) (s : Set γ) (hF : UniformCauchySeqOn F atTop s)
    (hFcont : ∀ n, ContinuousOn (F n) s) :
    ∃ U : γ → ℝ, TendstoUniformlyOn F U atTop s ∧ ContinuousOn U s := by
  have h_exists : ∀ x ∈ s, ∃ y : ℝ, Tendsto (fun n => F n x) atTop (𝓝 y) := by
    intro x hx
    have h_cauchy : CauchySeq (fun n => F n x) := hF.cauchySeq hx
    exact cauchySeq_tendsto_of_complete h_cauchy
  let U : γ → ℝ := fun x => if h : x ∈ s then Classical.choose (h_exists x h) else 0
  have hU : ∀ x ∈ s, Tendsto (fun n => F n x) atTop (𝓝 (U x)) := by
    intro x hx
    dsimp [U]
    rw [dite_eq_left hx]
    exact Classical.choose_spec (h_exists x hx)
  have h_tendsto : TendstoUniformlyOn F U atTop s :=
    hF.tendstoUniformlyOn_of_tendsto hU
  have h_cont : ContinuousOn U s :=
    h_tendsto.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall hFcont))
  exact ⟨U, h_tendsto, h_cont⟩

/-! ### Consumer: the patched extensions have a continuous uniform limit
(paper label `mfd:prop-gluing`: "the limits `U^{(k)}` are.. Cauchy.. uniformly; the
limit `U` is continuous"), given only that they are dominated by the already
uniformly-convergent smooth catalogue (`hCatalogDense`'s `TendstoUniformlyOn
Bk (Ext b0) atTop`, as in `aux_prop_gluing_patches`/`aux_prop_gluing_limit_object`
above) via the cellwise maximum principle. -/

/-- Given the catalogue extensions `Bk` converge uniformly to `b0` on `s`
(`hCatalogDense`), and a patch family `F` continuous on `s` with
`dist (F k x) (F l x) ≤ dist (Bk k x) (Bk l x)` there (the maximum-principle
domination of paper label `mfd:prop-gluing`), `F` converges uniformly on `s` to a
continuous `U`. -/
theorem aux_prop_gluing_patch_uniformLimit_continuousOn {d : ℕ}
    (s : Set (SpatialCoordinates d))
    (Bk : ℕ → SpatialCoordinates d → ℝ) (b0 : SpatialCoordinates d → ℝ)
    (hBk : TendstoUniformlyOn Bk b0 atTop s)
    (F : ℕ → SpatialCoordinates d → ℝ) (hFcont : ∀ n, ContinuousOn (F n) s)
    (hdom : ∀ k l : ℕ, ∀ x ∈ s, dist (F k x) (F l x) ≤ dist (Bk k x) (Bk l x)) :
    ∃ U : SpatialCoordinates d → ℝ, TendstoUniformlyOn F U atTop s ∧ ContinuousOn U s := by
  have hBcauchy : UniformCauchySeqOn Bk atTop s := hBk.uniformCauchySeqOn
  have hFcauchy : UniformCauchySeqOn F atTop s :=
    aux_prop_gluing_uniformCauchySeqOn_of_le Bk F hBcauchy hdom
  exact aux_prop_gluing_uniformCauchySeqOn_continuousOn_limit F s hFcauchy hFcont


end

/-! ## (GluePatchA) -/

/-! ### Coefficient congruence on a cell. -/

theorem aux_prop_gluing_harmonic_congr {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : MeasurableSet W) {a a' : SpatialCoordinates d → ℝ} (h : ∀ x ∈ W, a x = a' x)
    {u : H1Function W} (hu : IsWeaklyHarmonicOn a W u) : IsWeaklyHarmonicOn a' W u := by
  intro φ
  rw [← hu φ]
  exact setIntegral_congr_fun hW (fun x hx => by simp only [h x hx])

theorem aux_prop_gluing_energy_congr {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : MeasurableSet W) {a a' : SpatialCoordinates d → ℝ} (h : ∀ x ∈ W, a x = a' x)
    (u : H1Function W) : energy a W u = energy a' W u := by
  unfold energy
  exact setIntegral_congr_fun hW (fun x hx => by simp only [h x hx])

theorem aux_prop_gluing_infimum_congr {d : ℕ} {W : Set (SpatialCoordinates d)}
    (hW : MeasurableSet W) {a a' : SpatialCoordinates d → ℝ} (h : ∀ x ∈ W, a x = a' x)
    (beta : H1Function W) :
    cellDirichletInfimum a W beta = cellDirichletInfimum a' W beta := by
  unfold cellDirichletInfimum
  simp_rw [aux_prop_gluing_energy_congr hW h]

/-- A coefficient continuous on the closed enlarged cube extends continuously. -/
theorem aux_prop_gluing_coeff_extension {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsClosed K) (A : SpatialCoordinates d → ℝ) (hA : ContinuousOn A K) :
    ∃ a : SpatialCoordinates d → ℝ, Continuous a ∧ ∀ x ∈ K, a x = A x := by
  let f : C(K, ℝ) := ⟨fun x : K => A x, (continuousOn_iff_continuous_domRestrict.mp hA)⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hK f
  refine ⟨g, g.continuous, ?_⟩
  intro x hx
  have hxg := congrArg (fun h : C(K, ℝ) => h ⟨x, hx⟩) hg
  simpa [f] using! hxg

/-! ### Grid cell geometry. -/

theorem aux_prop_gluing_cell_eq {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h3r : 0 < 3 * r) (k : OddGridIndex d (triadicHalf 1)) :
    ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) =
      (centeredCube (oddGridCenter z (3 * r) (triadicHalf 1) k) r hr :
        Set (SpatialCoordinates d)) := by
  have hm : triadicHalf 1 = 1 := by decide
  show Metric.ball (oddGridCenter z (3 * r) (triadicHalf 1) k)
      ((3 * r / (2 * ((triadicHalf 1 : ℕ) : ℝ) + 1)) / 2) =
    Metric.ball (oddGridCenter z (3 * r) (triadicHalf 1) k) (r / 2)
  congr 1
  rw [hm]
  push_cast
  ring

theorem aux_prop_gluing_cell_domain {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h3r : 0 < 3 * r) (k : OddGridIndex d (triadicHalf 1)) :
    IsOpenBoundedConvexDomain
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) := by
  rw [aux_prop_gluing_cell_eq z r hr h3r k]
  exact isOpenBoundedConvexDomain_centeredCube _ hr

theorem aux_prop_gluing_cell_nonempty {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h3r : 0 < 3 * r) (k : OddGridIndex d (triadicHalf 1)) :
    ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)).Nonempty := by
  rw [aux_prop_gluing_cell_eq z r hr h3r k]
  exact ⟨_, Metric.mem_ball_self (by positivity)⟩

theorem aux_prop_gluing_cell_rescale_frontier {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (h3r : 0 < 3 * r) (k : OddGridIndex d (triadicHalf 1)) :
    ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)),
      (fun i => oddGridCenter z (3 * r) (triadicHalf 1) k i + r * y i) ∈
        frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) := by
  intro y hy
  rw [aux_prop_gluing_cell_eq z r hr h3r k]
  exact aux_prop_gluing_rescale_mem_frontier _ r hr y hy

/-! ### Cellwise maximum principle for differences (paper label `mfd:prop-gluing`). -/

theorem aux_prop_gluing_harmonic_diff_le {d : ℕ} [NeZero d] (W : Set (SpatialCoordinates d))
    (hW : IsOpenBoundedConvexDomain W) (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hlam : 0 < lam) (ha : Continuous a) (hab : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam)
    (u v φ ψ : H1Function W) (hu : IsWeaklyHarmonicOn a W u) (hv : IsWeaklyHarmonicOn a W v)
    (hut : HasZeroTraceDifferenceOn W u φ) (hvt : HasZeroTraceDifferenceOn W v ψ)
    (hucont : ContinuousOn u.toFun (closure W)) (hvcont : ContinuousOn v.toFun (closure W))
    (M : ℝ) (hM : ∀ y, φ.toFun y - ψ.toFun y ≤ M) :
    ∀ x ∈ closure W, u.toFun x - v.toFun x ≤ M := by
  have hWopen : IsOpen W := hW.1
  have hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField a) :=
    isEllipticFieldOn_scalar hWopen.measurableSet ha.measurable hlam hab
  have hdiff : IsWeaklyHarmonicOn a W (u - v) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.isWeaklyHarmonicOn_sub hEll hu hv
  obtain ⟨w, hw, -⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.exists_h10Function_solutionDifference_sub_boundaryDifference
      hut hvt
  have hmem : MemH10 W (fun y => (u - v).toFun y - (φ - ψ).toFun y) := by
    refine ⟨w, ?_⟩
    funext y
    rw [hw y]
    simp only [H1Function.sub_toFun]
  have hupper :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.hasBoundaryUpperBoundOn_of_datum_le
      hW hmem (fun y => by simpa only [H1Function.sub_toFun] using hM y)
  have hameas : AEStronglyMeasurable a (volumeMeasureOn W) := ha.aestronglyMeasurable
  have hbounds : ∀ᵐ y ∂(volumeMeasureOn W), lam ≤ a y ∧ a y ≤ Lam := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
    exact hab y hy
  have hae := SubdiffusiveProcess.CoarseGrainingVocab.ae_le_of_isWeaklyHarmonicOn hW hlam hameas hbounds
    hdiff hupper
  have hcont : ContinuousOn (fun y => u.toFun y - v.toFun y) (closure W) := hucont.sub hvcont
  have hae' : ∀ᵐ y ∂(volume.restrict W), u.toFun y - v.toFun y ≤ M := by
    filter_upwards [hae] with y hy
    simpa only [H1Function.sub_toFun] using hy
  have hW' : ∀ x ∈ W, u.toFun x - v.toFun x ≤ M :=
    le_of_ae_le_of_continuousOn hWopen (hcont.mono subset_closure) hae'
  intro x hx
  exact ContinuousWithinAt.closure_le hx ((hcont x hx).mono subset_closure)
    continuousWithinAt_const hW'

theorem aux_prop_gluing_harmonic_diff_abs_le {d : ℕ} [NeZero d] (W : Set (SpatialCoordinates d))
    (hW : IsOpenBoundedConvexDomain W) (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hlam : 0 < lam) (ha : Continuous a) (hab : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam)
    (u v φ ψ : H1Function W) (hu : IsWeaklyHarmonicOn a W u) (hv : IsWeaklyHarmonicOn a W v)
    (hut : HasZeroTraceDifferenceOn W u φ) (hvt : HasZeroTraceDifferenceOn W v ψ)
    (hucont : ContinuousOn u.toFun (closure W)) (hvcont : ContinuousOn v.toFun (closure W))
    (M : ℝ) (hM : ∀ y, |φ.toFun y - ψ.toFun y| ≤ M) :
    ∀ x ∈ closure W, |u.toFun x - v.toFun x| ≤ M := by
  intro x hx
  have h1 := aux_prop_gluing_harmonic_diff_le W hW a lam Lam hlam ha hab u v φ ψ hu hv hut hvt
    hucont hvcont M (fun y => (le_abs_self _).trans (hM y)) x hx
  have h2 := aux_prop_gluing_harmonic_diff_le W hW a lam Lam hlam ha hab v u ψ φ hv hu hvt hut
    hvcont hucont M (fun y => by
      have h := neg_le_abs (φ.toFun y - ψ.toFun y)
      have h' := hM y
      linarith) x hx
  rw [abs_le]
  constructor <;> linarith

/-! ### Dirichlet principle on a cell. -/

theorem aux_prop_gluing_energy_eq_infimum {d : ℕ} [NeZero d] (W : Set (SpatialCoordinates d))
    (hW : IsOpenBoundedConvexDomain W) (hne : W.Nonempty) (a : SpatialCoordinates d → ℝ)
    (lam Lam : ℝ) (hlam : 0 < lam) (ha : Continuous a)
    (hab : ∀ x ∈ W, lam ≤ a x ∧ a x ≤ Lam)
    (w : H1Function W) (hw : IsWeaklyHarmonicOn a W w) :
    energy a W w = cellDirichletInfimum a W w := by
  have hEll := isEllipticFieldOn_scalar hW.1.measurableSet ha.measurable hlam hab
  exact energy_eq_sInf_sameTrace_of_isWeaklyHarmonicOn hW hne hEll hw
    (aux_prop_gluing_zeroTrace_refl W w)

/-! ### Sobolev data and the cell decomposition of the response form. -/

theorem aux_prop_gluing_sobolevDataOfH1_sub {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (u v : H1Function (Ω : Set (SpatialCoordinates d))) :
    sobolevDataOfH1 (u - v) = sobolevDataOfH1 u - sobolevDataOfH1 v := by
  unfold sobolevDataOfH1
  ext1
  · simp only [Prod.fst_sub]
    rw [← MemLp.toLp_sub]
    apply (MemLp.toLp_eq_toLp_iff _ _).mpr
    exact Filter.Eventually.of_forall (fun x => by simp)
  · funext i
    simp only [Prod.snd_sub, Pi.sub_apply]
    rw [← MemLp.toLp_sub]
    apply (MemLp.toLp_eq_toLp_iff _ _).mpr
    exact Filter.Eventually.of_forall (fun x => by simp)

theorem aux_prop_gluing_responseForm_eq_energy {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (aC : PositiveCoefficient Ω) (a : SpatialCoordinates d → ℝ)
    (haC : ((aC.val : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] a)
    (Lam : ℝ) (ha0 : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), 0 ≤ a x)
    (haLam : ∀ x ∈ (Ω : Set (SpatialCoordinates d)), a x ≤ Lam)
    (hameas : AEStronglyMeasurable a (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (x : S.space) (D : H1Function (Ω : Set (SpatialCoordinates d)))
    (hx : (x : SobolevData Ω) = sobolevDataOfH1 D) :
    responseForm S aC x x = energy a (Ω : Set (SpatialCoordinates d)) D := by
  rw [responseForm_apply, hx]
  unfold energy
  have hi : ∀ i : Fin d, ∫ y in (Ω : Set (SpatialCoordinates d)),
      aC.val y * ((sobolevDataOfH1 D).2 i y * (sobolevDataOfH1 D).2 i y) =
      ∫ y in (Ω : Set (SpatialCoordinates d)), a y * (D.grad y i * D.grad y i) := by
    intro i
    apply integral_congr_ae
    filter_upwards [haC, sobolevDataOfH1_snd_coeFn D i] with y h1 h2
    rw [h1, h2]
  simp_rw [hi]
  rw [← integral_finsetSum]
  · congr 1
    funext y
    simp only [vecDot, Finset.mul_sum]
  · intro i _
    have hint : Integrable (fun y => D.grad y i * D.grad y i)
        (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
      (D.gradMemL2 i).integrable_mul (D.gradMemL2 i)
    refine Integrable.bdd_mul (c := Lam) hint hameas ?_
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (ha0 y hy)]
    exact haLam y hy

theorem aux_prop_gluing_energy_split {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (a : SpatialCoordinates d → ℝ) (Lam : ℝ)
    (ha0 : ∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), 0 ≤ a x)
    (haLam : ∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), a x ≤ Lam)
    (hameas : AEStronglyMeasurable a
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (D : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) :
    energy a (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) D =
      ∑ k : OddGridIndex d (triadicHalf 1),
        energy a ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          (D.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)) := by
  unfold energy
  have hint : IntegrableOn (fun x => a x * vecDot (D.grad x) (D.grad x))
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    aux_prop_gluing_weighted_integrable _ (centeredCube z (3 * r) h3r).isOpen.measurableSet
      a Lam ha0 haLam hameas D D
  rw [← setIntegral_congr_set (oddGrid_union_ae_eq z h3r (triadicHalf 1))]
  rw [integral_iUnion_fintype (fun k => (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen.measurableSet)
    (oddGridCell_pairwiseDisjoint z h3r _) (fun k => hint.mono_set (hcellsub k))]
  rfl

/-! ## (GluePatchB) -/

/-- Cellwise maximum principle for two finite-cutoff patches on the whole closed
enlarged cube (paper label `mfd:prop-gluing`: `‖U_N^{(k)} - U_N^{(l)}‖_∞ ≤ ‖β_k - β_l‖_∞`). -/
theorem aux_prop_gluing_patch_max {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam) (ha : Continuous a)
    (hab : ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam)
    (u v φ ψ : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hu : ∀ k : OddGridIndex d (triadicHalf 1), IsWeaklyHarmonicOn a
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))
      (u.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)))
    (hv : ∀ k : OddGridIndex d (triadicHalf 1), IsWeaklyHarmonicOn a
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))
      (v.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)))
    (hut : ∀ k : OddGridIndex d (triadicHalf 1), HasZeroTraceDifferenceOn
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))
      (u.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))
      (φ.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)))
    (hvt : ∀ k : OddGridIndex d (triadicHalf 1), HasZeroTraceDifferenceOn
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))
      (v.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))
      (ψ.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)))
    (hucont : ContinuousOn u.toFun
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hvcont : ContinuousOn v.toFun
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (M : ℝ) (hM : ∀ y, |φ.toFun y - ψ.toFun y| ≤ M) :
    ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      |u.toFun x - v.toFun x| ≤ M := by
  intro x hx
  rw [← oddGridCell_closure_iUnion_eq_closure_centeredCube z h3r (triadicHalf 1)] at hx
  obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
  have hcl : closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) ⊆
      closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    closure_mono (hcellsub k)
  exact aux_prop_gluing_harmonic_diff_abs_le _ (aux_prop_gluing_cell_domain z r hr h3r k)
    a lam Lam hlam ha (fun y hy => hab y (subset_closure (hcellsub k hy)))
    (u.restrict _ (hcellsub k)) (v.restrict _ (hcellsub k))
    (φ.restrict _ (hcellsub k)) (ψ.restrict _ (hcellsub k)) (hu k) (hv k) (hut k) (hvt k)
    (hucont.mono hcl) (hvcont.mono hcl) M hM x hxk

/-- The response form controls the full graph norm on the response space
(Poincaré plus coercivity). -/
theorem aux_prop_gluing_norm_le_grad {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (x : S.space) (K : ℝ≥0)
    (hP : ‖(x : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient S.space x‖) :
    ‖x‖ ≤ (max K 1 : ℝ≥0) * ‖subspaceGradient S.space x‖ := by
  have hs : subspaceGradient S.space x = sobolevGradient (x : SobolevData Ω) := by
    simp [subspaceGradient]
  rw [hs] at hP ⊢
  have hn : ‖x‖ = ‖(x : SobolevData Ω)‖ := (Submodule.norm_coe x).symm
  rw [hn]
  exact sobolevData_norm_le_gradient (x : SobolevData Ω) hP

theorem aux_prop_gluing_form_eq_grad {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (aC : PositiveCoefficient Ω) (x : S.space) :
    responseForm S aC x x =
      weightedGradientForm aC.val (subspaceGradient S.space x) (subspaceGradient S.space x) :=
  rfl

theorem aux_prop_gluing_norm_le_form {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (aC : PositiveCoefficient Ω) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ x : S.space,
      C * (‖x‖ / K) ^ 2 ≤ responseForm S aC x x := by
  obtain ⟨K, hP⟩ := S.poincare
  obtain ⟨c, hc, hca⟩ := aC.property
  obtain ⟨C, hC, hcoer⟩ := weightedGradientForm_coercive aC.val hc hca
  have hKp : (1 : ℝ) ≤ ((max K 1 : ℝ≥0) : ℝ) := by exact_mod_cast le_max_right K 1
  refine ⟨((max K 1 : ℝ≥0) : ℝ), C, by linarith, hC, fun x => ?_⟩
  have h1 := aux_prop_gluing_norm_le_grad S x K (hP x)
  have h2 := hcoer (subspaceGradient S.space x)
  rw [aux_prop_gluing_form_eq_grad]
  have hq : ‖x‖ / ((max K 1 : ℝ≥0) : ℝ) ≤ ‖subspaceGradient S.space x‖ := by
    rw [div_le_iff₀ (by linarith)]
    linarith [mul_comm (((max K 1 : ℝ≥0) : ℝ)) ‖subspaceGradient S.space x‖]
  have hq0 : 0 ≤ ‖x‖ / ((max K 1 : ℝ≥0) : ℝ) := div_nonneg (norm_nonneg _) (by linarith)
  calc C * (‖x‖ / ((max K 1 : ℝ≥0) : ℝ)) ^ 2 ≤ C * ‖subspaceGradient S.space x‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact pow_le_pow_left₀ hq0 hq 2
    _ = C * ‖subspaceGradient S.space x‖ * ‖subspaceGradient S.space x‖ := by ring
    _ ≤ _ := h2

/-- A response-form Cauchy sequence converges in the response space. -/
theorem aux_prop_gluing_space_limit {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (aC : PositiveCoefficient Ω) (WS : ℕ → S.space)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ l ≥ J,
      responseForm S aC (WS j - WS l) (WS j - WS l) ≤ ε) :
    ∃ US : S.space, Tendsto WS atTop (𝓝 US) := by
  obtain ⟨K, C, hK, hC, hbound⟩ := aux_prop_gluing_norm_le_form S aC
  have : CompleteSpace S.space := S.closed.completeSpace_coe
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨J, hJ⟩ := hCauchy (C * (ε / (2 * K)) ^ 2) (by positivity)
  refine ⟨J, fun j hj l hl => ?_⟩
  rw [dist_eq_norm]
  have h1 := hbound (WS j - WS l)
  have h2 := hJ j hj l hl
  have h3 : (‖WS j - WS l‖ / K) ^ 2 ≤ (ε / (2 * K)) ^ 2 := by
    have := h1.trans h2
    exact le_of_mul_le_mul_left this hC
  have h4 : ‖WS j - WS l‖ / K ≤ ε / (2 * K) :=
    (pow_le_pow_iff_left₀ (div_nonneg (norm_nonneg _) hK.le) (by positivity) two_ne_zero).mp h3
  have h5 : ‖WS j - WS l‖ ≤ ε / 2 := by
    rw [div_le_div_iff₀ hK (by positivity)] at h4
    nlinarith
  linarith

/-- Integrals against a fixed square-integrable weight on a subset pass to the
`L²` limit. -/
theorem aux_prop_gluing_tendsto_setIntegral_mul {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (V : Set (SpatialCoordinates d)) (hV : MeasurableSet V)
    (hVΩ : V ⊆ (Ω : Set (SpatialCoordinates d)))
    (h : SpatialCoordinates d → ℝ) (hh : MemLp h 2 (volume.restrict V))
    (f : ℕ → DomainL2 Ω) (g : DomainL2 Ω) (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => ∫ x in V, h x * (f n : SpatialCoordinates d → ℝ) x) atTop
      (𝓝 (∫ x in V, h x * (g : SpatialCoordinates d → ℝ) x)) := by
  have hrr : (volume.restrict (Ω : Set (SpatialCoordinates d))).restrict V =
      volume.restrict V := by
    rw [Measure.restrict_restrict hV, inter_eq_left.mpr hVΩ]
  have hmem : MemLp (V.indicator h) 2 (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    rw [memLp_indicator_iff_restrict hV, hrr]
    exact hh
  set H : DomainL2 Ω := hmem.toLp _ with hH
  have key : ∀ F : DomainL2 Ω, inner ℝ H F = ∫ x in V, h x * (F : SpatialCoordinates d → ℝ) x := by
    intro F
    rw [L2.inner_def]
    have hcongr : ∫ x, inner ℝ ((H : SpatialCoordinates d → ℝ) x) ((F : SpatialCoordinates d → ℝ) x)
          ∂(volume.restrict (Ω : Set (SpatialCoordinates d))) =
        ∫ x, V.indicator (fun x => h x * (F : SpatialCoordinates d → ℝ) x) x
          ∂(volume.restrict (Ω : Set (SpatialCoordinates d))) := by
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with x hx
      rw [hx]
      by_cases hxV : x ∈ V
      · simp [Set.indicator_of_mem hxV, mul_comm]
      · simp [Set.indicator_of_notMem hxV]
    rw [hcongr, integral_indicator hV, hrr]
  simp_rw [← key]
  exact tendsto_const_nhds.inner hf

/-- Weak harmonicity on a cell passes to `L²` limits of the gradients. -/
theorem aux_prop_gluing_harmonic_limit {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (V : Set (SpatialCoordinates d)) (hV : MeasurableSet V)
    (hVΩ : V ⊆ (Ω : Set (SpatialCoordinates d)))
    (a : SpatialCoordinates d → ℝ) (Lam : ℝ) (ha0 : ∀ x ∈ V, 0 ≤ a x)
    (haLam : ∀ x ∈ V, a x ≤ Lam) (hameas : AEStronglyMeasurable a (volume.restrict V))
    (G : ℕ → Fin d → DomainL2 Ω) (Glim : Fin d → DomainL2 Ω)
    (hG : ∀ i, Tendsto (fun n => G n i) atTop (𝓝 (Glim i)))
    (u : ℕ → H1Function V)
    (hu : ∀ n i, (fun x => (u n).grad x i) =ᵐ[volume.restrict V]
      ((G n i : DomainL2 Ω) : SpatialCoordinates d → ℝ))
    (hharm : ∀ n, IsWeaklyHarmonicOn a V (u n))
    (U : H1Function V)
    (hU : ∀ i, (fun x => U.grad x i) =ᵐ[volume.restrict V]
      ((Glim i : DomainL2 Ω) : SpatialCoordinates d → ℝ)) :
    IsWeaklyHarmonicOn a V U := by
  intro φ
  have hw : ∀ i : Fin d, MemLp (fun x => a x * φ.toH1Function.grad x i) 2 (volume.restrict V) := by
    intro i
    refine MemLp.of_le_mul (c := Lam) (φ.toH1Function.gradMemL2 i) ?_ ?_
    · exact hameas.mul (φ.toH1Function.gradMemL2 i).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hV] with x hx
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (ha0 x hx)]
      exact mul_le_mul_of_nonneg_right (haLam x hx) (norm_nonneg _)
  have hexpand : ∀ w : H1Function V, (∀ i : Fin d, MemLp (fun x => w.grad x i) 2 (volume.restrict V)) →
      ∫ x in V, vecDot (a x • w.grad x) (φ.toH1Function.grad x) =
        ∑ i : Fin d, ∫ x in V, (a x * φ.toH1Function.grad x i) * w.grad x i := by
    intro w hwm
    rw [← integral_finsetSum]
    · congr 1
      funext x
      simp only [vecDot, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    · intro i _
      exact (hw i).integrable_mul (hwm i)
  have hn : ∀ n, ∑ i : Fin d, ∫ x in V, (a x * φ.toH1Function.grad x i) *
      ((G n i : DomainL2 Ω) : SpatialCoordinates d → ℝ) x = 0 := by
    intro n
    rw [← hharm n φ, hexpand (u n) (u n).gradMemL2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    apply integral_congr_ae
    filter_upwards [hu n i] with x hx
    rw [hx]
  have hlim : Tendsto (fun n => ∑ i : Fin d, ∫ x in V, (a x * φ.toH1Function.grad x i) *
      ((G n i : DomainL2 Ω) : SpatialCoordinates d → ℝ) x) atTop
      (𝓝 (∑ i : Fin d, ∫ x in V, (a x * φ.toH1Function.grad x i) *
        ((Glim i : DomainL2 Ω) : SpatialCoordinates d → ℝ) x)) :=
    tendsto_finsetSum _ (fun i _ =>
      aux_prop_gluing_tendsto_setIntegral_mul V hV hVΩ _ (hw i) _ _ (hG i))
  simp_rw [hn] at hlim
  have hzero := tendsto_nhds_unique tendsto_const_nhds hlim
  rw [hexpand U U.gradMemL2, hzero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply integral_congr_ae
  filter_upwards [hU i] with x hx
  rw [hx]

/-- An `H¹` carrier with a prescribed representative of the `L²` coordinate of a
response-space element. -/
theorem aux_prop_gluing_h1_of_space {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (US : S.space) (Uf : SpatialCoordinates d → ℝ)
    (hU : (((US : SobolevData Ω).1 : DomainL2 Ω) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] Uf) :
    ∃ U : H1Function (Ω : Set (SpatialCoordinates d)),
      U.toFun = Uf ∧
      U.grad = (fun x i => (((US : SobolevData Ω).2 i : DomainL2 Ω) :
        SpatialCoordinates d → ℝ) x) ∧
      (US : SobolevData Ω) = sobolevDataOfH1 U := by
  have hweak := (mem_weakSobolevGraph_iff_hasWeakGradientOn (US : SobolevData Ω)).mp
    (S.le_weak US.2)
  have hweakU : HasWeakGradientOn (Ω : Set (SpatialCoordinates d)) Uf
      (fun x i => (((US : SobolevData Ω).2 i : DomainL2 Ω) : SpatialCoordinates d → ℝ) x) :=
    fun i => _root_.SubdiffusiveProcess.EllipticRegularity.hasWeakPartialDerivOn_congr_ae hU (Filter.EventuallyEq.refl _ _) (hweak i)
  have hmem : MemL2On (Ω : Set (SpatialCoordinates d)) Uf :=
    (Lp.memLp ((US : SobolevData Ω).1)).ae_eq hU
  let U : H1Function (Ω : Set (SpatialCoordinates d)) :=
    { toFun := Uf
      grad := fun x i => (((US : SobolevData Ω).2 i : DomainL2 Ω) : SpatialCoordinates d → ℝ) x
      memL2 := hmem
      gradMemL2 := fun i => Lp.memLp _
      hasWeakGradient := hweakU }
  refine ⟨U, rfl, rfl, ?_⟩
  unfold sobolevDataOfH1
  ext1
  · apply Lp.ext
    filter_upwards [hU, MemLp.coeFn_toLp U.memL2] with x h1 h2
    rw [h2, h1]
  · funext i
    exact (Lp.toLp_coeFn ((US : SobolevData Ω).2 i) (Lp.memLp _)).symm

/-! ## (GluePatchC) -/

/-- : the energy of the difference of two finite-cutoff cell-harmonic
patches is bounded, cell by cell, by `eq:mfd-2` for the difference of their
data. -/
theorem aux_prop_gluing_grid_energy_bound {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta : ℝ) (_hbeta0 : 0 ≤ beta)
    (An a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam) (ha : Continuous a)
    (hab : ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam)
    (haA : ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      a x = An x)
    (C : ℝ) (hC : 0 ≤ C) (Ug UgStar : OddGridIndex d (triadicHalf 1) → ℝ)
    (hUg : ∀ k, 0 ≤ Ug k ∧ Ug k ≤ UgStar k)
    (hGridBound : ∀ (k : OddGridIndex d (triadicHalf 1)),
        ∀ e : H1Function
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
              Set (SpatialCoordinates d)),
        ContinuousOn e.toFun
            (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun →
        cellDirichletInfimum An
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
              Set (SpatialCoordinates d)) e ≤
          C * Ug k * r ^ ((d : ℝ) - 2) *
            cellBoundaryQuotientNorm beta
              (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun ^ 2)
    (u v : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hu : ∀ k : OddGridIndex d (triadicHalf 1), IsWeaklyHarmonicOn a
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))
      (u.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)))
    (hv : ∀ k : OddGridIndex d (triadicHalf 1), IsWeaklyHarmonicOn a
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))
      (v.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)))
    (hucont : ContinuousOn u.toFun
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hvcont : ContinuousOn v.toFun
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (G : SpatialCoordinates d → ℝ)
    (hface : ∀ k : OddGridIndex d (triadicHalf 1),
      ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
        u.toFun x - v.toFun x = G x)
    (hG : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G)
    (hGb : BddAbove {w : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), w = |G x|}) :
    energy a (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) (u - v) ≤
      (∑ k : OddGridIndex d (triadicHalf 1),
        C * UgStar k * r ^ ((d : ℝ) - 2) * (max 1 (r ^ beta)) ^ 2) *
        _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G ^ 2 := by
  have hQmeas := (centeredCube z (3 * r) h3r).isOpen.measurableSet
  have ha0Q : ∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), 0 ≤ a x :=
    fun x hx => hlam.le.trans (hab x (subset_closure hx)).1
  have haLQ : ∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), a x ≤ Lam :=
    fun x hx => (hab x (subset_closure hx)).2
  rw [aux_prop_gluing_energy_split z r h3r hcellsub a Lam ha0Q haLQ
    ha.aestronglyMeasurable (u - v), Finset.sum_mul]
  refine Finset.sum_le_sum (fun k _ => ?_)
  set V : Set (SpatialCoordinates d) := ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) with hV
  have hVdom := aux_prop_gluing_cell_domain z r hr h3r k
  have hVne := aux_prop_gluing_cell_nonempty z r hr h3r k
  have hVmeas : MeasurableSet V := (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen.measurableSet
  have hVcl : closure V ⊆ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    closure_mono (hcellsub k)
  have habV : ∀ x ∈ V, lam ≤ a x ∧ a x ≤ Lam := fun x hx => hab x (subset_closure (hcellsub k hx))
  have hEll := isEllipticFieldOn_scalar hVmeas ha.measurable hlam habV
  set D : H1Function V :=
    (u - v).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k) with hD
  have hDeq : D = u.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k) -
      v.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k) := rfl
  have hDharm : IsWeaklyHarmonicOn a V D := by
    rw [hDeq]
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.isWeaklyHarmonicOn_sub hEll (hu k) (hv k)
  have hDcont : ContinuousOn D.toFun (closure V) := by
    have : D.toFun = fun x => u.toFun x - v.toFun x := by
      rw [hD]
      exact H1Function.sub_toFun u v
    rw [this]
    exact (hucont.sub hvcont).mono hVcl
  have hDface : ∀ x ∈ frontier V, D.toFun x = G x := by
    intro x hx
    have : D.toFun x = u.toFun x - v.toFun x := by
      rw [hD]
      exact congrFun (H1Function.sub_toFun u v) x
    rw [this]
    exact hface k x hx
  -- the rescaling chart maps the unit frontier into the cell frontier
  have hS : ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      (fun i => oddGridCenter z (3 * r) (triadicHalf 1) k i + r * y i) ∈
        closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    fun y hy => hVcl (frontier_subset_closure
      (aux_prop_gluing_cell_rescale_frontier z r hr h3r k y hy))
  have hresc : ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      rescaledDatum (oddGridCenter z (3 * r) (triadicHalf 1) k) r G y =
        rescaledDatum (oddGridCenter z (3 * r) (triadicHalf 1) k) r D.toFun y :=
    fun y hy => (hDface _ (aux_prop_gluing_cell_rescale_frontier z r hr h3r k y hy)).symm
  have hclassG : IsCellBoundaryClass beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r G :=
    ⟨aux_prop_gluing_isHolderOn_rescale_gen _ r hr _ hS beta G hG,
      aux_prop_gluing_bddAbove_rescale _ r _ hS G hGb⟩
  have hclassD : IsCellBoundaryClass beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r
      D.toFun := by
    refine ⟨aux_prop_gluing_isHolderOn_congr _ _ _ beta hresc hclassG.1, ?_⟩
    obtain ⟨M, hM⟩ := hclassG.2
    refine ⟨M, ?_⟩
    rintro w ⟨y, hy, rfl⟩
    rw [← hresc y hy]
    exact hM ⟨y, hy, rfl⟩
  have hnorm : cellBoundaryQuotientNorm beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r
      D.toFun = cellBoundaryQuotientNorm beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r G :=
    (aux_prop_gluing_quotientCBetaNorm_congr beta _ _ _ hresc).symm
  have hNle := aux_prop_gluing_quotientNorm_le _ r hr _ hS beta G hG hGb
  have hN0 := aux_prop_gluing_quotientNorm_nonneg beta
    (oddGridCenter z (3 * r) (triadicHalf 1) k) r G
  have hbound := hGridBound k D hDcont hclassD
  have heq : energy a V D = cellDirichletInfimum An V D := by
    rw [aux_prop_gluing_energy_eq_infimum V hVdom hVne a lam Lam hlam ha habV D hDharm]
    exact aux_prop_gluing_infimum_congr hVmeas
      (fun x hx => haA x (subset_closure (hcellsub k hx))) D
  have hrpow : 0 ≤ r ^ ((d : ℝ) - 2) := Real.rpow_nonneg hr.le _
  have hcA := aux_prop_gluing_cAlphaNorm_nonneg beta
    (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G
  have hm0 : 0 ≤ max 1 (r ^ beta) := le_trans zero_le_one (le_max_left _ _)
  change energy a V D ≤ _
  rw [heq, hnorm] at *
  calc cellDirichletInfimum An V D ≤ C * Ug k * r ^ ((d : ℝ) - 2) *
        cellBoundaryQuotientNorm beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r G ^ 2 :=
        hbound
    _ ≤ C * UgStar k * r ^ ((d : ℝ) - 2) *
        (max 1 (r ^ beta) * _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G) ^ 2 := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ hrpow
          exact mul_le_mul_of_nonneg_left (hUg k).2 hC
        · exact pow_le_pow_left₀ hN0 hNle 2
        · positivity
        · exact mul_nonneg (mul_nonneg hC ((hUg k).1.trans (hUg k).2)) hrpow
    _ = C * UgStar k * r ^ ((d : ℝ) - 2) * max 1 (r ^ beta) ^ 2 *
        _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G ^ 2 := by
        ring

/-! ## (GluePatchD) -/

/-- Uniform part of the completion (paper label `mfd:prop-gluing`): the finite-cutoff patches of
uniformly convergent catalogue data converge uniformly on the closed cube, with
the maximum-principle comparison inherited by the limit. -/
theorem aux_prop_gluing_patch_uniform {d : ℕ} (s : Set (SpatialCoordinates d))
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hBs : TendstoUniformly Bs B atTop)
    (F : ℕ → SpatialCoordinates d → ℝ) (hFcont : ∀ j, ContinuousOn (F j) s)
    (hmax : ∀ j l M, (∀ y, |Bs j y - Bs l y| ≤ M) → ∀ x ∈ s, |F j x - F l x| ≤ M) :
    ∃ Uf : SpatialCoordinates d → ℝ, TendstoUniformlyOn F Uf atTop s ∧ ContinuousOn Uf s ∧
      ∀ l M, (∀ y, |B y - Bs l y| ≤ M) → ∀ x ∈ s, |Uf x - F l x| ≤ M := by
  have hBsC : UniformCauchySeqOn Bs atTop univ :=
    (tendstoUniformlyOn_univ.mpr hBs).uniformCauchySeqOn
  have hFC : UniformCauchySeqOn F atTop s := by
    rw [Metric.uniformCauchySeqOn_iff] at hBsC ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hBsC (ε / 2) (by positivity)
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    have h := hmax m n (ε / 2) (fun y => by
      have := hN m hm n hn y (mem_univ y)
      rw [Real.dist_eq] at this
      exact this.le) x hx
    rw [Real.dist_eq]
    linarith
  obtain ⟨Uf, hUf, hUfc⟩ := aux_prop_gluing_uniformCauchySeqOn_continuousOn_limit F s hFC hFcont
  refine ⟨Uf, hUf, hUfc, fun l M hM x hx => ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ j in atTop, |F j x - F l x| ≤ M + ε := by
    have hBu := (Metric.tendstoUniformly_iff.mp hBs) ε hε
    filter_upwards [hBu] with j hj
    apply hmax j l (M + ε) (fun y => ?_) x hx
    have h1 := hj y
    rw [Real.dist_eq] at h1
    have h2 := hM y
    calc |Bs j y - Bs l y| = |(Bs j y - B y) + (B y - Bs l y)| := by ring_nf
      _ ≤ |Bs j y - B y| + |B y - Bs l y| := abs_add_le _ _
      _ ≤ ε + M := by
          have : |Bs j y - B y| = |B y - Bs j y| := abs_sub_comm _ _
          linarith
      _ = M + ε := by ring
  have hlim : Tendsto (fun j => |F j x - F l x|) atTop (𝓝 |Uf x - F l x|) :=
    ((hUf.tendsto_at hx).sub tendsto_const_nhds).abs
  exact le_of_tendsto hlim hev

/-- The closed enlarged cube is compact. -/
theorem aux_prop_gluing_closure_compact {d : ℕ} (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    IsCompact (closure (centeredCube z R hR : Set (SpatialCoordinates d))) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure
    (centeredCube_isBounded z hR).closure

/-- A function continuous on the closed cube is square integrable on the cube. -/
theorem aux_prop_gluing_memLp_of_continuousOn {d : ℕ} (z : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) (f : SpatialCoordinates d → ℝ)
    (hf : ContinuousOn f (closure (centeredCube z R hR : Set (SpatialCoordinates d)))) :
    MemLp f 2 (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) := by
  have : IsFiniteMeasure (volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))) :=
    isFiniteMeasure_restrict.mpr (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top)
  obtain ⟨M, hM⟩ := (aux_prop_gluing_closure_compact z R hR).exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable
    (centeredCube z R hR).isOpen.measurableSet) M ?_
  filter_upwards [ae_restrict_mem (centeredCube z R hR).isOpen.measurableSet] with x hx
  exact hM x (subset_closure hx)

/-- : completion of the smooth-catalogue patches for fixed cutoff. -/
theorem aux_prop_gluing_patch_limit {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ) (hlam : 0 < lam) (ha : Continuous a)
    (hab : ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam)
    (aC : PositiveCoefficient (centeredCube z (3 * r) h3r))
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hBs : TendstoUniformly Bs B atTop)
    (PhiH : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hPhiH : ∀ j, (PhiH j).toFun = Bs j)
    (W : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (WS : ℕ → S.space)
    (hWS : ∀ j, (WS j : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (W j))
    (hWcont : ∀ j, ContinuousOn (W j).toFun
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hWzero : ∀ j, ∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      (W j).toFun x = 0)
    (hWharm : ∀ j (k : OddGridIndex d (triadicHalf 1)), IsWeaklyHarmonicOn a
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))
      ((W j).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)))
    (hWtrace : ∀ j (k : OddGridIndex d (triadicHalf 1)), HasZeroTraceDifferenceOn
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))
      ((W j).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))
      ((PhiH j).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)))
    (hWface : ∀ j (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
        (W j).toFun x = Bs j x)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ l ≥ J,
      responseForm S aC (WS j - WS l) (WS j - WS l) ≤ ε) :
    ∃ (U : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (US : S.space),
      (US : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 U ∧
      ContinuousOn U.toFun
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        U.toFun x = 0) ∧
      (∀ k : OddGridIndex d (triadicHalf 1),
        IsWeaklyHarmonicOn a
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
              Set (SpatialCoordinates d))
            (U.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)) ∧
          ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
            U.toFun x = B x) ∧
      (∀ l M, (∀ y, |B y - Bs l y| ≤ M) →
        ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          |U.toFun x - (W l).toFun x| ≤ M) := by
  have hQmeas : MeasurableSet (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) := (centeredCube z (3 * r) h3r).isOpen.measurableSet
  have hfin : volume (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ≠ ⊤ := by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top
  -- maximum principle between patches
  have hmax : ∀ j l M, (∀ y, |Bs j y - Bs l y| ≤ M) →
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), |(W j).toFun x - (W l).toFun x| ≤ M := by
    intro j l M hM
    exact aux_prop_gluing_patch_max z r hr h3r hcellsub a lam Lam hlam ha hab (W j) (W l)
      (PhiH j) (PhiH l) (hWharm j) (hWharm l) (hWtrace j) (hWtrace l) (hWcont j) (hWcont l) M
      (fun y => by rw [hPhiH j, hPhiH l]; exact hM y)
  obtain ⟨Uf, hUf, hUfc, hcomp⟩ := aux_prop_gluing_patch_uniform (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) Bs B hBs
    (fun j => (W j).toFun) hWcont hmax
  obtain ⟨US, hUS⟩ := aux_prop_gluing_space_limit S aC WS hCauchy
  -- identification of the L² coordinate
  have hmemU := aux_prop_gluing_memLp_of_continuousOn z (3 * r) h3r Uf hUfc
  have hL2a : Tendsto (fun j => ((WS j : SobolevData (centeredCube z (3 * r) h3r)).1))
      atTop (𝓝 (hmemU.toLp Uf)) :=
    aux_prop_gluing_tendsto_L2_of_uniform hfin _ (fun j => (W j).toFun) _ Uf
      (fun j => by rw [hWS j]; exact sobolevDataOfH1_fst_coeFn (W j))
      (MemLp.coeFn_toLp hmemU) (hUf.mono subset_closure)
  have hcoord : Continuous (fun x : S.space => ((x : SobolevData (centeredCube z (3 * r) h3r)).1)) :=
    continuous_fst.comp continuous_subtype_val
  have hL2b : Tendsto (fun j => ((WS j : SobolevData (centeredCube z (3 * r) h3r)).1))
      atTop (𝓝 ((US : SobolevData (centeredCube z (3 * r) h3r)).1)) :=
    (hcoord.tendsto US).comp hUS
  have hideq := tendsto_nhds_unique hL2a hL2b
  have hUae : (((US : SobolevData (centeredCube z (3 * r) h3r)).1 :
      DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uf := by
    rw [← hideq]
    exact MemLp.coeFn_toLp hmemU
  obtain ⟨U, hUfun, hUgrad, hUdata⟩ := aux_prop_gluing_h1_of_space S US Uf hUae
  refine ⟨U, US, hUdata, by rw [hUfun]; exact hUfc, ?_, ?_, ?_⟩
  · intro x hx
    rw [hUfun]
    have hxcl : x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) := frontier_subset_closure hx
    have h1 := hUf.tendsto_at hxcl
    have h2 : (fun j => (W j).toFun x) = fun _ => (0 : ℝ) := funext fun j => hWzero j x hx
    rw [h2] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  · intro k
    have hVmeas := (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen.measurableSet
    refine ⟨?_, ?_⟩
    · have hgrad : ∀ i, Tendsto (fun n => (WS n : SobolevData (centeredCube z (3 * r) h3r)).2 i)
          atTop (𝓝 ((US : SobolevData (centeredCube z (3 * r) h3r)).2 i)) := by
        intro i
        have hc : Continuous (fun x : S.space =>
            (x : SobolevData (centeredCube z (3 * r) h3r)).2 i) :=
          (continuous_apply i).comp (continuous_snd.comp continuous_subtype_val)
        exact (hc.tendsto US).comp hUS
      refine aux_prop_gluing_harmonic_limit (Ω := centeredCube z (3 * r) h3r) _ hVmeas (hcellsub k) a Lam
        (fun x hx => hlam.le.trans (hab x (subset_closure (hcellsub k hx))).1)
        (fun x hx => (hab x (subset_closure (hcellsub k hx))).2)
        ha.aestronglyMeasurable
        (fun n i => (WS n : SobolevData (centeredCube z (3 * r) h3r)).2 i)
        (fun i => (US : SobolevData (centeredCube z (3 * r) h3r)).2 i) hgrad
        (fun n => (W n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))
        (fun n i => ?_) (fun n => hWharm n k) _ (fun i => ?_)
      · have h0 := sobolevDataOfH1_snd_coeFn (W n) i
        rw [← hWS n] at h0
        have h1 : (((WS n : SobolevData (centeredCube z (3 * r) h3r)).2 i :
            DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))]
            fun x => (W n).grad x i :=
          ae_restrict_of_ae_restrict_of_subset (hcellsub k) h0
        exact h1.symm
      · exact Filter.Eventually.of_forall (fun x => by
          show U.grad x i = _
          rw [hUgrad])
    · intro x hx
      rw [hUfun]
      have hxcl : x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
        closure_mono (hcellsub k) (frontier_subset_closure hx)
      have h1 := hUf.tendsto_at hxcl
      have h2 : (fun j => (W j).toFun x) = fun j => Bs j x := funext fun j => hWface j k x hx
      rw [h2] at h1
      exact tendsto_nhds_unique h1 (hBs.tendsto_at x)
  · intro l M hM x hx
    rw [hUfun]
    exact hcomp l M hM x hx

/-! ## (GlueCat) -/

theorem aux_prop_gluing_inner_eq_integral {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (f g : DomainL2 Ω) :
    inner ℝ f g = ∫ x, (f : SpatialCoordinates d → ℝ) x * (g : SpatialCoordinates d → ℝ) x
      ∂(volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  rw [L2.inner_def]
  congr 1
  funext x
  simp [mul_comm]

/-- : for a catalogue datum, the smooth mesh patches together with
`prop_boundary` (whose represented `L²` input is `hCatalogL2`). -/
theorem aux_prop_gluing_catalog_package
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta alpha : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha) (ha1 : alpha < 1)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (hAcont : ∀ n : ℕ, ContinuousOn (A n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] A n)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ A n x ∧ A n x ≤ Lam)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ w : DomainL2 (centeredCube z (3 * r) h3r),
        Tendsto (fun n => ∫ x, w x
            * ((vN n : SobolevData (centeredCube z (3 * r) h3r)).1) x
            ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
          atTop (𝓝 (∫ x, w x * v x
            ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))))) →
      E.energy v ≤
        Filter.liminf (fun n => (responseForm S (aC n) (vN n) (vN n) : EReal)) atTop)
    (hRecovery : ∀ v ∈ E.domain, ∃ vN : ℕ → S.space,
      Tendsto (fun n => ((vN n : SobolevData (centeredCube z (3 * r) h3r)).1,
          (responseForm S (aC n) (vN n) (vN n) : EReal)))
        atTop (𝓝 (v, E.energy v)))
    (Dq : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)))
    (hDq : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
      (centeredCube z r hr : Set (SpatialCoordinates d)) Dq)
    (hDirichlet : ∃ EDir : _root_.SubdiffusiveProcess.DirichletForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))),
      EDir.toClosedForm = E)
    (t : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (Kstar : ℝ) (hKstar : ∀ n, KN n ≤ Kstar)
    (hfrac : ∀ w : S.space,
      cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => w.val.1) < ⊤)
    (hcoercive : ∀ n (w : S.space),
      ‖w.val.1‖ ^ 2 +
          volume.real (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
              (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
        KN n * responseForm S (aC n) w w)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O →
      closure O ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n)
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
              chic n ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            x ∉ O → chic n x = 0) ∧
          responseForm S (aC n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
    (hEnergyMeasures :
      (∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space),
        u ∈ E.domain →
        Tendsto (fun n => ((uN n).val.1,
          (responseForm S (aC n) (uN n) (uN n) : EReal))) atTop
          (𝓝 (u, E.energy u)) →
        ∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC n).val y *
                ∑ i : Fin d, ((uN n : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂(Gamma.measure u)))) ∧
      (∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
          (uN : ℕ → S.space) (E0 : ℝ)
          (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
        nu Set.univ < (⊤ : ENNReal) →
        nu ((closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))ᶜ) = 0 →
        StrictMono sigma →
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        (∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x, φ x ∂(((volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
              (fun y => ENNReal.ofReal ((aC (sigma n)).val y *
                ∑ i : Fin d, ((uN (sigma n) : SobolevData
                  (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
            (𝓝 (∫ x, φ x ∂nu))) →
        u ∈ E.domain ∧
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gamma.measure u B ≤ nu B) ∧
      (∀ (u v : DomainL2 (centeredCube z (3 * r) h3r))
          (uN vN : ℕ → S.space) (E0 : ℝ),
        Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
        (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
        v ∈ E.domain →
        Tendsto (fun n => ((vN n).val.1,
          (responseForm S (aC n) (vN n) (vN n) : EReal))) atTop
          (𝓝 (v, E.energy v)) →
        ∀ φ : SpatialCoordinates d → ℝ,
          ContinuousOn φ
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          Tendsto (fun n =>
            ∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
              φ x * ((aC n).val x *
                ∑ i : Fin d,
                  ((uN n : SobolevData (centeredCube z (3 * r) h3r)).2 i x) *
                  ((vN n : SobolevData (centeredCube z (3 * r) h3r)).2 i x))) atTop
            (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ))))
    (hZeroTrace : ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
      let qc := centeredCube zc rc hrc
      (qc : Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
      ∀ D : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)),
        _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E (qc : Set (SpatialCoordinates d)) D →
      ∀ w ∈ E.domain, ∀ wc : SpatialCoordinates d → ℝ,
        ContinuousOn wc
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        (w : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] wc →
        (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), wc x = 0) →
        ∀ wq : DomainL2 (centeredCube z (3 * r) h3r),
          (wq : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
              (closure (qc : Set (SpatialCoordinates d))).indicator wc →
          wq ∈ D ∧
            E.form wq wq =
              (Gamma.measure w (qc : Set (SpatialCoordinates d))).toReal)
    (hKilledCells : ∀ k : OddGridIndex d (triadicHalf 1),
      ∃ D : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)),
        (_root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) D))
    (Catalog : Set (SpatialCoordinates d → ℝ))
    (hCatalog : ∀ Phi ∈ Catalog,
      ContDiff ℝ ∞ Phi ∧ HasCompactSupport Phi ∧
        tsupport Phi ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hCatalogBounds : ∀ Phi, Phi ∈ Catalog →
      ∀ PhiH : H1Function
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        PhiH.toFun = Phi →
        ∃ Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ,
          (∀ k : OddGridIndex d (triadicHalf 1),
            0 ≤ Bcell k ∧ 0 ≤ Hcell k) ∧
          ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1))
            (w : H1Function
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))),
            IsWeaklyHarmonicOn (A n)
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w →
            HasZeroTraceDifferenceOn
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w
              (PhiH.restrict
                (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                (hcellsub k)) →
            energy (A n)
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w ≤ Bcell k ∧
            (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
              ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
                ((volume.restrict
                  ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))).withDensity
                  (fun y => ENNReal.ofReal ((A n) y *
                    ∑ i : Fin d, (w.grad y i) ^ 2)))
                  (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t)) ∧
            ∃ wc : SpatialCoordinates d → ℝ,
              ContinuousOn wc
                (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) ∧
              w.toFun =ᵐ[volume.restrict
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))] wc ∧
              (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                ∀ y ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                  |wc x - wc y| ≤ Hcell k * dist x y ^ alpha) ∧
              (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                |wc x| ≤ Hcell k))
    (hCatalogL2 : ∀ Phi, Phi ∈ Catalog →
      ∀ PhiH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        PhiH.toFun = Phi →
        ∀ (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
          (UNS : ℕ → S.space),
          (∀ n : ℕ, (UNS n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (UN n)) →
          (∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
            IsWeaklyHarmonicOn (A n)
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
              ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)) ∧
            HasZeroTraceDifferenceOn
              ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
              ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))
              (PhiH.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))) →
          ∃ uBar : DomainL2 (centeredCube z (3 * r) h3r),
            Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
    (Phi : SpatialCoordinates d → ℝ) (hPhi : Phi ∈ Catalog) :
    ∃ (PhiH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (Phiq : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
      (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (UNS : ℕ → S.space)
      (U : DomainL2 (centeredCube z (3 * r) h3r)) (Uc : SpatialCoordinates d → ℝ),
      PhiH.toFun = Phi ∧ Phiq.toFun = Phi ∧
      (∀ n : ℕ,
        (UNS n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (UN n) ∧
        ContinuousOn (UN n).toFun
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
        (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          (UN n).toFun x = 0) ∧
        ∀ k : OddGridIndex d (triadicHalf 1),
          IsWeaklyHarmonicOn (A n)
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
            ((UN n).restrict
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k)) ∧
          HasZeroTraceDifferenceOn
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
            ((UN n).restrict
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k))
            (PhiH.restrict
              (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
              (hcellsub k)) ∧
          ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
            (UN n).toFun x = Phi x) ∧
      U ∈ E.domain ∧
      ContinuousOn Uc
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (U : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc ∧
      TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Uc x = Phi x) ∧
      Gamma.measure U (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 ∧
      (∀ φ : DomainL2 (centeredCube z (3 * r) h3r), φ ∈ Dq → E.form U φ = 0) ∧
      Tendsto (fun n => cellDirichletInfimum (A n)
        (centeredCube z r hr : Set (SpatialCoordinates d)) Phiq) atTop
        (𝓝 ((Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)) ∧
      (∀ V : DomainL2 (centeredCube z (3 * r) h3r),
        V ∈ E.domain →
        ∀ Vc : SpatialCoordinates d → ℝ,
        ContinuousOn Vc
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        (V : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Vc x = Phi x) →
        (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          (Gamma.measure V (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) := by
  obtain ⟨EDir, rfl⟩ := hDirichlet
  obtain ⟨PhiH, Phiq, UN, UNS, Bcell, Hcell, hPhiH, hPhiq, hBH, hUN, hEn, hGr, hHo⟩ :=
    prop_gluing_smooth_mesh d hd z r hr h3r hcellsub alpha t ht htd S hS A hAcont hell
      Catalog hCatalog hCatalogBounds Phi hPhi
  obtain ⟨uBar, huBar⟩ := hCatalogL2 Phi hPhi PhiH hPhiH UN UNS (fun n => (hUN n).1)
    (fun n k => ⟨((hUN n).2.2.2 k).1, ((hUN n).2.2.2 k).2.1⟩)
  have hPhiData := hCatalog Phi hPhi
  have hGrowth : ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
      ∀ x ∈ closure (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
        Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
          (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d))).withDensity
          (fun y => ENNReal.ofReal ((aC n).val y *
            ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))
          (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t) := by
    intro n k x hx rr hrr hrr1
    have hden : (fun y => ENNReal.ofReal ((aC n).val y *
          ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2))
        =ᵐ[volume.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Set (SpatialCoordinates d))]
        (fun y => ENNReal.ofReal ((A n) y *
          ∑ i : Fin d, ((UNS n : SobolevData (centeredCube z (3 * r) h3r)).2 i y) ^ 2)) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hcellsub k) (haC n)] with y hy
      rw [hy]
    rw [withDensity_congr_ae hden]
    exact hGr n k x hx rr hrr hrr1
  have hLower' : ∀ (vn : ℕ → S.space) (v : DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ f : DomainL2 (centeredCube z (3 * r) h3r),
        Tendsto (fun n => inner ℝ f (vn n).val.1) atTop (𝓝 (inner ℝ f v))) →
      EDir.toClosedForm.energy v ≤
        Filter.liminf (fun n => (responseForm S (aC n) (vn n) (vn n) : EReal)) atTop := by
    intro vn v hv
    apply hLower vn v
    intro w
    have h := hv w
    simp only [aux_prop_gluing_inner_eq_integral] at h
    exact h
  obtain ⟨U, Uc, hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8, hU9⟩ :=
    prop_boundary d hd z r hr h3r EDir Gamma
      (centeredCube z r hr : Set (SpatialCoordinates d)) rfl Dq hDq S hS A aC hAcont haC hell
      Phi Phi hPhiData.1 hPhiData.2.1 hPhiData.2.2 (fun _ _ => rfl) PhiH hPhiH Phiq hPhiq
      UN UNS (fun n => (hUN n).1) uBar huBar hcellsub
      (fun n k => ((hUN n).2.2.2 k).1) (fun n k => ((hUN n).2.2.2 k).2.1)
      (fun n k => ((hUN n).2.2.2 k).2.2.1) (fun n k => ((hUN n).2.2.2 k).2.2.2)
      t alpha ht htd (by linarith) ha1 Bcell Hcell (fun k => (hBH k).1) (fun k => (hBH k).2)
      hEn hGrowth hHo hLower' hRecovery KN hKN Kstar hKstar hfrac hcoercive hInterp hcutoffs
      hEnergyMeasures hZeroTrace hKilledCells
  refine ⟨PhiH, Phiq, UN, UNS, U, Uc, hPhiH, hPhiq, ?_, hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8,
    hU9⟩
  intro n
  refine ⟨(hUN n).1, (hUN n).2.1, (hUN n).2.2.1, fun k => ?_⟩
  exact ⟨((hUN n).2.2.2 k).1, ((hUN n).2.2.2 k).2.1, ((hUN n).2.2.2 k).2.2.2⟩

/-! ## (GlueLimA) -/

/-! ### Hölder algebra on the closed cube. -/

theorem aux_prop_gluing_isHolderOn_sub {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (f g : SpatialCoordinates d → ℝ) (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f)
    (hg : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S g) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S (fun x => f x - g x) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, ?_⟩
  rintro v ⟨x, hx, y, hy, hne, rfl⟩
  have hepos := aux_prop_gluing_euclid_pos x y hne
  have hebpos : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta :=
    Real.rpow_pos_of_pos hepos beta
  have h1 := hM ⟨x, hx, y, hy, hne, rfl⟩
  have h2 := hN ⟨x, hx, y, hy, hne, rfl⟩
  simp only at h1 h2 ⊢
  rw [div_le_iff₀ hebpos] at h1 h2 ⊢
  calc |f x - g x - (f y - g y)| = |(f x - f y) - (g x - g y)| := by ring_nf
    _ ≤ |f x - f y| + |g x - g y| := abs_sub _ _
    _ ≤ _ := by linarith

theorem aux_prop_gluing_isHolderOn_neg {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (hf : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S f) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S (fun x => -f x) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨M, ?_⟩
  rintro v ⟨x, hx, y, hy, hne, rfl⟩
  have h := hM ⟨x, hx, y, hy, hne, rfl⟩
  have habs : |-f x - -f y| = |f x - f y| := by
    rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
  simp only at h ⊢
  rw [habs]
  exact h

theorem aux_prop_gluing_bddAbove_abs_sub {d : ℕ} (S : Set (SpatialCoordinates d))
    (f g : SpatialCoordinates d → ℝ) (hf : BddAbove {v : ℝ | ∃ x ∈ S, v = |f x|})
    (hg : BddAbove {v : ℝ | ∃ x ∈ S, v = |g x|}) :
    BddAbove {v : ℝ | ∃ x ∈ S, v = |f x - g x|} := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  have h1 := hM ⟨x, hx, rfl⟩
  have h2 := hN ⟨x, hx, rfl⟩
  exact (abs_sub _ _).trans (add_le_add h1 h2)

theorem aux_prop_gluing_cAlphaNorm_neg {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S (fun x => -f x) = _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S f := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet
  congr 2
  · ext v
    simp only [mem_ofPred_eq, abs_neg]
  · ext v
    constructor
    · rintro ⟨x, hx, y, hy, hne, rfl⟩
      refine ⟨x, hx, y, hy, hne, ?_⟩
      rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
    · rintro ⟨x, hx, y, hy, hne, rfl⟩
      refine ⟨x, hx, y, hy, hne, ?_⟩
      rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]

theorem aux_prop_gluing_cAlphaNorm_congr {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (f g : SpatialCoordinates d → ℝ) (h : ∀ x, f x = g x) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S f = _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S g := by
  rw [show f = g from funext h]

theorem aux_prop_gluing_closure_nontrivial {d : ℕ} (hd : 1 ≤ d) (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) :
    (closure (centeredCube z R hR : Set (SpatialCoordinates d))).Nontrivial := by
  let i0 : Fin d := ⟨0, by omega⟩
  let x2 : SpatialCoordinates d := Function.update z i0 (z i0 + R / 4)
  refine ⟨z, subset_closure (Metric.mem_ball_self (by positivity)), x2, subset_closure ?_, ?_⟩
  · show x2 ∈ Metric.ball z (R / 2)
    rw [Metric.mem_ball, dist_pi_lt_iff (by positivity)]
    intro i
    by_cases hi : i = i0
    · subst hi
      simp only [x2, Function.update_self, Real.dist_eq]
      rw [show z i0 + R / 4 - z i0 = R / 4 by ring, abs_of_pos (by positivity)]
      linarith
    · simp only [x2, Function.update_of_ne hi, dist_self]
      positivity
  · intro h
    have := congrFun h i0
    simp only [x2, Function.update_self] at this
    linarith

/-! ### Three-epsilon argument for the responses (paper label `mfd:prop-gluing`). -/

theorem aux_prop_gluing_response_three_eps (a : ℕ → ℝ) (ak : ℕ → ℕ → ℝ) (l : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n) (hak0 : ∀ k n, 0 ≤ ak k n)
    (hak : ∀ k, Tendsto (ak k) atTop (𝓝 (l k)))
    (eps : ℕ → ℝ) (heps : Tendsto eps atTop (𝓝 0))
    (hclose : ∀ k n, |Real.sqrt (a n) - Real.sqrt (ak k n)| ≤ eps k) :
    ∃ L : ℝ, Tendsto a atTop (𝓝 L) ∧ Tendsto l atTop (𝓝 L) ∧
      ∀ k, |Real.sqrt L - Real.sqrt (l k)| ≤ eps k := by
  have hsk : ∀ k, Tendsto (fun n => Real.sqrt (ak k n)) atTop (𝓝 (Real.sqrt (l k))) :=
    fun k => (Real.continuous_sqrt.tendsto _).comp (hak k)
  obtain ⟨M, hM⟩ := aux_prop_gluing_three_eps (fun n => Real.sqrt (a n))
    (fun k n => Real.sqrt (ak k n)) eps (fun k => ⟨_, hsk k⟩) heps hclose
  have hM0 : 0 ≤ M := ge_of_tendsto' hM (fun n => Real.sqrt_nonneg _)
  have hl0 : ∀ k, 0 ≤ l k := fun k => ge_of_tendsto' (hak k) (fun n => hak0 k n)
  have hsqL : Real.sqrt (M ^ 2) = M := Real.sqrt_sq hM0
  have hcl : ∀ k, |M - Real.sqrt (l k)| ≤ eps k := by
    intro k
    have hlim : Tendsto (fun n => |Real.sqrt (a n) - Real.sqrt (ak k n)|) atTop
        (𝓝 |M - Real.sqrt (l k)|) := (hM.sub (hsk k)).abs
    exact le_of_tendsto' hlim (hclose k)
  refine ⟨M ^ 2, ?_, ?_, fun k => by rw [hsqL]; exact hcl k⟩
  · have h2 : Tendsto (fun n => (Real.sqrt (a n)) ^ 2) atTop (𝓝 (M ^ 2)) := hM.pow 2
    refine h2.congr (fun n => ?_)
    exact Real.sq_sqrt (ha0 n)
  · have hsl : Tendsto (fun k => Real.sqrt (l k)) atTop (𝓝 M) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) heps
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hcl k
    have h2 : Tendsto (fun k => (Real.sqrt (l k)) ^ 2) atTop (𝓝 (M ^ 2)) := hsl.pow 2
    refine h2.congr (fun k => ?_)
    exact Real.sq_sqrt (hl0 k)

/-! ### Energy-measure continuity in the form norm (paper label `mfd:prop-gluing`). -/

theorem aux_prop_gluing_form_neg_self {X : Type*} [MeasurableSpace X] {m : Measure X}
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    E.form (-u) (-u) = E.form u u := by
  rw [E.form_neg_left hu (E.domain.neg_mem hu), E.form_neg_right hu hu, neg_neg]

theorem aux_prop_gluing_gamma_seq_limit {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : Measure X} {E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m} (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (Vk : ℕ → Lp ℝ 2 m) (V : Lp ℝ 2 m) (hVk : ∀ k, Vk k ∈ E.domain) (hV : V ∈ E.domain)
    (hlim : Tendsto (fun k => E.form (Vk k - V) (Vk k - V)) atTop (𝓝 0))
    {B : Set X} (hB : MeasurableSet B) :
    Tendsto (fun k => (Γ.measure (Vk k) B).toReal) atTop (𝓝 (Γ.measure V B).toReal) := by
  have hd : ∀ k, Vk k - V ∈ E.domain := fun k => E.domain.sub_mem (hVk k) hV
  have hd' : ∀ k, V - Vk k ∈ E.domain := fun k => E.domain.sub_mem hV (hVk k)
  have hbound : ∀ k, |Real.sqrt (Γ.measure (Vk k) B).toReal - Real.sqrt (Γ.measure V B).toReal|
      ≤ Real.sqrt (E.form (Vk k - V) (Vk k - V)) := by
    intro k
    have h1 : Real.sqrt (Γ.measure (Vk k) B).toReal ≤
        Real.sqrt (Γ.measure V B).toReal + Real.sqrt (Γ.measure (Vk k - V) B).toReal := by
      have := aux_prop_gluing_sqrt_gamma_add_le Γ hV (hd k) hB
      rwa [add_sub_cancel] at this
    have h2 : Real.sqrt (Γ.measure V B).toReal ≤
        Real.sqrt (Γ.measure (Vk k) B).toReal + Real.sqrt (Γ.measure (V - Vk k) B).toReal := by
      have := aux_prop_gluing_sqrt_gamma_add_le Γ (hVk k) (hd' k) hB
      rwa [add_sub_cancel] at this
    have h3 : Real.sqrt (Γ.measure (Vk k - V) B).toReal ≤
        Real.sqrt (E.form (Vk k - V) (Vk k - V)) :=
      Real.sqrt_le_sqrt (Γ.toReal_measure_le_form (hd k) B)
    have h4 : Real.sqrt (Γ.measure (V - Vk k) B).toReal ≤
        Real.sqrt (E.form (Vk k - V) (Vk k - V)) := by
      have h5 := Γ.toReal_measure_le_form (hd' k) B
      have h6 : E.form (V - Vk k) (V - Vk k) = E.form (Vk k - V) (Vk k - V) := by
        rw [show V - Vk k = -(Vk k - V) by abel]
        exact aux_prop_gluing_form_neg_self E (hd k)
      rw [h6] at h5
      exact Real.sqrt_le_sqrt h5
    rw [abs_le]
    constructor <;> linarith
  have hs0 : Tendsto (fun k => Real.sqrt (E.form (Vk k - V) (Vk k - V))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    simpa using! this
  have hsq : Tendsto (fun k => Real.sqrt (Γ.measure (Vk k) B).toReal) atTop
      (𝓝 (Real.sqrt (Γ.measure V B).toReal)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => by
      rw [Real.norm_eq_abs]; exact hbound k) hs0
  have h2 := hsq.pow 2
  simp only [Real.sq_sqrt ENNReal.toReal_nonneg] at h2
  exact h2

theorem aux_prop_gluing_form_seq_limit {X : Type*} [MeasurableSpace X]
    {m : Measure X} (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m)
    (Vk : ℕ → Lp ℝ 2 m) (V : Lp ℝ 2 m) (hVk : ∀ k, Vk k ∈ E.domain) (hV : V ∈ E.domain)
    (hlim : Tendsto (fun k => E.form (Vk k - V) (Vk k - V)) atTop (𝓝 0))
    (φ : Lp ℝ 2 m) (hφ : φ ∈ E.domain) :
    Tendsto (fun k => E.form (Vk k) φ) atTop (𝓝 (E.form V φ)) := by
  have hd : ∀ k, Vk k - V ∈ E.domain := fun k => E.domain.sub_mem (hVk k) hV
  have hs0 : Tendsto (fun k => Real.sqrt (E.form (Vk k - V) (Vk k - V)) *
      Real.sqrt (E.form φ φ)) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hlim).mul_const (Real.sqrt (E.form φ φ))
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hs0
  rw [Real.norm_eq_abs, ← E.form_sub_left (hVk k) hV hφ]
  exact E.abs_form_le (hd k) hφ

/-! ## (GlueLimB) -/

/-- : `E_N^Q(U_N^{(k)} - U_N^{(l)}) ≤ C ‖β_k - β_l‖²_{C^β}`, on the response space. -/
theorem aux_prop_gluing_pair_energy {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (An : SpatialCoordinates d → ℝ)
    (hAncont : ContinuousOn An
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (lam Lam : ℝ) (hlam : 0 < lam)
    (hAnb : ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      lam ≤ An x ∧ An x ≤ Lam)
    (aC : PositiveCoefficient (centeredCube z (3 * r) h3r))
    (haC : ((aC.val : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] An)
    (C : ℝ) (hC : 0 ≤ C) (Ug UgStar : OddGridIndex d (triadicHalf 1) → ℝ)
    (hUg : ∀ k, 0 ≤ Ug k ∧ Ug k ≤ UgStar k)
    (hGridBound : ∀ (k : OddGridIndex d (triadicHalf 1)),
        ∀ e : H1Function
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
              Set (SpatialCoordinates d)),
        ContinuousOn e.toFun
            (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun →
        cellDirichletInfimum An
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
              Set (SpatialCoordinates d)) e ≤
          C * Ug k * r ^ ((d : ℝ) - 2) *
            cellBoundaryQuotientNorm beta
              (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun ^ 2)
    (u v : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (us vs : S.space)
    (hus : (us : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 u)
    (hvs : (vs : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 v)
    (hu : ∀ k : OddGridIndex d (triadicHalf 1), IsWeaklyHarmonicOn An
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))
      (u.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)))
    (hv : ∀ k : OddGridIndex d (triadicHalf 1), IsWeaklyHarmonicOn An
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))
      (v.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)))
    (hucont : ContinuousOn u.toFun
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hvcont : ContinuousOn v.toFun
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (G : SpatialCoordinates d → ℝ)
    (hface : ∀ k : OddGridIndex d (triadicHalf 1),
      ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
          Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
        u.toFun x - v.toFun x = G x)
    (hG : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G)
    (hGb : BddAbove {w : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), w = |G x|}) :
    responseForm S aC (us - vs) (us - vs) ≤
      (∑ k : OddGridIndex d (triadicHalf 1),
        C * UgStar k * r ^ ((d : ℝ) - 2) * (max 1 (r ^ beta)) ^ 2) *
        _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G ^ 2 := by
  obtain ⟨a, hac, haeq⟩ := aux_prop_gluing_coeff_extension _ isClosed_closure An hAncont
  have hab : ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam := fun x hx => by rw [haeq x hx]; exact hAnb x hx
  have hQmeas := (centeredCube z (3 * r) h3r).isOpen.measurableSet
  have haC' : ((aC.val : SpatialCoordinates d → ℝ))
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] a := by
    filter_upwards [haC, ae_restrict_mem hQmeas] with x h1 h2
    rw [h1, haeq x (subset_closure h2)]
  have hdata : ((us - vs : S.space) : SobolevData (centeredCube z (3 * r) h3r)) =
      sobolevDataOfH1 (u - v) := by
    rw [Submodule.coe_sub, hus, hvs, aux_prop_gluing_sobolevDataOfH1_sub]
  have hcellA : ∀ k : OddGridIndex d (triadicHalf 1), ∀ x ∈
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)), An x = a x :=
    fun k x hx => (haeq x (subset_closure (hcellsub k hx))).symm
  rw [aux_prop_gluing_responseForm_eq_energy S aC a haC' Lam
    (fun x hx => hlam.le.trans (hab x (subset_closure hx)).1)
    (fun x hx => (hab x (subset_closure hx)).2) hac.aestronglyMeasurable (us - vs) (u - v) hdata]
  exact aux_prop_gluing_grid_energy_bound z r hr h3r hcellsub beta hbeta0 An a lam Lam hlam hac
    hab haeq C hC Ug UgStar hUg hGridBound u v
    (fun k => aux_prop_gluing_harmonic_congr
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen.measurableSet (hcellA k) (hu k))
    (fun k => aux_prop_gluing_harmonic_congr
      (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen.measurableSet (hcellA k) (hv k))
    hucont hvcont G hface hG hGb

/-- The catalogue approximants are Cauchy in `C^β(closure Q)`. -/
theorem aux_prop_gluing_catalog_cAlpha_cauchy {d : ℕ} (hd : 1 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (beta : ℝ)
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hHol : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z R hR : Set (SpatialCoordinates d))) (fun x => Bs k x - B x))
    (hBdd : ∀ k, BddAbove {v : ℝ | ∃ x ∈ closure
      (centeredCube z R hR : Set (SpatialCoordinates d)), v = |Bs k x - B x|}) :
    ∀ j l, _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta (closure (centeredCube z R hR : Set (SpatialCoordinates d)))
        (fun x => Bs j x - Bs l x) ≤
      _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta (closure (centeredCube z R hR : Set (SpatialCoordinates d)))
          (fun x => Bs j x - B x) +
        _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta (closure (centeredCube z R hR : Set (SpatialCoordinates d)))
          (fun x => Bs l x - B x) := by
  intro j l
  have h := aux_prop_gluing_cAlphaNorm_sub_le beta _ (fun x => Bs j x - B x)
    (fun x => Bs l x - B x) (aux_prop_gluing_closure_nontrivial hd z R hR)
    (hBdd j) (hBdd l) (hHol j) (hHol l)
  rw [aux_prop_gluing_cAlphaNorm_congr beta _ (fun x => Bs j x - Bs l x)
    (fun x => (Bs j x - B x) - (Bs l x - B x)) (fun x => by ring)]
  exact h

/-- Hölder and boundedness of catalogue differences. -/
theorem aux_prop_gluing_catalog_diff_holder {d : ℕ}
    (S : Set (SpatialCoordinates d)) (beta : ℝ)
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hHol : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S (fun x => Bs k x - B x))
    (hBdd : ∀ k, BddAbove {v : ℝ | ∃ x ∈ S, v = |Bs k x - B x|}) (j l : ℕ) :
    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta S (fun x => Bs j x - Bs l x) ∧
      BddAbove {v : ℝ | ∃ x ∈ S, v = |Bs j x - Bs l x|} := by
  have h1 := aux_prop_gluing_isHolderOn_sub beta S _ _ (hHol j) (hHol l)
  have h2 := aux_prop_gluing_bddAbove_abs_sub S _ _ (hBdd j) (hBdd l)
  refine ⟨aux_prop_gluing_isHolderOn_congr S _ _ beta (fun x _ => by ring) h1, ?_⟩
  obtain ⟨M, hM⟩ := h2
  refine ⟨M, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  have := hM ⟨x, hx, rfl⟩
  rwa [show Bs j x - B x - (Bs l x - B x) = Bs j x - Bs l x by ring] at this

/-- The Cauchy criterion used by the completion, from the uniform energy bound. -/
theorem aux_prop_gluing_cauchy_of_bound (F : ℕ → ℕ → ℝ) (e : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (he0 : ∀ k, 0 ≤ e k) (he : Tendsto e atTop (𝓝 0))
    (hF : ∀ j l, F j l ≤ K * (e j + e l) ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ l ≥ J, F j l ≤ ε := by
  intro ε hε
  set δ : ℝ := Real.sqrt (ε / (K + 1)) / 2 with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds hδpos))
  refine ⟨J, fun j hj l hl => ?_⟩
  have h1 := hJ j hj
  have h2 := hJ l hl
  have hsum : e j + e l ≤ 2 * δ := by linarith
  have hsum0 : 0 ≤ e j + e l := add_nonneg (he0 j) (he0 l)
  have hsq : (e j + e l) ^ 2 ≤ (2 * δ) ^ 2 := pow_le_pow_left₀ hsum0 hsum 2
  have h2δ : (2 * δ) ^ 2 = ε / (K + 1) := by
    rw [hδ, show 2 * (Real.sqrt (ε / (K + 1)) / 2) = Real.sqrt (ε / (K + 1)) by ring,
      Real.sq_sqrt (by positivity)]
  calc F j l ≤ K * (e j + e l) ^ 2 := hF j l
    _ ≤ K * (ε / (K + 1)) := by rw [← h2δ]; exact mul_le_mul_of_nonneg_left hsq hK
    _ ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by linarith)]
        nlinarith

/-! ## (GlueLimC) -/

/-- Uniform convergence on the closed cube of functions supported in the cube is
global uniform convergence. -/
theorem aux_prop_gluing_tendstoUniformly_global {d : ℕ} (K : Set (SpatialCoordinates d))
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hBs : TendstoUniformlyOn Bs B atTop K)
    (hBs0 : ∀ k, ∀ y ∉ K, Bs k y = 0) (hB0 : ∀ y ∉ K, B y = 0) :
    TendstoUniformly Bs B atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have h := (Metric.tendstoUniformlyOn_iff.mp hBs) ε hε
  filter_upwards [h] with k hk y
  by_cases hy : y ∈ K
  · exact hk y hy
  · rw [hBs0 k y hy, hB0 y hy, dist_self]
    exact hε

/-- : the finite-cutoff cell-harmonic patches of the Hölder datum,
with the maximum-principle comparison to the catalogue patches. -/
theorem aux_prop_gluing_holder_patches {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (hAcont : ∀ n : ℕ, ContinuousOn (A n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] A n)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ A n x ∧ A n x ≤ Lam)
    (C : ℝ) (hC : 0 ≤ C)
    (Ugrid : OddGridIndex d (triadicHalf 1) → ℕ → ℝ)
    (UgridStar : OddGridIndex d (triadicHalf 1) → ℝ)
    (hUg : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      0 ≤ Ugrid k n ∧ Ugrid k n ≤ UgridStar k)
    (hGridBound : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      ∀ e : H1Function
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)),
      ContinuousOn e.toFun
          (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun →
      cellDirichletInfimum (A n)
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) e ≤
        C * Ugrid k n * r ^ ((d : ℝ) - 2) *
          cellBoundaryQuotientNorm beta
            (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun ^ 2)
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hBsU : TendstoUniformly Bs B atTop)
    (hBsHol : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => Bs k x - B x))
    (hBsBdd : ∀ k, BddAbove {v : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), v = |Bs k x - B x|})
    (hBsNorm : Tendsto (fun k => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs k x - B x)) atTop (𝓝 0))
    (PhiH : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hPhiH : ∀ k, (PhiH k).toFun = Bs k)
    (W : ℕ → ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (WS : ℕ → ℕ → S.space)
    (hW : ∀ k n,
      (WS k n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (W k n) ∧
      ContinuousOn (W k n).toFun
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        (W k n).toFun x = 0) ∧
      ∀ c : OddGridIndex d (triadicHalf 1),
        IsWeaklyHarmonicOn (A n)
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((W k n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c)) ∧
        HasZeroTraceDifferenceOn
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((W k n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c))
          ((PhiH k).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c)) ∧
        ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
          (W k n).toFun x = Bs k x) :
    ∃ (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (UNS : ℕ → S.space),
      (∀ n : ℕ,
          (UNS n).val = sobolevDataOfH1 (UN n) ∧
          ContinuousOn (UN n).toFun
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            (UN n).toFun x = 0) ∧
          ∀ k : OddGridIndex d (triadicHalf 1),
            IsWeaklyHarmonicOn (A n)
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
                ((UN n).restrict
                  (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)) ∧
            ∀ x ∈ frontier
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
              (UN n).toFun x = B x) ∧
      (∀ n k M, (∀ y, |B y - Bs k y| ≤ M) →
        ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          |(UN n).toFun x - (W k n).toFun x| ≤ M) := by
  set Kg : ℝ := ∑ c : OddGridIndex d (triadicHalf 1),
    C * UgridStar c * r ^ ((d : ℝ) - 2) * (max 1 (r ^ beta)) ^ 2 with hKg
  have hKg0 : 0 ≤ Kg := Finset.sum_nonneg (fun c _ => by
    have := (hUg c 0).1.trans (hUg c 0).2
    have : 0 ≤ r ^ ((d : ℝ) - 2) := Real.rpow_nonneg hr.le _
    positivity)
  have he0 : ∀ k, 0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => Bs k x - B x) := fun k => aux_prop_gluing_cAlphaNorm_nonneg _ _ _
  have key : ∀ n : ℕ, ∃ (U : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (US : S.space),
      (US : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 U ∧
      ContinuousOn U.toFun
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        U.toFun x = 0) ∧
      (∀ k : OddGridIndex d (triadicHalf 1),
        IsWeaklyHarmonicOn (A n)
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
              Set (SpatialCoordinates d))
            (U.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)) ∧
          ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
            U.toFun x = B x) ∧
      (∀ l M, (∀ y, |B y - Bs l y| ≤ M) →
        ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          |U.toFun x - (W l n).toFun x| ≤ M) := by
    intro n
    obtain ⟨lam, Lam, hlam, hb⟩ := hell n
    obtain ⟨a, hac, haeq⟩ := aux_prop_gluing_coeff_extension _ isClosed_closure (A n) (hAcont n)
    have hab : ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ a x ∧ a x ≤ Lam := fun x hx => by rw [haeq x hx]; exact hb x hx
    have hcellA : ∀ c : OddGridIndex d (triadicHalf 1), ∀ x ∈
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) c : Opens (SpatialCoordinates d)) :
          Set (SpatialCoordinates d)), A n x = a x :=
      fun c x hx => (haeq x (subset_closure (hcellsub c hx))).symm
    have hcellA' : ∀ c : OddGridIndex d (triadicHalf 1), ∀ x ∈
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) c : Opens (SpatialCoordinates d)) :
          Set (SpatialCoordinates d)), a x = A n x :=
      fun c x hx => haeq x (subset_closure (hcellsub c hx))
    have hCauchy : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ l ≥ J,
        responseForm S (aC n) (WS j n - WS l n) (WS j n - WS l n) ≤ ε := by
      refine aux_prop_gluing_cauchy_of_bound
        (fun j l => responseForm S (aC n) (WS j n - WS l n) (WS j n - WS l n))
        _ Kg hKg0 he0 hBsNorm (fun j l => ?_)
      obtain ⟨hGj, hGb⟩ := aux_prop_gluing_catalog_diff_holder _ beta Bs B hBsHol hBsBdd j l
      have hpe := aux_prop_gluing_pair_energy z r hr h3r hcellsub beta hbeta0 S (A n) (hAcont n)
        lam Lam hlam hb (aC n) (haC n) C hC (fun c => Ugrid c n) UgridStar (fun c => hUg c n)
        (fun c => hGridBound c n) (W j n) (W l n) (WS j n) (WS l n) (hW j n).1 (hW l n).1
        (fun c => ((hW j n).2.2.2 c).1) (fun c => ((hW l n).2.2.2 c).1)
        (hW j n).2.1 (hW l n).2.1 (fun x => Bs j x - Bs l x)
        (fun c x hx => by rw [((hW j n).2.2.2 c).2.2 x hx, ((hW l n).2.2.2 c).2.2 x hx])
        hGj hGb
      have hsub := aux_prop_gluing_catalog_cAlpha_cauchy (by omega) z (3 * r) h3r beta Bs B
        hBsHol hBsBdd j l
      have hn0 := aux_prop_gluing_cAlphaNorm_nonneg beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs j x - Bs l x)
      refine hpe.trans (mul_le_mul_of_nonneg_left ?_ hKg0)
      exact pow_le_pow_left₀ hn0 hsub 2
    obtain ⟨U, US, h1, h2, h3, h4, h5⟩ := aux_prop_gluing_patch_limit z r hr h3r hcellsub S a lam
      Lam hlam hac hab (aC n) Bs B hBsU PhiH hPhiH (fun j => W j n) (fun j => WS j n)
      (fun j => (hW j n).1) (fun j => (hW j n).2.1) (fun j => (hW j n).2.2.1)
      (fun j c => aux_prop_gluing_harmonic_congr
        (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen.measurableSet (hcellA c)
        ((hW j n).2.2.2 c).1)
      (fun j c => ((hW j n).2.2.2 c).2.1) (fun j c => ((hW j n).2.2.2 c).2.2) hCauchy
    refine ⟨U, US, h1, h2, h3, fun c => ⟨?_, (h4 c).2⟩, h5⟩
    exact aux_prop_gluing_harmonic_congr
      (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen.measurableSet (hcellA' c) (h4 c).1
  choose UN UNS h1 h2 h3 h4 h5 using key
  exact ⟨UN, UNS, fun n => ⟨h1 n, h2 n, h3 n, h4 n⟩, fun n k M hM x hx => h5 n k M hM x hx⟩

/-! ## (GlueLimD) -/

/-- Paper `eq:mfd-2` on the cell `q`, in square-root form, for a datum that agrees
on `∂q` with a `C^β(closure Q)` function. -/
theorem aux_prop_gluing_q_bound {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta : ℝ) (An : SpatialCoordinates d → ℝ) (C UStar Uqn : ℝ) (hC : 0 ≤ C)
    (hUqn : 0 ≤ Uqn ∧ Uqn ≤ UStar)
    (hBound : ∀ e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
        ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta z r e.toFun →
        cellDirichletInfimum An (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
          C * Uqn * r ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta z r e.toFun ^ 2)
    (e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hecont : ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (G : SpatialCoordinates d → ℝ)
    (hface : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), e.toFun x = G x)
    (hG : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G)
    (hGb : BddAbove {w : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), w = |G x|}) :
    Real.sqrt (cellDirichletInfimum An (centeredCube z r hr : Set (SpatialCoordinates d)) e) ≤
      Real.sqrt (C * UStar * r ^ ((d : ℝ) - 2)) *
        (max 1 (r ^ beta) * _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G) := by
  have hS : ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      (fun i => z i + r * y i) ∈
        closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    fun y hy => closure_mono hqQ (frontier_subset_closure
      (aux_prop_gluing_rescale_mem_frontier z r hr y hy))
  have hresc : ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      rescaledDatum z r G y = rescaledDatum z r e.toFun y :=
    fun y hy => (hface _ (aux_prop_gluing_rescale_mem_frontier z r hr y hy)).symm
  have hclassG : IsCellBoundaryClass beta z r G :=
    ⟨aux_prop_gluing_isHolderOn_rescale_gen z r hr _ hS beta G hG,
      aux_prop_gluing_bddAbove_rescale z r _ hS G hGb⟩
  have hclass : IsCellBoundaryClass beta z r e.toFun := by
    refine ⟨aux_prop_gluing_isHolderOn_congr _ _ _ beta hresc hclassG.1, ?_⟩
    obtain ⟨M, hM⟩ := hclassG.2
    refine ⟨M, ?_⟩
    rintro w ⟨y, hy, rfl⟩
    rw [← hresc y hy]
    exact hM ⟨y, hy, rfl⟩
  have hnorm : cellBoundaryQuotientNorm beta z r e.toFun = cellBoundaryQuotientNorm beta z r G :=
    (aux_prop_gluing_quotientCBetaNorm_congr beta _ _ _ hresc).symm
  have hNle := aux_prop_gluing_quotientNorm_le z r hr _ hS beta G hG hGb
  have hN0 := aux_prop_gluing_quotientNorm_nonneg beta z r G
  have hb := hBound e hecont hclass
  rw [hnorm] at hb
  have hrpow : 0 ≤ r ^ ((d : ℝ) - 2) := Real.rpow_nonneg hr.le _
  have hX0 : 0 ≤ max 1 (r ^ beta) * _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (aux_prop_gluing_cAlphaNorm_nonneg _ _ _)
  have hle : cellDirichletInfimum An (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
      C * UStar * r ^ ((d : ℝ) - 2) *
        (max 1 (r ^ beta) * _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G) ^ 2 := by
    refine hb.trans ?_
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUqn.2 hC) hrpow
    · exact pow_le_pow_left₀ hN0 hNle 2
    · positivity
    · exact mul_nonneg (mul_nonneg hC (hUqn.1.trans hUqn.2)) hrpow
  calc Real.sqrt (cellDirichletInfimum An (centeredCube z r hr : Set (SpatialCoordinates d)) e)
      ≤ Real.sqrt (C * UStar * r ^ ((d : ℝ) - 2) *
        (max 1 (r ^ beta) * _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) G) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = _ := by rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hX0]

/-- : the Hölder responses converge (three-epsilon argument). -/
theorem aux_prop_gluing_response {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta : ℝ)
    (A : ℕ → SpatialCoordinates d → ℝ)
    (hAcont : ∀ n : ℕ, ContinuousOn (A n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ A n x ∧ A n x ≤ Lam)
    (C UStar : ℝ) (hC : 0 ≤ C)
    (Uq : ℕ → ℝ) (hUq : ∀ n : ℕ, 0 ≤ Uq n ∧ Uq n ≤ UStar)
    (hBound : ∀ n : ℕ, ∀ e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
        ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta z r e.toFun →
        cellDirichletInfimum (A n) (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
          C * Uq n * r ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta z r e.toFun ^ 2)
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hBscont : ∀ k, Continuous (Bs k))
    (hBsHol : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => Bs k x - B x))
    (hBsBdd : ∀ k, BddAbove {v : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), v = |Bs k x - B x|})
    (hBsNorm : Tendsto (fun k => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs k x - B x)) atTop (𝓝 0))
    (Phiq : ℕ → H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hPhiq : ∀ k, (Phiq k).toFun = Bs k)
    (l : ℕ → ℝ)
    (hl : ∀ k, Tendsto (fun n => cellDirichletInfimum (A n)
      (centeredCube z r hr : Set (SpatialCoordinates d)) (Phiq k)) atTop (𝓝 (l k)))
    (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNcont : ∀ n, ContinuousOn (UN n).toFun
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hUNq : ∀ n, ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (UN n).toFun x = B x) :
    ∃ L : ℝ, Tendsto (fun n => cellDirichletInfimum (A n)
        (centeredCube z r hr : Set (SpatialCoordinates d))
        ((UN n).restrict (centeredCube z r hr).isOpen hqQ)) atTop (𝓝 L) ∧
      Tendsto l atTop (𝓝 L) := by
  have hqmeas := (centeredCube z r hr).isOpen.measurableSet
  set eps : ℕ → ℝ := fun k => Real.sqrt (C * UStar * r ^ ((d : ℝ) - 2)) *
    (max 1 (r ^ beta) * _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => Bs k x - B x)) with heps_def
  have heps : Tendsto eps atTop (𝓝 0) := by
    have := (hBsNorm.const_mul (max 1 (r ^ beta))).const_mul
      (Real.sqrt (C * UStar * r ^ ((d : ℝ) - 2)))
    simpa using this
  have hneg : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => B x - Bs k x) := fun k =>
    aux_prop_gluing_isHolderOn_congr _ _ _ beta (fun x _ => by ring)
      (aux_prop_gluing_isHolderOn_neg beta _ _ (hBsHol k))
  have hnegb : ∀ k, BddAbove {v : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), v = |B x - Bs k x|} := by
    intro k
    obtain ⟨M, hM⟩ := hBsBdd k
    refine ⟨M, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    rw [abs_sub_comm]
    exact hM ⟨x, hx, rfl⟩
  have hnegn : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => B x - Bs k x) = _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => Bs k x - B x) := by
    intro k
    rw [← aux_prop_gluing_cAlphaNorm_neg beta _ (fun x => Bs k x - B x)]
    exact aux_prop_gluing_cAlphaNorm_congr beta _ _ _ (fun x => by ring)
  have hclose : ∀ k n, |Real.sqrt (cellDirichletInfimum (A n)
      (centeredCube z r hr : Set (SpatialCoordinates d))
      ((UN n).restrict (centeredCube z r hr).isOpen hqQ)) -
      Real.sqrt (cellDirichletInfimum (A n)
        (centeredCube z r hr : Set (SpatialCoordinates d)) (Phiq k))| ≤ eps k := by
    intro k n
    obtain ⟨lam, Lam, hlam, hb⟩ := hell n
    have hq_cl : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
      fun x hx => subset_closure (hqQ hx)
    have ha0 : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ A n x :=
      fun x hx => hlam.le.trans (hb x (hq_cl x hx)).1
    have haL : ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), A n x ≤ Lam :=
      fun x hx => (hb x (hq_cl x hx)).2
    have hameas : AEStronglyMeasurable (A n)
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
      ((hAcont n).mono (fun x hx => hq_cl x hx)).aestronglyMeasurable hqmeas
    set β := (UN n).restrict (centeredCube z r hr).isOpen hqQ with hβ
    have h1 := aux_prop_gluing_sqrt_infimum_sub_le _ hqmeas (A n) Lam ha0 haL hameas β (Phiq k)
    have h2 := aux_prop_gluing_sqrt_infimum_sub_le _ hqmeas (A n) Lam ha0 haL hameas (Phiq k) β
    have hcl : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) := closure_mono hqQ
    have hf1 : (β - Phiq k).toFun = fun x => (UN n).toFun x - Bs k x := by
      rw [H1Function.sub_toFun, hβ]
      funext x
      show (UN n).toFun x - (Phiq k).toFun x = _
      rw [hPhiq k]
    have hf2 : (Phiq k - β).toFun = fun x => Bs k x - (UN n).toFun x := by
      rw [H1Function.sub_toFun, hβ]
      funext x
      show (Phiq k).toFun x - (UN n).toFun x = _
      rw [hPhiq k]
    have hb1 := aux_prop_gluing_q_bound z r hr h3r hqQ beta (A n) C UStar (Uq n) hC (hUq n)
      (hBound n) (β - Phiq k)
      (by rw [hf1]; exact ((hUNcont n).mono hcl).sub (hBscont k).continuousOn)
      (fun x => B x - Bs k x) (fun x hx => by rw [hf1]; simp only; rw [hUNq n x hx])
      (hneg k) (hnegb k)
    have hb2 := aux_prop_gluing_q_bound z r hr h3r hqQ beta (A n) C UStar (Uq n) hC (hUq n)
      (hBound n) (Phiq k - β)
      (by rw [hf2]; exact (hBscont k).continuousOn.sub ((hUNcont n).mono hcl))
      (fun x => Bs k x - B x) (fun x hx => by rw [hf2]; simp only; rw [hUNq n x hx])
      (hBsHol k) (hBsBdd k)
    rw [hnegn k] at hb1
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨L, hL1, hL2, -⟩ := aux_prop_gluing_response_three_eps _ _ l
    (fun n => aux_prop_gluing_infimum_nonneg _ hqmeas (A n) (fun x hx => by
      obtain ⟨lam, Lam, hlam, hb⟩ := hell n
      exact hlam.le.trans (hb x (subset_closure (hqQ hx))).1) _)
    (fun k n => aux_prop_gluing_infimum_nonneg _ hqmeas (A n) (fun x hx => by
      obtain ⟨lam, Lam, hlam, hb⟩ := hell n
      exact hlam.le.trans (hb x (subset_closure (hqQ hx))).1) _)
    hl eps heps hclose
  exact ⟨L, hL1, hL2⟩

/-! ## (GlueLimE) -/

/-- The maximum principle between catalogue patches, uniformly in the cutoff. -/
theorem aux_prop_gluing_catalog_patch_max {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (hAcont : ∀ n : ℕ, ContinuousOn (A n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ A n x ∧ A n x ≤ Lam)
    (Bs : ℕ → SpatialCoordinates d → ℝ)
    (PhiH : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hPhiH : ∀ k, (PhiH k).toFun = Bs k)
    (W : ℕ → ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (WS : ℕ → ℕ → S.space)
    (hW : ∀ k n,
      (WS k n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (W k n) ∧
      ContinuousOn (W k n).toFun
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        (W k n).toFun x = 0) ∧
      ∀ c : OddGridIndex d (triadicHalf 1),
        IsWeaklyHarmonicOn (A n)
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((W k n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c)) ∧
        HasZeroTraceDifferenceOn
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((W k n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c))
          ((PhiH k).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c)) ∧
        ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
          (W k n).toFun x = Bs k x) :
    ∀ n j l M, (∀ y, |Bs j y - Bs l y| ≤ M) →
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        |(W j n).toFun x - (W l n).toFun x| ≤ M := by
  intro n j l M hM
  obtain ⟨lam, Lam, hlam, hb⟩ := hell n
  obtain ⟨a, hac, haeq⟩ := aux_prop_gluing_coeff_extension _ isClosed_closure (A n) (hAcont n)
  have hab : ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam := fun x hx => by rw [haeq x hx]; exact hb x hx
  have hcellA : ∀ c : OddGridIndex d (triadicHalf 1), ∀ x ∈
      ((oddGridCell z (3 * r) h3r (triadicHalf 1) c : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)), A n x = a x :=
    fun c x hx => (haeq x (subset_closure (hcellsub c hx))).symm
  exact aux_prop_gluing_patch_max z r hr h3r hcellsub a lam Lam hlam hac hab (W j n) (W l n)
    (PhiH j) (PhiH l)
    (fun c => aux_prop_gluing_harmonic_congr
      (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen.measurableSet (hcellA c)
      ((hW j n).2.2.2 c).1)
    (fun c => aux_prop_gluing_harmonic_congr
      (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen.measurableSet (hcellA c)
      ((hW l n).2.2.2 c).1)
    (fun c => ((hW j n).2.2.2 c).2.1) (fun c => ((hW l n).2.2.2 c).2.1)
    (hW j n).2.1 (hW l n).2.1 M (fun y => by rw [hPhiH j, hPhiH l]; exact hM y)

/-- The comparison passes to the represented limits. -/
theorem aux_prop_gluing_limit_catalog_max {d : ℕ} (s : Set (SpatialCoordinates d))
    (Bs : ℕ → SpatialCoordinates d → ℝ) (F : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (Uck : ℕ → SpatialCoordinates d → ℝ)
    (hconv : ∀ k, TendstoUniformlyOn (fun n => F k n) (Uck k) atTop s)
    (hmax : ∀ n j l M, (∀ y, |Bs j y - Bs l y| ≤ M) → ∀ x ∈ s, |F j n x - F l n x| ≤ M) :
    ∀ j l M, (∀ y, |Bs j y - Bs l y| ≤ M) → ∀ x ∈ s, |Uck j x - Uck l x| ≤ M := by
  intro j l M hM x hx
  have hlim : Tendsto (fun n => |F j n x - F l n x|) atTop (𝓝 |Uck j x - Uck l x|) :=
    (((hconv j).tendsto_at hx).sub ((hconv l).tendsto_at hx)).abs
  exact le_of_tendsto' hlim (fun n => hmax n j l M hM x hx)

/-- Three-epsilon uniform convergence of the Hölder patches (paper label `mfd:prop-gluing`). -/
theorem aux_prop_gluing_limit_uniform {d : ℕ} (s : Set (SpatialCoordinates d))
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hBsU : TendstoUniformly Bs B atTop)
    (UNf : ℕ → SpatialCoordinates d → ℝ) (F : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (Uck : ℕ → SpatialCoordinates d → ℝ) (Uc : SpatialCoordinates d → ℝ)
    (hcomp1 : ∀ n k M, (∀ y, |B y - Bs k y| ≤ M) → ∀ x ∈ s, |UNf n x - F k n x| ≤ M)
    (hconv : ∀ k, TendstoUniformlyOn (fun n => F k n) (Uck k) atTop s)
    (hcomp2 : ∀ k M, (∀ y, |B y - Bs k y| ≤ M) → ∀ x ∈ s, |Uc x - Uck k x| ≤ M) :
    TendstoUniformlyOn UNf Uc atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨k, hk⟩ := ((Metric.tendstoUniformly_iff.mp hBsU) (ε / 4) hδ).exists
  have hkM : ∀ y, |B y - Bs k y| ≤ ε / 4 := fun y => by
    have := hk y
    rw [Real.dist_eq] at this
    exact this.le
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hconv k)) (ε / 4) hδ] with n hn x hx
  have h1 := hcomp1 n k (ε / 4) hkM x hx
  have h2 := hn x hx
  have h3 := hcomp2 k (ε / 4) hkM x hx
  rw [Real.dist_eq] at h2 ⊢
  calc |Uc x - UNf n x| = |(Uc x - Uck k x) + (Uck k x - F k n x) + (F k n x - UNf n x)| := by
        ring_nf
    _ ≤ |Uc x - Uck k x| + |Uck k x - F k n x| + |F k n x - UNf n x| := abs_add_three _ _ _
    _ < ε := by
        rw [abs_sub_comm (F k n x)]
        linarith

/-- : the lower bound transfers the uniform finite-cutoff energy bound
of differences to the limit form. -/
theorem aux_prop_gluing_limit_form_bound {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (aC : ℕ → PositiveCoefficient Ω)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 Ω),
      (∀ w : DomainL2 Ω,
        Tendsto (fun n => ∫ x, w x
            * ((vN n : SobolevData Ω).1) x
            ∂(volume.restrict (Ω : Set (SpatialCoordinates d))))
          atTop (𝓝 (∫ x, w x * v x
            ∂(volume.restrict (Ω : Set (SpatialCoordinates d)))))) →
      E.energy v ≤
        Filter.liminf (fun n => (responseForm S (aC n) (vN n) (vN n) : EReal)) atTop)
    (u v : ℕ → S.space) (U V : DomainL2 Ω) (hU : U ∈ E.domain) (hV : V ∈ E.domain)
    (hu : Tendsto (fun n => ((u n : SobolevData Ω).1)) atTop (𝓝 U))
    (hv : Tendsto (fun n => ((v n : SobolevData Ω).1)) atTop (𝓝 V))
    (K : ℝ) (hK : ∀ n, responseForm S (aC n) (u n - v n) (u n - v n) ≤ K) :
    E.form (U - V) (U - V) ≤ K := by
  have hweak : ∀ w : DomainL2 Ω,
      Tendsto (fun n => ∫ x, w x * (((u n - v n : S.space) : SobolevData Ω).1) x
          ∂(volume.restrict (Ω : Set (SpatialCoordinates d))))
        atTop (𝓝 (∫ x, w x * (U - V) x ∂(volume.restrict (Ω : Set (SpatialCoordinates d))))) := by
    intro w
    simp_rw [← aux_prop_gluing_inner_eq_integral]
    have hd : Tendsto (fun n => (((u n - v n : S.space) : SobolevData Ω).1)) atTop
        (𝓝 (U - V)) := by
      have := hu.sub hv
      refine this.congr (fun n => ?_)
      rw [Submodule.coe_sub, Prod.fst_sub]
    exact tendsto_const_nhds.inner hd
  have h := hLower (fun n => u n - v n) (U - V) hweak
  rw [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energy_of_mem E (E.domain.sub_mem hU hV)] at h
  have hK' : Filter.liminf (fun n => (responseForm S (aC n) (u n - v n) (u n - v n) : EReal))
      atTop ≤ (K : EReal) :=
    Filter.liminf_le_of_frequently_le'
      (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n =>
        EReal.coe_le_coe_iff.mpr (hK n))))
  exact EReal.coe_le_coe_iff.mp (h.trans hK')

/-! ## (GlueLimF) -/

theorem aux_prop_gluing_catalog_limit_form_bound {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (_hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (hAcont : ∀ n : ℕ, ContinuousOn (A n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] A n)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ A n x ∧ A n x ≤ Lam)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (_Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ w : DomainL2 (centeredCube z (3 * r) h3r),
        Tendsto (fun n => ∫ x, w x
            * ((vN n : SobolevData (centeredCube z (3 * r) h3r)).1) x
            ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
          atTop (𝓝 (∫ x, w x * v x
            ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))))) →
      E.energy v ≤
        Filter.liminf (fun n => (responseForm S (aC n) (vN n) (vN n) : EReal)) atTop)
    (Dq : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)))
    (_hDq : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
      (centeredCube z r hr : Set (SpatialCoordinates d)) Dq)
    (C : ℝ) (hC : 0 ≤ C)
    (Ugrid : OddGridIndex d (triadicHalf 1) → ℕ → ℝ)
    (UgridStar : OddGridIndex d (triadicHalf 1) → ℝ)
    (hUg : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      0 ≤ Ugrid k n ∧ Ugrid k n ≤ UgridStar k)
    (hGridBound : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      ∀ e : H1Function
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)),
      ContinuousOn e.toFun
          (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun →
      cellDirichletInfimum (A n)
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) e ≤
        C * Ugrid k n * r ^ ((d : ℝ) - 2) *
          cellBoundaryQuotientNorm beta
            (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun ^ 2)
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (_hBsU : TendstoUniformly Bs B atTop)
    (hBsHol : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => Bs k x - B x))
    (hBsBdd : ∀ k, BddAbove {v : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), v = |Bs k x - B x|})
    (_hBsNorm : Tendsto (fun k => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs k x - B x)) atTop (𝓝 0))
    (b : SpatialCoordinates d → ℝ)
    (_hBb : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), B x = b x)
    (PhiH : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (_hPhiH : ∀ k, (PhiH k).toFun = Bs k)
    (W : ℕ → ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (WS : ℕ → ℕ → S.space)
    (hW : ∀ k n,
      (WS k n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (W k n) ∧
      ContinuousOn (W k n).toFun
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        (W k n).toFun x = 0) ∧
      ∀ c : OddGridIndex d (triadicHalf 1),
        IsWeaklyHarmonicOn (A n)
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((W k n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c)) ∧
        HasZeroTraceDifferenceOn
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((W k n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c))
          ((PhiH k).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c)) ∧
        ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
          (W k n).toFun x = Bs k x)
    (Uk : ℕ → DomainL2 (centeredCube z (3 * r) h3r)) (Uck : ℕ → SpatialCoordinates d → ℝ)
    (hUk1 : ∀ k, Uk k ∈ E.domain)
    (hUk3 : ∀ k, (Uk k : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uck k)
    (hUk4 : ∀ k, TendstoUniformlyOn (fun n => (W k n).toFun) (Uck k) atTop
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))) :
    ∀ j l, E.form (Uk j - Uk l) (Uk j - Uk l) ≤
      (∑ c : OddGridIndex d (triadicHalf 1),
        C * UgridStar c * r ^ ((d : ℝ) - 2) * (max 1 (r ^ beta)) ^ 2) *
      (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs j x - B x) + _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs l x - B x)) ^ 2 := by
  have hfin : volume (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ≠ ⊤ := by
    rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top
  have hKg0 : 0 ≤ ∑ c : OddGridIndex d (triadicHalf 1),
      C * UgridStar c * r ^ ((d : ℝ) - 2) * (max 1 (r ^ beta)) ^ 2 :=
    Finset.sum_nonneg (fun c _ => by
      have := (hUg c 0).1.trans (hUg c 0).2
      have : 0 ≤ r ^ ((d : ℝ) - 2) := Real.rpow_nonneg hr.le _
      positivity)
  have hWL2 : ∀ k, Tendsto (fun n => ((WS k n : SobolevData (centeredCube z (3 * r) h3r)).1))
      atTop (𝓝 (Uk k)) := fun k =>
    aux_prop_gluing_tendsto_L2_of_uniform hfin _ (fun n => (W k n).toFun) (Uk k) (Uck k)
      (fun n => by rw [(hW k n).1]; exact sobolevDataOfH1_fst_coeFn (W k n)) (hUk3 k)
      ((hUk4 k).mono subset_closure)
  intro j l
  obtain ⟨hGj, hGb⟩ := aux_prop_gluing_catalog_diff_holder _ beta Bs B hBsHol hBsBdd j l
  have hsub := aux_prop_gluing_catalog_cAlpha_cauchy (by omega) z (3 * r) h3r beta Bs B
    hBsHol hBsBdd j l
  have hn0 := aux_prop_gluing_cAlphaNorm_nonneg beta
    (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (fun x => Bs j x - Bs l x)
  have hK : ∀ n, responseForm S (aC n) (WS j n - WS l n) (WS j n - WS l n) ≤
      (∑ c : OddGridIndex d (triadicHalf 1),
        C * UgridStar c * r ^ ((d : ℝ) - 2) * (max 1 (r ^ beta)) ^ 2) *
      (_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs j x - B x) + _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs l x - B x)) ^ 2 := by
    intro n
    obtain ⟨lam, Lam, hlam, hb⟩ := hell n
    have hpe := aux_prop_gluing_pair_energy z r hr h3r hcellsub beta hbeta0 S (A n) (hAcont n)
      lam Lam hlam hb (aC n) (haC n) C hC (fun c => Ugrid c n) UgridStar (fun c => hUg c n)
      (fun c => hGridBound c n) (W j n) (W l n) (WS j n) (WS l n) (hW j n).1 (hW l n).1
      (fun c => ((hW j n).2.2.2 c).1) (fun c => ((hW l n).2.2.2 c).1)
      (hW j n).2.1 (hW l n).2.1 (fun x => Bs j x - Bs l x)
      (fun c x hx => by rw [((hW j n).2.2.2 c).2.2 x hx, ((hW l n).2.2.2 c).2.2 x hx])
      hGj hGb
    exact hpe.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hsub 2) hKg0)
  exact aux_prop_gluing_limit_form_bound S aC E hLower (fun n => WS j n) (fun n => WS l n)
    (Uk j) (Uk l) (hUk1 j) (hUk1 l) (hWL2 j) (hWL2 l) _ hK

/-- : the represented limits `U^{(k)}` of the catalogue patches
are Cauchy in the `E`-norm and uniformly; the limit is the harmonic extension of
the Hölder datum with every conclusion of `prop_boundary`. -/
theorem aux_prop_gluing_limit_object {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r)
    (hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (beta : ℝ) (hbeta0 : 0 ≤ beta)
    (S : ResponseSpace (centeredCube z (3 * r) h3r))
    (A : ℕ → SpatialCoordinates d → ℝ)
    (hAcont : ∀ n : ℕ, ContinuousOn (A n)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
    (haC : ∀ n : ℕ,
      ((aC n).val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] A n)
    (hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        lam ≤ A n x ∧ A n x ≤ Lam)
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z (3 * r) h3r)),
      (∀ w : DomainL2 (centeredCube z (3 * r) h3r),
        Tendsto (fun n => ∫ x, w x
            * ((vN n : SobolevData (centeredCube z (3 * r) h3r)).1) x
            ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
          atTop (𝓝 (∫ x, w x * v x
            ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))))) →
      E.energy v ≤
        Filter.liminf (fun n => (responseForm S (aC n) (vN n) (vN n) : EReal)) atTop)
    (Dq : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)))
    (hDq : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
      (centeredCube z r hr : Set (SpatialCoordinates d)) Dq)
    (C : ℝ) (hC : 0 ≤ C)
    (Ugrid : OddGridIndex d (triadicHalf 1) → ℕ → ℝ)
    (UgridStar : OddGridIndex d (triadicHalf 1) → ℝ)
    (hUg : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      0 ≤ Ugrid k n ∧ Ugrid k n ≤ UgridStar k)
    (hGridBound : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
      ∀ e : H1Function
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)),
      ContinuousOn e.toFun
          (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
              Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
      IsCellBoundaryClass beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun →
      cellDirichletInfimum (A n)
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) e ≤
        C * Ugrid k n * r ^ ((d : ℝ) - 2) *
          cellBoundaryQuotientNorm beta
            (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun ^ 2)
    (Bs : ℕ → SpatialCoordinates d → ℝ) (B : SpatialCoordinates d → ℝ)
    (hBsU : TendstoUniformly Bs B atTop)
    (hBsHol : ∀ k, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => Bs k x - B x))
    (hBsBdd : ∀ k, BddAbove {v : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), v = |Bs k x - B x|})
    (hBsNorm : Tendsto (fun k => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
        (fun x => Bs k x - B x)) atTop (𝓝 0))
    (b : SpatialCoordinates d → ℝ)
    (hBb : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), B x = b x)
    (PhiH : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hPhiH : ∀ k, (PhiH k).toFun = Bs k)
    (W : ℕ → ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (WS : ℕ → ℕ → S.space)
    (hW : ∀ k n,
      (WS k n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (W k n) ∧
      ContinuousOn (W k n).toFun
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        (W k n).toFun x = 0) ∧
      ∀ c : OddGridIndex d (triadicHalf 1),
        IsWeaklyHarmonicOn (A n)
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((W k n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c)) ∧
        HasZeroTraceDifferenceOn
          ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
          ((W k n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c))
          ((PhiH k).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) c).isOpen
            (hcellsub c)) ∧
        ∀ x ∈ frontier ((oddGridCell z (3 * r) h3r (triadicHalf 1) c :
            Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
          (W k n).toFun x = Bs k x)
    (Uk : ℕ → DomainL2 (centeredCube z (3 * r) h3r)) (Uck : ℕ → SpatialCoordinates d → ℝ)
    (hUk1 : ∀ k, Uk k ∈ E.domain)
    (hUk2 : ∀ k, ContinuousOn (Uck k)
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hUk3 : ∀ k, (Uk k : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uck k)
    (hUk4 : ∀ k, TendstoUniformlyOn (fun n => (W k n).toFun) (Uck k) atTop
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
    (hUk5 : ∀ k, ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      Uck k x = Bs k x)
    (hUk6 : ∀ k, Gamma.measure (Uk k)
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0)
    (hUk7 : ∀ k, ∀ φ : DomainL2 (centeredCube z (3 * r) h3r), φ ∈ Dq → E.form (Uk k) φ = 0)
    (hUk9 : ∀ k, ∀ V : DomainL2 (centeredCube z (3 * r) h3r),
      V ∈ E.domain →
      ∀ Vc : SpatialCoordinates d → ℝ,
      ContinuousOn Vc
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
      (V : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Vc x = Bs k x) →
      (Gamma.measure (Uk k) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (Gamma.measure V (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
    (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
    (hUNcomp : ∀ n k M, (∀ y, |B y - Bs k y| ≤ M) →
      ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
        |(UN n).toFun x - (W k n).toFun x| ≤ M)
    (L : ℝ)
    (hlL : Tendsto (fun k => (Gamma.measure (Uk k)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) atTop (𝓝 L)) :
    ∃ U : DomainL2 (centeredCube z (3 * r) h3r), ∃ Uc : SpatialCoordinates d → ℝ,
      U ∈ E.domain ∧
      ContinuousOn Uc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      ((U : DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc ∧
      TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Uc x = b x) ∧
      Gamma.measure U (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 ∧
      (∀ phi ∈ Dq, E.form U phi = 0) ∧
      (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal = L ∧
      (∀ V ∈ E.domain, ∀ Vc : SpatialCoordinates d → ℝ,
        ContinuousOn Vc
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        ((V : DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Vc x = b x) →
        (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          (Gamma.measure V (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) := by
  have hfin : volume (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ≠ ⊤ := by
    rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top
  have hqcl : frontier (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) :=
    frontier_subset_closure.trans (closure_mono hqQ)
  -- comparison of catalogue limits
  have hmaxn := aux_prop_gluing_catalog_patch_max z r hr h3r hcellsub S A hAcont hell Bs PhiH
    hPhiH W WS hW
  have hmaxlim := aux_prop_gluing_limit_catalog_max _ Bs (fun k n => (W k n).toFun) Uck hUk4 hmaxn
  obtain ⟨Uc, hUcU, hUcc, hUccomp⟩ := aux_prop_gluing_patch_uniform _ Bs B hBsU Uck hUk2 hmaxlim
  have hmemUc := aux_prop_gluing_memLp_of_continuousOn z (3 * r) h3r Uc hUcc
  set U : DomainL2 (centeredCube z (3 * r) h3r) := hmemUc.toLp Uc with hUdef
  have hUae : ((U : DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc :=
    MemLp.coeFn_toLp hmemUc
  have hL2 : Tendsto Uk atTop (𝓝 U) :=
    aux_prop_gluing_tendsto_L2_of_uniform hfin Uk Uck U Uc hUk3 hUae (hUcU.mono subset_closure)
  have hKg0 : 0 ≤ ∑ c : OddGridIndex d (triadicHalf 1),
      C * UgridStar c * r ^ ((d : ℝ) - 2) * (max 1 (r ^ beta)) ^ 2 :=
    Finset.sum_nonneg (fun c _ => by
      have := (hUg c 0).1.trans (hUg c 0).2
      have : 0 ≤ r ^ ((d : ℝ) - 2) := Real.rpow_nonneg hr.le _
      positivity)
  have he0 : ∀ k, 0 ≤ _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
      (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (fun x => Bs k x - B x) := fun k => aux_prop_gluing_cAlphaNorm_nonneg _ _ _
  have hFk := aux_prop_gluing_catalog_limit_form_bound hd z r hr h3r hqQ hcellsub beta hbeta0 S A
    hAcont aC haC hell E Gamma hLower Dq hDq C hC Ugrid UgridStar hUg hGridBound Bs B hBsU hBsHol
    hBsBdd hBsNorm b hBb PhiH hPhiH W WS hW Uk Uck hUk1 hUk3 hUk4
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      E.form (Uk p - Uk q) (Uk p - Uk q) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := aux_prop_gluing_cauchy_of_bound
      (fun j l => E.form (Uk j - Uk l) (Uk j - Uk l)) _ _ hKg0 he0 hBsNorm hFk (ε / 2)
      (by positivity)
    exact ⟨N, fun p hp q hq => (hN p hp q hq).trans_lt (by linarith)⟩
  obtain ⟨hUdom, hEN⟩ := E.mem_domain_of_tendsto_of_formCauchy Uk hUk1 U hL2 hcauchy
  have hform : Tendsto (fun k => E.form (Uk k - U) (Uk k - U)) atTop (𝓝 0) :=
    squeeze_zero (fun k => E.form_nonneg _ (E.domain.sub_mem (hUk1 k) hUdom))
      (fun k => E.form_le_energyNormSq) hEN
  have hUcb : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Uc x = b x := by
    intro x hx
    have h1 := hUcU.tendsto_at (hqcl hx)
    have h2 : (fun k => Uck k x) = fun k => Bs k x := funext fun k => hUk5 k x hx
    rw [h2] at h1
    rw [← hBb x hx]
    exact tendsto_nhds_unique h1 (hBsU.tendsto_at x)
  refine ⟨U, Uc, hUdom, hUcc, hUae, ?_, hUcb, ?_, ?_, ?_, ?_⟩
  · exact aux_prop_gluing_limit_uniform _ Bs B hBsU (fun n => (UN n).toFun)
      (fun k n => (W k n).toFun) Uck Uc hUNcomp hUk4 hUccomp
  · have hlim := aux_prop_gluing_gamma_seq_limit Gamma Uk U hUk1 hUdom hform
      (isClosed_frontier (s := (centeredCube z r hr : Set (SpatialCoordinates d)))).measurableSet
    have h0 : (fun k => (Gamma.measure (Uk k)
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d)))).toReal) = fun _ => 0 :=
      funext fun k => by rw [hUk6 k]; rfl
    rw [h0] at hlim
    have hz := tendsto_nhds_unique tendsto_const_nhds hlim
    rcases (ENNReal.toReal_eq_zero_iff _).mp hz.symm with h | h
    · exact h
    · exact absurd h (Gamma.measure_ne_top hUdom _)
  · intro phi hphi
    have hlim := aux_prop_gluing_form_seq_limit E Uk U hUk1 hUdom hform phi (hDq.le_domain hphi)
    have h0 : (fun k => E.form (Uk k) phi) = fun _ => 0 := funext fun k => hUk7 k phi hphi
    rw [h0] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  · have hlim := aux_prop_gluing_gamma_seq_limit Gamma Uk U hUk1 hUdom hform
      (centeredCube z r hr).isOpen.measurableSet
    exact tendsto_nhds_unique hlim hlL
  · intro V hV Vc hVc hVae hVb
    have hVk : ∀ k, V + (Uk k - U) ∈ E.domain :=
      fun k => E.domain.add_mem hV (E.domain.sub_mem (hUk1 k) hUdom)
    have hmin : ∀ k, (Gamma.measure (Uk k) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
        (Gamma.measure (V + (Uk k - U)) (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
      intro k
      refine hUk9 k (V + (Uk k - U)) (hVk k) (fun x => Vc x + (Uck k x - Uc x))
        (hVc.add ((hUk2 k).sub hUcc)) ?_ ?_
      · filter_upwards [Lp.coeFn_add V (Uk k - U), Lp.coeFn_sub (Uk k) U, hVae, hUk3 k, hUae]
          with x h1 h2 h3 h4 h5
        rw [h1, Pi.add_apply, h2, Pi.sub_apply, h3, h4, h5]
      · intro x hx
        rw [hVb x hx, hUk5 k x hx, hUcb x hx]
        ring
    have hlimU := aux_prop_gluing_gamma_seq_limit Gamma Uk U hUk1 hUdom hform
      (centeredCube z r hr).isOpen.measurableSet
    have hformV : Tendsto (fun k => E.form (V + (Uk k - U) - V) (V + (Uk k - U) - V)) atTop
        (𝓝 0) := by
      refine hform.congr (fun k => ?_)
      rw [add_sub_cancel_left]
    have hlimV := aux_prop_gluing_gamma_seq_limit Gamma (fun k => V + (Uk k - U)) V hVk hV
      hformV (centeredCube z r hr).isOpen.measurableSet
    exact le_of_tendsto_of_tendsto' hlimU hlimV hmin

/-- Gluing of the cell responses and their limiting representatives. The proof combines the smooth-mesh construction, face-mass identity and replacement estimates; its displayed coefficient, Sobolev and convergence inputs remain explicit. -/
theorem prop_gluing
    (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h3r : 0 < 3 * r) :
    ∀ (hqQ : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (hcellsub : ∀ k : OddGridIndex d (triadicHalf 1),
        ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)) ⊆
          (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (beta alpha : ℝ) (_hbeta : 1 / 2 < beta) (_hba : beta < alpha) (_ha1 : alpha < 1)
      (S : ResponseSpace (centeredCube z (3 * r) h3r))
      (_hS : S.space = killedSobolevGraph (centeredCube z (3 * r) h3r))
      (A : ℕ → SpatialCoordinates d → ℝ)
      (_hAcont : ∀ n : ℕ, ContinuousOn (A n)
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
      (aC : ℕ → PositiveCoefficient (centeredCube z (3 * r) h3r))
      (_haC : ∀ n : ℕ,
        ((aC n).val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] A n)
      (_hell : ∀ n : ℕ, ∃ lam Lam : ℝ, 0 < lam ∧
        ∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          lam ≤ A n x ∧ A n x ≤ Lam)
      (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
        (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
      (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
      (_hLower : ∀ (vN : ℕ → S.space) (v : DomainL2 (centeredCube z (3 * r) h3r)),
        (∀ w : DomainL2 (centeredCube z (3 * r) h3r),
          Tendsto (fun n => ∫ x, w x
              * ((vN n : SobolevData (centeredCube z (3 * r) h3r)).1) x
              ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
            atTop (𝓝 (∫ x, w x * v x
              ∂(volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))))) →
        E.energy v ≤
          Filter.liminf (fun n => (responseForm S (aC n) (vN n) (vN n) : EReal)) atTop)
      (_hRecovery : ∀ v ∈ E.domain, ∃ vN : ℕ → S.space,
        Tendsto (fun n => ((vN n : SobolevData (centeredCube z (3 * r) h3r)).1,
            (responseForm S (aC n) (vN n) (vN n) : EReal)))
          atTop (𝓝 (v, E.energy v)))
      (Dq : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)))
      (_hDq : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
        (centeredCube z r hr : Set (SpatialCoordinates d)) Dq)
      (_hTruncate : ∀ v ∈ E.domain, ∀ vc : SpatialCoordinates d → ℝ,
        ContinuousOn vc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        ((v : DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] vc →
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), vc x = 0) →
        ∃ w : DomainL2 (centeredCube z (3 * r) h3r), w ∈ Dq ∧
          ((w : DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
              ((closure (centeredCube z r hr : Set (SpatialCoordinates d))).indicator vc) ∧
          E.form w w
            = (Gamma.measure v (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
      (_hDirichlet : ∃ EDir : _root_.SubdiffusiveProcess.DirichletForm
        (volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))),
        EDir.toClosedForm = E)
      (t : ℝ) (_ht : (d : ℝ) - 1 < t) (_htd : t < (d : ℝ))
      (KN : ℕ → ℝ) (_hKN : ∀ n, 0 ≤ KN n)
      (Kstar : ℝ) (_hKstar : ∀ n, KN n ≤ Kstar)
      (_hfrac : ∀ w : S.space,
        cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => w.val.1) < ⊤)
      (_hcoercive : ∀ n (w : S.space),
        ‖w.val.1‖ ^ 2 +
            volume.real (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) *
              ((cubeFractionalL2Seminorm hd z (3 * r) h3r _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
                (fun _ : Fin 1 => w.val.1)).toReal) ^ 2 ≤
          KN n * responseForm S (aC n) w w)
      (_hInterp : CubeFractionalInterpolationInput d hd)
      (_hcutoffs : ∀ (K O : Set (SpatialCoordinates d)),
        IsCompact K → IsOpen O → K ⊆ O →
        closure O ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
        ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
          (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
          IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
            ContinuousOn (chic n)
              (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
            ((chi n).val.1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict
                (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
                chic n ∧
            (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
              0 ≤ chic n x ∧ chic n x ≤ 1) ∧
            (∀ x ∈ V, chic n x = 1) ∧
            (∀ x ∈ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
              x ∉ O → chic n x = 0) ∧
            responseForm S (aC n) (chi n) (chi n) ≤ B ∧
            (∀ x ∈ closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
              ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
              ((volume.restrict
                (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))).withDensity
                (fun y => ENNReal.ofReal ((aC n).val y *
                  ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
                (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t)))
      (_hEnergyMeasures :
        (∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
            (uN : ℕ → S.space),
          u ∈ E.domain →
          Tendsto (fun n => ((uN n).val.1,
            (responseForm S (aC n) (uN n) (uN n) : EReal))) atTop
            (𝓝 (u, E.energy u)) →
          ∀ φ : SpatialCoordinates d → ℝ,
            ContinuousOn φ
              (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
            Tendsto (fun n =>
              ∫ x, φ x ∂(((volume.restrict
                (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
                (fun y => ENNReal.ofReal ((aC n).val y *
                  ∑ i : Fin d, ((uN n : SobolevData
                    (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
              (𝓝 (∫ x, φ x ∂(Gamma.measure u)))) ∧
        (∀ (u : DomainL2 (centeredCube z (3 * r) h3r))
            (uN : ℕ → S.space) (E0 : ℝ)
            (nu : Measure (SpatialCoordinates d)) (sigma : ℕ → ℕ),
          nu Set.univ < (⊤ : ENNReal) →
          nu ((closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))ᶜ) = 0 →
          StrictMono sigma →
          Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
          (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
          (∀ φ : SpatialCoordinates d → ℝ,
            ContinuousOn φ
              (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
            Tendsto (fun n =>
              ∫ x, φ x ∂(((volume.restrict
                (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))).withDensity
                (fun y => ENNReal.ofReal ((aC (sigma n)).val y *
                  ∑ i : Fin d, ((uN (sigma n) : SobolevData
                    (centeredCube z (3 * r) h3r)).2 i y) ^ 2)))) atTop
              (𝓝 (∫ x, φ x ∂nu))) →
          u ∈ E.domain ∧
            ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
              Gamma.measure u B ≤ nu B) ∧
        (∀ (u v : DomainL2 (centeredCube z (3 * r) h3r))
            (uN vN : ℕ → S.space) (E0 : ℝ),
          Tendsto (fun n => (uN n).val.1) atTop (𝓝 u) →
          (∀ n : ℕ, responseForm S (aC n) (uN n) (uN n) ≤ E0) →
          v ∈ E.domain →
          Tendsto (fun n => ((vN n).val.1,
            (responseForm S (aC n) (vN n) (vN n) : EReal))) atTop
            (𝓝 (v, E.energy v)) →
          ∀ φ : SpatialCoordinates d → ℝ,
            ContinuousOn φ
              (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
            Tendsto (fun n =>
              ∫ x in (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
                φ x * ((aC n).val x *
                  ∑ i : Fin d,
                    ((uN n : SobolevData (centeredCube z (3 * r) h3r)).2 i x) *
                    ((vN n : SobolevData (centeredCube z (3 * r) h3r)).2 i x))) atTop
              (𝓝 (_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ φ))))
      (_hZeroTrace : ∀ (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc),
        let qc := centeredCube zc rc hrc
        (qc : Set (SpatialCoordinates d)) ⊆
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) →
        ∀ D : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)),
          _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E (qc : Set (SpatialCoordinates d)) D →
        ∀ w ∈ E.domain, ∀ wc : SpatialCoordinates d → ℝ,
          ContinuousOn wc
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
          (w : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict
              (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] wc →
          (∀ x ∈ frontier (qc : Set (SpatialCoordinates d)), wc x = 0) →
          ∀ wq : DomainL2 (centeredCube z (3 * r) h3r),
            (wq : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict
                (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))]
                (closure (qc : Set (SpatialCoordinates d))).indicator wc →
            wq ∈ D ∧
              E.form wq wq =
                (Gamma.measure w (qc : Set (SpatialCoordinates d))).toReal)
      (_hKilledCells : ∀ k : OddGridIndex d (triadicHalf 1),
        ∃ D : Submodule ℝ (DomainL2 (centeredCube z (3 * r) h3r)),
          (_root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
            (oddGridCell z (3 * r) h3r (triadicHalf 1) k : Set (SpatialCoordinates d)) D))
      (C UStar : ℝ) (_hC : 0 ≤ C) (_hUS : 0 ≤ UStar)
      (Uq : ℕ → ℝ) (_hUq : ∀ n : ℕ, 0 ≤ Uq n ∧ Uq n ≤ UStar)
      (Ugrid : OddGridIndex d (triadicHalf 1) → ℕ → ℝ)
      (UgridStar : OddGridIndex d (triadicHalf 1) → ℝ)
      (_hUg : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
        0 ≤ Ugrid k n ∧ Ugrid k n ≤ UgridStar k)
      (_hBound : ∀ n : ℕ, ∀ e : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
        ContinuousOn e.toFun (closure (centeredCube z r hr : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta z r e.toFun →
        cellDirichletInfimum (A n) (centeredCube z r hr : Set (SpatialCoordinates d)) e ≤
          C * Uq n * r ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta z r e.toFun ^ 2)
      (_hGridBound : ∀ (k : OddGridIndex d (triadicHalf 1)) (n : ℕ),
        ∀ e : H1Function
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
              Set (SpatialCoordinates d)),
        ContinuousOn e.toFun
            (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun →
        cellDirichletInfimum (A n)
            ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) :
              Set (SpatialCoordinates d)) e ≤
          C * Ugrid k n * r ^ ((d : ℝ) - 2) *
            cellBoundaryQuotientNorm beta
              (oddGridCenter z (3 * r) (triadicHalf 1) k) r e.toFun ^ 2)
      (Catalog : Set (SpatialCoordinates d → ℝ)) (_hCountable : Catalog.Countable)
      (_hCatalog : ∀ Phi ∈ Catalog,
        ContDiff ℝ ∞ Phi ∧ HasCompactSupport Phi ∧
          tsupport Phi ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (Ext : (SpatialCoordinates d → ℝ) →ₗ[ℝ] (SpatialCoordinates d → ℝ))
      (_hExtTrace : ∀ b0, ∀ x ∈ frontier
        (centeredCube z r hr : Set (SpatialCoordinates d)), Ext b0 x = b0 x)
      (_hExtCongr : ∀ b0 b1,
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), b0 x = b1 x) →
        Ext b0 = Ext b1)
      (_hCatalogFixed : ∀ Phi ∈ Catalog, Ext Phi = Phi)
      (_hExtRegular : ∀ b0 : SpatialCoordinates d → ℝ,
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b0 →
        ContinuousOn (Ext b0)
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
        HasCompactSupport (Ext b0) ∧
        tsupport (Ext b0) ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ∧
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) (Ext b0))
      (_hCatalogDense : ∀ b0 : SpatialCoordinates d → ℝ,
        _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
          (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b0 →
        ∃ Bk : ℕ → SpatialCoordinates d → ℝ,
          (∀ k : ℕ, Bk k ∈ Catalog) ∧
          (∀ k : ℕ, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn beta
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
            (fun x => Bk k x - Ext b0 x)) ∧
          Tendsto (fun k => _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta
              (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
              (fun x => Bk k x - Ext b0 x))
            atTop (𝓝 0) ∧
          TendstoUniformlyOn Bk (Ext b0) atTop
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))))
      (_hCatalogBounds : ∀ Phi, Phi ∈ Catalog →
        ∀ PhiH : H1Function
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          PhiH.toFun = Phi →
          ∃ Bcell Hcell : OddGridIndex d (triadicHalf 1) → ℝ,
            (∀ k : OddGridIndex d (triadicHalf 1),
              0 ≤ Bcell k ∧ 0 ≤ Hcell k) ∧
            ∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1))
              (w : H1Function
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))),
              IsWeaklyHarmonicOn (A n)
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w →
              HasZeroTraceDifferenceOn
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w
                (PhiH.restrict
                  (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen
                  (hcellsub k)) →
              energy (A n)
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) w ≤ Bcell k ∧
              (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                  Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
                  ((volume.restrict
                    ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))).withDensity
                    (fun y => ENNReal.ofReal ((A n) y *
                      ∑ i : Fin d, (w.grad y i) ^ 2)))
                    (Metric.ball x rr) ≤ ENNReal.ofReal (Bcell k * rr ^ t)) ∧
              ∃ wc : SpatialCoordinates d → ℝ,
                ContinuousOn wc
                  (closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) ∧
                w.toFun =ᵐ[volume.restrict
                  ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))] wc ∧
                (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                  ∀ y ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                    |wc x - wc y| ≤ Hcell k * dist x y ^ alpha) ∧
                (∀ x ∈ closure ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
                  |wc x| ≤ Hcell k))
      (_hCatalogL2 : ∀ Phi, Phi ∈ Catalog →
        ∀ PhiH : H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
          PhiH.toFun = Phi →
          ∀ (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
            (UNS : ℕ → S.space),
            (∀ n : ℕ, (UNS n : SobolevData (centeredCube z (3 * r) h3r)) = sobolevDataOfH1 (UN n)) →
            (∀ (n : ℕ) (k : OddGridIndex d (triadicHalf 1)),
              IsWeaklyHarmonicOn (A n)
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
                ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)) ∧
              HasZeroTraceDifferenceOn
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
                ((UN n).restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))
                (PhiH.restrict (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k))) →
            ∃ uBar : DomainL2 (centeredCube z (3 * r) h3r),
              Tendsto (fun n => (UNS n).val.1) atTop (𝓝 uBar))
      (b : SpatialCoordinates d → ℝ)
      (_hb : _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) b),
    ∃ (B : SpatialCoordinates d → ℝ)
      (UN : ℕ → H1Function (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)))
      (UNS : ℕ → S.space),
      IsCellBoundaryClass beta z r b ∧
      ContinuousOn B
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      HasCompactSupport B ∧
      tsupport B ⊆ (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)) ∧
      _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) B ∧
      B = Ext b ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), B x = b x) ∧
      (∀ n : ℕ,
          (UNS n).val = sobolevDataOfH1 (UN n) ∧
          ContinuousOn (UN n).toFun
            (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ frontier (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)),
            (UN n).toFun x = 0) ∧
          ∀ k : OddGridIndex d (triadicHalf 1),
            IsWeaklyHarmonicOn (A n)
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))
                ((UN n).restrict
                  (oddGridCell z (3 * r) h3r (triadicHalf 1) k).isOpen (hcellsub k)) ∧
            ∀ x ∈ frontier
                ((oddGridCell z (3 * r) h3r (triadicHalf 1) k :
                    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
              (UN n).toFun x = B x) ∧
    ∃ L : ℝ, ∃ U : DomainL2 (centeredCube z (3 * r) h3r), ∃ Uc : SpatialCoordinates d → ℝ,
      Tendsto (fun n => cellDirichletInfimum (A n)
          (centeredCube z r hr : Set (SpatialCoordinates d))
          ((UN n).restrict (centeredCube z r hr).isOpen hqQ))
        atTop (𝓝 L) ∧
      L ≤ C * UStar * r ^ ((d : ℝ) - 2) * cellBoundaryQuotientNorm beta z r b ^ 2 ∧
      U ∈ E.domain ∧
      ContinuousOn Uc (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      ((U : DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Uc ∧
      TendstoUniformlyOn (fun n => (UN n).toFun) Uc atTop
        (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Uc x = b x) ∧
      Gamma.measure U (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 ∧
      (∀ phi ∈ Dq, E.form U phi = 0) ∧
      (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal = L ∧
      (∀ V ∈ E.domain, ∀ Vc : SpatialCoordinates d → ℝ,
        ContinuousOn Vc
          (closure (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))) →
        ((V : DomainL2 (centeredCube z (3 * r) h3r)) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict
            (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d))] Vc →
        (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), Vc x = b x) →
        (Gamma.measure U (centeredCube z r hr : Set (SpatialCoordinates d))).toReal ≤
          (Gamma.measure V (centeredCube z r hr : Set (SpatialCoordinates d))).toReal) := by
  intro hqQ hcellsub beta alpha hbeta hba ha1 S hS A hAcont aC haC hell E Gamma hLower hRecovery
    Dq hDq hTruncate hDirichlet t ht htd KN hKN Kstar hKstar hfrac hcoercive hInterp hcutoffs
    hEnergyMeasures hZeroTrace hKilledCells C UStar hC hUS Uq hUq Ugrid UgridStar hUg hBound
    hGridBound Catalog hCountable hCatalog Ext hExtTrace hExtCongr hCatalogFixed hExtRegular
    hCatalogDense hCatalogBounds hCatalogL2 b hb
  have : NeZero d := ⟨by omega⟩
  have hbeta0 : 0 ≤ beta := by linarith
  obtain ⟨hcls, hBc, hBsupp, hBts, hBhol, -, hBtr⟩ :=
    aux_prop_gluing_datum_block z r hr h3r beta alpha hbeta hba Ext hExtTrace hExtRegular b hb
  obtain ⟨Bs, hBsCat, hBsHol, hBsNorm, hBsUnif⟩ := hCatalogDense b hb
  have hBsU : TendstoUniformly Bs (Ext b) atTop :=
    aux_prop_gluing_tendstoUniformly_global _ Bs (Ext b) hBsUnif
      (fun k y hy => image_eq_zero_of_notMem_tsupport
        (fun h => hy (subset_closure ((hCatalog _ (hBsCat k)).2.2 h))))
      (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (subset_closure (hBts h))))
  have hBsBdd : ∀ k, BddAbove {v : ℝ | ∃ x ∈ closure
      (centeredCube z (3 * r) h3r : Set (SpatialCoordinates d)), v = |Bs k x - Ext b x|} :=
    fun k => aux_prop_gluing_bddAbove_abs_of_isHolderOn _ _ (Real.sqrt (d : ℝ) * (3 * r)) beta
      (by positivity)
      (fun x hx y hy => aux_prop_gluing_euclid_le_of_mem_closure z (3 * r) h3r x y hx hy)
      hbeta0 (hBsHol k)
  have hpkg := fun k => aux_prop_gluing_catalog_package d hd z r hr h3r hcellsub beta alpha hbeta
    hba ha1 S hS A hAcont aC haC hell E Gamma hLower hRecovery Dq hDq hDirichlet t ht htd KN hKN
    Kstar hKstar hfrac hcoercive hInterp hcutoffs hEnergyMeasures hZeroTrace hKilledCells Catalog
    hCatalog hCatalogBounds hCatalogL2 (Bs k) (hBsCat k)
  choose PhiH Phiq W WS Uk Uck hPhiH hPhiq hW hUk1 hUk2 hUk3 hUk4 hUk5 hUk6 hUk7 hUk8 hUk9
    using hpkg
  obtain ⟨UN, UNS, hpatch, hUNcomp⟩ := aux_prop_gluing_holder_patches hd z r hr h3r hcellsub beta
    hbeta0 S A hAcont aC haC hell C hC Ugrid UgridStar hUg hGridBound Bs (Ext b) hBsU hBsHol
    hBsBdd hBsNorm PhiH hPhiH W WS hW
  have hUNq : ∀ n : ℕ, ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (UN n).toFun x = b x :=
    aux_prop_gluing_face_values_central z r hr h3r hcellsub A Ext b hExtTrace UN UNS hpatch
  obtain ⟨L, hL, hlL⟩ := aux_prop_gluing_response z r hr h3r hqQ beta A hAcont hell C UStar hC Uq
    hUq hBound Bs (Ext b) (fun k => (hCatalog _ (hBsCat k)).1.continuous) hBsHol hBsBdd hBsNorm
    Phiq hPhiq _ hUk8 UN (fun n => (hpatch n).2.1)
    (fun n x hx => (hUNq n x hx).trans (hExtTrace b x hx).symm)
  have hLb := aux_prop_gluing_bound z r hr h3r hqQ beta A C UStar hC Uq hUq hBound b hcls UN
    (fun n => (hpatch n).2.1) hUNq L hL
  obtain ⟨U, Uc, hrest⟩ := aux_prop_gluing_limit_object hd z r hr h3r hqQ hcellsub beta hbeta0 S A
    hAcont aC haC hell E Gamma hLower Dq hDq C hC Ugrid UgridStar hUg hGridBound Bs (Ext b) hBsU
    hBsHol hBsBdd hBsNorm b hBtr PhiH hPhiH W WS hW Uk Uck hUk1 hUk2 hUk3 hUk4 hUk5 hUk6 hUk7 hUk9
    UN hUNcomp L hlL
  exact ⟨Ext b, UN, UNS, hcls, hBc, hBsupp, hBts, hBhol, rfl, hBtr, hpatch, L, U, Uc, hL, hLb,
    hrest⟩

end SubdiffusiveProcess.Paper
