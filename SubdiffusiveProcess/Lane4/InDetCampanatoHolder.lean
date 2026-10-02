import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase




open MeasureTheory Set Metric Filter Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane4 SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
namespace Paper

/-! ## Elementary geometry of sup-metric windows -/

/-- The sup distance is at most the Euclidean distance used by `holderRatioSet`. -/
theorem aux_in_deterministic_regularity_dist_le_euclid {d : ℕ} (x y : SpatialCoordinates d) :
    dist x y ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  refine (dist_pi_le_iff (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.dist_eq, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- Volume of a sup-metric ball. -/
theorem aux_in_deterministic_regularity_volume_ball {d : ℕ} (x : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) : volume.real (ball x r) = (2 * r) ^ d := by
  show (volume (ball x r)).toReal = _
  rw [Real.volume_pi_ball x hr, Fintype.card_fin, ENNReal.toReal_ofReal (by positivity)]

/-- A window of side `ρ ≤ s` around a point of the closed cube contains a sup-ball of
radius `ρ / 4`. -/
theorem aux_in_deterministic_regularity_window_contains {d : ℕ} (c x : SpatialCoordinates d)
    {s ρ : ℝ} (hρ : 0 < ρ) (hρs : ρ ≤ s) (hx : x ∈ closedBall c (s / 2)) :
    ∃ y : SpatialCoordinates d, ball y (ρ / 4) ⊆ ball x (ρ / 2) ∩ ball c (s / 2) := by
  refine ⟨fun i => if x i ≤ c i then x i + ρ / 4 else x i - ρ / 4, ?_⟩
  intro z hz
  have hs : 0 < s := hρ.trans_le hρs
  rw [mem_ball, dist_pi_lt_iff (by positivity)] at hz
  rw [mem_closedBall, dist_pi_le_iff (by positivity)] at hx
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_pi_lt_iff (by positivity)]
    intro i
    have h1 : |z i - (if x i ≤ c i then x i + ρ / 4 else x i - ρ / 4)| < ρ / 4 := by
      simpa [Real.dist_eq] using hz i
    rw [Real.dist_eq, abs_lt]
    rw [abs_lt] at h1
    split_ifs at h1 <;> constructor <;> linarith [h1.1, h1.2]
  · rw [mem_ball, dist_pi_lt_iff (by positivity)]
    intro i
    have h1 : |z i - (if x i ≤ c i then x i + ρ / 4 else x i - ρ / 4)| < ρ / 4 := by
      simpa [Real.dist_eq] using hz i
    have h2 := hx i
    rw [Real.dist_eq, abs_lt]
    rw [Real.dist_eq, abs_le] at h2
    rw [abs_lt] at h1
    split_ifs at h1 with h
    · constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · push_neg at h
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Two-sided volume bounds for a window around a point of the closed cube. -/
theorem aux_in_deterministic_regularity_window_volume {d : ℕ} (c x : SpatialCoordinates d)
    {s ρ : ℝ} (hρ : 0 < ρ) (hρs : ρ ≤ s) (hx : x ∈ closedBall c (s / 2)) :
    (ρ / 2) ^ d ≤ volume.real (ball x (ρ / 2) ∩ ball c (s / 2)) ∧
      volume.real (ball x (ρ / 2) ∩ ball c (s / 2)) ≤ ρ ^ d := by
  have hfin : volume (ball x (ρ / 2)) ≠ ⊤ := measure_ball_lt_top.ne
  have hfin' : volume (ball x (ρ / 2) ∩ ball c (s / 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)
  obtain ⟨y, hy⟩ := aux_in_deterministic_regularity_window_contains c x hρ hρs hx
  refine ⟨?_, ?_⟩
  · have h1 := measureReal_mono hy hfin'
    rw [aux_in_deterministic_regularity_volume_ball y (by positivity)] at h1
    calc (ρ / 2) ^ d = (2 * (ρ / 4)) ^ d := by ring
      _ ≤ _ := h1
  · have h1 := measureReal_mono (μ := volume) (inter_subset_left :
      ball x (ρ / 2) ∩ ball c (s / 2) ⊆ ball x (ρ / 2)) hfin
    rw [aux_in_deterministic_regularity_volume_ball x (by positivity)] at h1
    calc _ ≤ (2 * (ρ / 2)) ^ d := h1
      _ = ρ ^ d := by ring

/-! ## Averages -/

/-- `(⨍_B h)² ≤ ⨍_B h²`. -/
theorem aux_in_deterministic_regularity_sq_avg_le {d : ℕ} {B : Set (SpatialCoordinates d)}
    (hvol : volume B ≠ ⊤) {h : SpatialCoordinates d → ℝ} (hi : IntegrableOn h B)
    (hi2 : IntegrableOn (fun y => h y ^ 2) B) :
    ((volume.real B)⁻¹ * ∫ y in B, h y) ^ 2 ≤ (volume.real B)⁻¹ * ∫ y in B, h y ^ 2 := by
  rcases (measureReal_nonneg : 0 ≤ volume.real B).eq_or_lt with hV0 | hVpos
  · rw [← hV0]; simp
  have hint : ∫ y in B, h y = volume.real B * ((volume.real B)⁻¹ * ∫ y in B, h y) := by
    rw [← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul]
  generalize hm : (volume.real B)⁻¹ * ∫ y in B, h y = m at hint ⊢
  have hconst : IntegrableOn (fun _ : SpatialCoordinates d => m ^ 2) B :=
    integrableOn_const hvol
  have hlin : IntegrableOn (fun y => 2 * m * h y) B := hi.const_mul _
  have hexp : ∫ y in B, (h y - m) ^ 2 =
      ((∫ y in B, h y ^ 2) - 2 * m * (∫ y in B, h y)) + m ^ 2 * volume.real B := by
    have hpt : (fun y => (h y - m) ^ 2) = fun y => (h y ^ 2 - 2 * m * h y) + m ^ 2 := by
      funext y; ring
    rw [hpt, integral_add (f := fun y => h y ^ 2 - 2 * m * h y) (g := fun _ => m ^ 2)
      (hi2.sub hlin) hconst,
      integral_sub (f := fun y => h y ^ 2) (g := fun y => 2 * m * h y) hi2 hlin,
      integral_const_mul, setIntegral_const, smul_eq_mul]
    ring
  have hnn : 0 ≤ ∫ y in B, (h y - m) ^ 2 := integral_nonneg fun y => sq_nonneg _
  rw [hexp, hint] at hnn
  have hkey : m ^ 2 * volume.real B ≤ ∫ y in B, h y ^ 2 := by nlinarith
  rw [le_inv_mul_iff₀ hVpos]
  linarith

/-- Comparison of the averages on nested windows `B' ⊆ B` by the oscillation on `B`. -/
theorem aux_in_deterministic_regularity_avg_sub_avg_le {d : ℕ}
    {Kset B B' : Set (SpatialCoordinates d)} (hK : IsCompact Kset)
    {U : SpatialCoordinates d → ℝ} (hU : ContinuousOn U Kset) (hBK : B ⊆ Kset)
    (hB'B : B' ⊆ B) (hvol' : 0 < volume.real B') :
    |((volume.real B')⁻¹ * ∫ t in B', U t) - (volume.real B)⁻¹ * ∫ t in B, U t| ≤
      Real.sqrt (volume.real B / volume.real B') *
        normalizedL2On B (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) := by
  set A := (volume.real B)⁻¹ * ∫ t in B, U t with hA
  have hKfin : volume Kset ≠ ⊤ := hK.measure_lt_top.ne
  have hBfin : volume B ≠ ⊤ := ne_top_of_le_ne_top hKfin (measure_mono hBK)
  have hB'fin : volume B' ≠ ⊤ := ne_top_of_le_ne_top hBfin (measure_mono hB'B)
  have hUK : IntegrableOn U Kset := hU.integrableOn_compact hK
  have hU2K : IntegrableOn (fun y => (U y - A) ^ 2) Kset :=
    ((hU.sub continuousOn_const).pow 2).integrableOn_compact hK
  have hUB' : IntegrableOn U B' := hUK.mono_set (hB'B.trans hBK)
  have hU2B : IntegrableOn (fun y => (U y - A) ^ 2) B := hU2K.mono_set hBK
  have hU2B' : IntegrableOn (fun y => (U y - A) ^ 2) B' := hU2B.mono_set hB'B
  have hVle : volume.real B' ≤ volume.real B := measureReal_mono hB'B hBfin
  have hVpos : 0 < volume.real B := hvol'.trans_le hVle
  -- the average of `U - A` on `B'`
  have hshift : (volume.real B')⁻¹ * ∫ t in B', (U t - A) =
      ((volume.real B')⁻¹ * ∫ t in B', U t) - A := by
    rw [integral_sub hUB' (integrableOn_const hB'fin), setIntegral_const, smul_eq_mul,
      mul_sub, ← mul_assoc, inv_mul_cancel₀ hvol'.ne', one_mul]
  have hjensen := aux_in_deterministic_regularity_sq_avg_le (h := fun y => U y - A) hB'fin
    (hUB'.sub (integrableOn_const hB'fin)) hU2B'
  rw [hshift] at hjensen
  -- enlarge the integration domain
  have hmono : ∫ y in B', (U y - A) ^ 2 ≤ ∫ y in B, (U y - A) ^ 2 :=
    setIntegral_mono_set hU2B (Eventually.of_forall fun y => sq_nonneg _)
      (Eventually.of_forall hB'B)
  have hstep : (volume.real B')⁻¹ * ∫ y in B', (U y - A) ^ 2 ≤
      (volume.real B / volume.real B') *
        ((volume.real B)⁻¹ * ∫ y in B, (U y - A) ^ 2) := by
    have heq : (volume.real B / volume.real B') *
        ((volume.real B)⁻¹ * ∫ y in B, (U y - A) ^ 2) =
        (volume.real B')⁻¹ * ∫ y in B, (U y - A) ^ 2 := by
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hvol'.le)
  have hnorm : normalizedL2On B (fun y => U y - A) =
      Real.sqrt ((volume.real B)⁻¹ * ∫ y in B, (U y - A) ^ 2) := rfl
  rw [hnorm, ← Real.sqrt_mul (div_nonneg hVpos.le hvol'.le), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (hjensen.trans hstep)

/-- An average of a function uniformly close to a constant is close to that constant. -/
theorem aux_in_deterministic_regularity_avg_sub_const_le {d : ℕ}
    {B : Set (SpatialCoordinates d)} (hfin : volume B ≠ ⊤) (hpos : 0 < volume.real B)
    {U : SpatialCoordinates d → ℝ} (hi : IntegrableOn U B) (a ε : ℝ)
    (hε : ∀ y ∈ B, |U y - a| ≤ ε) :
    |((volume.real B)⁻¹ * ∫ t in B, U t) - a| ≤ ε := by
  have hsub : ((volume.real B)⁻¹ * ∫ t in B, U t) - a =
      (volume.real B)⁻¹ * ∫ t in B, (U t - a) := by
    rw [integral_sub hi (integrableOn_const hfin), setIntegral_const, smul_eq_mul,
      mul_sub, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  rw [hsub, abs_mul, abs_inv, abs_of_pos hpos]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := B)
    (f := fun t => U t - a) (lt_top_iff_ne_top.2 hfin) (C := ε)
    (fun y hy => by simpa [Real.norm_eq_abs] using hε y hy)
  rw [Real.norm_eq_abs] at h
  rw [inv_mul_le_iff₀ hpos]
  linarith [mul_comm ε (volume.real B)]






def aux_in_deterministic_regularity_avg {d : ℕ} (B : Set (SpatialCoordinates d))
    (U : SpatialCoordinates d → ℝ) : ℝ :=
  (volume.real B)⁻¹ * ∫ t in B, U t



def aux_in_deterministic_regularity_window {d : ℕ} (c : SpatialCoordinates d) (s : ℝ)
    (x : SpatialCoordinates d) (D : ℕ) : Set (SpatialCoordinates d) :=
  ball x (s * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩ ball c (s / 2)

theorem aux_in_deterministic_regularity_three_zpow_pos (D : ℕ) :
    0 < (3 : ℝ) ^ (-(D : ℤ)) := zpow_pos (by norm_num) _

theorem aux_in_deterministic_regularity_three_zpow_le_one (D : ℕ) :
    (3 : ℝ) ^ (-(D : ℤ)) ≤ 1 := by
  rw [zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem aux_in_deterministic_regularity_three_zpow_succ (D : ℕ) :
    (3 : ℝ) ^ (-((D + 1 : ℕ) : ℤ)) = (3 : ℝ) ^ (-(D : ℤ)) / 3 := by
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ, mul_inv, div_eq_mul_inv]

theorem aux_in_deterministic_regularity_three_zpow_add_le (D n : ℕ) :
    (3 : ℝ) ^ (-((D + n : ℕ) : ℤ)) ≤ (1 / 3 : ℝ) ^ n := by
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  exact inv_anti₀ (pow_pos (by norm_num) _) (pow_le_pow_right₀ (by norm_num) (by omega))

/-- Basic facts on a depth window around a point of the closed cube. -/
theorem aux_in_deterministic_regularity_window_facts {d : ℕ} (c : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) (x : SpatialCoordinates d) (hx : x ∈ closedBall c (s / 2)) (D : ℕ) :
    IsOpen (aux_in_deterministic_regularity_window c s x D) ∧
    aux_in_deterministic_regularity_window c s x D ⊆ closedBall c (s / 2) ∧
    (s * (3 : ℝ) ^ (-(D : ℤ)) / 2) ^ d ≤
      volume.real (aux_in_deterministic_regularity_window c s x D) ∧
    volume.real (aux_in_deterministic_regularity_window c s x D) ≤
      (s * (3 : ℝ) ^ (-(D : ℤ))) ^ d ∧
    0 < volume.real (aux_in_deterministic_regularity_window c s x D) := by
  have hρ : 0 < s * (3 : ℝ) ^ (-(D : ℤ)) :=
    mul_pos hs (aux_in_deterministic_regularity_three_zpow_pos D)
  have hρs : s * (3 : ℝ) ^ (-(D : ℤ)) ≤ s :=
    mul_le_of_le_one_right hs.le (aux_in_deterministic_regularity_three_zpow_le_one D)
  obtain ⟨hlo, hhi⟩ := aux_in_deterministic_regularity_window_volume c x hρ hρs hx
  exact ⟨isOpen_ball.inter isOpen_ball, inter_subset_right.trans ball_subset_closedBall,
    hlo, hhi, lt_of_lt_of_le (by positivity) hlo⟩

/-- The depth windows are nested. -/
theorem aux_in_deterministic_regularity_window_succ_subset {d : ℕ} (c : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) (x : SpatialCoordinates d) (D : ℕ) :
    aux_in_deterministic_regularity_window c s x (D + 1) ⊆
      aux_in_deterministic_regularity_window c s x D := by
  refine inter_subset_inter_left _ (ball_subset_ball ?_)
  rw [aux_in_deterministic_regularity_three_zpow_succ]
  have := aux_in_deterministic_regularity_three_zpow_pos D
  nlinarith

/-- Volume ratio of a depth-`D` window and a contained depth-`D+1` window. -/
theorem aux_in_deterministic_regularity_window_ratio {d : ℕ} (c : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) (x y : SpatialCoordinates d) (hx : x ∈ closedBall c (s / 2))
    (hy : y ∈ closedBall c (s / 2)) (D : ℕ) :
    volume.real (aux_in_deterministic_regularity_window c s x D) /
      volume.real (aux_in_deterministic_regularity_window c s y (D + 1)) ≤ 6 ^ d := by
  obtain ⟨-, -, -, hxhi, -⟩ := aux_in_deterministic_regularity_window_facts c hs x hx D
  obtain ⟨-, -, hylo, -, hypos⟩ :=
    aux_in_deterministic_regularity_window_facts c hs y hy (D + 1)
  rw [div_le_iff₀ hypos]
  rw [aux_in_deterministic_regularity_three_zpow_succ] at hylo
  calc volume.real (aux_in_deterministic_regularity_window c s x D)
      ≤ (s * (3 : ℝ) ^ (-(D : ℤ))) ^ d := hxhi
    _ = 6 ^ d * (s * ((3 : ℝ) ^ (-(D : ℤ)) / 3) / 2) ^ d := by
        rw [← mul_pow]; congr 1; ring
    _ ≤ 6 ^ d * volume.real (aux_in_deterministic_regularity_window c s y (D + 1)) :=
        mul_le_mul_of_nonneg_left hylo (by positivity)

/-- Comparison of the averages of a depth-`D` window and a contained depth-`D+1` window. -/
theorem aux_in_deterministic_regularity_window_avg_le {d : ℕ} (c : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) {U : SpatialCoordinates d → ℝ}
    (hU : ContinuousOn U (closedBall c (s / 2)))
    (x y : SpatialCoordinates d) (hx : x ∈ closedBall c (s / 2))
    (hy : y ∈ closedBall c (s / 2)) (D : ℕ)
    (hsub : aux_in_deterministic_regularity_window c s y (D + 1) ⊆
      aux_in_deterministic_regularity_window c s x D) :
    |aux_in_deterministic_regularity_avg (aux_in_deterministic_regularity_window c s y (D + 1)) U -
        aux_in_deterministic_regularity_avg (aux_in_deterministic_regularity_window c s x D) U| ≤
      Real.sqrt (6 ^ d) *
        normalizedL2On (aux_in_deterministic_regularity_window c s x D)
          (fun z => U z - aux_in_deterministic_regularity_avg
            (aux_in_deterministic_regularity_window c s x D) U) := by
  obtain ⟨-, hxK, -, -, -⟩ := aux_in_deterministic_regularity_window_facts c hs x hx D
  obtain ⟨-, -, -, -, hypos⟩ := aux_in_deterministic_regularity_window_facts c hs y hy (D + 1)
  have h := aux_in_deterministic_regularity_avg_sub_avg_le (isCompact_closedBall c (s / 2)) hU
    hxK hsub hypos
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  exact Real.sqrt_le_sqrt (aux_in_deterministic_regularity_window_ratio c hs x y hx hy D)

/-- Geometric partial sums. -/
theorem aux_in_deterministic_regularity_geom_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, θ ^ i ≤ (1 - θ)⁻¹ := by
  rw [geom_sum_eq hθ1.ne n]
  have h1 : 0 < 1 - θ := by linarith
  rw [show (θ ^ n - 1) / (θ - 1) = (1 - θ ^ n) / (1 - θ) by
    rw [div_eq_div_iff (by linarith) h1.ne']; ring, div_eq_mul_inv]
  have : 0 ≤ θ ^ n := pow_nonneg hθ0 n
  nlinarith [inv_pos.2 h1]

/-- **Pointwise Campanato estimate.**  At every point of the open cube, the value of the
continuous function differs from its depth-`D` window average by at most
`√(6^d) (1-θ)⁻¹ K θ^D`. -/
theorem aux_in_deterministic_regularity_pointwise {d : ℕ} (c : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) {U : SpatialCoordinates d → ℝ}
    (hU : ContinuousOn U (closedBall c (s / 2))) {K θ : ℝ} (hK : 0 ≤ K) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcamp : ∀ (D : ℕ), ∀ x ∈ ball c (s / 2),
      normalizedL2On (aux_in_deterministic_regularity_window c s x D)
          (fun z => U z - aux_in_deterministic_regularity_avg
            (aux_in_deterministic_regularity_window c s x D) U) ≤ K * θ ^ D)
    (x : SpatialCoordinates d) (hx : x ∈ ball c (s / 2)) (D : ℕ) :
    |U x - aux_in_deterministic_regularity_avg (aux_in_deterministic_regularity_window c s x D) U|
      ≤ Real.sqrt (6 ^ d) * (1 - θ)⁻¹ * K * θ ^ D := by
  set a : ℕ → ℝ := fun i =>
    aux_in_deterministic_regularity_avg (aux_in_deterministic_regularity_window c s x i) U with ha
  have hxc : x ∈ closedBall c (s / 2) := ball_subset_closedBall hx
  have h6 : 0 ≤ Real.sqrt (6 ^ d) := Real.sqrt_nonneg _
  have hstep : ∀ i, |a (i + 1) - a i| ≤ Real.sqrt (6 ^ d) * (K * θ ^ i) := fun i =>
    (aux_in_deterministic_regularity_window_avg_le c hs hU x x hxc hxc i
      (aux_in_deterministic_regularity_window_succ_subset c hs x i)).trans
      (mul_le_mul_of_nonneg_left (hcamp i x hx) h6)
  have htele : ∀ n : ℕ, |a (D + n) - a D| ≤
      Real.sqrt (6 ^ d) * K * θ ^ D * ∑ i ∈ Finset.range n, θ ^ i := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 := hstep (D + n)
      calc |a (D + (n + 1)) - a D| ≤ |a (D + n + 1) - a (D + n)| + |a (D + n) - a D| := by
            rw [show D + (n + 1) = D + n + 1 by omega]
            exact abs_sub_le _ _ _
        _ ≤ Real.sqrt (6 ^ d) * (K * θ ^ (D + n)) +
              Real.sqrt (6 ^ d) * K * θ ^ D * ∑ i ∈ Finset.range n, θ ^ i := add_le_add h1 ih
        _ = Real.sqrt (6 ^ d) * K * θ ^ D * (∑ i ∈ Finset.range n, θ ^ i + θ ^ n) := by
            rw [pow_add]; ring
  have htele' : ∀ n : ℕ, |a (D + n) - a D| ≤ Real.sqrt (6 ^ d) * (1 - θ)⁻¹ * K * θ ^ D := by
    intro n
    refine (htele n).trans ?_
    have hg := aux_in_deterministic_regularity_geom_le hθ0 hθ1 n
    have hnn : 0 ≤ Real.sqrt (6 ^ d) * K * θ ^ D := by positivity
    calc Real.sqrt (6 ^ d) * K * θ ^ D * ∑ i ∈ Finset.range n, θ ^ i
        ≤ Real.sqrt (6 ^ d) * K * θ ^ D * (1 - θ)⁻¹ := mul_le_mul_of_nonneg_left hg hnn
      _ = _ := by ring
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hδU⟩ := Metric.continuousWithinAt_iff.1 (hU x hxc) ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 2 * δ / s by positivity)
    (show (1 / 3 : ℝ) < 1 by norm_num)
  have hclose : |a (D + n) - U x| ≤ ε := by
    obtain ⟨hWo, hWK, -, -, hWpos⟩ :=
      aux_in_deterministic_regularity_window_facts c hs x hxc (D + n)
    have hWfin : volume (aux_in_deterministic_regularity_window c s x (D + n)) ≠ ⊤ :=
      ne_top_of_le_ne_top (isCompact_closedBall c (s / 2)).measure_lt_top.ne (measure_mono hWK)
    refine aux_in_deterministic_regularity_avg_sub_const_le hWfin hWpos
      ((hU.integrableOn_compact (isCompact_closedBall c (s / 2))).mono_set hWK) (U x) ε ?_
    intro y hy
    have hyx : dist y x < δ := by
      have h1 : dist y x < s * (3 : ℝ) ^ (-((D + n : ℕ) : ℤ)) / 2 := hy.1
      have h2 := aux_in_deterministic_regularity_three_zpow_add_le D n
      have h3 : s * (1 / 3 : ℝ) ^ n < 2 * δ := by
        rw [lt_div_iff₀ hs] at hn; linarith
      nlinarith
    have := hδU (hWK hy) hyx
    rw [Real.dist_eq] at this
    exact this.le
  calc |U x - a D| ≤ |U x - a (D + n)| + |a (D + n) - a D| := abs_sub_le _ _ _
    _ ≤ ε + Real.sqrt (6 ^ d) * (1 - θ)⁻¹ * K * θ ^ D := by
        rw [abs_sub_comm] at hclose
        exact add_le_add hclose (htele' n)
    _ = _ := by ring

theorem aux_in_deterministic_regularity_three_zpow_eq (m : ℕ) :
    (3 : ℝ) ^ (-(m : ℤ)) = (1 / 3 : ℝ) ^ m := by
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- `(3^(-α))^D = (3^(-D))^α`. -/
theorem aux_in_deterministic_regularity_theta_pow (alpha : ℝ) (D : ℕ) :
    ((3 : ℝ) ^ (-alpha)) ^ D = ((3 : ℝ) ^ (-(D : ℤ))) ^ alpha := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast,
    ← Real.rpow_mul (by norm_num)]
  congr 1
  push_cast
  ring

/-- **Hölder bound at comparable distance**, with the matching depth found by `Nat.find`. -/
theorem aux_in_deterministic_regularity_holder_small {d : ℕ} (c : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) {U : SpatialCoordinates d → ℝ}
    (hU : ContinuousOn U (closedBall c (s / 2))) {K θ : ℝ} (hK : 0 ≤ K) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcamp : ∀ (D : ℕ), ∀ x ∈ ball c (s / 2),
      normalizedL2On (aux_in_deterministic_regularity_window c s x D)
          (fun z => U z - aux_in_deterministic_regularity_avg
            (aux_in_deterministic_regularity_window c s x D) U) ≤ K * θ ^ D)
    (x y : SpatialCoordinates d) (hx : x ∈ ball c (s / 2)) (hy : y ∈ ball c (s / 2))
    (hxy : 0 < dist x y) (h3 : 3 * dist x y ≤ s) :
    ∃ D : ℕ, s * (3 : ℝ) ^ (-(D : ℤ)) < 9 * dist x y ∧
      |U x - U y| ≤
        (2 * (Real.sqrt (6 ^ d) * (1 - θ)⁻¹) + Real.sqrt (6 ^ d)) * K * θ ^ D := by
  classical
  have hex : ∃ D : ℕ, s * (3 : ℝ) ^ (-((D + 1 : ℕ) : ℤ)) < 3 * dist x y := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 3 * dist x y / s by positivity)
      (show (1 / 3 : ℝ) < 1 by norm_num)
    refine ⟨n, ?_⟩
    rw [aux_in_deterministic_regularity_three_zpow_eq, pow_succ]
    rw [lt_div_iff₀ hs] at hn
    have : 0 ≤ (1 / 3 : ℝ) ^ n := by positivity
    nlinarith
  set D := Nat.find hex with hDdef
  have hD : s * (3 : ℝ) ^ (-((D + 1 : ℕ) : ℤ)) < 3 * dist x y := Nat.find_spec hex
  have hDge : 3 * dist x y ≤ s * (3 : ℝ) ^ (-(D : ℤ)) := by
    rcases Nat.eq_zero_or_pos D with h0 | hpos
    · rw [h0]; simpa using h3
    · obtain ⟨m, hm⟩ : ∃ m, D = m + 1 := ⟨D - 1, by omega⟩
      have hmin := Nat.find_min hex (show m < Nat.find hex by omega)
      push_neg at hmin
      rw [hm]; exact hmin
  rw [aux_in_deterministic_regularity_three_zpow_succ] at hD
  have hρ := aux_in_deterministic_regularity_three_zpow_pos D
  have hxc : x ∈ closedBall c (s / 2) := ball_subset_closedBall hx
  have hyc : y ∈ closedBall c (s / 2) := ball_subset_closedBall hy
  have hsub : aux_in_deterministic_regularity_window c s y (D + 1) ⊆
      aux_in_deterministic_regularity_window c s x D := by
    refine fun z hz => ⟨?_, hz.2⟩
    have hz1 : dist z y < s * (3 : ℝ) ^ (-((D + 1 : ℕ) : ℤ)) / 2 := hz.1
    rw [aux_in_deterministic_regularity_three_zpow_succ] at hz1
    show dist z x < s * (3 : ℝ) ^ (-(D : ℤ)) / 2
    have := dist_triangle z y x
    rw [dist_comm y x] at this
    linarith
  refine ⟨D, by linarith, ?_⟩
  have h1 := aux_in_deterministic_regularity_pointwise c hs hU hK hθ0 hθ1 hcamp x hx D
  have h2 := aux_in_deterministic_regularity_pointwise c hs hU hK hθ0 hθ1 hcamp y hy (D + 1)
  have h3' := (aux_in_deterministic_regularity_window_avg_le c hs hU x y hxc hyc D hsub).trans
    (mul_le_mul_of_nonneg_left (hcamp D x hx) (Real.sqrt_nonneg _))
  have hθD : θ ^ (D + 1) ≤ θ ^ D := pow_le_pow_of_le_one hθ0 hθ1.le (Nat.le_succ D)
  have hS : 0 ≤ Real.sqrt (6 ^ d) * (1 - θ)⁻¹ * K :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.2 (by linarith))) hK
  have h2' : |U y - aux_in_deterministic_regularity_avg
      (aux_in_deterministic_regularity_window c s y (D + 1)) U| ≤
      Real.sqrt (6 ^ d) * (1 - θ)⁻¹ * K * θ ^ D :=
    h2.trans (mul_le_mul_of_nonneg_left hθD hS)
  set ax := aux_in_deterministic_regularity_avg (aux_in_deterministic_regularity_window c s x D) U
  set ay := aux_in_deterministic_regularity_avg
    (aux_in_deterministic_regularity_window c s y (D + 1)) U
  calc |U x - U y| ≤ |U x - ax| + |ay - ax| + |U y - ay| := by
        have e1 := abs_sub_le (U x) ax (U y)
        have e2 := abs_sub_le ax ay (U y)
        rw [abs_sub_comm ax ay] at e2
        rw [abs_sub_comm (U y) ay] at *
        linarith
    _ ≤ Real.sqrt (6 ^ d) * (1 - θ)⁻¹ * K * θ ^ D + Real.sqrt (6 ^ d) * (K * θ ^ D) +
        Real.sqrt (6 ^ d) * (1 - θ)⁻¹ * K * θ ^ D := add_le_add (add_le_add h1 h3') h2'
    _ = _ := by ring



def aux_in_deterministic_regularity_holderConst (d : ℕ) (alpha : ℝ) : ℝ :=
  27 * (2 * (Real.sqrt (6 ^ d) * (1 - (3 : ℝ) ^ (-alpha))⁻¹) + Real.sqrt (6 ^ d))

theorem aux_in_deterministic_regularity_theta_lt_one {alpha : ℝ} (halpha : 0 < alpha) :
    (3 : ℝ) ^ (-alpha) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem aux_in_deterministic_regularity_holderConst_nonneg (d : ℕ) {alpha : ℝ}
    (halpha : 0 < alpha) : 0 ≤ aux_in_deterministic_regularity_holderConst d alpha := by
  have h := aux_in_deterministic_regularity_theta_lt_one halpha
  unfold aux_in_deterministic_regularity_holderConst
  have : 0 ≤ (1 - (3 : ℝ) ^ (-alpha))⁻¹ := inv_nonneg.2 (by linarith)
  positivity

/-- A point of the segment. -/
theorem aux_in_deterministic_regularity_dist_segment {d : ℕ} (x y : SpatialCoordinates d)
    (a b : ℝ) :
    dist (x + a • (y - x)) (x + b • (y - x)) = |a - b| * dist x y := by
  rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, ← dist_eq_norm,
    dist_comm]

/-- **Hölder bound on the open cube.** -/
theorem aux_in_deterministic_regularity_holder_ball {d : ℕ} (c : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) {alpha : ℝ} (halpha : alpha ∈ Ioo (0 : ℝ) 1)
    {U : SpatialCoordinates d → ℝ}
    (hU : ContinuousOn U (closedBall c (s / 2))) {K : ℝ} (hK : 0 ≤ K)
    (hcamp : ∀ (D : ℕ), ∀ x ∈ ball c (s / 2),
      normalizedL2On (aux_in_deterministic_regularity_window c s x D)
          (fun z => U z - aux_in_deterministic_regularity_avg
            (aux_in_deterministic_regularity_window c s x D) U) ≤
        K * ((3 : ℝ) ^ (-alpha)) ^ D) :
    ∀ x ∈ ball c (s / 2), ∀ y ∈ ball c (s / 2),
      |U x - U y| ≤ aux_in_deterministic_regularity_holderConst d alpha * K *
        (dist x y / s) ^ alpha := by
  have hθ0 : 0 ≤ (3 : ℝ) ^ (-alpha) := by positivity
  have hθ1 := aux_in_deterministic_regularity_theta_lt_one halpha.1
  set C1 := 2 * (Real.sqrt (6 ^ d) * (1 - (3 : ℝ) ^ (-alpha))⁻¹) + Real.sqrt (6 ^ d) with hC1
  have hC1nn : 0 ≤ C1 := by
    have : 0 ≤ (1 - (3 : ℝ) ^ (-alpha))⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  -- one step at comparable distance
  have hstep : ∀ x' ∈ ball c (s / 2), ∀ y' ∈ ball c (s / 2), 0 < dist x' y' →
      3 * dist x' y' ≤ s → |U x' - U y'| ≤ 9 * C1 * K * (dist x' y' / s) ^ alpha := by
    intro x' hx' y' hy' hpos h3
    obtain ⟨D, hDlt, hbound⟩ := aux_in_deterministic_regularity_holder_small c hs hU hK hθ0 hθ1
      hcamp x' y' hx' hy' hpos h3
    refine hbound.trans ?_
    rw [aux_in_deterministic_regularity_theta_pow]
    have hb : (3 : ℝ) ^ (-(D : ℤ)) ≤ 9 * (dist x' y' / s) := by
      rw [mul_div_assoc', le_div_iff₀ hs]; linarith
    have h1 : ((3 : ℝ) ^ (-(D : ℤ))) ^ alpha ≤ (9 * (dist x' y' / s)) ^ alpha :=
      Real.rpow_le_rpow (by positivity) hb halpha.1.le
    have h2 : (9 * (dist x' y' / s)) ^ alpha ≤ 9 * (dist x' y' / s) ^ alpha := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (9 : ℝ) ^ alpha ≤ (9 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) halpha.2.le
        _ = 9 := Real.rpow_one 9
    calc C1 * K * ((3 : ℝ) ^ (-(D : ℤ))) ^ alpha ≤ C1 * K * (9 * (dist x' y' / s) ^ alpha) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hC1nn hK)
      _ = 9 * C1 * K * (dist x' y' / s) ^ alpha := by ring
  intro x hx y hy
  rcases (dist_nonneg : 0 ≤ dist x y).eq_or_lt with h0 | hpos
  · rw [← h0, dist_le_zero.1 h0.symm.le]
    simp only [sub_self, abs_zero]
    have := aux_in_deterministic_regularity_holderConst_nonneg d halpha.1
    positivity
  have hlt : dist x y < s := by
    have := dist_triangle x c y
    have h1 : dist x c < s / 2 := hx
    have h2 : dist c y < s / 2 := by rw [dist_comm]; exact hy
    linarith
  set p : ℝ → SpatialCoordinates d := fun t => x + t • (y - x) with hp
  have hpmem : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ ball c (s / 2) := fun t ht =>
    (convex_ball c (s / 2)).add_smul_sub_mem hx hy ht
  have hp0 : p 0 = x := by simp [hp]
  have hp1 : p 1 = y := by simp [hp]
  have hpd : ∀ a b : ℝ, |a - b| = 1 / 3 → dist (p a) (p b) = dist x y / 3 := by
    intro a b hab
    rw [hp, aux_in_deterministic_regularity_dist_segment, hab]; ring
  have hseg : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → |a - b| = 1 / 3 →
      |U (p a) - U (p b)| ≤ 9 * C1 * K * (dist x y / s) ^ alpha := by
    intro a b ha hb hab
    have hd := hpd a b hab
    have h := hstep (p a) (hpmem a ha) (p b) (hpmem b hb) (by rw [hd]; positivity)
      (by rw [hd]; linarith)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [hd]
    exact Real.rpow_le_rpow (by positivity) (by
      rw [div_div, div_le_div_iff₀ (by positivity) hs]; nlinarith) halpha.1.le
  have e1 := hseg 0 (1 / 3) ⟨le_rfl, zero_le_one⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
  have e2 := hseg (1 / 3) (2 / 3) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    (by norm_num [abs_of_neg])
  have e3 := hseg (2 / 3) 1 ⟨by norm_num, by norm_num⟩ ⟨zero_le_one, le_rfl⟩
    (by norm_num [abs_of_neg])
  rw [hp0] at e1
  rw [hp1] at e3
  have htri : |U x - U y| ≤ |U x - U (p (1 / 3))| + |U (p (1 / 3)) - U (p (2 / 3))| +
      |U (p (2 / 3)) - U y| := by
    have t1 := abs_sub_le (U x) (U (p (1 / 3))) (U y)
    have t2 := abs_sub_le (U (p (1 / 3))) (U (p (2 / 3))) (U y)
    linarith
  calc |U x - U y| ≤ 3 * (9 * C1 * K * (dist x y / s) ^ alpha) := by linarith
    _ = aux_in_deterministic_regularity_holderConst d alpha * K * (dist x y / s) ^ alpha := by
        rw [aux_in_deterministic_regularity_holderConst, ← hC1]; ring

/-- **Hölder bound on the closed cube**, by continuity from the open cube. -/
theorem aux_in_deterministic_regularity_holder_closedBall {d : ℕ} (c : SpatialCoordinates d)
    {s : ℝ} (hs : 0 < s) {alpha : ℝ} (halpha : alpha ∈ Ioo (0 : ℝ) 1)
    {U : SpatialCoordinates d → ℝ}
    (hU : ContinuousOn U (closedBall c (s / 2))) {K : ℝ} (hK : 0 ≤ K)
    (hcamp : ∀ (D : ℕ), ∀ x ∈ ball c (s / 2),
      normalizedL2On (aux_in_deterministic_regularity_window c s x D)
          (fun z => U z - aux_in_deterministic_regularity_avg
            (aux_in_deterministic_regularity_window c s x D) U) ≤
        K * ((3 : ℝ) ^ (-alpha)) ^ D) :
    ∀ x ∈ closedBall c (s / 2), ∀ y ∈ closedBall c (s / 2),
      |U x - U y| ≤ aux_in_deterministic_regularity_holderConst d alpha * K *
        (dist x y / s) ^ alpha := by
  set Ch := aux_in_deterministic_regularity_holderConst d alpha
  let F : SpatialCoordinates d × SpatialCoordinates d → ℝ := fun p =>
    |U p.1 - U p.2| - Ch * K * (dist p.1 p.2 / s) ^ alpha
  have hF : ContinuousOn F (closedBall c (s / 2) ×ˢ closedBall c (s / 2)) := by
    refine ContinuousOn.sub ?_ ?_
    · exact ((hU.comp continuousOn_fst fun p hp => hp.1).sub
        (hU.comp continuousOn_snd fun p hp => hp.2)).abs
    · refine continuousOn_const.mul ?_
      exact ((continuous_dist.continuousOn).div_const s).rpow_const
        fun _ _ => Or.inr halpha.1.le
  have hclosed := hF.preimage_isClosed_of_isClosed
    (isClosed_closedBall.prod isClosed_closedBall) (isClosed_Iic (a := (0 : ℝ)))
  have hsub : ball c (s / 2) ×ˢ ball c (s / 2) ⊆
      (closedBall c (s / 2) ×ˢ closedBall c (s / 2)) ∩ F ⁻¹' Iic 0 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    refine ⟨⟨ball_subset_closedBall hx, ball_subset_closedBall hy⟩, ?_⟩
    show F (x, y) ≤ 0
    have := aux_in_deterministic_regularity_holder_ball c hs halpha hU hK hcamp x hx y hy
    simp only [F]
    linarith
  have hcl : closure (ball c (s / 2) ×ˢ ball c (s / 2)) =
      closedBall c (s / 2) ×ˢ closedBall c (s / 2) := by
    rw [closure_prod_eq, closure_ball c (by positivity : s / 2 ≠ 0)]
  intro x hx y hy
  have hmem : (x, y) ∈ closure (ball c (s / 2) ×ˢ ball c (s / 2)) := by
    rw [hcl]; exact ⟨hx, hy⟩
  have := (closure_minimal hsub hclosed hmem).2
  simp only [mem_preimage, mem_Iic, F] at this
  linarith



theorem aux_in_deterministic_regularity_campanato_holder {d : ℕ} (alpha : ℝ)
    (halpha : alpha ∈ Ioo (0 : ℝ) 1)
    (qcenter : SpatialCoordinates d) (qside : ℝ) (hqpos : 0 < qside)
    (U : SpatialCoordinates d → ℝ)
    (hU : ContinuousOn U
      (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))))
    (K : ℝ) (hK : 0 ≤ K)
    (hcamp : ∀ (D : ℕ), ∀ x ∈ (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
      let B : Set (SpatialCoordinates d) :=
        Metric.ball x (qside * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
          (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))
      normalizedL2On B (fun y => U y - (volume.real B)⁻¹ * ∫ t in B, U t) ≤
        K * ((3 : ℝ) ^ (-alpha)) ^ D) :
    IsHolderOn alpha
        (closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d))) U ∧
      (∀ x ∈ closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)),
          |U x - U y| ≤ aux_in_deterministic_regularity_holderConst d alpha * K *
            (dist x y / qside) ^ alpha) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
          (fun x => U (qcenter + qside • x) - U qcenter) ≤
        2 * aux_in_deterministic_regularity_holderConst d alpha * K := by
  have hq : (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) =
      ball qcenter (qside / 2) := rfl
  have hcl : closure (centeredCube qcenter qside hqpos : Set (SpatialCoordinates d)) =
      closedBall qcenter (qside / 2) := by
    rw [hq, closure_ball qcenter (by positivity : qside / 2 ≠ 0)]
  rw [hcl] at hU ⊢
  set Ch := aux_in_deterministic_regularity_holderConst d alpha with hCh
  have hChnn : 0 ≤ Ch := aux_in_deterministic_regularity_holderConst_nonneg d halpha.1
  have hHol := aux_in_deterministic_regularity_holder_closedBall qcenter hqpos halpha hU hK
    (fun D x hx => hcamp D x hx)
  refine ⟨?_, hHol, ?_⟩
  · -- bounded difference quotients
    refine ⟨Ch * K / qside ^ alpha, ?_⟩
    rintro v ⟨x, hx, y, hy, hne, rfl⟩
    have hd : 0 < dist x y := dist_pos.2 hne
    have he := aux_in_deterministic_regularity_dist_le_euclid x y
    have he0 : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := hd.trans_le he
    have hea : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha := Real.rpow_pos_of_pos he0 _
    rw [div_le_iff₀ hea]
    calc |U x - U y| ≤ Ch * K * (dist x y / qside) ^ alpha := hHol x hx y hy
      _ ≤ Ch * K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) / qside) ^ alpha :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
            (div_le_div_of_nonneg_right he hqpos.le) halpha.1.le) (mul_nonneg hChnn hK)
      _ = Ch * K / qside ^ alpha * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha := by
          rw [Real.div_rpow he0.le hqpos.le]; ring
  · -- the rescaled `C^α` norm
    have hcube : (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
        closedBall 0 (1 / 2) := rfl
    have hmap : ∀ x ∈ closedBall (0 : SpatialCoordinates d) (1 / 2),
        qcenter + qside • x ∈ closedBall qcenter (qside / 2) := by
      intro x hx
      rw [mem_closedBall, dist_zero_right] at hx
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hqpos]
      nlinarith
    have hc : qcenter ∈ closedBall qcenter (qside / 2) := mem_closedBall_self (by positivity)
    unfold cAlphaNorm holderSeminorm
    rw [hcube]
    have hsup : sSup {v : ℝ | ∃ x ∈ closedBall (0 : SpatialCoordinates d) (1 / 2),
        v = |U (qcenter + qside • x) - U qcenter|} ≤ Ch * K := by
      refine Real.sSup_le ?_ (mul_nonneg hChnn hK)
      rintro v ⟨x, hx, rfl⟩
      refine (hHol _ (hmap x hx) qcenter hc).trans ?_
      have hx' := hx
      rw [mem_closedBall, dist_zero_right] at hx'
      have hdist : dist (qcenter + qside • x) qcenter / qside ≤ 1 := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hqpos,
          div_le_one hqpos]
        nlinarith
      calc Ch * K * (dist (qcenter + qside • x) qcenter / qside) ^ alpha ≤ Ch * K * 1 :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_one (by positivity) hdist halpha.1.le)
              (mul_nonneg hChnn hK)
        _ = Ch * K := mul_one _
    have hsemi : sSup (holderRatioSet alpha (closedBall (0 : SpatialCoordinates d) (1 / 2))
        (fun x => U (qcenter + qside • x) - U qcenter)) ≤ Ch * K := by
      refine Real.sSup_le ?_ (mul_nonneg hChnn hK)
      rintro v ⟨x, hx, y, hy, hne, rfl⟩
      have hd : 0 < dist x y := dist_pos.2 hne
      have he := aux_in_deterministic_regularity_dist_le_euclid x y
      have he0 : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := hd.trans_le he
      have hea : 0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha :=
        Real.rpow_pos_of_pos he0 _
      rw [div_le_iff₀ hea, sub_sub_sub_cancel_right]
      have hscale : dist (qcenter + qside • x) (qcenter + qside • y) / qside = dist x y := by
        rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hqpos,
          mul_div_cancel_left₀ _ hqpos.ne']
      calc |U (qcenter + qside • x) - U (qcenter + qside • y)|
          ≤ Ch * K * (dist (qcenter + qside • x) (qcenter + qside • y) / qside) ^ alpha :=
            hHol _ (hmap x hx) _ (hmap y hy)
        _ = Ch * K * dist x y ^ alpha := by rw [hscale]
        _ ≤ Ch * K * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ^ alpha :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd.le he halpha.1.le)
              (mul_nonneg hChnn hK)
    linarith

end Paper
