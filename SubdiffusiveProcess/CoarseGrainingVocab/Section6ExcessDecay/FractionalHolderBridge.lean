module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Discharge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6DerivedSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows






@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open MeasureTheory
open Homogenization hiding Vec
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The triadic annuli around a point -/

/-- The radius `R · 3^{-i}` of the `i`-th triadic shell. -/
def annulusRadius (R : ℝ) (i : ℕ) : ℝ := R * (3 : ℝ) ^ (-(i : ℝ))

theorem annulusRadius_zero (R : ℝ) : annulusRadius R 0 = R := by
  rw [annulusRadius]
  norm_num

theorem annulusRadius_pos {R : ℝ} (hR : 0 < R) (i : ℕ) : 0 < annulusRadius R i := by
  rw [annulusRadius]
  positivity

theorem annulusRadius_succ (R : ℝ) (i : ℕ) :
    annulusRadius R (i + 1) = annulusRadius R i / 3 := by
  have hexp : (-((i + 1 : ℕ) : ℝ)) = -(i : ℝ) + (-1 : ℝ) := by push_cast; ring
  rw [annulusRadius, annulusRadius, hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    Real.rpow_neg_one]
  ring

theorem annulusRadius_eq_pow (R : ℝ) (i : ℕ) : annulusRadius R i = R * (1 / 3 : ℝ) ^ i := by
  rw [annulusRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast, one_div,
    inv_pow]

/-- **The `i`-th triadic annulus** `{ R·3^{-i-1} ≤ |p-q| < R·3^{-i} }` around `p`. -/
def triadicAnnulus (p : Vec d) (R : ℝ) (i : ℕ) : Set (Vec d) :=
  {q | annulusRadius R (i + 1) ≤ dist p q ∧ dist p q < annulusRadius R i}

theorem measurableSet_triadicAnnulus (p : Vec d) (R : ℝ) (i : ℕ) :
    MeasurableSet (triadicAnnulus p R i) := by
  have hcont : Continuous fun q : Vec d => dist p q := continuous_const.dist continuous_id
  exact (measurableSet_le measurable_const hcont.measurable).inter
    (measurableSet_lt hcont.measurable measurable_const)

theorem triadicAnnulus_subset_ball (p : Vec d) (R : ℝ) (i : ℕ) :
    triadicAnnulus p R i ⊆ Metric.ball p (annulusRadius R i) := by
  intro q hq
  rw [Metric.mem_ball, dist_comm]
  exact hq.2

/-- **The annuli cover the punctured ball.**  The centre is separated out
because the integrand takes the junk value `0^{-β} = 0` there. -/
theorem ball_subset_singleton_union_triadicAnnulus (p : Vec d) {R : ℝ} (hR : 0 < R) :
    Metric.ball p R ⊆ ({p} : Set (Vec d)) ∪ ⋃ i : ℕ, triadicAnnulus p R i := by
  classical
  intro q hq
  rcases eq_or_ne q p with rfl | hqp
  · exact Or.inl rfl
  refine Or.inr ?_
  have hdpos : 0 < dist p q := dist_pos.mpr (Ne.symm hqp)
  have hlt : dist p q < R := by
    rw [dist_comm]
    exact Metric.mem_ball.mp hq
  have hex : ∃ n : ℕ, annulusRadius R (n + 1) ≤ dist p q := by
    obtain ⟨n, hn⟩ :=
      exists_pow_lt_of_lt_one (div_pos hdpos hR) (by norm_num : (1 : ℝ) / 3 < 1)
    refine ⟨n, ?_⟩
    have hnR : R * (1 / 3 : ℝ) ^ n < dist p q := by
      have := (lt_div_iff₀ hR).mp hn
      linarith only [this]
    have hpn : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ n := by positivity
    have hmono : (1 / 3 : ℝ) ^ (n + 1) ≤ (1 / 3 : ℝ) ^ n := by
      rw [pow_succ]
      linarith only [hpn]
    have hscale : R * (1 / 3 : ℝ) ^ (n + 1) ≤ R * (1 / 3 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hmono hR.le
    rw [annulusRadius_eq_pow R (n + 1)]
    linarith only [hnR, hscale]
  have key : ∀ i : ℕ, (∀ k, k < i → ¬ annulusRadius R (k + 1) ≤ dist p q) →
      dist p q < annulusRadius R i := by
    intro i hmin
    match i with
    | 0 => rw [annulusRadius_zero]; exact hlt
    | (k + 1) =>
      have hk := hmin k (by omega)
      push Not at hk
      exact hk
  exact Set.mem_iUnion.mpr
    ⟨Nat.find hex, Nat.find_spec hex, key _ fun k hk => Nat.find_min hex hk⟩

/-! ## 2. The geometric sequence of shell contributions -/

/-- `T_i = (R·3^{-i-1})^{-β} · (2·R·3^{-i})^d`, the `i`-th shell contribution. -/
def annulusTerm (d : ℕ) (R beta : ℝ) (i : ℕ) : ℝ :=
  annulusRadius R (i + 1) ^ (-beta) * (2 * annulusRadius R i) ^ d

/-- The common ratio `3^β / 3^d` of the shell contributions. -/
def annulusRatio (d : ℕ) (beta : ℝ) : ℝ := (3 : ℝ) ^ beta / (3 : ℝ) ^ d

theorem annulusRatio_pos (d : ℕ) (beta : ℝ) : 0 < annulusRatio d beta := by
  rw [annulusRatio]
  positivity

theorem annulusRatio_lt_one {beta : ℝ} (hbd : beta < (d : ℝ)) : annulusRatio d beta < 1 := by
  have hnum : (3 : ℝ) ^ beta < (3 : ℝ) ^ ((d : ℕ) : ℝ) :=
    Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 3) |>.mpr hbd
  rw [Real.rpow_natCast] at hnum
  have hden : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
  rw [annulusRatio, div_lt_one hden]
  exact hnum

theorem annulusTerm_pos {R : ℝ} (hR : 0 < R) (beta : ℝ) (i : ℕ) :
    0 < annulusTerm d R beta i := by
  have h1 : (0 : ℝ) < annulusRadius R (i + 1) ^ (-beta) :=
    Real.rpow_pos_of_pos (annulusRadius_pos hR (i + 1)) _
  have h2 : (0 : ℝ) < (2 * annulusRadius R i) ^ d := by
    have := annulusRadius_pos hR i
    positivity
  rw [annulusTerm]
  exact mul_pos h1 h2

theorem annulusTerm_succ {R : ℝ} (hR : 0 < R) (beta : ℝ) (i : ℕ) :
    annulusTerm d R beta (i + 1) = annulusRatio d beta * annulusTerm d R beta i := by
  have ha : (0 : ℝ) < annulusRadius R (i + 1) := annulusRadius_pos hR (i + 1)
  have hb : (0 : ℝ) < annulusRadius R i := annulusRadius_pos hR i
  have hfirst : annulusRadius R (i + 1 + 1) ^ (-beta) =
      (3 : ℝ) ^ beta * annulusRadius R (i + 1) ^ (-beta) := by
    rw [annulusRadius_succ, Real.div_rpow ha.le (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    field_simp
  have hsecond : (2 * annulusRadius R (i + 1)) ^ d =
      (2 * annulusRadius R i) ^ d / (3 : ℝ) ^ d := by
    rw [annulusRadius_succ, show 2 * (annulusRadius R i / 3) = 2 * annulusRadius R i / 3 by ring,
      div_pow]
  rw [annulusTerm, annulusTerm, annulusRatio, hfirst, hsecond]
  ring

theorem annulusTerm_eq_geometric {R : ℝ} (hR : 0 < R) (beta : ℝ) :
    ∀ i : ℕ, annulusTerm d R beta i = annulusTerm d R beta 0 * annulusRatio d beta ^ i
  | 0 => by rw [pow_zero, mul_one]
  | (i + 1) => by
    rw [annulusTerm_succ hR beta i, annulusTerm_eq_geometric hR beta i, pow_succ]
    ring

/-! ## 3. The shell estimate -/

theorem volume_triadicAnnulus_le {p : Vec d} {R : ℝ} (hR : 0 < R) (i : ℕ) :
    volume (triadicAnnulus p R i) ≤ ENNReal.ofReal ((2 * annulusRadius R i) ^ d) := by
  refine (measure_mono (triadicAnnulus_subset_ball p R i)).trans ?_
  rw [Real.volume_pi_ball p (annulusRadius_pos hR i), Fintype.card_fin]

theorem lintegral_triadicAnnulus_le {p : Vec d} {R beta : ℝ} (hR : 0 < R) (hbeta : 0 ≤ beta)
    (i : ℕ) :
    ∫⁻ q in triadicAnnulus p R i, ENNReal.ofReal (dist p q ^ (-beta)) ∂volume ≤
      ENNReal.ofReal (annulusTerm d R beta i) := by
  have hpt : ∀ q ∈ triadicAnnulus p R i,
      ENNReal.ofReal (dist p q ^ (-beta)) ≤
        ENNReal.ofReal (annulusRadius R (i + 1) ^ (-beta)) := by
    intro q hq
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (annulusRadius_pos hR (i + 1)) hq.1 (neg_nonpos.mpr hbeta))
  calc ∫⁻ q in triadicAnnulus p R i, ENNReal.ofReal (dist p q ^ (-beta)) ∂volume
      ≤ ∫⁻ _ in triadicAnnulus p R i,
          ENNReal.ofReal (annulusRadius R (i + 1) ^ (-beta)) ∂volume :=
        setLIntegral_mono' (measurableSet_triadicAnnulus p R i) hpt
    _ = ENNReal.ofReal (annulusRadius R (i + 1) ^ (-beta)) * volume (triadicAnnulus p R i) :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (annulusRadius R (i + 1) ^ (-beta)) *
          ENNReal.ofReal ((2 * annulusRadius R i) ^ d) :=
        mul_le_mul' le_rfl (volume_triadicAnnulus_le hR i)
    _ = ENNReal.ofReal (annulusTerm d R beta i) := by
        rw [annulusTerm, ← ENNReal.ofReal_mul
          (Real.rpow_nonneg (annulusRadius_pos hR (i + 1)).le _)]

/-! ## 4. The ball estimate -/

/-- `C_rad(d,β) = 2^d · 3^β · (1 - 3^{β-d})^{-1}`, in the closed form the shell
sum produces: `(R/3)^{-β}(2R)^d` divided by `1 - 3^β/3^d`, at `R = 1`. -/
def radialKernelConst (d : ℕ) (beta : ℝ) : ℝ :=
  ((1 : ℝ) / 3) ^ (-beta) * (2 : ℝ) ^ d / (1 - annulusRatio d beta)

theorem one_sub_annulusRatio_pos {beta : ℝ} (hbd : beta < (d : ℝ)) :
    0 < 1 - annulusRatio d beta := by
  have := annulusRatio_lt_one hbd
  linarith only [this]

theorem radialKernelConst_pos {beta : ℝ} (hbd : beta < (d : ℝ)) :
    0 < radialKernelConst d beta := by
  have hden := one_sub_annulusRatio_pos hbd
  have hnum : (0 : ℝ) < ((1 : ℝ) / 3) ^ (-beta) * (2 : ℝ) ^ d := by
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < (1 : ℝ) / 3) (-beta)
    positivity
  rw [radialKernelConst]
  exact div_pos hnum hden

/-- `T_0 = (R/3)^{-β} (2R)^d`, in the factored form used by the sum. -/
theorem annulusTerm_zero {R : ℝ} (hR : 0 < R) (beta : ℝ) :
    annulusTerm d R beta 0 = R ^ (-beta) * ((1 : ℝ) / 3) ^ (-beta) * ((2 : ℝ) ^ d * R ^ d) := by
  have hrad : annulusRadius R (0 + 1) = R * ((1 : ℝ) / 3) := by
    rw [annulusRadius_succ, annulusRadius_zero]
    ring
  rw [annulusTerm, hrad, annulusRadius_zero,
    Real.mul_rpow hR.le (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3), mul_pow]

/-- **The radial kernel integral on a ball.**

For `0 < β < d`, in the ambient supremum metric,
`∫_{B(p,R)} |p-q|^{-β} dq ≤ C_rad(d,β) · R^{d} · R^{-β}`. -/
theorem lintegral_ball_dist_rpow_neg_le {p : Vec d} {R beta : ℝ} (hR : 0 < R)
    (hbeta : 0 < beta) (hbd : beta < (d : ℝ)) :
    ∫⁻ q in Metric.ball p R, ENNReal.ofReal (dist p q ^ (-beta)) ∂volume ≤
      ENNReal.ofReal (radialKernelConst d beta * (R ^ d * R ^ (-beta))) := by
  have hcentre : ∫⁻ q in ({p} : Set (Vec d)),
      ENNReal.ofReal (dist p q ^ (-beta)) ∂volume = 0 := by
    have hpt : ∀ q ∈ ({p} : Set (Vec d)),
        ENNReal.ofReal (dist p q ^ (-beta)) ≤ (0 : ℝ≥0∞) := by
      intro q hq
      rw [show q = p from hq, dist_self, Real.zero_rpow (by linarith only [hbeta] : -beta ≠ 0),
        ENNReal.ofReal_zero]
    refine le_antisymm ?_ zero_le
    calc ∫⁻ q in ({p} : Set (Vec d)), ENNReal.ofReal (dist p q ^ (-beta)) ∂volume
        ≤ ∫⁻ _ in ({p} : Set (Vec d)), (0 : ℝ≥0∞) ∂volume :=
          setLIntegral_mono' (measurableSet_singleton p) hpt
      _ = 0 := lintegral_zero
  have hgeom : ∑' i : ℕ, ENNReal.ofReal (annulusTerm d R beta i) =
      ENNReal.ofReal (annulusTerm d R beta 0) *
        (1 - ENNReal.ofReal (annulusRatio d beta))⁻¹ := by
    have hterm : ∀ i : ℕ, ENNReal.ofReal (annulusTerm d R beta i) =
        ENNReal.ofReal (annulusTerm d R beta 0) * ENNReal.ofReal (annulusRatio d beta) ^ i := by
      intro i
      rw [annulusTerm_eq_geometric hR beta i,
        ENNReal.ofReal_mul (annulusTerm_pos hR beta 0).le,
        ENNReal.ofReal_pow (annulusRatio_pos d beta).le]
    rw [tsum_congr hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hsum : ∫⁻ q in Metric.ball p R, ENNReal.ofReal (dist p q ^ (-beta)) ∂volume ≤
      ∑' i : ℕ, ENNReal.ofReal (annulusTerm d R beta i) := by
    calc ∫⁻ q in Metric.ball p R, ENNReal.ofReal (dist p q ^ (-beta)) ∂volume
        ≤ ∫⁻ q in ({p} : Set (Vec d)) ∪ ⋃ i : ℕ, triadicAnnulus p R i,
            ENNReal.ofReal (dist p q ^ (-beta)) ∂volume :=
          lintegral_mono_set (ball_subset_singleton_union_triadicAnnulus p hR)
      _ ≤ (∫⁻ q in ({p} : Set (Vec d)), ENNReal.ofReal (dist p q ^ (-beta)) ∂volume) +
            ∫⁻ q in ⋃ i : ℕ, triadicAnnulus p R i,
              ENNReal.ofReal (dist p q ^ (-beta)) ∂volume :=
          lintegral_union_le _ _ _
      _ = ∫⁻ q in ⋃ i : ℕ, triadicAnnulus p R i,
            ENNReal.ofReal (dist p q ^ (-beta)) ∂volume := by rw [hcentre, zero_add]
      _ ≤ ∑' i : ℕ, ∫⁻ q in triadicAnnulus p R i,
            ENNReal.ofReal (dist p q ^ (-beta)) ∂volume :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' i : ℕ, ENNReal.ofReal (annulusTerm d R beta i) :=
          ENNReal.tsum_le_tsum fun i => lintegral_triadicAnnulus_le hR hbeta.le i
  refine hsum.trans ?_
  rw [hgeom]
  have hone : (1 : ℝ≥0∞) - ENNReal.ofReal (annulusRatio d beta) =
      ENNReal.ofReal (1 - annulusRatio d beta) := by
    rw [ENNReal.ofReal_sub _ (annulusRatio_pos d beta).le, ENNReal.ofReal_one]
  rw [hone, ← ENNReal.ofReal_inv_of_pos (one_sub_annulusRatio_pos hbd),
    ← ENNReal.ofReal_mul (annulusTerm_pos hR beta 0).le]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [annulusTerm_zero hR beta, radialKernelConst]
  field_simp

/-- Points are null in `Vec d` once `d ≥ 1`. -/
theorem volume_singleton_eq_zero (hd : 1 ≤ d) (p : Vec d) :
    volume ({p} : Set (Vec d)) = 0 := by
  rw [← Metric.closedBall_zero, Real.volume_pi_closedBall p le_rfl, Fintype.card_fin, mul_zero,
    zero_pow (by omega : d ≠ 0), ENNReal.ofReal_zero]

/-- **The radial kernel integral, with the `ℝ≥0∞`-native kernel `‖p-q‖ₑ^{-β}`.**

The two kernels differ only on the diagonal — where the real junk value is
`0^{-β} = 0` and the `ℝ≥0∞` value is `⊤` — which is null because `0 < β < d`
forces `1 ≤ d`. -/
theorem lintegral_enorm_sub_rpow_neg_le_of_subset_ball {p : Vec d} {R beta : ℝ}
    {A : Set (Vec d)} (hA : A ⊆ Metric.ball p R) (hR : 0 < R) (hbeta : 0 < beta)
    (hbd : beta < (d : ℝ)) :
    ∫⁻ q in A, ‖p - q‖ₑ ^ (-beta) ∂volume ≤
      ENNReal.ofReal (radialKernelConst d beta * (R ^ d * R ^ (-beta))) := by
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · exfalso
      rw [h0] at hbd
      norm_num at hbd
      linarith only [hbeta, hbd]
    · exact hpos
  have hcentre : ∫⁻ q in ({p} : Set (Vec d)), ‖p - q‖ₑ ^ (-beta) ∂volume = 0 :=
    setLIntegral_measure_zero _ _ (volume_singleton_eq_zero hd p)
  have hmeasdiff : MeasurableSet (Metric.ball p R \ ({p} : Set (Vec d))) :=
    (Metric.isOpen_ball.measurableSet).diff (measurableSet_singleton p)
  have hpt : ∀ q ∈ Metric.ball p R \ ({p} : Set (Vec d)),
      ‖p - q‖ₑ ^ (-beta) ≤ ENNReal.ofReal (dist p q ^ (-beta)) := by
    intro q hq
    have hne : q ≠ p := hq.2
    have hpos : 0 < dist p q := dist_pos.mpr (Ne.symm hne)
    have henorm : ‖p - q‖ₑ = ENNReal.ofReal (dist p q) := by
      rw [dist_eq_norm, ← ofReal_norm]
    rw [henorm, ENNReal.ofReal_rpow_of_pos hpos]
  have hcover : Metric.ball p R ⊆
      (Metric.ball p R \ ({p} : Set (Vec d))) ∪ ({p} : Set (Vec d)) := by
    intro q hq
    by_cases h : q = p
    · exact Or.inr h
    · exact Or.inl ⟨hq, h⟩
  calc ∫⁻ q in A, ‖p - q‖ₑ ^ (-beta) ∂volume
      ≤ ∫⁻ q in Metric.ball p R, ‖p - q‖ₑ ^ (-beta) ∂volume := lintegral_mono_set hA
    _ ≤ ∫⁻ q in (Metric.ball p R \ ({p} : Set (Vec d))) ∪ ({p} : Set (Vec d)),
          ‖p - q‖ₑ ^ (-beta) ∂volume := lintegral_mono_set hcover
    _ ≤ (∫⁻ q in Metric.ball p R \ ({p} : Set (Vec d)), ‖p - q‖ₑ ^ (-beta) ∂volume) +
          ∫⁻ q in ({p} : Set (Vec d)), ‖p - q‖ₑ ^ (-beta) ∂volume := lintegral_union_le _ _ _
    _ = ∫⁻ q in Metric.ball p R \ ({p} : Set (Vec d)), ‖p - q‖ₑ ^ (-beta) ∂volume := by
        rw [hcentre, add_zero]
    _ ≤ ∫⁻ q in Metric.ball p R \ ({p} : Set (Vec d)),
          ENNReal.ofReal (dist p q ^ (-beta)) ∂volume := setLIntegral_mono' hmeasdiff hpt
    _ ≤ ∫⁻ q in Metric.ball p R, ENNReal.ofReal (dist p q ^ (-beta)) ∂volume :=
        lintegral_mono_set Set.sdiff_subset
    _ ≤ ENNReal.ofReal (radialKernelConst d beta * (R ^ d * R ^ (-beta))) :=
        lintegral_ball_dist_rpow_neg_le hR hbeta hbd

/-! ## 5. The Gagliardo exponent of a `C^{0,1/2}` field -/

/-- `β(d,s) = d + 2s - 1`: the singularity exponent of the
`fractionalKernel` of a `C^{0,1/2}` field at fractional index `s`. -/
def gagliardoBeta (d : ℕ) (s : ℝ) : ℝ := (d : ℝ) + 2 * s - 1

theorem gagliardoBeta_pos {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) : 0 < gagliardoBeta d s := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rw [gagliardoBeta]
  linarith only [hd', hs0]

theorem gagliardoBeta_lt {s : ℝ} (hs : s < 1 / 2) : gagliardoBeta d s < (d : ℝ) := by
  rw [gagliardoBeta]
  linarith only [hs]

/-! ## 6. The pointwise majorant on the fractional kernel -/

/-- A `C^{0,1/2}` bound turns the `fractionalKernel` into the radial
kernel `K · |p-q|^{-β/2}` — here already squared and transferred to the ambient
supremum norm, which is the metric the radial estimate of §4 is written in. -/
theorem fractionalKernel_sq_le {W : Set (Vec d)} {f : Vec d → Vec d} {K s : ℝ}
    (hbeta : 0 ≤ gagliardoBeta d s) (hf : HolderSeminormBoundOn W (1 / 2) K f)
    {p q : Vec d} (hp : p ∈ W) (hq : q ∈ W) (hpq : p ≠ q) :
    fractionalKernel s f (p, q) ^ 2 ≤ K ^ 2 * ‖p - q‖ ^ (-gagliardoBeta d s) := by
  have hnormpos : 0 < ‖p - q‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hpq
  have hle : ‖p - q‖ ≤ euclideanNorm (p - q) := norm_le_euclideanNorm _
  have hepos : 0 < euclideanNorm (p - q) := lt_of_lt_of_le hnormpos hle
  have hden : 0 < euclideanNorm (p - q) ^ (s + (d : ℝ) / 2) := Real.rpow_pos_of_pos hepos _
  have hker : fractionalKernel s f (p, q) =
      euclideanNorm (f p - f q) / euclideanNorm (p - q) ^ (s + (d : ℝ) / 2) := rfl
  have hnonneg : 0 ≤ fractionalKernel s f (p, q) := by
    rw [hker]
    exact div_nonneg (euclideanNorm_nonneg _) hden.le
  have hsplit : euclideanNorm (p - q) ^ (-gagliardoBeta d s / 2) *
      euclideanNorm (p - q) ^ (s + (d : ℝ) / 2) = euclideanNorm (p - q) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hepos]
    congr 1
    rw [gagliardoBeta]
    ring
  have hup : fractionalKernel s f (p, q) ≤ K * euclideanNorm (p - q) ^ (-gagliardoBeta d s / 2) := by
    rw [hker, div_le_iff₀ hden]
    calc euclideanNorm (f p - f q)
        ≤ K * euclideanNorm (p - q) ^ (1 / 2 : ℝ) := hf p hp q hq
      _ = K * euclideanNorm (p - q) ^ (-gagliardoBeta d s / 2) *
            euclideanNorm (p - q) ^ (s + (d : ℝ) / 2) := by rw [mul_assoc, hsplit]
  have hsq := mul_self_le_mul_self hnonneg hup
  have hcollapse : (K * euclideanNorm (p - q) ^ (-gagliardoBeta d s / 2)) *
      (K * euclideanNorm (p - q) ^ (-gagliardoBeta d s / 2)) =
      K ^ 2 * euclideanNorm (p - q) ^ (-gagliardoBeta d s) := by
    rw [show K * euclideanNorm (p - q) ^ (-gagliardoBeta d s / 2) *
          (K * euclideanNorm (p - q) ^ (-gagliardoBeta d s / 2)) =
        K ^ 2 * (euclideanNorm (p - q) ^ (-gagliardoBeta d s / 2) *
          euclideanNorm (p - q) ^ (-gagliardoBeta d s / 2)) by ring,
      ← Real.rpow_add hepos]
    congr 2
    ring
  have hradial : euclideanNorm (p - q) ^ (-gagliardoBeta d s) ≤
      ‖p - q‖ ^ (-gagliardoBeta d s) :=
    Real.rpow_le_rpow_of_nonpos hnormpos hle (neg_nonpos.mpr hbeta)
  have hKsq : (0 : ℝ) ≤ K ^ 2 := sq_nonneg K
  calc fractionalKernel s f (p, q) ^ 2
      = fractionalKernel s f (p, q) * fractionalKernel s f (p, q) := by ring
    _ ≤ K ^ 2 * euclideanNorm (p - q) ^ (-gagliardoBeta d s) := by
        rw [← hcollapse]; exact hsq
    _ ≤ K ^ 2 * ‖p - q‖ ^ (-gagliardoBeta d s) := by
        exact mul_le_mul_of_nonneg_left hradial hKsq

/-- The `ℝ≥0∞` form of `fractionalKernel_sq_le`, valid on the whole of `W × W`
(on the diagonal the kernel is the junk value `0`). -/
theorem enorm_fractionalKernel_sq_le {W : Set (Vec d)} {f : Vec d → Vec d} {K s : ℝ}
    (hbeta : 0 ≤ gagliardoBeta d s) (hf : HolderSeminormBoundOn W (1 / 2) K f)
    {z : Vec d × Vec d} (h1 : z.1 ∈ W) (h2 : z.2 ∈ W) :
    ‖fractionalKernel s f z‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (K ^ 2) * ‖z.1 - z.2‖ₑ ^ (-gagliardoBeta d s) := by
  rcases eq_or_ne z.1 z.2 with heq | hne
  · have hzero : fractionalKernel s f z = 0 := by
      have hnum : euclideanNorm (f z.1 - f z.2) = 0 := by
        rw [heq, sub_self, euclideanNorm_zero]
      show euclideanNorm (f z.1 - f z.2) /
        euclideanNorm (z.1 - z.2) ^ (s + (d : ℝ) / 2) = 0
      rw [hnum, zero_div]
    rw [hzero, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
    exact zero_le
  have hnormpos : 0 < ‖z.1 - z.2‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hne
  have hnonneg : 0 ≤ fractionalKernel s f z := by
    show 0 ≤ euclideanNorm (f z.1 - f z.2) /
      euclideanNorm (z.1 - z.2) ^ (s + (d : ℝ) / 2)
    exact div_nonneg (euclideanNorm_nonneg _) (Real.rpow_nonneg (euclideanNorm_nonneg _) _)
  have hE : ‖fractionalKernel s f z‖ₑ = ENNReal.ofReal (fractionalKernel s f z) := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hreal : fractionalKernel s f z ^ 2 ≤ K ^ 2 * ‖z.1 - z.2‖ ^ (-gagliardoBeta d s) := by
    have := fractionalKernel_sq_le (d := d) (W := W) (f := f) (K := K) (s := s) hbeta hf h1 h2 hne
    simpa using this
  have hrpow : (ENNReal.ofReal (fractionalKernel s f z)) ^ (2 : ℝ) =
      ENNReal.ofReal (fractionalKernel s f z ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hnonneg (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast (fractionalKernel s f z) 2]
    norm_num
  have hsplit : ENNReal.ofReal (K ^ 2 * ‖z.1 - z.2‖ ^ (-gagliardoBeta d s)) =
      ENNReal.ofReal (K ^ 2) * ‖z.1 - z.2‖ₑ ^ (-gagliardoBeta d s) := by
    rw [ENNReal.ofReal_mul (sq_nonneg K), ← ofReal_norm,
      ENNReal.ofReal_rpow_of_pos hnormpos]
  rw [hE, hrpow, ← hsplit]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ## 7. The window integral -/

/-- The Gagliardo double integral of a `C^{0,1/2}` field on a window of
supremum diameter at most `R`. -/
theorem lintegral_fractionalKernel_sq_le {W : Set (Vec d)} {f : Vec d → Vec d} {K R s : ℝ}
    (hWmeas : MeasurableSet W) (hball : ∀ p ∈ W, W ⊆ Metric.ball p R) (hR : 0 < R)
    (hbeta : 0 < gagliardoBeta d s) (hbd : gagliardoBeta d s < (d : ℝ))
    (hf : HolderSeminormBoundOn W (1 / 2) K f) :
    ∫⁻ z in W ×ˢ W, ‖fractionalKernel s f z‖ₑ ^ (2 : ℝ) ∂(volume.prod volume) ≤
      ENNReal.ofReal (K ^ 2) *
        (ENNReal.ofReal (radialKernelConst d (gagliardoBeta d s) *
            (R ^ d * R ^ (-gagliardoBeta d s))) * volume W) := by
  have hkermeas : Measurable fun z : Vec d × Vec d =>
      ‖z.1 - z.2‖ₑ ^ (-gagliardoBeta d s) :=
    ENNReal.continuous_rpow_const.measurable.comp (measurable_fst.sub measurable_snd).enorm
  set M : ℝ≥0∞ := ENNReal.ofReal (radialKernelConst d (gagliardoBeta d s) *
    (R ^ d * R ^ (-gagliardoBeta d s))) with hMdef
  calc ∫⁻ z in W ×ˢ W, ‖fractionalKernel s f z‖ₑ ^ (2 : ℝ) ∂(volume.prod volume)
      ≤ ∫⁻ z in W ×ˢ W, ENNReal.ofReal (K ^ 2) *
          ‖z.1 - z.2‖ₑ ^ (-gagliardoBeta d s) ∂(volume.prod volume) :=
        setLIntegral_mono' (hWmeas.prod hWmeas)
          fun z hz => enorm_fractionalKernel_sq_le hbeta.le hf hz.1 hz.2
    _ = ENNReal.ofReal (K ^ 2) *
          ∫⁻ z in W ×ˢ W, ‖z.1 - z.2‖ₑ ^ (-gagliardoBeta d s) ∂(volume.prod volume) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (K ^ 2) *
          ∫⁻ p in W, ∫⁻ q in W, ‖p - q‖ₑ ^ (-gagliardoBeta d s) ∂volume ∂volume := by
        rw [← Measure.prod_restrict, MeasureTheory.lintegral_prod _ hkermeas.aemeasurable]
    _ ≤ ENNReal.ofReal (K ^ 2) * ∫⁻ _ in W, M ∂volume :=
        mul_le_mul' le_rfl (setLIntegral_mono' hWmeas fun p hp =>
          lintegral_enorm_sub_rpow_neg_le_of_subset_ball (hball p hp) hR hbeta hbd)
    _ = ENNReal.ofReal (K ^ 2) * (M * volume W) := by rw [setLIntegral_const]

/-! ## 8. The embedding, with the honest radial constant -/

/-- **`C^{0,1/2}(W) ↪ H̲^s(W)`, with the explicit radial constant.**

If `f` obeys the Hölder-`1/2` bound `K` on `W`, if `W` has supremum diameter at
most `R` (in the form `W ⊆ B(p,R)` for every `p ∈ W`), and if `0 < β(d,s) < d`,
then the normalized fractional seminorm obeys

```text
  [f]_{H̲^s(W)} ≤ √s · K · √( C_rad(d,β) · R^d · R^{-β} ) .
```

The `√s` comes from the `(s/|W|)^{1/2}` prefactor of the
`fractionalSeminormOn`; the window volume cancels exactly. -/
theorem fractionalSeminormOn_le_of_holderSeminormBoundOn {W : Set (Vec d)} {f : Vec d → Vec d}
    {K R s : ℝ} (hWmeas : MeasurableSet W) (hW0 : volume W ≠ 0) (hWtop : volume W ≠ ⊤)
    (hball : ∀ p ∈ W, W ⊆ Metric.ball p R) (hR : 0 < R) (hs0 : 0 ≤ s)
    (hbeta : 0 < gagliardoBeta d s) (hbd : gagliardoBeta d s < (d : ℝ)) (hK : 0 ≤ K)
    (hf : HolderSeminormBoundOn W (1 / 2) K f) :
    fractionalSeminormOn W s f ≤
      ENNReal.ofReal (Real.sqrt s * K *
        Real.sqrt (radialKernelConst d (gagliardoBeta d s) *
          (R ^ d * R ^ (-gagliardoBeta d s)))) := by
  set cM : ℝ := radialKernelConst d (gagliardoBeta d s) *
    (R ^ d * R ^ (-gagliardoBeta d s)) with hcMdef
  have hcM : 0 ≤ cM := by
    have h1 := (radialKernelConst_pos hbd).le
    have h2 : (0 : ℝ) < R ^ d := by positivity
    have h3 : (0 : ℝ) < R ^ (-gagliardoBeta d s) := Real.rpow_pos_of_pos hR _
    rw [hcMdef]
    positivity
  set v : ℝ≥0∞ := volume W with hvdef
  set I : ℝ≥0∞ := ∫⁻ z, ‖fractionalKernel s f z‖ₑ ^ (2 : ℝ)
    ∂((volume.restrict W).prod (volume.restrict W)) with hIdef
  have hI : I ≤ ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal cM * v) := by
    rw [hIdef, Measure.prod_restrict]
    exact lintegral_fractionalKernel_sq_le hWmeas hball hR hbeta hbd hf
  have hfc : ContinuousOn (fun x => HilbertVec.ofVec (f x)) W := by
      rw [Metric.continuousOn_iff]
      intro b hb ε hε
      refine ⟨(ε / (K + 1)) ^ 2 / ((d : ℝ) + 1), by positivity, ?_⟩
      intro a ha hab
      have hKb : euclideanNorm (f a - f b) ≤ K * euclideanNorm (a - b) ^ (1 / 2 : ℝ) :=
        hf a ha b hb
      have hcmp : euclideanNorm (a - b) ≤ (d : ℝ) * dist a b := by
        have h := HilbertVec.norm_ofVec_le_mul_norm (a - b)
        rw [euclideanNorm_eq_norm_ofVec]
        simpa [dist_eq_norm] using h
      have hdab : (d : ℝ) * dist a b ≤ (ε / (K + 1)) ^ 2 := by
        have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        have hab' : dist a b ≤ (ε / (K + 1)) ^ 2 / ((d : ℝ) + 1) := le_of_lt hab
        have h1 : (d : ℝ) * dist a b ≤ (d : ℝ) * ((ε / (K + 1)) ^ 2 / ((d : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hab' hd0
        have h2 : (d : ℝ) * ((ε / (K + 1)) ^ 2 / ((d : ℝ) + 1)) ≤ (ε / (K + 1)) ^ 2 := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) + 1)]
          nlinarith [sq_nonneg (ε / (K + 1)), hd0]
        linarith only [h1, h2]
      have hpow : euclideanNorm (a - b) ^ (1 / 2 : ℝ) ≤ ε / (K + 1) := by
        have hchain : euclideanNorm (a - b) ≤ (ε / (K + 1)) ^ 2 :=
          le_trans hcmp hdab
        have hmono : euclideanNorm (a - b) ^ (1 / 2 : ℝ)
            ≤ ((ε / (K + 1)) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (euclideanNorm_nonneg _) hchain (by norm_num)
        have hsq : ((ε / (K + 1)) ^ 2 : ℝ) ^ (1 / 2 : ℝ) = ε / (K + 1) := by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
        rwa [hsq] at hmono
      have hfinal : euclideanNorm (f a - f b) < ε := by
        have h1 : K * euclideanNorm (a - b) ^ (1 / 2 : ℝ) ≤ K * (ε / (K + 1)) :=
          mul_le_mul_of_nonneg_left hpow hK
        have h2 : K * (ε / (K + 1)) < ε := by
          rw [mul_div_assoc'] at *
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K + 1)]
          nlinarith only [hε, hK]
        linarith only [hKb, h1, h2]
      have hsub : HilbertVec.ofVec (f a - f b)
          = HilbertVec.ofVec (f a) - HilbertVec.ofVec (f b) := by
        simp
      have hdist : dist (HilbertVec.ofVec (f a)) (HilbertVec.ofVec (f b))
          = euclideanNorm (f a - f b) := by
        rw [dist_eq_norm, euclideanNorm_eq_norm_ofVec, hsub]
      rw [hdist]
      exact hfinal
  have hfm := hfc.aestronglyMeasurable (μ := volume) hWmeas
  have hnum := ((hfm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).sub
    (hfm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)).norm
  have hden : Measurable (fun z : Vec d × Vec d =>
      euclideanNorm (z.1 - z.2) ^ (s + (d : ℝ) / 2)) := by
    simpa only [euclideanNorm_eq_norm_ofVec, HilbertVec.ofVecL_apply, Function.comp_def] using!
      (((HilbertVec.ofVecL d).continuous.comp
        (continuous_fst.sub continuous_snd)).norm.measurable.pow measurable_const)
  have hkernel : AEStronglyMeasurable (fractionalKernel s f)
      ((volume.restrict W).prod (volume.restrict W)) := by
    unfold fractionalKernel
    simpa only [euclideanNorm_eq_norm_ofVec, HilbertVec.ofVec,
      WithLp.toLp_sub, Pi.sub_def, Pi.div_def, Function.comp_def] using!
      (hnum.aemeasurable.div hden.aemeasurable).aestronglyMeasurable
  have heL : eLpNorm (fractionalKernel s f) 2
      ((volume.restrict W).prod (volume.restrict W)) = I ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hkernel, hIdef]
    norm_num
  have hcancel : (ENNReal.ofReal s / v) * (ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal cM * v)) =
      ENNReal.ofReal s * ENNReal.ofReal (K ^ 2) * ENNReal.ofReal cM := by
    calc (ENNReal.ofReal s / v) * (ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal cM * v))
        = (ENNReal.ofReal s * ENNReal.ofReal (K ^ 2) * ENNReal.ofReal cM) * (v⁻¹ * v) := by
          rw [ENNReal.div_eq_inv_mul]; ring
      _ = ENNReal.ofReal s * ENNReal.ofReal (K ^ 2) * ENNReal.ofReal cM := by
          rw [ENNReal.inv_mul_cancel hW0 hWtop, mul_one]
  have hreal : ENNReal.ofReal s * ENNReal.ofReal (K ^ 2) * ENNReal.ofReal cM =
      ENNReal.ofReal (s * K ^ 2 * cM) := by
    rw [← ENNReal.ofReal_mul hs0, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s * K ^ 2)]
  have hsqrt : Real.sqrt (s * K ^ 2 * cM) = Real.sqrt s * K * Real.sqrt cM := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ s * K ^ 2), Real.sqrt_mul hs0,
      Real.sqrt_sq hK]
  rw [fractionalSeminormOn, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hkernel, heL]
  calc (ENNReal.ofReal s / v) ^ (1 / 2 : ℝ) * I ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal s / v) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal cM * v)) ^ (1 / 2 : ℝ) :=
        mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hI (by norm_num))
    _ = ((ENNReal.ofReal s / v) *
          (ENNReal.ofReal (K ^ 2) * (ENNReal.ofReal cM * v))) ^ (1 / 2 : ℝ) :=
        (ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)).symm
    _ = ENNReal.ofReal (s * K ^ 2 * cM) ^ (1 / 2 : ℝ) := by rw [hcancel, hreal]
    _ = ENNReal.ofReal (Real.sqrt s * K * Real.sqrt cM) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← Real.sqrt_eq_rpow, hsqrt]

/-! ## 9. The `s`-uniform constant on the paper's range `s ∈ (0,1/4]` -/

/-- `C_H(d) = √((5/2)·6^d)`: the `d`-only Hölder-to-fractional constant, valid
uniformly over the paper's fractional range `s ∈ (0,1/4]`.  The section 6
statements quantify their constant **before** `s`, so an `s`-dependent constant
would not be consumable. -/
def fractionalHolderConst (d : ℕ) : ℝ := Real.sqrt ((5 / 2) * 6 ^ d)

theorem fractionalHolderConst_pos (d : ℕ) : 0 < fractionalHolderConst d := by
  rw [fractionalHolderConst]
  have : (0 : ℝ) < (5 / 2) * 6 ^ d := by positivity
  exact Real.sqrt_pos.mpr this

theorem fractionalHolderConst_nonneg (d : ℕ) : 0 ≤ fractionalHolderConst d :=
  (fractionalHolderConst_pos d).le

/-- `3^{-1/2} ≤ 3/5`, the numerical fact behind the `s`-uniform constant. -/
private theorem three_rpow_neg_half_le : (3 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 5 := by
  set t : ℝ := (3 : ℝ) ^ (-(1 / 2) : ℝ) with htdef
  have htpos : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hsq : t ^ 2 = 1 / 3 := by
    rw [htdef, ← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2) : ℝ)) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  by_contra hcon
  push Not at hcon
  have hlt : ((3 : ℝ) / 5) ^ 2 < t ^ 2 := by
    have := mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 3 / 5) hcon
    simpa [pow_two] using this
  rw [hsq] at hlt
  norm_num at hlt

/-- On `0 < s ≤ 1/4` the radial constant is bounded by the `d`-only value
`(5/2)·6^d`: the singularity exponent obeys `β ≤ d - 1/2`, so the geometric
ratio `3^{β-d}` is at most `3^{-1/2} ≤ 3/5`. -/
theorem radialKernelConst_le {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s ≤ 1 / 4) :
    radialKernelConst d (gagliardoBeta d s) ≤ (5 / 2) * 6 ^ d := by
  have hbeta : 0 < gagliardoBeta d s := gagliardoBeta_pos hd hs0
  have hbd : gagliardoBeta d s < (d : ℝ) := gagliardoBeta_lt (by linarith only [hs])
  have hbhalf : gagliardoBeta d s - (d : ℝ) ≤ -(1 / 2) := by
    rw [gagliardoBeta]
    linarith only [hs]
  have hratio : annulusRatio d (gagliardoBeta d s) ≤ 3 / 5 := by
    have hrw : annulusRatio d (gagliardoBeta d s) =
        (3 : ℝ) ^ (gagliardoBeta d s - (d : ℝ)) := by
      rw [annulusRatio, Real.rpow_sub (by norm_num), Real.rpow_natCast]
    rw [hrw]
    refine le_trans ?_ three_rpow_neg_half_le
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hbhalf
  have hden : (2 : ℝ) / 5 ≤ 1 - annulusRatio d (gagliardoBeta d s) := by
    linarith only [hratio]
  have hdenpos : (0 : ℝ) < 1 - annulusRatio d (gagliardoBeta d s) := by
    linarith only [hden]
  have hnum : ((1 : ℝ) / 3) ^ (-gagliardoBeta d s) * (2 : ℝ) ^ d ≤ 6 ^ d := by
    have hone : ((1 : ℝ) / 3) ^ (-gagliardoBeta d s) = (3 : ℝ) ^ gagliardoBeta d s := by
      rw [show ((1 : ℝ) / 3) = (3 : ℝ)⁻¹ by norm_num,
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg]
    have hle : (3 : ℝ) ^ gagliardoBeta d s ≤ (3 : ℝ) ^ d := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hbd.le
      rwa [Real.rpow_natCast] at this
    have h2 : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    have hsix : (6 : ℝ) ^ d = (3 : ℝ) ^ d * (2 : ℝ) ^ d := by
      rw [← mul_pow]; norm_num
    rw [hone, hsix]
    exact mul_le_mul_of_nonneg_right hle h2.le
  rw [radialKernelConst, div_le_iff₀ hdenpos]
  calc ((1 : ℝ) / 3) ^ (-gagliardoBeta d s) * (2 : ℝ) ^ d
      ≤ 6 ^ d := hnum
    _ = ((5 / 2) * 6 ^ d) * (2 / 5) := by ring
    _ ≤ ((5 / 2) * 6 ^ d) * (1 - annulusRatio d (gagliardoBeta d s)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)



theorem fractionalSeminormOn_le_of_holderHalf {W : Set (Vec d)} {f : Vec d → Vec d}
    {K R s : ℝ} (hd : 1 ≤ d) (hWmeas : MeasurableSet W) (hW0 : volume W ≠ 0)
    (hWtop : volume W ≠ ⊤) (hball : ∀ p ∈ W, W ⊆ Metric.ball p R) (hR : 0 < R)
    (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hK : 0 ≤ K)
    (hf : HolderSeminormBoundOn W (1 / 2) K f) :
    fractionalSeminormOn W s f ≤
      ENNReal.ofReal (fractionalHolderConst d * Real.sqrt s * K * R ^ (1 / 2 - s : ℝ)) := by
  have hbeta : 0 < gagliardoBeta d s := gagliardoBeta_pos hd hs0
  have hbd : gagliardoBeta d s < (d : ℝ) := gagliardoBeta_lt (by linarith only [hs])
  refine (fractionalSeminormOn_le_of_holderSeminormBoundOn hWmeas hW0 hWtop hball hR hs0.le
    hbeta hbd hK hf).trans (ENNReal.ofReal_le_ofReal ?_)
  have hRd : R ^ d * R ^ (-gagliardoBeta d s) = R ^ (1 - 2 * s) := by
    rw [← Real.rpow_natCast R d, ← Real.rpow_add hR]
    congr 1
    rw [gagliardoBeta]
    ring
  have hprod : radialKernelConst d (gagliardoBeta d s) * (R ^ d * R ^ (-gagliardoBeta d s)) ≤
      ((5 / 2) * 6 ^ d) * R ^ (1 - 2 * s) := by
    rw [hRd]
    exact mul_le_mul_of_nonneg_right (radialKernelConst_le hd hs0 hs)
      (Real.rpow_nonneg hR.le _)
  have hsqrtprod : Real.sqrt (((5 / 2) * 6 ^ d) * R ^ (1 - 2 * s)) =
      fractionalHolderConst d * R ^ (1 / 2 - s : ℝ) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (5 / 2) * 6 ^ d), fractionalHolderConst]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
    congr 1
    ring
  have hmono : Real.sqrt (radialKernelConst d (gagliardoBeta d s) *
      (R ^ d * R ^ (-gagliardoBeta d s))) ≤ fractionalHolderConst d * R ^ (1 / 2 - s : ℝ) := by
    rw [← hsqrtprod]
    exact Real.sqrt_le_sqrt hprod
  have hfront : (0 : ℝ) ≤ Real.sqrt s * K := by positivity
  calc Real.sqrt s * K * Real.sqrt (radialKernelConst d (gagliardoBeta d s) *
        (R ^ d * R ^ (-gagliardoBeta d s)))
      ≤ Real.sqrt s * K * (fractionalHolderConst d * R ^ (1 / 2 - s : ℝ)) :=
        mul_le_mul_of_nonneg_left hmono hfront
    _ = fractionalHolderConst d * Real.sqrt s * K * R ^ (1 / 2 - s : ℝ) := by ring

/-! ## 10. The Hölder seminorm is itself a Hölder bound -/

/-- The Hölder class is antitone in the window. -/
theorem memHolder_mono {V W : Set (Vec d)} {alpha : ℝ} {f : Vec d → Vec d}
    (hf : MemHolder W alpha f) (hVW : V ⊆ W) : MemHolder V alpha f := by
  obtain ⟨K, hK, hfK⟩ := hf
  exact ⟨K, hK, fun p hp q hq => hfK p (hVW hp) q (hVW hq)⟩

/-- The explicit Hölder seminorm of a member of the class is nonnegative (it is
the junk value `0` exactly when the window carries fewer than two points). -/
theorem holderSeminormOn_nonneg {W : Set (Vec d)} {alpha : ℝ} {f : Vec d → Vec d}
    (hf : MemHolder W alpha f) : 0 ≤ holderSeminormOn W alpha f := by
  classical
  by_cases hne : ({r : ℝ | ∃ p ∈ W, ∃ q ∈ W, p ≠ q ∧
      r = euclideanNorm (f p - f q) / euclideanNorm (p - q) ^ alpha}).Nonempty
  · obtain ⟨r, hr⟩ := hne
    have hr0 : 0 ≤ r := by
      obtain ⟨p, _, q, _, _, rfl⟩ := hr
      exact div_nonneg (euclideanNorm_nonneg _) (Real.rpow_nonneg (euclideanNorm_nonneg _) _)
    exact hr0.trans (le_csSup (bddAbove_holderQuotients_of_memHolder hf) hr)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    show (0 : ℝ) ≤ sSup _
    rw [hne, Real.sSup_empty]

/-- **The explicit Hölder seminorm is an admissible Hölder bound.**  This is the
step that lets the printed `[∇h]_{W^{1/2,∞}}` on the right of the
excess-decay conclusion be fed into the embedding of §9. -/
theorem holderSeminormBoundOn_holderSeminormOn {W : Set (Vec d)} {alpha : ℝ}
    {f : Vec d → Vec d} (halpha : 0 < alpha) (hf : MemHolder W alpha f) :
    HolderSeminormBoundOn W alpha (holderSeminormOn W alpha f) f := by
  intro p hp q hq
  rcases eq_or_ne p q with rfl | hpq
  · have h1 : euclideanNorm (f p - f p) = 0 := by rw [sub_self, euclideanNorm_zero]
    have h2 : euclideanNorm (p - p) = 0 := by rw [sub_self, euclideanNorm_zero]
    rw [h1, h2, Real.zero_rpow (ne_of_gt halpha), mul_zero]
  · have hnorm : euclideanNorm (p - q) ≠ 0 := by
      intro hzero
      exact hpq (sub_eq_zero.mp (euclideanNorm_eq_zero_iff.mp hzero))
    have hden : 0 < euclideanNorm (p - q) ^ alpha :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (euclideanNorm_nonneg _) (Ne.symm hnorm)) alpha
    have hmem : euclideanNorm (f p - f q) / euclideanNorm (p - q) ^ alpha ∈
        {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
          r = euclideanNorm (f x - f y) / euclideanNorm (x - y) ^ alpha} :=
      ⟨p, hp, q, hq, hpq, rfl⟩
    exact (div_le_iff₀ hden).mp (le_csSup (bddAbove_holderQuotients_of_memHolder hf) hmem)

/-! ## 11. The window geometry: cubes are supremum balls -/

/-- Two points of a translate of `□_j` are at ambient distance less than `3^j`. -/
theorem dist_lt_of_mem_translatedCube {j : ℤ} {c p q : Vec d}
    (hp : p ∈ translatedCube d j c) (hq : q ∈ translatedCube d j c) :
    dist p q < (3 : ℝ) ^ j := by
  have hjpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hp' : ∀ i, (-(1 / 2 : ℝ)) * (3 : ℝ) ^ j < (p - c) i ∧
      (p - c) i < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
    have h := mem_translatedCube_iff.mp hp
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at h
    exact h
  have hq' : ∀ i, (-(1 / 2 : ℝ)) * (3 : ℝ) ^ j < (q - c) i ∧
      (q - c) i < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
    have h := mem_translatedCube_iff.mp hq
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at h
    exact h
  rw [dist_pi_lt_iff hjpos]
  intro i
  have hpi := hp' i
  have hqi := hq' i
  simp only [Pi.sub_apply] at hpi hqi
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith only [hpi.1, hpi.2, hqi.1, hqi.2]

/-- Every point of `□_m` sees the whole cube inside the supremum ball of
radius `3^m`. -/
theorem cube_subset_ball {m : ℤ} {p : Vec d} (hp : p ∈ cube d m) :
    cube d m ⊆ Metric.ball p ((3 : ℝ) ^ m) := by
  intro q hq
  have hp' : p ∈ translatedCube d m (0 : Vec d) := ⟨p, hp, by simp⟩
  have hq' : q ∈ translatedCube d m (0 : Vec d) := ⟨q, hq, by simp⟩
  exact Metric.mem_ball.mpr (dist_lt_of_mem_translatedCube hq' hp')

/-- Every point of `U_{m,j}(x)` sees the whole window inside the supremum ball
of radius `3^j`. -/
theorem truncatedCube_subset_ball {m j : ℤ} {x p : Vec d}
    (hp : p ∈ truncatedCube d m j x) :
    truncatedCube d m j x ⊆ Metric.ball p ((3 : ℝ) ^ j) := by
  intro q hq
  exact Metric.mem_ball.mpr (dist_lt_of_mem_translatedCube
    (truncatedCube_subset_translatedCube d m j x hq)
    (truncatedCube_subset_translatedCube d m j x hp))

/-! ## 12. The membership guard `MemHolder ⟹ MemFractionalOn` -/

/-- **The guard of the consumers.**  `l.excess.decay.good.scales.GMC`
hypothesises `MemHolder (□_m) (1/2) ∇h`, while
`l.harmonic.approximation.good.scales.GMC` demands `MemFractionalOn (□_m) s ∇h`.
This is the implication that closes the gap. -/
theorem memFractionalOn_of_holderSeminormBoundOn {W : Set (Vec d)} {f : Vec d → Vec d}
    {K R s : ℝ} (hd : 1 ≤ d) (hWmeas : MeasurableSet W) (hW0 : volume W ≠ 0)
    (hWtop : volume W ≠ ⊤) (hball : ∀ p ∈ W, W ⊆ Metric.ball p R) (hR : 0 < R)
    (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hK : 0 ≤ K)
    (hf : HolderSeminormBoundOn W (1 / 2) K f) :
    MemFractionalOn W s f :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (fractionalSeminormOn_le_of_holderHalf hd hWmeas hW0 hWtop hball hR hs0 hs hK hf)

theorem memFractionalOn_cube_of_memHolder {m : ℤ} {f : Vec d → Vec d} {s : ℝ}
    (hd : 1 ≤ d) (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hf : MemHolder (cube d m) (1 / 2) f) :
    MemFractionalOn (cube d m) s f := by
  obtain ⟨K, hK, hfK⟩ := hf
  have hopen : IsOpen (cube d m) := (isOpenBoundedConvexDomain_cube d m).isOpen
  refine memFractionalOn_of_holderSeminormBoundOn (R := (3 : ℝ) ^ m) hd
    hopen.measurableSet ?_ ?_ (fun p hp => cube_subset_ball hp) (zpow_pos (by norm_num) m)
    hs0 hs hK hfK
  · exact (hopen.measure_pos volume ⟨0, zero_mem_cube d m⟩).ne'
  · exact (isOpenBoundedConvexDomain_cube d m).volume_lt_top.ne

theorem memFractionalOn_truncatedCube_of_memHolder {m j : ℤ} {x : Vec d}
    {f : Vec d → Vec d} {s : ℝ} (hd : 1 ≤ d) (hx : x ∈ cube d m) (hs0 : 0 < s)
    (hs : s ≤ 1 / 4) (hf : MemHolder (truncatedCube d m j x) (1 / 2) f) :
    MemFractionalOn (truncatedCube d m j x) s f := by
  obtain ⟨K, hK, hfK⟩ := hf
  have hopen : IsOpen (truncatedCube d m j x) := isOpen_truncatedCube d m j x
  refine memFractionalOn_of_holderSeminormBoundOn (R := (3 : ℝ) ^ j) hd
    (measurableSet_truncatedCube d m j x) ?_ ?_
    (fun p hp => truncatedCube_subset_ball hp) (zpow_pos (by norm_num) j) hs0 hs hK hfK
  · exact (hopen.measure_pos volume ⟨x, mem_truncatedCube_self j hx⟩).ne'
  · exact (volume_truncatedCube_lt_top d m j x).ne

/-! ## 13. The printed display at the excess-decay windows -/

/-- The embedding at a truncated window, with `R := 3^j`. -/
theorem fractionalSeminormOn_truncatedCube_toReal_le {m j : ℤ} {x : Vec d}
    {f : Vec d → Vec d} {K s : ℝ} (hd : 1 ≤ d) (hx : x ∈ cube d m)
    (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hK : 0 ≤ K)
    (hf : HolderSeminormBoundOn (truncatedCube d m j x) (1 / 2) K f) :
    (fractionalSeminormOn (truncatedCube d m j x) s f).toReal ≤
      fractionalHolderConst d * Real.sqrt s * K * ((3 : ℝ) ^ j) ^ (1 / 2 - s : ℝ) := by
  have hopen : IsOpen (truncatedCube d m j x) := isOpen_truncatedCube d m j x
  have hrhs : (0 : ℝ) ≤ fractionalHolderConst d * Real.sqrt s * K *
      ((3 : ℝ) ^ j) ^ (1 / 2 - s : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (fractionalHolderConst_nonneg d) (Real.sqrt_nonneg s)) hK)
      (Real.rpow_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 3) j).le _)
  refine ENNReal.toReal_le_of_le_ofReal hrhs ?_
  exact fractionalSeminormOn_le_of_holderHalf hd (measurableSet_truncatedCube d m j x)
    (hopen.measure_pos volume ⟨x, mem_truncatedCube_self j hx⟩).ne'
    (volume_truncatedCube_lt_top d m j x).ne
    (fun p hp => truncatedCube_subset_ball hp) (zpow_pos (by norm_num) j) hs0 hs hK hf

/-- **Step 8 of the printed proof of `l.excess.decay.good.scales.GMC`**,
paper label `l.excess.decay.good.scales.GMC`, verbatim:

```text
  3^{sn} [f]_{H̲^s(U_{m,n}(x))} ≤ C_H(d) · s^{1/2} · 3^{n/2} · [f]_{W^{1/2,∞}(U_{m,n}(x))} .
```

The `3^{n(1/2-s)}` of the embedding and the `3^{sn}` of the display combine to
exactly `3^{n/2}`; the `s^{1/2}` survives untouched. -/
theorem three_rpow_mul_fractionalSeminormOn_truncatedCube_le {m j : ℤ} {x : Vec d}
    {f : Vec d → Vec d} {K s : ℝ} (hd : 1 ≤ d) (hx : x ∈ cube d m)
    (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hK : 0 ≤ K)
    (hf : HolderSeminormBoundOn (truncatedCube d m j x) (1 / 2) K f) :
    (3 : ℝ) ^ (s * (j : ℝ)) * (fractionalSeminormOn (truncatedCube d m j x) s f).toReal ≤
      fractionalHolderConst d * Real.sqrt s * (3 : ℝ) ^ ((j : ℝ) / 2) * K := by
  have hpow : (0 : ℝ) < (3 : ℝ) ^ (s * (j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hbase := fractionalSeminormOn_truncatedCube_toReal_le hd hx hs0 hs hK hf
  have hcollapse : (3 : ℝ) ^ (s * (j : ℝ)) * ((3 : ℝ) ^ j) ^ (1 / 2 - s : ℝ) =
      (3 : ℝ) ^ ((j : ℝ) / 2) := by
    rw [← Real.rpow_intCast (3 : ℝ) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  calc (3 : ℝ) ^ (s * (j : ℝ)) * (fractionalSeminormOn (truncatedCube d m j x) s f).toReal
      ≤ (3 : ℝ) ^ (s * (j : ℝ)) *
          (fractionalHolderConst d * Real.sqrt s * K * ((3 : ℝ) ^ j) ^ (1 / 2 - s : ℝ)) :=
        mul_le_mul_of_nonneg_left hbase hpow.le
    _ = fractionalHolderConst d * Real.sqrt s *
          ((3 : ℝ) ^ (s * (j : ℝ)) * ((3 : ℝ) ^ j) ^ (1 / 2 - s : ℝ)) * K := by ring
    _ = fractionalHolderConst d * Real.sqrt s * (3 : ℝ) ^ ((j : ℝ) / 2) * K := by
        rw [hcollapse]

/-- The same display stated directly against the explicit Hölder seminorm
`[f]_{W^{1/2,∞}}`, which is the object printed on the right-hand side of the
`l.excess.decay.good.scales.GMC` conclusion. -/
theorem three_rpow_mul_fractionalSeminormOn_truncatedCube_le_holderSeminormOn {m j : ℤ}
    {x : Vec d} {f : Vec d → Vec d} {s : ℝ} (hd : 1 ≤ d) (hx : x ∈ cube d m)
    (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    (hf : MemHolder (truncatedCube d m j x) (1 / 2) f) :
    (3 : ℝ) ^ (s * (j : ℝ)) * (fractionalSeminormOn (truncatedCube d m j x) s f).toReal ≤
      fractionalHolderConst d * Real.sqrt s * (3 : ℝ) ^ ((j : ℝ) / 2) *
        holderSeminormOn (truncatedCube d m j x) (1 / 2) f :=
  three_rpow_mul_fractionalSeminormOn_truncatedCube_le hd hx hs0 hs
    (holderSeminormOn_nonneg hf)
    (holderSeminormBoundOn_holderSeminormOn (by norm_num) hf)

/-! ## 14. The `s`-power bookkeeping of step 9 -/



theorem holderLeg_le {m j : ℤ} {x : Vec d} {f : Vec d → Vec d} {s : ℝ}
    (hd : 1 ≤ d) (hx : x ∈ cube d m) (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    (hf : MemHolder (truncatedCube d m j x) (1 / 2) f) :
    s ^ (-4 : ℝ) * ((3 : ℝ) ^ (-j) *
        ((3 : ℝ) ^ ((1 + s) * (j : ℝ)) *
          (fractionalSeminormOn (truncatedCube d m j x) s f).toReal)) ≤
      fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((j : ℝ) / 2) *
        holderSeminormOn (truncatedCube d m j x) (1 / 2) f := by
  have hdisp := three_rpow_mul_fractionalSeminormOn_truncatedCube_le_holderSeminormOn
    hd hx hs0 hs hf
  have hmul : (0 : ℝ) < s ^ (-4 : ℝ) := Real.rpow_pos_of_pos hs0 _
  have hfront : (3 : ℝ) ^ (-j) * (3 : ℝ) ^ ((1 + s) * (j : ℝ)) =
      (3 : ℝ) ^ (s * (j : ℝ)) := by
    rw [← Real.rpow_intCast (3 : ℝ) (-j), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hspow : s ^ (-4 : ℝ) * Real.sqrt s = s ^ (-7 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs0]
    norm_num
  calc s ^ (-4 : ℝ) * ((3 : ℝ) ^ (-j) *
        ((3 : ℝ) ^ ((1 + s) * (j : ℝ)) *
          (fractionalSeminormOn (truncatedCube d m j x) s f).toReal))
      = s ^ (-4 : ℝ) * ((3 : ℝ) ^ (s * (j : ℝ)) *
          (fractionalSeminormOn (truncatedCube d m j x) s f).toReal) := by
        rw [show (3 : ℝ) ^ (-j) * ((3 : ℝ) ^ ((1 + s) * (j : ℝ)) *
              (fractionalSeminormOn (truncatedCube d m j x) s f).toReal) =
            ((3 : ℝ) ^ (-j) * (3 : ℝ) ^ ((1 + s) * (j : ℝ))) *
              (fractionalSeminormOn (truncatedCube d m j x) s f).toReal from by ring, hfront]
    _ ≤ s ^ (-4 : ℝ) * (fractionalHolderConst d * Real.sqrt s *
          (3 : ℝ) ^ ((j : ℝ) / 2) * holderSeminormOn (truncatedCube d m j x) (1 / 2) f) :=
        mul_le_mul_of_nonneg_left hdisp hmul.le
    _ = fractionalHolderConst d * (s ^ (-4 : ℝ) * Real.sqrt s) *
          (3 : ℝ) ^ ((j : ℝ) / 2) * holderSeminormOn (truncatedCube d m j x) (1 / 2) f := by
        ring
    _ = fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((j : ℝ) / 2) *
          holderSeminormOn (truncatedCube d m j x) (1 / 2) f := by rw [hspow]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
