import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FellerBridge
import MarkovProcess.Main

/-!
# The given kernel semigroup is the Feller semigroup of the resolvent datum

`P` is conservative with a continuous-path realization `K` (finite-dimensional distributions `P`),
and has the resolvent `D` as the Laplace transform of its transition integrals. The semigroup
`D.fellerKernelSemigroup` has the same Laplace transforms; both have time-continuous transition
integrals on `C₀`; Laplace uniqueness and the Riesz identification of measures give `P = P'`.
-/
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open scoped ENNReal NNReal ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

/-- Change of variables `s = exp (-t)` in the Laplace integral at a positive integer. -/
theorem laplace_change_of_variables {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ t, |g t| ≤ C) (n : ℕ) (hn : 1 ≤ n) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) * g t =
      ∫ s in Ioc (0 : ℝ) 1, s ^ (n - 1) * g (-Real.log s) := by
  have hderiv : ∀ x ∈ Ioi (0:ℝ),
      HasDerivWithinAt (fun t => Real.exp (-t)) (-Real.exp (-x)) (Ioi (0:ℝ)) x := by
    intro x hx
    have h : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-x)) x := by
      have hc := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
      simpa [mul_neg_one] using hc
    exact h.hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ => Real.exp (-t)) (Ioi (0:ℝ)) := by
    intro a ha b hb hab
    exact neg_inj.mp (Real.exp_injective hab)
  have himg : (fun t : ℝ => Real.exp (-t)) '' Ioi (0:ℝ) = Ioo (0:ℝ) 1 := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mem_Ioi] at ht
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
    · rintro ⟨hs0, hs1⟩
      refine ⟨-Real.log s, ?_, ?_⟩
      · rw [mem_Ioi]
        have hl := Real.log_neg hs0 hs1
        linarith
      · simp [Real.exp_log hs0]
  have hA : (∫ x in Ioo (0:ℝ) 1, x ^ (n - 1) * g (-Real.log x))
      = ∫ x in Ioi (0:ℝ),
          |-Real.exp (-x)| • ((Real.exp (-x)) ^ (n - 1) * g (-Real.log (Real.exp (-x)))) := by
    have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
      (f := fun t => Real.exp (-t)) (f' := fun t => -Real.exp (-t))
      measurableSet_Ioi hderiv hinj (fun x => x ^ (n - 1) * g (-Real.log x))
    rwa [himg] at h
  have hsimp : (∫ t in Ioi (0:ℝ),
        |-Real.exp (-t)| • ((Real.exp (-t)) ^ (n - 1) * g (-Real.log (Real.exp (-t)))))
      = ∫ t in Ioi (0:ℝ), Real.exp (-(n:ℝ) * t) * g t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change |-Real.exp (-t)| • ((Real.exp (-t)) ^ (n - 1) * g (-Real.log (Real.exp (-t))))
      = Real.exp (-(n:ℝ) * t) * g t
    rw [abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul]
    have hlog : -Real.log (Real.exp (-t)) = t := by rw [Real.log_exp, neg_neg]
    rw [hlog]
    have heq : Real.exp (-t) * Real.exp (-t) ^ (n - 1) = Real.exp (-(n:ℝ) * t) := by
      rw [← Real.exp_nat_mul (-t) (n-1), ← Real.exp_add]
      congr 1
      have hcast : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by
        have h' : ((n - 1 : ℕ) : ℝ) + 1 = (n:ℝ) := by exact_mod_cast Nat.sub_add_cancel hn
        linarith
      rw [hcast]; ring
    rw [← mul_assoc, heq]
  have hC : (∫ x in Ioo (0:ℝ) 1, x ^ (n - 1) * g (-Real.log x))
      = ∫ x in Ioc (0:ℝ) 1, x ^ (n - 1) * g (-Real.log x) :=
    setIntegral_congr_set Ioo_ae_eq_Ioc
  rw [← hsimp, ← hA, hC]

theorem integral_poly_mul_eq_zero {q : ℝ → ℝ} (hq : ContinuousOn q (Ioc (0 : ℝ) 1)) {C : ℝ}
    (hC : ∀ s ∈ Ioc (0 : ℝ) 1, |q s| ≤ C)
    (h0 : ∀ n : ℕ, 1 ≤ n → ∫ s in Ioc (0 : ℝ) 1, s ^ (n - 1) * q s = 0)
    (p : Polynomial ℝ) : ∫ s in Ioc (0 : ℝ) 1, p.eval s * q s = 0 := by
  have hint : ∀ i : ℕ, IntegrableOn (fun s : ℝ => s ^ i * q s) (Ioc (0:ℝ) 1) := by
    intro i
    refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ C ?_
    · exact ((continuous_pow i).continuousOn.mul hq).aestronglyMeasurable measurableSet_Ioc
    · rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with s hs
      obtain ⟨hs0, hs1⟩ := hs
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have hle : |s| ^ i ≤ 1 := by
        rw [abs_of_pos hs0]
        exact pow_le_one₀ (le_of_lt hs0) hs1
      calc |s| ^ i * |q s| ≤ 1 * C :=
            mul_le_mul hle (hC s ⟨hs0, hs1⟩) (abs_nonneg _) (by norm_num)
        _ = C := one_mul C
  have hint2 : ∀ i : ℕ, IntegrableOn (fun s : ℝ => p.coeff i * (s ^ i * q s)) (Ioc (0:ℝ) 1) :=
    fun i => (hint i).const_mul (p.coeff i)
  have hpt : ∀ s : ℝ, (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (s ^ i * q s))
      = p.eval s * q s := by
    intro s
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun s => (hpt s).symm))]
  rw [integral_finset_sum _ (fun i hi => hint2 i)]
  simp only [integral_const_mul]
  apply Finset.sum_eq_zero
  intro i hi
  have hz : ∫ s in Ioc (0:ℝ) 1, s ^ i * q s = 0 := by
    simpa using h0 (i + 1) (by omega)
  rw [hz]
  ring

theorem integral_cont_mul_eq_zero {q : ℝ → ℝ} (hq : ContinuousOn q (Ioc (0 : ℝ) 1)) {C : ℝ}
    (hC : ∀ s ∈ Ioc (0 : ℝ) 1, |q s| ≤ C)
    (hpoly : ∀ p : Polynomial ℝ, ∫ s in Ioc (0 : ℝ) 1, p.eval s * q s = 0)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Icc (0 : ℝ) 1)) :
    ∫ s in Ioc (0 : ℝ) 1, φ s * q s = 0 := by
  have hCnonneg : 0 ≤ C :=
    le_trans (abs_nonneg (q (1/2))) (hC (1/2) ⟨by norm_num, by norm_num⟩)
  have hbound : ∀ ε > 0, |∫ s in Ioc (0:ℝ) 1, φ s * q s| ≤ ε * C := by
    intro ε hε
    rcases exists_polynomial_near_of_continuousOn 0 1 φ hφ ε hε with ⟨p, hp⟩
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
      (p.continuous.continuousOn (s := Icc (0:ℝ) 1))
    have hMnonneg : 0 ≤ M :=
      le_trans (abs_nonneg (p.eval (1/2)))
        (by simpa [Real.norm_eq_abs] using hM (1/2) ⟨by norm_num, by norm_num⟩)
    have hpint : IntegrableOn (fun s => p.eval s * q s) (Ioc (0:ℝ) 1) volume :=
      IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
        ((p.continuous.continuousOn (s := Ioc (0:ℝ) 1)).mul hq |>.aestronglyMeasurable measurableSet_Ioc)
        (M * C) (by
          filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hM s (Ioc_subset_Icc_self hs)) (hC s hs) (abs_nonneg _) hMnonneg)
    have hdiff_ae : ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) 1), ‖(φ s - p.eval s) * q s‖ ≤ ε * C := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs, abs_mul]
      have hlt : |φ s - p.eval s| < ε := by
        rw [abs_sub_comm]
        exact hp s (Ioc_subset_Icc_self hs)
      exact mul_le_mul hlt.le (hC s hs) (abs_nonneg _) hε.le
    have hint : IntegrableOn (fun s => (φ s - p.eval s) * q s) (Ioc (0:ℝ) 1) volume :=
      IntegrableOn.of_bound (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
        (ContinuousOn.sub (hφ.mono Ioc_subset_Icc_self)
          (p.continuous.continuousOn (s := Ioc (0:ℝ) 1)) |>.mul hq |>.aestronglyMeasurable measurableSet_Ioc)
        (ε * C) hdiff_ae
    have hnorm : ‖∫ s in Ioc (0:ℝ) 1, (φ s - p.eval s) * q s‖ ≤ ε * C := by
      have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0:ℝ) 1)) hdiff_ae
      simpa [Measure.real, Real.volume_Ioc] using h
    have hsplit : ∫ s in Ioc (0:ℝ) 1, φ s * q s = ∫ s in Ioc (0:ℝ) 1, (φ s - p.eval s) * q s := by
      have h1 : ∫ s in Ioc (0:ℝ) 1, φ s * q s
          = ∫ s in Ioc (0:ℝ) 1, ((φ s - p.eval s) * q s + p.eval s * q s) := by
        apply integral_congr_ae
        filter_upwards with s
        ring
      rw [h1, integral_add hint hpint, hpoly p, add_zero]
    rw [hsplit]
    simpa only [Real.norm_eq_abs] using hnorm
  have hle0 : |∫ s in Ioc (0:ℝ) 1, φ s * q s| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hε : 0 < δ / (C + 1) := by positivity
    have h1 := hbound (δ / (C + 1)) hε
    have h2 : δ / (C + 1) * C ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < C + 1)]
      nlinarith [hδ.le]
    linarith
  exact abs_eq_zero.mp (le_antisymm hle0 (abs_nonneg _))

theorem eq_zero_of_integral_cont_mul_eq_zero {q : ℝ → ℝ} (hq : ContinuousOn q (Ioc (0 : ℝ) 1))
    (hcont : ∀ φ : ℝ → ℝ, ContinuousOn φ (Icc (0 : ℝ) 1) →
      ∫ s in Ioc (0 : ℝ) 1, φ s * q s = 0) :
    ∀ s ∈ Ioc (0 : ℝ) 1, q s = 0 := by
  intro s0 hs0
  by_contra hne
  have hs0_pos : 0 < s0 := hs0.1
  have hs0_le : s0 ≤ 1 := hs0.2
  have hq_s0 : ContinuousWithinAt q (Ioc (0:ℝ) 1) s0 := hq.continuousWithinAt hs0
  rw [Metric.continuousWithinAt_iff] at hq_s0
  have hε : 0 < |q s0| / 2 := by
    have : 0 < |q s0| := abs_pos.mpr hne
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := hq_s0 (|q s0| / 2) hε
  let a : ℝ := max (s0 - δ / 2) (s0 / 2)
  let b : ℝ := min (s0 + δ / 2) 1
  have ha1 : s0 - δ / 2 ≤ a := le_max_left _ _
  have ha2 : s0 / 2 ≤ a := le_max_right _ _
  have hb1 : b ≤ s0 + δ / 2 := min_le_left _ _
  have hb2 : b ≤ 1 := min_le_right _ _
  have ha_lt_s0 : a < s0 := max_lt (by linarith) (by linarith)
  have hs0_le_b : s0 ≤ b := le_min (by linarith) hs0_le
  have ha_pos : 0 < a := lt_of_lt_of_le (by linarith : 0 < s0 / 2) ha2
  have hab : a < b := lt_of_lt_of_le ha_lt_s0 hs0_le_b
  have hsub01 : Icc a b ⊆ Ioc (0:ℝ) 1 := by
    intro x hx
    exact ⟨lt_of_lt_of_le ha_pos hx.1, le_trans hx.2 hb2⟩
  have hsubIoc : Ioc a b ⊆ Ioc (0:ℝ) 1 := by
    intro x hx
    exact ⟨lt_trans ha_pos hx.1, le_trans hx.2 hb2⟩
  have hsubIcc : Icc a b ⊆ Icc (0:ℝ) 1 := by
    intro x hx
    exact ⟨le_trans (le_of_lt ha_pos) hx.1, le_trans hx.2 hb2⟩
  have hq_ab : ContinuousOn q (Icc a b) := hq.mono hsub01
  let tent : ℝ → ℝ := fun s => max 0 (min (s - a) (b - s))
  have htent_cont : ContinuousOn tent (Icc (0:ℝ) 1) :=
    (show Continuous tent from by
      apply Continuous.max continuous_const
      exact Continuous.min (continuous_id.sub continuous_const)
        (continuous_const.sub continuous_id)).continuousOn
  let c : ℝ := q s0 / |q s0|
  have hφ_cont : ContinuousOn (fun s => c * tent s) (Icc (0:ℝ) 1) :=
    (continuousOn_const (c := c) (s := Icc (0:ℝ) 1)).mul htent_cont
  have hφ_cont_ab : ContinuousOn (fun s => c * tent s) (Icc a b) := hφ_cont.mono hsubIcc
  have hF_cont : ContinuousOn (fun s => (c * tent s) * q s) (Icc a b) :=
    hφ_cont_ab.mul hq_ab
  have hsign : ∀ x ∈ Icc a b, c * q x = |q x| := by
    intro x hx
    have hx01 : x ∈ Ioc (0:ℝ) 1 := hsub01 hx
    have hdist : dist x s0 < δ := by
      rw [Real.dist_eq]
      have hxa : s0 - δ / 2 ≤ x := le_trans ha1 hx.1
      have hxb : x ≤ s0 + δ / 2 := le_trans hx.2 hb1
      have hle : |x - s0| ≤ δ / 2 := by
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      linarith
    have hqd : |q x - q s0| < |q s0| / 2 := by
      have h' := hδ hx01 hdist
      rwa [Real.dist_eq] at h'
    rcases lt_trichotomy (q s0) 0 with hlt | heq | hgt
    · have hqx : q x < 0 := by
        have h1 : |q s0| = -q s0 := abs_of_neg hlt
        rw [h1] at hqd
        have h2 : q x - q s0 < -q s0 / 2 := (abs_lt.mp hqd).2
        linarith
      have hc : c = -1 := by
        have hne0 : q s0 ≠ 0 := ne_of_lt hlt
        rw [show c = q s0 / |q s0| from rfl, abs_of_neg hlt, div_neg, div_self hne0]
      rw [hc, abs_of_neg hqx]
      ring
    · exact absurd heq hne
    · have hqx : 0 < q x := by
        have h1 : |q s0| = q s0 := abs_of_pos hgt
        rw [h1] at hqd
        have h2 : -(q s0 / 2) < q x - q s0 := (abs_lt.mp hqd).1
        linarith
      have hc : c = 1 := by
        have hne0 : q s0 ≠ 0 := ne_of_gt hgt
        rw [show c = q s0 / |q s0| from rfl, abs_of_pos hgt, div_self hne0]
      rw [hc, abs_of_pos hqx]
      ring
  have hnonneg : ∀ x ∈ Ioc a b, 0 ≤ (c * tent x) * q x := by
    intro x hx
    have hxIcc : x ∈ Icc a b := ⟨le_of_lt hx.1, hx.2⟩
    have hcq : c * q x = |q x| := hsign x hxIcc
    have htent_nonneg : 0 ≤ tent x := le_max_left _ _
    have hprod : (c * tent x) * q x = tent x * |q x| := by
      calc (c * tent x) * q x = tent x * (c * q x) := by ring
        _ = tent x * |q x| := by rw [hcq]
    rw [hprod]
    exact mul_nonneg htent_nonneg (abs_nonneg _)
  have hm_mem : (a + b) / 2 ∈ Icc a b := by
    constructor <;> linarith [hab]
  have htent_m : 0 < tent ((a + b) / 2) := by
    have h1 : 0 < (a + b) / 2 - a := by linarith
    have h2 : 0 < b - (a + b) / 2 := by linarith
    change 0 < max 0 (min ((a + b) / 2 - a) (b - (a + b) / 2))
    rw [max_eq_right (le_of_lt (lt_min h1 h2))]
    exact lt_min h1 h2
  have hqd_m : |q ((a + b) / 2) - q s0| < |q s0| / 2 := by
    have h' := hδ (hsub01 hm_mem) (by
      rw [Real.dist_eq]
      have hle : |(a + b) / 2 - s0| ≤ δ / 2 := by
        rw [abs_le]
        constructor <;> linarith [ha1, hb1, hm_mem.1, hm_mem.2]
      linarith)
    rwa [Real.dist_eq] at h'
  have htri : |q s0| ≤ |q ((a + b) / 2) - q s0| + |q ((a + b) / 2)| := by
    calc |q s0| = |(q s0 - q ((a + b) / 2)) + q ((a + b) / 2)| := by ring_nf
      _ ≤ |q s0 - q ((a + b) / 2)| + |q ((a + b) / 2)| := abs_add_le _ _
      _ = |q ((a + b) / 2) - q s0| + |q ((a + b) / 2)| := by rw [abs_sub_comm]
  have hqabs_pos : 0 < |q ((a + b) / 2)| := by linarith
  have hF_pos : 0 < (c * tent ((a + b) / 2)) * q ((a + b) / 2) := by
    have hcq_m : c * q ((a + b) / 2) = |q ((a + b) / 2)| := hsign ((a + b) / 2) hm_mem
    have hprod : (c * tent ((a + b) / 2)) * q ((a + b) / 2)
        = tent ((a + b) / 2) * |q ((a + b) / 2)| := by
      calc (c * tent ((a + b) / 2)) * q ((a + b) / 2)
          = tent ((a + b) / 2) * (c * q ((a + b) / 2)) := by ring
        _ = tent ((a + b) / 2) * |q ((a + b) / 2)| := by rw [hcq_m]
    rw [hprod]
    exact mul_pos htent_m hqabs_pos
  have hInt_pos : 0 < ∫ s in a..b, (c * tent s) * q s :=
    intervalIntegral.integral_pos hab hF_cont hnonneg ⟨(a + b) / 2, hm_mem, hF_pos⟩
  have hInt_ab_eq : ∫ s in a..b, (c * tent s) * q s
      = ∫ s in Ioc a b, (c * tent s) * q s :=
    intervalIntegral.integral_of_le (le_of_lt hab)
  have hzero_out : ∀ x ∈ Ioc (0:ℝ) 1 \ Ioc a b, (c * tent x) * q x = 0 := by
    intro x hx
    have hxs : x ∉ Ioc a b := hx.2
    have htent0 : tent x = 0 := by
      rcases le_or_gt x a with hxa | hxa
      · change max 0 (min (x - a) (b - x)) = 0
        rw [max_eq_left]
        exact le_trans (min_le_left _ _) (by linarith)
      · have hxb : b < x := by
          by_contra hcon
          exact hxs ⟨hxa, le_of_not_gt hcon⟩
        change max 0 (min (x - a) (b - x)) = 0
        rw [max_eq_left]
        exact le_trans (min_le_right _ _) (by linarith)
    rw [htent0]
    ring
  have hIoc_eq : ∫ s in Ioc (0:ℝ) 1, (c * tent s) * q s
      = ∫ s in Ioc a b, (c * tent s) * q s :=
    setIntegral_eq_of_subset_of_forall_diff_eq_zero (μ := volume)
      (f := fun s => (c * tent s) * q s) (measurableSet_Ioc) hsubIoc hzero_out
  have hzero_hyp : ∫ s in Ioc (0:ℝ) 1, (c * tent s) * q s = 0 :=
    hcont (fun s => c * tent s) hφ_cont
  have hmain : 0 < ∫ s in Ioc (0:ℝ) 1, (c * tent s) * q s := by
    rw [hIoc_eq, ← hInt_ab_eq]
    exact hInt_pos
  exact absurd hzero_hyp (ne_of_gt hmain)

/-- Vanishing of all moments `∫₀¹ s^(n-1) q(s) ds` of a bounded continuous function on `(0,1]`
forces `q = 0` on `(0,1]` (Weierstrass). -/
theorem moments_vanish_unit {q : ℝ → ℝ} (hq : ContinuousOn q (Ioc (0 : ℝ) 1)) {C : ℝ}
    (hC : ∀ s ∈ Ioc (0 : ℝ) 1, |q s| ≤ C)
    (h0 : ∀ n : ℕ, 1 ≤ n → ∫ s in Ioc (0 : ℝ) 1, s ^ (n - 1) * q s = 0) :
    ∀ s ∈ Ioc (0 : ℝ) 1, q s = 0 :=
  eq_zero_of_integral_cont_mul_eq_zero hq
    (integral_cont_mul_eq_zero hq hC (integral_poly_mul_eq_zero hq hC h0))

/-- Laplace uniqueness for bounded continuous functions on `ℝ`: if the Laplace transforms of
`g` (over `Ioi 0`) vanish at every positive integer, then `g` vanishes on `[0, ∞)`. -/
theorem laplace_unique {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ} (hC : ∀ t, |g t| ≤ C)
    (h0 : ∀ n : ℕ, 1 ≤ n →
      ∫ t in Ioi (0 : ℝ), Real.exp (-(n : ℝ) * t) * g t = 0) :
    ∀ t : ℝ, 0 ≤ t → g t = 0 := by
  intro t ht
  have hq : ContinuousOn (fun s : ℝ => g (-Real.log s)) (Ioc (0 : ℝ) 1) := by
    apply hg.continuousOn.comp
    · exact (Real.continuousOn_log.mono (fun s hs => ne_of_gt hs.1)).neg
    · intro s _; exact mem_univ _
  have hz := moments_vanish_unit hq (C := C) (fun s _ => hC _)
    (fun n hn => (laplace_change_of_variables hg hC n hn).symm.trans (h0 n hn))
  have hle : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have := hz (Real.exp (-t)) ⟨Real.exp_pos _, hle⟩
  simpa using this

/-- A finite measure on `ℝ^d` is determined by its integrals of `C₀` functions. -/
theorem measure_ext_of_integral_c0 {μ ν : Measure (Fin d → ℝ)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ f : C₀(Fin d → ℝ, ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν := by
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  let χ : ℕ → (Fin d → ℝ) → ℝ := fun n x => max 0 (min 1 ((n:ℝ) + 1 - ‖x‖))
  have hχ_cont : ∀ n : ℕ, Continuous (χ n) := by
    intro n
    refine Continuous.max continuous_const (Continuous.min continuous_const ?_)
    exact (continuous_const : Continuous fun _ : Fin d → ℝ => (n:ℝ) + 1).sub continuous_norm
  have hχ_nonneg : ∀ (n : ℕ) (x : Fin d → ℝ), 0 ≤ χ n x := fun n x => le_max_left _ _
  have hχ_le_one : ∀ (n : ℕ) (x : Fin d → ℝ), χ n x ≤ 1 := by
    intro n x
    exact max_le (by norm_num) (min_le_left _ _)
  have hχ_supp : ∀ (n : ℕ) (x : Fin d → ℝ), (n:ℝ) + 1 ≤ ‖x‖ → χ n x = 0 := by
    intro n x hx
    have ha : (n:ℝ) + 1 - ‖x‖ ≤ 1 := by linarith
    have hb : (n:ℝ) + 1 - ‖x‖ ≤ 0 := by linarith
    show max 0 (min 1 ((n:ℝ) + 1 - ‖x‖)) = 0
    rw [min_eq_right ha]
    exact le_antisymm (max_le (le_refl 0) hb) (le_max_left 0 _)
  have hχ_one : ∀ (n : ℕ) (x : Fin d → ℝ), ‖x‖ ≤ (n:ℝ) → χ n x = 1 := by
    intro n x hx
    have ha : 1 ≤ (n:ℝ) + 1 - ‖x‖ := by linarith
    show max 0 (min 1 ((n:ℝ) + 1 - ‖x‖)) = 1
    rw [min_eq_left ha]
    exact max_eq_right (by norm_num : (0:ℝ) ≤ 1)
  have hC0 : ∀ n : ℕ, ∫ x, f x * χ n x ∂μ = ∫ x, f x * χ n x ∂ν := by
    intro n
    let F : CompactlySupportedContinuousMap (Fin d → ℝ) ℝ :=
      { toFun := fun x => f x * χ n x
        continuous_toFun := (map_continuous f).mul (hχ_cont n)
        hasCompactSupport' := by
          refine HasCompactSupport.intro (K := Metric.closedBall 0 ((n:ℝ) + 1))
            (isCompact_closedBall 0 _) ?_
          intro x hx
          rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
          exact mul_eq_zero_of_right _ (hχ_supp n x (le_of_lt hx)) }
    have := h (F : C₀(Fin d → ℝ, ℝ))
    simpa [F] using this
  have hbound : ∀ (n : ℕ) (x : Fin d → ℝ), ‖f x * χ n x‖ ≤ ‖f‖ := by
    intro n x
    rw [norm_mul]
    have h1 : ‖χ n x‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [hχ_nonneg n x], hχ_le_one n x⟩
    calc ‖f x‖ * ‖χ n x‖ ≤ ‖f‖ * 1 :=
          mul_le_mul (BoundedContinuousFunction.norm_coe_le_norm f x) h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖f‖ := mul_one _
  have hpoint : ∀ x : Fin d → ℝ, Tendsto (fun n => f x * χ n x) atTop (𝓝 (f x)) := by
    intro x
    have hev : ∀ᶠ n in atTop, χ n x = 1 := by
      filter_upwards [eventually_ge_atTop (Nat.ceil ‖x‖)] with n hn
      exact hχ_one n x ((Nat.le_ceil ‖x‖).trans (by exact_mod_cast hn))
    have h1 : Tendsto (fun n => χ n x) atTop (𝓝 (1:ℝ)) := tendsto_nhds_of_eventually_eq hev
    simpa using h1.const_mul (f x)
  have hlimμ : Tendsto (fun n => ∫ x, f x * χ n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun n x => f x * χ n x) (f := fun x => f x) (bound := fun _ : Fin d → ℝ => ‖f‖)
    · intro n
      exact ((map_continuous f).mul (hχ_cont n)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards with x
      exact hbound n x
    · filter_upwards with x
      exact hpoint x
  have hlimν : Tendsto (fun n => ∫ x, f x * χ n x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun n x => f x * χ n x) (f := fun x => f x) (bound := fun _ : Fin d → ℝ => ‖f‖)
    · intro n
      exact ((map_continuous f).mul (hχ_cont n)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards with x
      exact hbound n x
    · filter_upwards with x
      exact hpoint x
  have hlimν' : Tendsto (fun n => ∫ x, f x * χ n x ∂μ) atTop (𝓝 (∫ x, f x ∂ν)) :=
    hlimν.congr' (by filter_upwards with n; exact (hC0 n).symm)
  exact tendsto_nhds_unique hlimμ hlimν'

/-- The transition integral of a semigroup with a continuous-path realization is the path
integral at the fixed time. -/
theorem kernelIntegral_eq_path_integral
    (P : SubMarkovKernelSemigroup (Fin d → ℝ))
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ) (t : NNReal) :
    kernelIntegral (P t) f x = ∫ ω, f (ω t) ∂K x := by
  classical
  have hmev : Measurable (ContinuousPath.finsetEvaluation (alpha := Fin d → ℝ) ({t} : Finset ℝ≥0)) :=
    measurable_pi_lambda _ fun i => (continuous_eval_const (i : ℝ≥0)).measurable
  have hsingle : (SubMarkovKernelSemigroup.finiteSetKernel P ({t} : Finset ℝ≥0) x).map
      (fun w : ({t} : Finset ℝ≥0) → (Fin d → ℝ) => w ⟨t, Finset.mem_singleton_self t⟩) = P t x := by
    have hmo := SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet (α := Fin d → ℝ) ({t} : Finset ℝ≥0)
    rw [SubMarkovKernelSemigroup.finiteSetKernel_eq_map, Kernel.map_apply _ hmo,
      Measure.map_map (measurable_pi_apply _) hmo]
    have hcomp : ((fun w : ({t} : Finset ℝ≥0) → (Fin d → ℝ) => w ⟨t, Finset.mem_singleton_self t⟩) ∘
        SubMarkovKernelSemigroup.orderedPathToFiniteSet ({t} : Finset ℝ≥0)) =
        fun path : Fin 1 → (Fin d → ℝ) => path 0 := by
      funext path
      simp only [Function.comp_apply, SubMarkovKernelSemigroup.orderedPathToFiniteSet]
      congr 1
      apply Fin.ext
      have hlt := ((({t} : Finset ℝ≥0).orderIsoOfFin rfl).symm ⟨t, Finset.mem_singleton_self t⟩).isLt
      have hc : ({t} : Finset ℝ≥0).card = 1 := rfl
      change _ = 0
      omega
    rw [hcomp]
    obtain ⟨τ, hτ⟩ : ∃ τ : FiniteOrderedTimes 1, τ = SubMarkovKernelSemigroup.finiteSetTimes ({t} : Finset ℝ≥0) := ⟨_, rfl⟩
    have h1 := SubMarkovKernelSemigroup.finiteTimeKernel_one_map_eval P τ
    have hmem : τ 0 = t := by
      rw [hτ]
      exact Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ _)
    rw [hmem] at h1
    have h2 := DFunLike.congr_fun h1 x
    rw [Kernel.map_apply _ (measurable_pi_apply 0)] at h2
    rw [← hτ]
    exact h2
  have key2 : ∫ w : ({t} : Finset ℝ≥0) → (Fin d → ℝ),
        f (w ⟨t, Finset.mem_singleton_self t⟩)
        ∂(SubMarkovKernelSemigroup.finiteSetKernel P ({t} : Finset ℝ≥0) x)
      = ∫ y, f y ∂(P t) x := by
    have key : ∫ y, f y ∂ Measure.map
          (fun w : ({t} : Finset ℝ≥0) → (Fin d → ℝ) => w ⟨t, Finset.mem_singleton_self t⟩)
          (SubMarkovKernelSemigroup.finiteSetKernel P ({t} : Finset ℝ≥0) x)
        = ∫ w : ({t} : Finset ℝ≥0) → (Fin d → ℝ),
            f (w ⟨t, Finset.mem_singleton_self t⟩)
            ∂(SubMarkovKernelSemigroup.finiteSetKernel P ({t} : Finset ℝ≥0) x) :=
      integral_map (measurable_pi_apply _).aemeasurable f.continuous.measurable.aestronglyMeasurable
    rw [hsingle] at key
    exact key.symm
  have key1 : ∫ w : ({t} : Finset ℝ≥0) → (Fin d → ℝ),
        f (w ⟨t, Finset.mem_singleton_self t⟩)
        ∂(K.map (ContinuousPath.finsetEvaluation (alpha := Fin d → ℝ) ({t} : Finset ℝ≥0)) x)
      = ∫ ω, f (ω t) ∂K x := by
    rw [Kernel.map_apply _ hmev]
    have hint : ∫ w : ({t} : Finset ℝ≥0) → (Fin d → ℝ),
          f (w ⟨t, Finset.mem_singleton_self t⟩)
          ∂ Measure.map (ContinuousPath.finsetEvaluation (alpha := Fin d → ℝ) ({t} : Finset ℝ≥0)) (K x)
        = ∫ ω, f (ContinuousPath.finsetEvaluation (alpha := Fin d → ℝ) ({t} : Finset ℝ≥0) ω
            ⟨t, Finset.mem_singleton_self t⟩) ∂K x :=
      integral_map hmev.aemeasurable
        (f.continuous.comp (continuous_apply _)).measurable.aestronglyMeasurable
    rw [hint]
    congr 1
  have hbridge : (∫ w : ({t} : Finset ℝ≥0) → (Fin d → ℝ),
        f (w ⟨t, Finset.mem_singleton_self t⟩)
        ∂(SubMarkovKernelSemigroup.finiteSetKernel P ({t} : Finset ℝ≥0) x))
      = (∫ w : ({t} : Finset ℝ≥0) → (Fin d → ℝ),
        f (w ⟨t, Finset.mem_singleton_self t⟩)
        ∂(K.map (ContinuousPath.finsetEvaluation (alpha := Fin d → ℝ) ({t} : Finset ℝ≥0)) x)) := by
    rw [(hfdd ({t} : Finset ℝ≥0) x).symm]
  exact key2.symm.trans (hbridge.trans key1)

/-- Sub-Markov kernels contract `C₀` functions pointwise. -/
theorem abs_kernelIntegral_le (P : SubMarkovKernelSemigroup (Fin d → ℝ)) (t : NNReal)
    (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ) : |kernelIntegral (P t) f x| ≤ ‖f‖ := by
  haveI : IsFiniteMeasure (P t x) :=
    ⟨lt_of_le_of_lt (P.isSubMarkovKernel t x) (by norm_num)⟩
  rw [← Real.norm_eq_abs]
  have hbound : ‖∫ y, f y ∂(P t x)‖ ≤ ‖f‖ * (P t x).real univ := by
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall ?_)
    intro y
    simpa using BoundedContinuousFunction.norm_coe_le_norm f.toBCF y
  have hμ : (P t x).real univ ≤ 1 := by
    rw [Measure.real]
    exact ENNReal.toReal_mono (by norm_num) (P.isSubMarkovKernel t x)
  calc ‖∫ y, f y ∂(P t x)‖ ≤ ‖f‖ * (P t x).real univ := hbound
    _ ≤ ‖f‖ * 1 := by gcongr
    _ = ‖f‖ := by ring

/-- Transition integrals of `C₀` functions are continuous in time for a semigroup with a
continuous-path realization. -/
theorem continuous_kernelIntegral_of_realization
    (P : SubMarkovKernelSemigroup (Fin d → ℝ))
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ) :
    Continuous fun t : ℝ => kernelIntegral (P (Real.toNNReal t)) f x := by
  have hfun : (fun t : ℝ => kernelIntegral (P (Real.toNNReal t)) f x) =
      fun t : ℝ => ∫ ω, f (ω (Real.toNNReal t)) ∂K x := by
    funext t
    exact kernelIntegral_eq_path_integral P K hfdd f x (Real.toNNReal t)
  rw [hfun]
  have hbound : ∀ (g : C₀(Fin d → ℝ, ℝ)) (y : Fin d → ℝ), ‖g y‖ ≤ ‖g‖ := by
    intro g y
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF y
  refine MeasureTheory.continuous_of_dominated
    (F := fun (t : ℝ) (ω : ContinuousPath (Fin d → ℝ)) => f (ω (Real.toNNReal t)))
    (bound := fun _ => ‖f‖) ?_ ?_ ?_ ?_
  · intro t
    exact ((map_continuous f).comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess (Real.toNNReal t)).stronglyMeasurable).aestronglyMeasurable
  · intro t
    filter_upwards with ω
    exact hbound f (ω (Real.toNNReal t))
  · exact integrable_const ‖f‖
  · filter_upwards with ω
    exact (map_continuous f).comp (ω.continuous.comp continuous_real_toNNReal)

/-- Transition integrals of a Feller semigroup are continuous in time. -/
theorem continuous_kernelIntegral_of_feller
    (P : SubMarkovKernelSemigroup (Fin d → ℝ)) (hF : P.IsFellerKernelSemigroup)
    (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ) :
    Continuous fun t : ℝ => kernelIntegral (P (Real.toNNReal t)) f x := by
  obtain ⟨hC0, hcont⟩ := hF
  have h1 : Continuous fun t : ℝ => (P.c0Operator hC0 (Real.toNNReal t)) f :=
    (hcont f).comp continuous_real_toNNReal
  have h2 : Continuous fun g : C₀(Fin d → ℝ, ℝ) => g x := by
    have h : Continuous fun g : C₀(Fin d → ℝ, ℝ) => g.toBCF x := by fun_prop
    simpa only [ZeroAtInftyContinuousMap.toBCF_apply] using h
  refine (h2.comp h1).congr ?_
  intro t
  simp only [Function.comp_apply]
  rw [SubMarkovKernelSemigroup.c0Operator_apply]

/-- Two kernel semigroups whose transition integrals of `C₀` functions are continuous in time and
have the same Laplace transforms coincide. -/
theorem semigroup_eq_of_laplace
    (P Q : SubMarkovKernelSemigroup (Fin d → ℝ))
    (hP : ∀ (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ),
      Continuous fun t : ℝ => kernelIntegral (P (Real.toNNReal t)) f x)
    (hQ : ∀ (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ),
      Continuous fun t : ℝ => kernelIntegral (Q (Real.toNNReal t)) f x)
    (hL : ∀ (μ : Semigroup.PositiveShift) (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ),
      ∫ t in Ioi (0 : ℝ), Real.exp (-(μ : ℝ) * t) * kernelIntegral (P (Real.toNNReal t)) f x =
        ∫ t in Ioi (0 : ℝ), Real.exp (-(μ : ℝ) * t) * kernelIntegral (Q (Real.toNNReal t)) f x) :
    P = Q := by
  have hzero : ∀ (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ) (t : NNReal),
      kernelIntegral (P t) f x = kernelIntegral (Q t) f x := by
    intro f x
    have hgcont : Continuous fun t : ℝ =>
        kernelIntegral (P (Real.toNNReal t)) f x - kernelIntegral (Q (Real.toNNReal t)) f x :=
      (hP f x).sub (hQ f x)
    have hgbound : ∀ t : ℝ,
        |kernelIntegral (P (Real.toNNReal t)) f x - kernelIntegral (Q (Real.toNNReal t)) f x| ≤
          2 * ‖f‖ := by
      intro t
      have h1 := abs_kernelIntegral_le P (Real.toNNReal t) f x
      have h2 := abs_kernelIntegral_le Q (Real.toNNReal t) f x
      calc |kernelIntegral (P (Real.toNNReal t)) f x - kernelIntegral (Q (Real.toNNReal t)) f x|
          = |kernelIntegral (P (Real.toNNReal t)) f x +
              -(kernelIntegral (Q (Real.toNNReal t)) f x)| := by rw [sub_eq_add_neg]
        _ ≤ |kernelIntegral (P (Real.toNNReal t)) f x| +
              |-(kernelIntegral (Q (Real.toNNReal t)) f x)| := abs_add_le _ _
        _ = |kernelIntegral (P (Real.toNNReal t)) f x| +
              |kernelIntegral (Q (Real.toNNReal t)) f x| := by rw [abs_neg]
        _ ≤ ‖f‖ + ‖f‖ := add_le_add h1 h2
        _ = 2 * ‖f‖ := by ring
    have hlaplace : ∀ n : ℕ, 1 ≤ n →
        ∫ t in Ioi (0:ℝ), Real.exp (-(n:ℝ)*t) *
          (kernelIntegral (P (Real.toNNReal t)) f x -
            kernelIntegral (Q (Real.toNNReal t)) f x) = 0 := by
      intro n hn
      have hnpos : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr (by omega)
      have hint1 : IntegrableOn
          (fun t : ℝ => Real.exp (-(n:ℝ)*t) * kernelIntegral (P (Real.toNNReal t)) f x)
          (Ioi 0) := by
        refine Integrable.mono' (g := fun t : ℝ => ‖f‖ * Real.exp (-(n:ℝ)*t))
          ((exp_neg_integrableOn_Ioi 0 (b := (n:ℝ)) hnpos).const_mul ‖f‖) ?_ ?_
        · exact (((by fun_prop : Continuous fun t : ℝ => Real.exp (-(n:ℝ)*t)).mul
            (hP f x))).aestronglyMeasurable
        · filter_upwards with t
          rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
          calc Real.exp (-(n:ℝ)*t) * |kernelIntegral (P (Real.toNNReal t)) f x|
              ≤ Real.exp (-(n:ℝ)*t) * ‖f‖ :=
                mul_le_mul_of_nonneg_left (abs_kernelIntegral_le P (Real.toNNReal t) f x)
                  (le_of_lt (Real.exp_pos _))
            _ = ‖f‖ * Real.exp (-(n:ℝ)*t) := by ring
      have hint2 : IntegrableOn
          (fun t : ℝ => Real.exp (-(n:ℝ)*t) * kernelIntegral (Q (Real.toNNReal t)) f x)
          (Ioi 0) := by
        refine Integrable.mono' (g := fun t : ℝ => ‖f‖ * Real.exp (-(n:ℝ)*t))
          ((exp_neg_integrableOn_Ioi 0 (b := (n:ℝ)) hnpos).const_mul ‖f‖) ?_ ?_
        · exact (((by fun_prop : Continuous fun t : ℝ => Real.exp (-(n:ℝ)*t)).mul
            (hQ f x))).aestronglyMeasurable
        · filter_upwards with t
          rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
          calc Real.exp (-(n:ℝ)*t) * |kernelIntegral (Q (Real.toNNReal t)) f x|
              ≤ Real.exp (-(n:ℝ)*t) * ‖f‖ :=
                mul_le_mul_of_nonneg_left (abs_kernelIntegral_le Q (Real.toNNReal t) f x)
                  (le_of_lt (Real.exp_pos _))
            _ = ‖f‖ * Real.exp (-(n:ℝ)*t) := by ring
      have hLμ : ∫ t in Ioi (0:ℝ), Real.exp (-(n:ℝ)*t) *
            kernelIntegral (P (Real.toNNReal t)) f x =
          ∫ t in Ioi (0:ℝ), Real.exp (-(n:ℝ)*t) *
            kernelIntegral (Q (Real.toNNReal t)) f x := by
        have := hL ⟨(n:ℝ), hnpos⟩ f x
        simpa using this
      simp only [mul_sub]
      rw [integral_sub hint1 hint2, hLμ, sub_self]
    have hforall := laplace_unique hgcont (C := 2 * ‖f‖) hgbound hlaplace
    intro t
    have h0 := hforall (t:ℝ) (by positivity)
    simpa only [Real.toNNReal_coe, sub_eq_zero] using h0
  apply SubMarkovKernelSemigroup.ext
  intro t
  apply Kernel.ext
  intro x
  haveI hPfin : IsFiniteMeasure ((P.kernel t) x) :=
    ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  haveI hQfin : IsFiniteMeasure ((Q.kernel t) x) :=
    ⟨lt_of_le_of_lt (Q.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  apply measure_ext_of_integral_c0
  intro f
  simpa only [kernelIntegral] using hzero f x t

/-- **The given semigroup is Feller.** -/
theorem isFeller_of_realization_and_datum
    (P : SubMarkovKernelSemigroup (Fin d → ℝ))
    (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (Fin d → ℝ))
    (hdense : ∀ mu, DenseRange (D.operator mu))
    (hlaplace : ∀ (mu : Semigroup.PositiveShift) (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ),
      D.solution mu f x = ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) f x)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) :
    P = D.fellerKernelSemigroup hdense ∧ P.IsFellerKernelSemigroup := by
  have hF' := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  have hPeq : P = D.fellerKernelSemigroup hdense :=
    semigroup_eq_of_laplace P _ (continuous_kernelIntegral_of_realization P K hfdd)
      (continuous_kernelIntegral_of_feller _ hF')
      (fun μ f x => (hlaplace μ f x).symm.trans (D.solution_eq_laplace hdense μ f x))
  exact ⟨hPeq, by rw [hPeq]; exact hF'⟩

end SubdiffusiveProcess.E7
