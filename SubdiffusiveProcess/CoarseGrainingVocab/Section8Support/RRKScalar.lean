module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic

@[expose] public section




open Real Set Filter Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKScalar

/-- `rrkFn a N r = r⁻¹ ^ N * exp (-a * (r⁻¹ - 1))` for `r > 0` and `0` for `r ≤ 0`. -/
def rrkFn (a : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  if 0 < r then (r⁻¹) ^ N * Real.exp (-a * (r⁻¹ - 1)) else 0

theorem rrkFn_of_nonpos (a : ℝ) (N : ℕ) {r : ℝ} (hr : r ≤ 0) : rrkFn a N r = 0 := by
  simp [rrkFn, not_lt.2 hr]

theorem rrkFn_of_pos (a : ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    rrkFn a N r = (r⁻¹) ^ N * Real.exp (-a * (r⁻¹ - 1)) := by
  simp [rrkFn, hr]

/-- The cancellation `r ^ N * ψ(r) = φ(r)`. -/
theorem pow_mul_rrkFn (a : ℝ) (N : ℕ) (r : ℝ) :
    r ^ N * rrkFn a N r = rrkFn a 0 r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [rrkFn_of_nonpos a N hr, rrkFn_of_nonpos a 0 hr]
  · rw [rrkFn_of_pos a N hr, rrkFn_of_pos a 0 hr, pow_zero, one_mul, ← mul_assoc,
      ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, one_mul]

/-- The semigroup law at the level of scalars. -/
theorem rrkFn_zero_mul (a b : ℝ) (r : ℝ) :
    rrkFn a 0 r * rrkFn b 0 r = rrkFn (a + b) 0 r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [rrkFn_of_nonpos _ 0 hr]
  · rw [rrkFn_of_pos a 0 hr, rrkFn_of_pos b 0 hr, rrkFn_of_pos (a + b) 0 hr, pow_zero]
    rw [one_mul, one_mul, one_mul, ← Real.exp_add]
    ring_nf

theorem rrkFn_nonneg (a : ℝ) (N : ℕ) (r : ℝ) : 0 ≤ rrkFn a N r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [rrkFn_of_nonpos a N hr]
  · rw [rrkFn_of_pos a N hr]
    positivity

/-- `u ^ k * exp (-(c * u)) ≤ (k / c) ^ k` for `u, c > 0` and `k ≥ 1`. -/
theorem pow_mul_exp_neg_le {k : ℕ} (hk : 0 < k) {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    u ^ k * Real.exp (-(c * u)) ≤ (k / c) ^ k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hx : (0:ℝ) < c * u / k := by positivity
  have h1 : (c * u / k) ^ k ≤ Real.exp (c * u) := by
    have := Real.add_one_le_exp (c * u / k)
    have h2 : c * u / k ≤ Real.exp (c * u / k) := by linarith
    calc (c * u / k) ^ k ≤ (Real.exp (c * u / k)) ^ k :=
          pow_le_pow_left₀ hx.le h2 k
      _ = Real.exp (k * (c * u / k)) := by rw [Real.exp_nat_mul]
      _ = Real.exp (c * u) := by rw [mul_div_cancel₀ _ hk0.ne']
  have hpos : (0:ℝ) < (c * u / k) ^ k := by positivity
  rw [Real.exp_neg]
  rw [mul_inv_le_iff₀ (Real.exp_pos _)]
  calc u ^ k = (k / c) ^ k * (c * u / k) ^ k := by
        rw [← mul_pow]; congr 1; field_simp
    _ ≤ (k / c) ^ k * Real.exp (c * u) := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- `u ^ N * exp (-a * (u - 1)) → 0` as `u → ∞`, for `a > 0`. -/
theorem tendsto_pow_mul_exp_atTop {a : ℝ} (ha : 0 < a) (N : ℕ) :
    Tendsto (fun u : ℝ => u ^ N * Real.exp (-a * (u - 1))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun v : ℝ => v ^ N * Real.exp (-v)) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  have hcomp : Tendsto (fun u : ℝ => (a * u) ^ N * Real.exp (-(a * u))) atTop (𝓝 0) :=
    hbase.comp (Filter.tendsto_id.const_mul_atTop ha)
  have h := hcomp.const_mul (Real.exp a * (a ^ N)⁻¹)
  rw [mul_zero] at h
  refine h.congr fun u => ?_
  have haN : (a : ℝ) ^ N ≠ 0 := by positivity
  simp only [mul_pow]
  rw [show -a * (u - 1) = -(a * u) + a by ring, Real.exp_add]
  field_simp

theorem continuous_rrkFn {a : ℝ} (ha : 0 < a) (N : ℕ) : Continuous (rrkFn a N) := by
  rw [continuous_iff_continuousAt]
  intro r
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have hev : rrkFn a N =ᶠ[𝓝 r] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds hr] with x hx using rrkFn_of_nonpos a N (le_of_lt hx)
    exact continuousAt_const.congr hev.symm
  · subst hr
    rw [ContinuousAt, rrkFn_of_nonpos a N le_rfl]
    nth_rewrite 1 [← nhdsLE_sup_nhdsGT (0:ℝ)]
    rw [tendsto_sup]
    constructor
    · refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (rrkFn_of_nonpos a N hx).symm
    · have h1 : Tendsto (fun r : ℝ => r⁻¹) (𝓝[>] (0:ℝ)) atTop := tendsto_inv_nhdsGT_zero
      have h2 := (tendsto_pow_mul_exp_atTop ha N).comp h1
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (rrkFn_of_pos a N hx).symm
  · have hcont : ContinuousAt (fun x : ℝ => (x⁻¹) ^ N * Real.exp (-a * (x⁻¹ - 1))) r := by
      have : ContinuousAt (fun x : ℝ => x⁻¹) r := continuousAt_inv₀ hr.ne'
      fun_prop (disch := exact hr.ne')
    refine hcont.congr ?_
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (rrkFn_of_pos a N hx).symm


section Lipschitz

theorem one_sub_exp_neg_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ 1 - Real.exp (-y) := by
  have : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  linarith

theorem one_sub_exp_neg_le (y : ℝ) : 1 - Real.exp (-y) ≤ y := by
  have := Real.add_one_le_exp (-y)
  linarith

theorem exp_sub_one_le_mul_exp (z : ℝ) : Real.exp z - 1 ≤ z * Real.exp z := by
  have h := Real.add_one_le_exp (-z)
  have hpos : (0:ℝ) < Real.exp z := Real.exp_pos z
  have h2 : (1 - z) * Real.exp z ≤ Real.exp (-z) * Real.exp z := by
    nlinarith [Real.exp_pos z]
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  nlinarith

/-- The uniform-in-`r` Lipschitz estimate in the parameter `a`, ordered form. -/
theorem rrkFn_sub_abs_le_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (N : ℕ) (r : ℝ) :
    |rrkFn a N r - rrkFn b N r| ≤
      (b - a) * (Real.exp a * (((N : ℝ) + 1) / a) ^ (N + 1) + Real.exp b) := by
  have hba : 0 ≤ b - a := by linarith
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hcst : 0 ≤ Real.exp a * (((N : ℝ) + 1) / a) ^ (N + 1) := by positivity
  rcases le_or_gt r 0 with hr | hr
  · simp [rrkFn_of_nonpos _ N hr]
    positivity
  · set u : ℝ := r⁻¹ with hu
    have hupos : 0 < u := by simpa [hu] using inv_pos.2 hr
    rw [rrkFn_of_pos a N hr, rrkFn_of_pos b N hr, ← hu]
    rcases le_or_gt 1 u with hu1 | hu1
    · -- `u ≥ 1`
      have hy : 0 ≤ (b - a) * (u - 1) := mul_nonneg hba (by linarith)
      have hfac : Real.exp (-b * (u - 1)) = Real.exp (-a * (u - 1)) * Real.exp (-((b - a) * (u - 1))) := by
        rw [← Real.exp_add]; ring_nf
      have hsplit : u ^ N * Real.exp (-a * (u - 1)) - u ^ N * Real.exp (-b * (u - 1))
          = u ^ N * Real.exp (-a * (u - 1)) * (1 - Real.exp (-((b - a) * (u - 1)))) := by
        rw [hfac]; ring
      rw [hsplit, abs_of_nonneg]
      · -- upper bound
        have hstep1 : u ^ N * Real.exp (-a * (u - 1)) * (1 - Real.exp (-((b - a) * (u - 1))))
            ≤ u ^ N * Real.exp (-a * (u - 1)) * ((b - a) * (u - 1)) := by
          have := one_sub_exp_neg_le ((b - a) * (u - 1))
          have hnn : 0 ≤ u ^ N * Real.exp (-a * (u - 1)) := by positivity
          exact mul_le_mul_of_nonneg_left this hnn
        have hstep2 : u ^ N * Real.exp (-a * (u - 1)) * ((b - a) * (u - 1))
            ≤ (b - a) * (Real.exp a * (u ^ (N + 1) * Real.exp (-(a * u)))) := by
          have hexp : Real.exp (-a * (u - 1)) = Real.exp a * Real.exp (-(a * u)) := by
            rw [← Real.exp_add]; ring_nf
          rw [hexp]
          have hle : u ^ N * (u - 1) ≤ u ^ (N + 1) := by
            have : u ^ N * (u - 1) ≤ u ^ N * u := by
              have : (0:ℝ) ≤ u ^ N := by positivity
              nlinarith
            simpa [pow_succ] using this
          have key : u ^ N * (Real.exp a * Real.exp (-(a * u))) * ((b - a) * (u - 1))
              = ((b - a) * (Real.exp a * Real.exp (-(a * u)))) * (u ^ N * (u - 1)) := by ring
          have key2 : (b - a) * (Real.exp a * (u ^ (N + 1) * Real.exp (-(a * u))))
              = ((b - a) * (Real.exp a * Real.exp (-(a * u)))) * u ^ (N + 1) := by ring
          rw [key, key2]
          exact mul_le_mul_of_nonneg_left hle (by positivity)
        have hstep3 : u ^ (N + 1) * Real.exp (-(a * u)) ≤ (((N : ℝ) + 1) / a) ^ (N + 1) := by
          have := pow_mul_exp_neg_le (k := N + 1) (Nat.succ_pos N) ha hupos
          simpa using this
        have hfin : (b - a) * (Real.exp a * (u ^ (N + 1) * Real.exp (-(a * u))))
            ≤ (b - a) * (Real.exp a * (((N : ℝ) + 1) / a) ^ (N + 1)) := by
          have : Real.exp a * (u ^ (N + 1) * Real.exp (-(a * u)))
              ≤ Real.exp a * (((N : ℝ) + 1) / a) ^ (N + 1) :=
            mul_le_mul_of_nonneg_left hstep3 (Real.exp_pos a).le
          exact mul_le_mul_of_nonneg_left this hba
        have hlast : (b - a) * (Real.exp a * (((N : ℝ) + 1) / a) ^ (N + 1))
            ≤ (b - a) * (Real.exp a * (((N : ℝ) + 1) / a) ^ (N + 1) + Real.exp b) := by
          have : (0:ℝ) ≤ Real.exp b := (Real.exp_pos b).le
          nlinarith
        linarith
      · have hnn : 0 ≤ u ^ N * Real.exp (-a * (u - 1)) := by positivity
        exact mul_nonneg hnn (one_sub_exp_neg_nonneg hy)
    · -- `0 < u < 1`
      have h1u : 0 < 1 - u := by linarith
      have hmono : Real.exp (-b * (u - 1)) ≥ Real.exp (-a * (u - 1)) := by
        apply Real.exp_le_exp.2
        nlinarith
      have hneg : u ^ N * Real.exp (-a * (u - 1)) - u ^ N * Real.exp (-b * (u - 1)) ≤ 0 := by
        have hnn : (0:ℝ) ≤ u ^ N := by positivity
        nlinarith
      rw [abs_of_nonpos hneg]
      have hfac : Real.exp (-b * (u - 1)) = Real.exp (-a * (u - 1)) * Real.exp ((b - a) * (1 - u)) := by
        rw [← Real.exp_add]; ring_nf
      have hsplit : -(u ^ N * Real.exp (-a * (u - 1)) - u ^ N * Real.exp (-b * (u - 1)))
          = u ^ N * Real.exp (-a * (u - 1)) * (Real.exp ((b - a) * (1 - u)) - 1) := by
        rw [hfac]; ring
      rw [hsplit]
      have hz : 0 ≤ (b - a) * (1 - u) := mul_nonneg hba h1u.le
      have hzle : (b - a) * (1 - u) ≤ b - a := by nlinarith
      have he1 : Real.exp ((b - a) * (1 - u)) - 1
          ≤ ((b - a) * (1 - u)) * Real.exp ((b - a) * (1 - u)) := exp_sub_one_le_mul_exp _
      have he2 : ((b - a) * (1 - u)) * Real.exp ((b - a) * (1 - u)) ≤ (b - a) * Real.exp (b - a) := by
        have hmono2 : Real.exp ((b - a) * (1 - u)) ≤ Real.exp (b - a) := Real.exp_le_exp.2 hzle
        nlinarith [Real.exp_pos ((b - a) * (1 - u))]
      have hun : u ^ N ≤ 1 := pow_le_one₀ hupos.le hu1.le
      have hea : Real.exp (-a * (u - 1)) ≤ Real.exp a := by
        apply Real.exp_le_exp.2
        nlinarith
      have hprod : u ^ N * Real.exp (-a * (u - 1)) * (Real.exp ((b - a) * (1 - u)) - 1)
          ≤ 1 * Real.exp a * ((b - a) * Real.exp (b - a)) := by
        have hA : 0 ≤ Real.exp ((b - a) * (1 - u)) - 1 := by
          have : (1:ℝ) ≤ Real.exp ((b - a) * (1 - u)) := Real.one_le_exp hz
          linarith
        have hB : 0 ≤ u ^ N * Real.exp (-a * (u - 1)) := by positivity
        have hC : u ^ N * Real.exp (-a * (u - 1)) ≤ 1 * Real.exp a := by
          nlinarith [Real.exp_pos (-a * (u - 1)), pow_nonneg hupos.le N, Real.exp_pos a]
        nlinarith [he1.trans he2]
      have hfinal : 1 * Real.exp a * ((b - a) * Real.exp (b - a)) = (b - a) * Real.exp b := by
        rw [one_mul]
        rw [show b = a + (b - a) by ring, Real.exp_add]
        ring_nf
      rw [hfinal] at hprod
      have : (b - a) * Real.exp b
          ≤ (b - a) * (Real.exp a * (((N : ℝ) + 1) / a) ^ (N + 1) + Real.exp b) := by
        nlinarith
      linarith

end Lipschitz

/-- The uniform-in-`r` Lipschitz estimate in the parameter, symmetric form:
on a parameter window `[m, M]` with `0 < m`, the map `a ↦ rrkFn a N` is Lipschitz
for the supremum norm in `r`. -/
theorem rrkFn_sub_abs_le {a b m M : ℝ} (hm : 0 < m) (hma : m ≤ a) (hmb : m ≤ b)
    (haM : a ≤ M) (hbM : b ≤ M) (N : ℕ) (r : ℝ) :
    |rrkFn a N r - rrkFn b N r| ≤
      |a - b| * (Real.exp M * (((N : ℝ) + 1) / m) ^ (N + 1) + Real.exp M) := by
  have key : ∀ c d : ℝ, m ≤ c → c ≤ d → d ≤ M →
      |rrkFn c N r - rrkFn d N r| ≤
        (d - c) * (Real.exp M * (((N : ℝ) + 1) / m) ^ (N + 1) + Real.exp M) := by
    intro c d hmc hcd hdM
    have hc : 0 < c := lt_of_lt_of_le hm hmc
    refine (rrkFn_sub_abs_le_of_le hc hcd N r).trans ?_
    have hdc : 0 ≤ d - c := by linarith
    have h1 : Real.exp c * (((N : ℝ) + 1) / c) ^ (N + 1)
        ≤ Real.exp M * (((N : ℝ) + 1) / m) ^ (N + 1) := by
      have hexp : Real.exp c ≤ Real.exp M := Real.exp_le_exp.2 (by linarith)
      have hdiv : ((N : ℝ) + 1) / c ≤ ((N : ℝ) + 1) / m := by
        apply div_le_div_of_nonneg_left (by positivity) hm hmc
      have hpow : (((N : ℝ) + 1) / c) ^ (N + 1) ≤ (((N : ℝ) + 1) / m) ^ (N + 1) :=
        pow_le_pow_left₀ (by positivity) hdiv _
      calc Real.exp c * (((N : ℝ) + 1) / c) ^ (N + 1)
          ≤ Real.exp c * (((N : ℝ) + 1) / m) ^ (N + 1) :=
            mul_le_mul_of_nonneg_left hpow (Real.exp_pos c).le
        _ ≤ Real.exp M * (((N : ℝ) + 1) / m) ^ (N + 1) :=
            mul_le_mul_of_nonneg_right hexp (by positivity)
    have h2 : Real.exp d ≤ Real.exp M := Real.exp_le_exp.2 hdM
    have := add_le_add h1 h2
    exact mul_le_mul_of_nonneg_left this hdc
  rcases le_total a b with hab | hab
  · have := key a b hma hab hbM
    rwa [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub]
  · have := key b a hmb hab haM
    rw [abs_sub_comm]
    rwa [abs_of_nonneg (by linarith : 0 ≤ a - b)]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKScalar
