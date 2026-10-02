import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKScalar




open MeasureTheory Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKScalar

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKLaplace

theorem rrkFn_le_one {a : ℝ} (ha : 0 ≤ a) {r : ℝ} (hr : r ≤ 1) : rrkFn a 0 r ≤ 1 := by
  rcases le_or_gt r 0 with h | h
  · rw [rrkFn_of_nonpos a 0 h]; norm_num
  · rw [rrkFn_of_pos a 0 h, pow_zero, one_mul]
    refine Real.exp_le_one_iff.2 ?_
    have h1 : (1:ℝ) ≤ r⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) h]
      simpa using hr
    nlinarith

theorem abs_rrkFn_le_one {a : ℝ} (ha : 0 ≤ a) {r : ℝ} (hr : r ≤ 1) : |rrkFn a 0 r| ≤ 1 := by
  rw [abs_of_nonneg (rrkFn_nonneg a 0 r)]
  exact rrkFn_le_one ha hr

theorem integral_exp_neg_mul_Ioi {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi (0:ℝ), Real.exp (-c * t) = c⁻¹ := by
  have h := integral_comp_mul_left_Ioi (fun t : ℝ => Real.exp (-t)) 0 hc
  simp only [mul_zero, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one] at h
  rw [← h]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [neg_mul]

theorem integral_exp_mul_rrkFn {s : ℝ} (hs : 0 < s) {r : ℝ} (hr : 0 ≤ r) :
    ∫ t in Ioi (0:ℝ), Real.exp (-s⁻¹ * t) * rrkFn (t / s) 0 r = s * r := by
  rcases eq_or_lt_of_le hr with h | h
  · rw [← h]
    simp [rrkFn_of_nonpos _ 0 le_rfl]
  · have hcongr : ∀ t ∈ Ioi (0:ℝ),
        Real.exp (-s⁻¹ * t) * rrkFn (t / s) 0 r = Real.exp (-(s * r)⁻¹ * t) := by
      intro t _
      rw [rrkFn_of_pos _ 0 h, pow_zero, one_mul, ← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_exp_neg_mul_Ioi (by positivity), inv_inv]

/-! ### The Laplace transform inside an abstract continuous functional calculus -/

section Abstract

variable {A : Type*} [CStarAlgebra A]

/-- `φ_c` restricted to the spectrum of `a`, as a point of `C(spectrum ℝ a, ℝ)`. -/
def specFn (a : A) (c : ℝ) : C(spectrum ℝ a, ℝ) :=
  if h : 0 < c then ⟨_, (continuous_rrkFn h 0).continuousOn.restrict⟩ else 0

theorem specFn_apply {a : A} {c : ℝ} (hc : 0 < c) (r : spectrum ℝ a) :
    specFn a c r = rrkFn c 0 (r : ℝ) := by
  rw [specFn, dif_pos hc]; rfl

theorem dist_specFn_le (a : A) {c b m M : ℝ} (hm : 0 < m) (hmc : m ≤ c) (hmb : m ≤ b)
    (hcM : c ≤ M) (hbM : b ≤ M) :
    dist (specFn a c) (specFn a b) ≤ |c - b| * (Real.exp M / m + Real.exp M) := by
  have hc : 0 < c := lt_of_lt_of_le hm hmc
  have hb : 0 < b := lt_of_lt_of_le hm hmb
  have hM : 0 < M := lt_of_lt_of_le hc hcM
  refine (ContinuousMap.dist_le (by positivity)).2 fun r => ?_
  rw [specFn_apply hc, specFn_apply hb, Real.dist_eq]
  have h := rrkFn_sub_abs_le hm hmc hmb hcM hbM 0 (r : ℝ)
  have hcst : Real.exp M * (((0 : ℕ) + 1 : ℝ) / m) ^ (0 + 1) + Real.exp M
      = Real.exp M / m + Real.exp M := by
    norm_num [div_eq_mul_inv]
  rw [hcst] at h
  exact h

theorem norm_specFn_le_one (a : A) (hspec : spectrum ℝ a ⊆ Icc 0 1) {c : ℝ} (hc : 0 < c) :
    ‖specFn a c‖ ≤ 1 := by
  refine (ContinuousMap.norm_le _ zero_le_one).2 fun r => ?_
  rw [specFn_apply hc, Real.norm_eq_abs]
  exact abs_rrkFn_le_one hc.le (hspec r.2).2

theorem continuousOn_specFn (a : A) : ContinuousOn (specFn a) (Ioi 0) := by
  intro c0 hc0
  have hc0' : (0 : ℝ) < c0 := hc0
  refine ContinuousAt.continuousWithinAt ?_
  refine (Metric.continuousAt_iff (f := specFn a) (a := c0)).2 ?_
  intro ε hε
  set L : ℝ := Real.exp (2 * c0) / (c0 / 2) + Real.exp (2 * c0) with hL
  have hLpos : 0 < L := by
    have h1 : (0 : ℝ) < Real.exp (2 * c0) := Real.exp_pos _
    have : (0 : ℝ) < c0 / 2 := by linarith
    positivity
  refine ⟨min (c0 / 2) (ε / (2 * L)), by positivity, fun {c} hd => ?_⟩
  have hd1 : |c - c0| < c0 / 2 := by
    rw [Real.dist_eq] at hd; exact lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : |c - c0| < ε / (2 * L) := by
    rw [Real.dist_eq] at hd; exact lt_of_lt_of_le hd (min_le_right _ _)
  have habs := abs_lt.mp hd1
  have hlow : c0 / 2 ≤ c := by linarith [habs.1]
  have hhigh : c ≤ 2 * c0 := by linarith [habs.2]
  calc dist (specFn a c) (specFn a c0) ≤ |c - c0| * L :=
        dist_specFn_le a (by linarith) hlow (by linarith) hhigh (by linarith)
    _ < (ε / (2 * L)) * L := mul_lt_mul_of_pos_right hd2 hLpos
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- `s · id` on the spectrum. -/
def idSpecFn (a : A) (s : ℝ) : C(spectrum ℝ a, ℝ) := ⟨fun r => s * (r : ℝ), by fun_prop⟩

theorem continuousOn_expSmulSpecFn (a : A) {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun t : ℝ => Real.exp (-s⁻¹ * t) • specFn a (t / s)) (Ioi 0) := by
  have hmaps : MapsTo (fun t : ℝ => t / s) (Ioi 0) (Ioi 0) := fun t ht => div_pos ht hs
  refine ContinuousOn.smul ?_ ((continuousOn_specFn a).comp
    (continuous_id.div_const s).continuousOn hmaps)
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn

theorem integrable_expSmulSpecFn (a : A) (hspec : spectrum ℝ a ⊆ Icc 0 1) {s : ℝ} (hs : 0 < s) :
    Integrable (fun t : ℝ => Real.exp (-s⁻¹ * t) • specFn a (t / s))
      (volume.restrict (Ioi 0)) := by
  refine Integrable.mono' (exp_neg_integrableOn_Ioi (0 : ℝ) (inv_pos.2 hs))
    ((continuousOn_expSmulSpecFn a hs).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-s⁻¹ * t) * ‖specFn a (t / s)‖
      ≤ Real.exp (-s⁻¹ * t) * 1 :=
        mul_le_mul_of_nonneg_left (norm_specFn_le_one a hspec (div_pos ht' hs))
          (Real.exp_pos _).le
    _ = Real.exp (-s⁻¹ * t) := mul_one _

theorem integral_specFn (a : A) (hspec : spectrum ℝ a ⊆ Icc 0 1) {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi (0:ℝ), Real.exp (-s⁻¹ * t) • specFn a (t / s)) = idSpecFn a s := by
  have hint := integrable_expSmulSpecFn a hspec hs
  refine ContinuousMap.ext fun r => ?_
  rw [ContinuousMap.integral_apply hint r]
  have hcongr : ∀ t ∈ Ioi (0:ℝ), (Real.exp (-s⁻¹ * t) • specFn a (t / s)) r
      = Real.exp (-s⁻¹ * t) * rrkFn (t / s) 0 (r : ℝ) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rw [ContinuousMap.smul_apply, specFn_apply (div_pos ht' hs), smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_exp_mul_rrkFn hs (hspec r.2).1]
  rfl

theorem cfcL_specFn {a : A} (ha : IsSelfAdjoint a) {c : ℝ} (hc : 0 < c) :
    cfcL (R := ℝ) ha (specFn a c) = cfc (rrkFn c 0) a := by
  rw [cfc_apply (rrkFn c 0) a ha (continuous_rrkFn hc 0).continuousOn, cfcL_apply]
  congr 1
  exact ContinuousMap.ext fun r => specFn_apply hc r

theorem aeeq_cfcL_specFn {a : A} (ha : IsSelfAdjoint a) {s : ℝ} (hs : 0 < s) :
    (fun t : ℝ => cfcL (R := ℝ) ha (Real.exp (-s⁻¹ * t) • specFn a (t / s)))
      =ᵐ[volume.restrict (Ioi 0)]
        fun t : ℝ => Real.exp (-s⁻¹ * t) • cfc (rrkFn (t / s) 0) a := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  rw [map_smul, cfcL_specFn ha (div_pos ht' hs)]

theorem integrable_expSmulCfc {a : A} (ha : IsSelfAdjoint a) (hspec : spectrum ℝ a ⊆ Icc 0 1)
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun t : ℝ => Real.exp (-s⁻¹ * t) • cfc (rrkFn (t / s) 0) a)
      (volume.restrict (Ioi 0)) :=
  ((cfcL (R := ℝ) ha).integrable_comp (integrable_expSmulSpecFn a hspec hs)).congr
    (aeeq_cfcL_specFn ha hs)

/-- **The Laplace transform of `t ↦ φ_{t/s}(a)`, computed inside the functional calculus.** -/
theorem integral_expSmulCfc {a : A} (ha : IsSelfAdjoint a) (hspec : spectrum ℝ a ⊆ Icc 0 1)
    {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi (0:ℝ), Real.exp (-s⁻¹ * t) • cfc (rrkFn (t / s) 0) a) = s • a := by
  have hint := integrable_expSmulSpecFn a hspec hs
  have h1 : (∫ t in Ioi (0:ℝ), Real.exp (-s⁻¹ * t) • cfc (rrkFn (t / s) 0) a)
      = ∫ t in Ioi (0:ℝ), cfcL (R := ℝ) ha (Real.exp (-s⁻¹ * t) • specFn a (t / s)) :=
    (integral_congr_ae (aeeq_cfcL_specFn ha hs)).symm
  rw [h1, ContinuousLinearMap.integral_comp_comm _ hint, integral_specFn a hspec hs, cfcL_apply]
  have h2 : cfcHom (R := ℝ) ha (idSpecFn a s) = cfc (fun r : ℝ => s * r) a := by
    rw [cfc_apply (fun r : ℝ => s * r) a ha (by fun_prop)]
    congr 1
  rw [h2, cfc_const_mul_id s a]

/-- `|r φ_c(r) - r| ≤ c` on `[0,1]`: the estimate behind strong continuity at `t = 0`. -/
theorem abs_mul_rrkFn_sub_le {c : ℝ} (hc : 0 ≤ c) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |rrkFn c 0 r * r - r| ≤ c := by
  rcases eq_or_lt_of_le hr0 with h | h
  · rw [← h]; simp [rrkFn_of_nonpos c 0 le_rfl, hc]
  · rw [rrkFn_of_pos c 0 h, pow_zero, one_mul]
    set y : ℝ := c * (r⁻¹ - 1) with hy
    have hinv : (1:ℝ) ≤ r⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) h]; simpa using hr1
    have hy0 : 0 ≤ y := by rw [hy]; exact mul_nonneg hc (by linarith)
    have hexp : Real.exp (-c * (r⁻¹ - 1)) = Real.exp (-y) := by rw [hy]; ring_nf
    rw [hexp]
    have hle : 1 - Real.exp (-y) ≤ y := one_sub_exp_neg_le y
    have hge : 0 ≤ 1 - Real.exp (-y) := one_sub_exp_neg_nonneg hy0
    have hrw : Real.exp (-y) * r - r = -(r * (1 - Real.exp (-y))) := by ring
    rw [hrw, abs_neg, abs_of_nonneg (mul_nonneg hr0 hge)]
    have hry : r * y = c * (1 - r) := by rw [hy]; field_simp
    calc r * (1 - Real.exp (-y)) ≤ r * y := mul_le_mul_of_nonneg_left hle hr0
      _ = c * (1 - r) := hry
      _ ≤ c := by nlinarith

theorem norm_cfc_rrkFn_le_one {a : A} (hspec : spectrum ℝ a ⊆ Icc 0 1) {c : ℝ} (hc : 0 < c) :
    ‖cfc (rrkFn c 0) a‖ ≤ 1 :=
  norm_cfc_le zero_le_one fun x hx => by
    rw [Real.norm_eq_abs]; exact abs_rrkFn_le_one hc.le (hspec hx).2

/-- **`φ_c(a) a → a` in norm as `c → 0`**, with the explicit rate `‖φ_c(a) a - a‖ ≤ c`. -/
theorem norm_cfc_rrkFn_mul_sub_le {a : A} (ha : IsSelfAdjoint a)
    (hspec : spectrum ℝ a ⊆ Icc 0 1) {c : ℝ} (hc : 0 < c) :
    ‖cfc (rrkFn c 0) a * a - a‖ ≤ c := by
  have hcont : ContinuousOn (rrkFn c 0) (spectrum ℝ a) := (continuous_rrkFn hc 0).continuousOn
  have hid : ContinuousOn (fun r : ℝ => r) (spectrum ℝ a) := continuousOn_id
  have h1 : cfc (fun r : ℝ => rrkFn c 0 r * r) a = cfc (rrkFn c 0) a * a := by
    rw [cfc_mul _ _ a hcont hid, cfc_id' ℝ a]
  have h2 : cfc (fun r : ℝ => rrkFn c 0 r * r - r) a = cfc (rrkFn c 0) a * a - a := by
    rw [cfc_sub _ _ a (hcont.mul hid) hid, h1, cfc_id' ℝ a]
  rw [← h2]
  exact norm_cfc_le hc.le fun x hx => by
    rw [Real.norm_eq_abs]; exact abs_mul_rrkFn_sub_le hc.le (hspec hx).1 (hspec hx).2

end Abstract

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKLaplace
