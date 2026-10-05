module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.UniformSpace.UniformConvergence

@[expose] public section

/-!
# Uniform-convergence calculus on compact windows

Deterministic toolkit for the anchored coefficient: exponentiating a locally
uniform limit, multiplying two locally uniform limits, and the two Lipschitz
seminorm estimates that accompany them.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Filter Topology

variable {X : Type*} [PseudoMetricSpace X] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-! ### Elementary exponential Lipschitz bound -/

/-- One-sided mean-value bound for `Real.exp` below a ceiling. -/
theorem exp_sub_exp_le_of_le {a b M : ℝ} (hba : b ≤ a) (haM : a ≤ M) :
    Real.exp a - Real.exp b ≤ Real.exp M * (a - b) := by
  have ht : 0 ≤ a - b := sub_nonneg.2 hba
  have hkey : Real.exp (a - b) - 1 ≤ (a - b) * Real.exp (a - b) := by
    have h := Real.add_one_le_exp (-(a - b))
    have hpos : 0 < Real.exp (a - b) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_left h hpos.le
    rw [← Real.exp_add] at hmul
    simp only [add_neg_cancel, Real.exp_zero] at hmul
    nlinarith [hmul]
  have hb : (0 : ℝ) < Real.exp b := Real.exp_pos b
  have hsplit : Real.exp a - Real.exp b =
      Real.exp b * (Real.exp (a - b) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    ring_nf
  have hstep : Real.exp b * (Real.exp (a - b) - 1) ≤
      Real.exp b * ((a - b) * Real.exp (a - b)) :=
    mul_le_mul_of_nonneg_left hkey hb.le
  have hcollapse : Real.exp b * ((a - b) * Real.exp (a - b)) =
      (a - b) * Real.exp a := by
    rw [← mul_assoc, mul_comm (Real.exp b) (a - b), mul_assoc, ← Real.exp_add]
    ring_nf
  have hfinal : (a - b) * Real.exp a ≤ (a - b) * Real.exp M :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 haM) ht
  rw [hsplit]
  calc Real.exp b * (Real.exp (a - b) - 1)
      ≤ Real.exp b * ((a - b) * Real.exp (a - b)) := hstep
    _ = (a - b) * Real.exp a := hcollapse
    _ ≤ (a - b) * Real.exp M := hfinal
    _ = Real.exp M * (a - b) := by ring

/-- Two-sided Lipschitz bound for `Real.exp` below a ceiling. -/
theorem abs_exp_sub_exp_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)),
      abs_of_nonneg (sub_nonneg.2 h)]
    exact exp_sub_exp_le_of_le h ha
  · rw [abs_sub_comm, abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 h)),
      abs_of_nonneg (sub_nonneg.2 h)]
    exact exp_sub_exp_le_of_le h hb

/-! ### Uniform bounds along a uniform limit -/

omit [PseudoMetricSpace X] [NormedSpace ℝ E] in
/-- A uniform limit is eventually bounded by any bound on the limit plus one. -/
theorem eventually_norm_le_of_tendstoUniformlyOn {F : ℕ → X → E} {f : X → E}
    {K : Set X} {B : ℝ} (hb : ∀ x ∈ K, ‖f x‖ ≤ B)
    (h : TendstoUniformlyOn F f atTop K) :
    ∀ᶠ L in atTop, ∀ x ∈ K, ‖F L x‖ ≤ B + 1 := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h 1 one_pos] with L hL x hx
  have hd : ‖f x - F L x‖ < 1 := by
    simpa only [dist_eq_norm] using hL x hx
  have hrev : ‖F L x‖ - ‖f x‖ ≤ ‖f x - F L x‖ := by
    simpa only [norm_sub_rev] using norm_sub_norm_le (F L x) (f x)
  have hfx := hb x hx
  linarith

omit [PseudoMetricSpace X] [NormedSpace ℝ E] in
/-- Postcomposition with a norm-nonincreasing map preserves uniform limits. -/
theorem tendstoUniformlyOn_comp_of_norm_sub_le {E' : Type*} [NormedAddCommGroup E']
    {F : ℕ → X → E} {f : X → E} {K : Set X} (Phi : E → E')
    (hPhi : ∀ a b : E, ‖Phi a - Phi b‖ ≤ ‖a - b‖)
    (h : TendstoUniformlyOn F f atTop K) :
    TendstoUniformlyOn (fun L x => Phi (F L x)) (fun x => Phi (f x)) atTop K := by
  refine Metric.tendstoUniformlyOn_iff.2 fun eps heps => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 h eps heps] with L hL x hx
  have hd : ‖f x - F L x‖ < eps := by simpa only [dist_eq_norm] using hL x hx
  calc dist (Phi (f x)) (Phi (F L x)) = ‖Phi (f x) - Phi (F L x)‖ := dist_eq_norm _ _
    _ ≤ ‖f x - F L x‖ := hPhi _ _
    _ < eps := hd

/-- Shifting the index of a uniform limit by one. -/
theorem tendstoUniformlyOn_natSucc {Y : Type*} [UniformSpace Y] {Z : Type*}
    {F : ℕ → Z → Y} {f : Z → Y} {K : Set Z}
    (h : TendstoUniformlyOn F f atTop K) :
    TendstoUniformlyOn (fun L => F (L + 1)) f atTop K :=
  fun U hU => (tendsto_add_atTop_nat 1).eventually (h U hU)

/-! ### Exponentiating a uniform limit -/

omit [PseudoMetricSpace X] in
/-- The exponential of a uniform limit converges uniformly on a window on
which the limit is bounded. -/
theorem tendstoUniformlyOn_exp {F : ℕ → X → ℝ} {f : X → ℝ} {K : Set X} {B : ℝ}
    (hb : ∀ x ∈ K, |f x| ≤ B) (h : TendstoUniformlyOn F f atTop K) :
    TendstoUniformlyOn (fun L x => Real.exp (F L x))
      (fun x => Real.exp (f x)) atTop K := by
  refine Metric.tendstoUniformlyOn_iff.2 fun eps heps => ?_
  have hbnorm : ∀ x ∈ K, ‖f x‖ ≤ B := fun x hx => hb x hx
  have hM : (0 : ℝ) < Real.exp (B + 1) := Real.exp_pos _
  have hquot : 0 < eps / Real.exp (B + 1) := div_pos heps hM
  filter_upwards [eventually_norm_le_of_tendstoUniformlyOn hbnorm h,
    Metric.tendstoUniformlyOn_iff.1 h (eps / Real.exp (B + 1)) hquot]
    with L hbdd hclose x hx
  have hFle : F L x ≤ B + 1 := (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs] using hbdd x hx)
  have hfle : f x ≤ B + 1 := by
    have := hb x hx
    have h1 : f x ≤ B := (le_abs_self _).trans this
    linarith
  have hdist : |f x - F L x| < eps / Real.exp (B + 1) := by
    simpa only [Real.dist_eq] using hclose x hx
  have hkey := abs_exp_sub_exp_le hfle hFle
  have : Real.exp (B + 1) * |f x - F L x| < eps := by
    calc Real.exp (B + 1) * |f x - F L x|
        < Real.exp (B + 1) * (eps / Real.exp (B + 1)) := by
          exact mul_lt_mul_of_pos_left hdist hM
      _ = eps := by field_simp
  simpa only [Real.dist_eq] using lt_of_le_of_lt hkey this

/-! ### Products of uniform limits -/

omit [PseudoMetricSpace X] in
/-- A scalar uniform limit times a vector uniform limit converges uniformly. -/
theorem tendstoUniformlyOn_smul {F : ℕ → X → ℝ} {f : X → ℝ} {G : ℕ → X → E}
    {g : X → E} {K : Set X} {A B : ℝ} (hA : 0 ≤ A) (hB0 : 0 ≤ B)
    (hfb : ∀ x ∈ K, ‖f x‖ ≤ A) (hgb : ∀ x ∈ K, ‖g x‖ ≤ B)
    (hF : TendstoUniformlyOn F f atTop K) (hG : TendstoUniformlyOn G g atTop K) :
    TendstoUniformlyOn (fun L x => F L x • G L x) (fun x => f x • g x)
      atTop K := by
  refine Metric.tendstoUniformlyOn_iff.2 fun eps heps => ?_
  have hden1 : (0 : ℝ) < 2 * (B + 1) := by linarith
  have hden2 : (0 : ℝ) < 2 * (A + 2) := by linarith
  filter_upwards [eventually_norm_le_of_tendstoUniformlyOn hfb hF,
    Metric.tendstoUniformlyOn_iff.1 hF (eps / (2 * (B + 1))) (div_pos heps hden1),
    Metric.tendstoUniformlyOn_iff.1 hG (eps / (2 * (A + 2))) (div_pos heps hden2)]
    with L hFbdd hFclose hGclose x hx
  have hgx : ‖g x‖ ≤ B := hgb x hx
  have hFx : ‖F L x‖ ≤ A + 1 := hFbdd x hx
  have hd1 : ‖f x - F L x‖ < eps / (2 * (B + 1)) := by
    simpa only [dist_eq_norm] using hFclose x hx
  have hd2 : ‖g x - G L x‖ < eps / (2 * (A + 2)) := by
    simpa only [dist_eq_norm] using hGclose x hx
  have hsplit : f x • g x - F L x • G L x =
      (f x - F L x) • g x + F L x • (g x - G L x) := by
    rw [sub_smul, smul_sub]
    abel
  have hbound : ‖f x • g x - F L x • G L x‖ ≤
      ‖f x - F L x‖ * B + (A + 1) * ‖g x - G L x‖ := by
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hgx (norm_nonneg _)
    · rw [norm_smul, Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hFx (norm_nonneg _)
  have h1 : ‖f x - F L x‖ * B < eps / 2 := by
    have hBle : ‖f x - F L x‖ * B ≤ ‖f x - F L x‖ * (B + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have : ‖f x - F L x‖ * (B + 1) < (eps / (2 * (B + 1))) * (B + 1) :=
      mul_lt_mul_of_pos_right hd1 (by linarith)
    have heq : (eps / (2 * (B + 1))) * (B + 1) = eps / 2 := by
      field_simp
    linarith [hBle, this, heq.le, heq.ge]
  have h2 : (A + 1) * ‖g x - G L x‖ < eps / 2 := by
    have hA1 : (0 : ℝ) < A + 2 := by linarith [hden2]
    have : (A + 1) * ‖g x - G L x‖ ≤ (A + 2) * ‖g x - G L x‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have hlt : (A + 2) * ‖g x - G L x‖ < (A + 2) * (eps / (2 * (A + 2))) :=
      mul_lt_mul_of_pos_left hd2 hA1
    have heq : (A + 2) * (eps / (2 * (A + 2))) = eps / 2 := by
      field_simp
    linarith
  have : ‖f x • g x - F L x • G L x‖ < eps := by linarith
  simpa only [dist_eq_norm] using this

/-! ### Lipschitz estimate for a product -/

/-- Product rule for explicit Lipschitz bounds on a window. -/
theorem dist_smul_sub_smul_le {φ : X → ℝ} {ψ : X → E} {S : Set X}
    {ca cb A B : ℝ}
    (hφL : ∀ x ∈ S, ∀ y ∈ S, |φ x - φ y| ≤ ca * dist x y)
    (hψL : ∀ x ∈ S, ∀ y ∈ S, ‖ψ x - ψ y‖ ≤ cb * dist x y)
    (hφB : ∀ x ∈ S, |φ x| ≤ A) (hψB : ∀ x ∈ S, ‖ψ x‖ ≤ B) :
    ∀ x ∈ S, ∀ y ∈ S, ‖φ x • ψ x - φ y • ψ y‖ ≤ (ca * B + A * cb) * dist x y := by
  intro x hx y hy
  have hsplit : φ x • ψ x - φ y • ψ y =
      (φ x - φ y) • ψ x + φ y • (ψ x - ψ y) := by
    rw [sub_smul, smul_sub]
    abel
  have h1 : ‖(φ x - φ y) • ψ x‖ ≤ (ca * dist x y) * B := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hφL x hx y hy) (hψB x hx) (norm_nonneg _)
      (le_trans (abs_nonneg _) (hφL x hx y hy))
  have h2 : ‖φ y • (ψ x - ψ y)‖ ≤ A * (cb * dist x y) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hφB y hy) (hψL x hx y hy) (norm_nonneg _)
      (le_trans (abs_nonneg _) (hφB y hy))
  calc ‖φ x • ψ x - φ y • ψ y‖
      ≤ ‖(φ x - φ y) • ψ x‖ + ‖φ y • (ψ x - ψ y)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ (ca * dist x y) * B + A * (cb * dist x y) := add_le_add h1 h2
    _ = (ca * B + A * cb) * dist x y := by ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
