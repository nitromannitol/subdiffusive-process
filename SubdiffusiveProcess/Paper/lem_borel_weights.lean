module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.lem_borel_weights_form
public import SubdiffusiveProcess.Paper.lem_weight_measurability
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.prop_21
public import SubdiffusiveProcess.Paper.rem_random_weights
public import SubdiffusiveProcess.Paper.conv_represented_sequence

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

section Biconjugation

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- Strong-convexity identity at a resolvent point `v` of `E + c` with datum `u`. -/
lemma aux_lem_borel_weights_resolvent_identity (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) {c : ℝ}
    {u v φ : Lp ℝ 2 m} (hv : v ∈ E.domain) (hφ : φ ∈ E.domain)
    (hres : ∀ ψ ∈ E.domain, E.form v ψ = c * inner ℝ (u - v) ψ) :
    E.form φ φ + c * ‖φ - u‖ ^ 2 =
      E.form v v + c * ‖v - u‖ ^ 2 + (E.form (φ - v) (φ - v) + c * ‖φ - v‖ ^ 2) := by
  have hd : φ - v ∈ E.domain := E.domain.sub_mem hφ hv
  have hE : E.form φ φ = E.form v v + 2 * E.form v (φ - v) + E.form (φ - v) (φ - v) := by
    have h := E.form_add_self hv hd
    rwa [add_sub_cancel] at h
  have hN : ‖φ - u‖ ^ 2 = ‖v - u‖ ^ 2 + 2 * inner ℝ (v - u) (φ - v) + ‖φ - v‖ ^ 2 := by
    have h : φ - u = (v - u) + (φ - v) := by abel
    rw [h, norm_add_sq_real]
  have hI : inner ℝ (v - u) (φ - v) = - inner ℝ (u - v) (φ - v) := by
    rw [← inner_neg_left, neg_sub]
  rw [hE, hN, hres _ hd, hI]
  ring

/-- Midpoint (parallelogram) identity for `E(φ) + c‖φ - u‖²`. -/
lemma aux_lem_borel_weights_midpoint (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) (c : ℝ)
    {a b : Lp ℝ 2 m} (u : Lp ℝ 2 m) (ha : a ∈ E.domain) (hb : b ∈ E.domain) :
    (E.form a a + c * ‖a - u‖ ^ 2) + (E.form b b + c * ‖b - u‖ ^ 2) =
      2 * (E.form ((1 / 2 : ℝ) • (a + b)) ((1 / 2 : ℝ) • (a + b)) +
        c * ‖(1 / 2 : ℝ) • (a + b) - u‖ ^ 2) +
      (1 / 2) * (E.form (a - b) (a - b) + c * ‖a - b‖ ^ 2) := by
  have hab : a + b ∈ E.domain := E.domain.add_mem ha hb
  have hE1 : E.form ((1 / 2 : ℝ) • (a + b)) ((1 / 2 : ℝ) • (a + b)) =
      (1 / 2) * ((1 / 2) * E.form (a + b) (a + b)) := by
    rw [E.form_smul_left _ _ hab _ (E.domain.smul_mem _ hab), E.form_smul_right _ hab hab]
  have hE2 : E.form (a - b) (a - b) = E.form a a - 2 * E.form a b + E.form b b := by
    have h := E.form_add_smul_self (-1) ha hb
    rw [neg_one_smul, ← sub_eq_add_neg] at h
    rw [h]; ring
  have hN1 : (1 / 2 : ℝ) • (a + b) - u = (1 / 2 : ℝ) • ((a - u) + (b - u)) := by module
  have hN2 : a - b = (a - u) - (b - u) := by abel
  have hpar := parallelogram_law_with_norm ℝ (a - u) (b - u)
  rw [hE1, E.form_add_self ha hb, hE2, hN1, hN2, norm_smul]
  have h12 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [h12]
  linear_combination (-c / 2) * hpar

/-- Continuity of the energy along convergence in the energy norm. -/
lemma aux_lem_borel_weights_energy_tendsto (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m)
    {φ : ℕ → Lp ℝ 2 m} {w : Lp ℝ 2 m} (hφ : ∀ k, φ k ∈ E.domain) (hw : w ∈ E.domain)
    (h : Tendsto (fun k => E.form (φ k - w) (φ k - w) + ‖φ k - w‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => E.form (φ k) (φ k)) atTop (𝓝 (E.form w w)) ∧
      Tendsto φ atTop (𝓝 w) := by
  have hd : ∀ k, φ k - w ∈ E.domain := fun k => E.domain.sub_mem (hφ k) hw
  have hE0 : Tendsto (fun k => E.form (φ k - w) (φ k - w)) atTop (𝓝 0) :=
    squeeze_zero (fun k => E.form_nonneg _ (hd k))
      (fun k => le_add_of_nonneg_right (by positivity)) h
  have hN0 : Tendsto (fun k => ‖φ k - w‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun k => by positivity)
      (fun k => le_add_of_nonneg_left (E.form_nonneg _ (hd k))) h
  have hNorm : Tendsto (fun k => ‖φ k - w‖) atTop (𝓝 0) := by
    have := hN0.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  refine ⟨?_, tendsto_iff_norm_sub_tendsto_zero.2 hNorm⟩
  have hcross : Tendsto (fun k => E.form w (φ k - w)) atTop (𝓝 0) := by
    have hs : Tendsto (fun k => Real.sqrt (E.form w w) * Real.sqrt (E.form (φ k - w) (φ k - w)))
        atTop (𝓝 0) := by
      have := (hE0.sqrt).const_mul (Real.sqrt (E.form w w))
      simpa using this
    refine squeeze_zero_norm (fun k => ?_) hs
    rw [Real.norm_eq_abs]
    exact E.abs_form_le hw (hd k)
  have hexp : ∀ k, E.form (φ k) (φ k) =
      E.form w w + 2 * E.form w (φ k - w) + E.form (φ k - w) (φ k - w) := by
    intro k
    have h := E.form_add_self hw (hd k)
    rwa [add_sub_cancel] at h
  simp_rw [hexp]
  simpa using (tendsto_const_nhds.add (hcross.const_mul 2)).add hE0

/-- Existence of the resolvent point: a minimizer of `E(φ) + c‖φ - u‖²` on `D(E)`,
with its Euler–Lagrange equation. -/
lemma aux_lem_borel_weights_resolvent_exists (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) {c : ℝ}
    (hc : 0 < c) (u : Lp ℝ 2 m) :
    ∃ v ∈ E.domain, ∀ ψ ∈ E.domain, E.form v ψ = c * inner ℝ (u - v) ψ := by
  set F : Lp ℝ 2 m → ℝ := fun φ => E.form φ φ + c * ‖φ - u‖ ^ 2 with hF
  set S : Set ℝ := F '' (E.domain : Set (Lp ℝ 2 m)) with hS
  have hSne : S.Nonempty := ⟨F 0, 0, E.domain.zero_mem, rfl⟩
  have hFnn : ∀ φ ∈ E.domain, 0 ≤ F φ := fun φ hφ =>
    add_nonneg (E.form_nonneg φ hφ) (by positivity)
  have hSbdd : BddBelow S := ⟨0, by rintro _ ⟨φ, hφ, rfl⟩; exact hFnn φ hφ⟩
  set m0 := sInf S with hm0
  have hm0le : ∀ φ ∈ E.domain, m0 ≤ F φ := fun φ hφ => csInf_le hSbdd ⟨φ, hφ, rfl⟩
  have hseq : ∀ k : ℕ, ∃ φ ∈ E.domain, F φ < m0 + 1 / ((k : ℝ) + 1) := by
    intro k
    have hlt : m0 < m0 + 1 / ((k : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    obtain ⟨_, ⟨φ, hφ, rfl⟩, hφlt⟩ := exists_lt_of_csInf_lt hSne hlt
    exact ⟨φ, hφ, hφlt⟩
  choose φ hφD hφlt using hseq
  have hpar : ∀ p q, E.form (φ p - φ q) (φ p - φ q) + c * ‖φ p - φ q‖ ^ 2 ≤
      2 * (1 / ((p : ℝ) + 1) + 1 / ((q : ℝ) + 1)) := by
    intro p q
    have hmid := aux_lem_borel_weights_midpoint E c u (hφD p) (hφD q)
    have hmin := hm0le _ (E.domain.smul_mem (1 / 2 : ℝ) (E.domain.add_mem (hφD p) (hφD q)))
    have hp := hφlt p
    have hq := hφlt q
    simp only [hF] at hmin hp hq
    linarith
  have hκ : 0 < min 1 c := lt_min one_pos hc
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      E.form (φ p - φ q) (φ p - φ q) + ‖φ p - φ q‖ ^ 2 < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / (min 1 c * ε))
    refine ⟨N, fun p hp q hq => ?_⟩
    have hEnn := E.form_nonneg _ (E.domain.sub_mem (hφD p) (hφD q))
    have hsq : 0 ≤ ‖φ p - φ q‖ ^ 2 := by positivity
    have h1 : min 1 c * (E.form (φ p - φ q) (φ p - φ q) + ‖φ p - φ q‖ ^ 2) ≤
        E.form (φ p - φ q) (φ p - φ q) + c * ‖φ p - φ q‖ ^ 2 := by
      have := min_le_left 1 c
      have := min_le_right 1 c
      nlinarith
    have hpN : 1 / ((p : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hp 1)
    have hqN : 1 / ((q : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hq 1)
    have hκε : 0 < min 1 c * ε := mul_pos hκ hε
    have h4 : 4 < (N : ℝ) * (min 1 c * ε) := (div_lt_iff₀ hκε).1 hN
    have h2 : 4 * (1 / ((N : ℝ) + 1)) < min 1 c * ε := by
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have h3 := hpar p q
    have h5 : min 1 c * (E.form (φ p - φ q) (φ p - φ q) + ‖φ p - φ q‖ ^ 2) <
        min 1 c * ε := by linarith
    exact lt_of_mul_lt_mul_left h5 hκ.le
  obtain ⟨w, hwD, hwlim⟩ := E.complete φ hφD hcauchy
  obtain ⟨hEw, hφw⟩ := aux_lem_borel_weights_energy_tendsto E hφD hwD hwlim
  have hFw : Tendsto (fun k => F (φ k)) atTop (𝓝 (F w)) := by
    have hn : Tendsto (fun k => ‖φ k - u‖) atTop (𝓝 ‖w - u‖) :=
      ((hφw.sub tendsto_const_nhds).norm)
    exact hEw.add ((hn.pow 2).const_mul c)
  have hFm : Tendsto (fun k => F (φ k)) atTop (𝓝 m0) := by
    have hup : Tendsto (fun k : ℕ => m0 + 1 / ((k : ℝ) + 1)) atTop (𝓝 m0) := by
      have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := m0)).add h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => hm0le _ (hφD k)) (fun k => (hφlt k).le)
  have hFwm : F w = m0 := tendsto_nhds_unique hFw hFm
  refine ⟨w, hwD, fun ψ hψ => ?_⟩
  set A := E.form w ψ - c * inner ℝ (u - w) ψ with hA
  set B := E.form ψ ψ + c * ‖ψ‖ ^ 2 with hB
  have hquad : ∀ t : ℝ, 0 ≤ B * (t * t) + (2 * A) * t + 0 := by
    intro t
    have hmin := hm0le _ (E.domain.add_mem hwD (E.domain.smul_mem t hψ))
    rw [← hFwm] at hmin
    simp only [hF] at hmin
    have hexpE := E.form_add_smul_self t hwD hψ
    have hn : w + t • ψ - u = (w - u) + t • ψ := by abel
    have hexpN : ‖w + t • ψ - u‖ ^ 2 =
        ‖w - u‖ ^ 2 + 2 * (t * inner ℝ (w - u) ψ) + t ^ 2 * ‖ψ‖ ^ 2 := by
      rw [hn, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hI : inner ℝ (w - u) ψ = - inner ℝ (u - w) ψ := by
      rw [← inner_neg_left, neg_sub]
    rw [hexpE, hexpN, hI] at hmin
    simp only [hA, hB]
    nlinarith [hmin]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have hA0 : A = 0 := by nlinarith [sq_nonneg A]
  simp only [hA] at hA0
  linarith

/-- At a resolvent point `v`, the dual supremum at the load `c (u - v)` is attained at `v`. -/
lemma aux_lem_borel_weights_resolvent_isLUB (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m) {c : ℝ}
    {u v : Lp ℝ 2 m} (hv : v ∈ E.domain)
    (hres : ∀ ψ ∈ E.domain, E.form v ψ = c * inner ℝ (u - v) ψ) :
    IsLUB {t : ℝ | ∃ w : Lp ℝ 2 m, w ∈ E.domain ∧
      t = 2 * inner ℝ (c • (u - v)) w - E.form w w} (E.form v v) := by
  refine IsGreatest.isLUB ⟨⟨v, hv, ?_⟩, ?_⟩
  · rw [real_inner_smul_left, ← hres v hv]; ring
  · rintro _ ⟨w, hw, rfl⟩
    rw [real_inner_smul_left, ← hres w hw]
    have hnn := E.form_nonneg _ (E.domain.sub_mem hw hv)
    have h := E.form_add_smul_self (-1) hw hv
    rw [neg_one_smul, ← sub_eq_add_neg] at h
    rw [h, E.form_symm w hw v hv] at hnn
    nlinarith [hnn]

/-- The value of the dual functional at the resolvent load. -/
lemma aux_lem_borel_weights_resolvent_value (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hLUB : ∀ f : Lp ℝ 2 m, IsLUB {t : ℝ | ∃ w : Lp ℝ 2 m, w ∈ E.domain ∧
      t = 2 * inner ℝ f w - E.form w w} (inner ℝ f (G f)))
    {c : ℝ} {u v : Lp ℝ 2 m} (hv : v ∈ E.domain)
    (hres : ∀ ψ ∈ E.domain, E.form v ψ = c * inner ℝ (u - v) ψ) :
    2 * inner ℝ (c • (u - v)) u - inner ℝ (c • (u - v)) (G (c • (u - v))) =
      E.form v v + 2 * c * ‖v - u‖ ^ 2 := by
  have hG : inner ℝ (c • (u - v)) (G (c • (u - v))) = E.form v v :=
    (hLUB (c • (u - v))).unique (aux_lem_borel_weights_resolvent_isLUB E hv hres)
  rw [hG, real_inner_smul_left]
  have hvv := hres v hv
  have hsplit : inner ℝ (u - v) u = inner ℝ (u - v) v + ‖u - v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← inner_add_right, add_sub_cancel]
  rw [hsplit, norm_sub_rev u v]
  nlinarith [hvv]

/-- Monotonicity and energy-Cauchy estimate along the resolvent points. -/
lemma aux_lem_borel_weights_resolvent_monotone (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m)
    {cn ck : ℝ} (hcn : 0 < cn) (hlt : cn < ck) {u vn vk : Lp ℝ 2 m}
    (hvn : vn ∈ E.domain) (hvk : vk ∈ E.domain)
    (hresn : ∀ ψ ∈ E.domain, E.form vn ψ = cn * inner ℝ (u - vn) ψ)
    (hresk : ∀ ψ ∈ E.domain, E.form vk ψ = ck * inner ℝ (u - vk) ψ) :
    E.form vn vn ≤ E.form vk vk ∧
      E.form (vk - vn) (vk - vn) ≤ E.form vk vk - E.form vn vn := by
  have h1 := aux_lem_borel_weights_resolvent_identity E hvn hvk hresn
  have h2 := aux_lem_borel_weights_resolvent_identity E hvk hvn hresk
  have hq : E.form (vn - vk) (vn - vk) = E.form (vk - vn) (vk - vn) := by
    rw [← neg_sub vk vn, E.form_neg_left (E.domain.sub_mem hvk hvn)
      (E.domain.neg_mem (E.domain.sub_mem hvk hvn)),
      E.form_neg_right (E.domain.sub_mem hvk hvn) (E.domain.sub_mem hvk hvn), neg_neg]
  have hδ : ‖vn - vk‖ = ‖vk - vn‖ := norm_sub_rev _ _
  rw [hq, hδ] at h2
  set q := E.form (vk - vn) (vk - vn)
  set δ := ‖vk - vn‖ ^ 2
  have hqnn : 0 ≤ q := E.form_nonneg _ (E.domain.sub_mem hvk hvn)
  have hδnn : 0 ≤ δ := by positivity
  have key : (ck - cn) * (E.form vk vk - E.form vn vn) = (ck + cn) * q + 2 * cn * ck * δ := by
    linear_combination ck * h1 + cn * h2
  have hck : 0 < ck := hcn.trans hlt
  have hRHS : (ck + cn) * q ≤ (ck - cn) * (E.form vk vk - E.form vn vn) := by
    rw [key]; nlinarith [mul_nonneg (mul_nonneg hcn.le hck.le) hδnn]
  have hmono : 0 ≤ E.form vk vk - E.form vn vn := by
    have h0 : (ck - cn) * 0 ≤ (ck - cn) * (E.form vk vk - E.form vn vn) := by
      rw [mul_zero]; exact (mul_nonneg (by positivity) hqnn).trans hRHS
    exact le_of_mul_le_mul_left h0 (by linarith)
  refine ⟨by linarith, ?_⟩
  have h3 : (ck + cn) * q ≤ (ck + cn) * (E.form vk vk - E.form vn vn) :=
    hRHS.trans (mul_le_mul_of_nonneg_right (by linarith) hmono)
  exact le_of_mul_le_mul_left h3 (by linarith)

/-- **Biconjugation.** If `⟪f, G f⟫` is the dual supremum of a closed form for every `f`,
then the extended energy of the form is the dual energy of `G`. -/
lemma aux_lem_borel_weights_energy_le_dual (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hLUB : ∀ f : Lp ℝ 2 m, IsLUB {t : ℝ | ∃ w : Lp ℝ 2 m, w ∈ E.domain ∧
      t = 2 * inner ℝ f w - E.form w w} (inner ℝ f (G f)))
    (u : Lp ℝ 2 m) :
    E.energy u ≤ ⨆ f : Lp ℝ 2 m, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) := by
  set L := ⨆ f : Lp ℝ 2 m, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) with hL
  by_cases hLtop : L = ⊤
  · rw [hLtop]; exact le_top
  have hL0 : (0 : EReal) ≤ L := le_iSup_of_le (0 : Lp ℝ 2 m) (by simp)
  have hLbot : L ≠ ⊥ := ne_bot_of_le_ne_bot EReal.zero_ne_bot hL0
  set ℓ := L.toReal with hℓdef
  have hℓ : L = (ℓ : EReal) := (EReal.coe_toReal hLtop hLbot).symm
  have hval : ∀ f : Lp ℝ 2 m, 2 * inner ℝ f u - inner ℝ f (G f) ≤ ℓ := by
    intro f
    have h := le_iSup (fun f : Lp ℝ 2 m => ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) f
    rw [← hL, hℓ] at h
    exact EReal.coe_le_coe_iff.1 h
  have hcpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  choose v hvD hvres using fun n : ℕ =>
    aux_lem_borel_weights_resolvent_exists E (hcpos n) u
  have hbound : ∀ n : ℕ, E.form (v n) (v n) + 2 * ((n : ℝ) + 1) * ‖v n - u‖ ^ 2 ≤ ℓ := by
    intro n
    rw [← aux_lem_borel_weights_resolvent_value E G hLUB (hvD n) (hvres n)]
    exact hval _
  have ha_le : ∀ n, E.form (v n) (v n) ≤ ℓ := fun n => by
    have := hbound n
    have : 0 ≤ 2 * ((n : ℝ) + 1) * ‖v n - u‖ ^ 2 := by positivity
    linarith
  have hb_le : ∀ n : ℕ, ‖v n - u‖ ^ 2 ≤ ℓ / 2 * (1 / ((n : ℝ) + 1)) := by
    intro n
    have h := hbound n
    have ha := E.form_nonneg _ (hvD n)
    rw [mul_one_div, le_div_iff₀ (hcpos n)]
    nlinarith
  have hmono : Monotone fun n => E.form (v n) (v n) := by
    refine monotone_nat_of_le_succ fun n => ?_
    exact (aux_lem_borel_weights_resolvent_monotone E (cn := (n : ℝ) + 1)
      (ck := ((n + 1 : ℕ) : ℝ) + 1) (hcpos n) (by push_cast; linarith)
      (hvD n) (hvD (n + 1)) (hvres n) (hvres (n + 1))).1
  have hqle : ∀ n k : ℕ, n ≤ k →
      E.form (v k - v n) (v k - v n) ≤ E.form (v k) (v k) - E.form (v n) (v n) := by
    intro n k hnk
    rcases hnk.lt_or_eq with hlt | rfl
    · exact (aux_lem_borel_weights_resolvent_monotone E (hcpos n)
        (by exact_mod_cast Nat.add_lt_add_right hlt 1) (hvD n) (hvD k) (hvres n) (hvres k)).2
    · simp [E.form_zero_left E.domain.zero_mem]
  have hbdd : BddAbove (Set.range fun n => E.form (v n) (v n)) :=
    ⟨ℓ, by rintro _ ⟨n, rfl⟩; exact ha_le n⟩
  have hatend := tendsto_atTop_ciSup hmono hbdd
  set A := ⨆ n, E.form (v n) (v n) with hA
  have haA : ∀ n, E.form (v n) (v n) ≤ A := fun n => le_ciSup hbdd n
  have hbt : Tendsto (fun n : ℕ => ‖v n - u‖ ^ 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := h0.const_mul (ℓ / 2)
    rw [mul_zero] at this
    exact squeeze_zero (fun n => by positivity) hb_le this
  have hvu : Tendsto v atTop (𝓝 u) := by
    have := hbt.sqrt
    rw [Real.sqrt_zero] at this
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      E.form (v p - v q) (v p - v q) + ‖v p - v q‖ ^ 2 < ε := by
    intro ε hε
    obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.1 hatend) (ε / 2) (by positivity)
    obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.1 hbt) (ε / 8) (by positivity)
    refine ⟨max N1 N2, fun p hp q hq => ?_⟩
    have hp1 : N1 ≤ p := le_of_max_le_left hp
    have hq1 : N1 ≤ q := le_of_max_le_left hq
    have hEpq : E.form (v p - v q) (v p - v q) < ε / 2 := by
      have hdp := hN1 p hp1
      have hdq := hN1 q hq1
      rw [Real.dist_eq, abs_sub_lt_iff] at hdp hdq
      rcases le_total q p with hqp | hpq
      · have := hqle q p hqp
        have := haA p
        linarith
      · have h := hqle p q hpq
        have hsym : E.form (v p - v q) (v p - v q) = E.form (v q - v p) (v q - v p) := by
          rw [← neg_sub (v q) (v p),
            E.form_neg_left (E.domain.sub_mem (hvD q) (hvD p))
              (E.domain.neg_mem (E.domain.sub_mem (hvD q) (hvD p))),
            E.form_neg_right (E.domain.sub_mem (hvD q) (hvD p))
              (E.domain.sub_mem (hvD q) (hvD p)), neg_neg]
        have := haA q
        linarith
    have hNpq : ‖v p - v q‖ ^ 2 < ε / 2 := by
      have hbp := hN2 p (le_of_max_le_right hp)
      have hbq := hN2 q (le_of_max_le_right hq)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hbp hbq
      have htri : ‖v p - v q‖ ≤ ‖v p - u‖ + ‖v q - u‖ := by
        have : v p - v q = (v p - u) - (v q - u) := by abel
        rw [this]; exact norm_sub_le _ _
      have h2 : ‖v p - v q‖ ^ 2 ≤ 2 * ‖v p - u‖ ^ 2 + 2 * ‖v q - u‖ ^ 2 := by
        nlinarith [norm_nonneg (v p - v q), sq_nonneg (‖v p - u‖ - ‖v q - u‖)]
      linarith
    linarith
  obtain ⟨w, hwD, hwlim⟩ := E.complete v hvD hcauchy
  obtain ⟨hEw, hvw⟩ := aux_lem_borel_weights_energy_tendsto E hvD hwD hwlim
  have hwu : w = u := tendsto_nhds_unique hvw hvu
  subst hwu
  rw [E.energy_of_mem hwD, hℓ]
  exact EReal.coe_le_coe_iff.2 (le_of_tendsto' hEw ha_le)

lemma aux_lem_borel_weights_energy_eq_dual (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm m)
    (G : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hLUB : ∀ f : Lp ℝ 2 m, IsLUB {t : ℝ | ∃ w : Lp ℝ 2 m, w ∈ E.domain ∧
      t = 2 * inner ℝ f w - E.form w w} (inner ℝ f (G f)))
    (u : Lp ℝ 2 m) :
    E.energy u = ⨆ f : Lp ℝ 2 m, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal) := by
  refine le_antisymm (aux_lem_borel_weights_energy_le_dual E G hLUB u) ?_
  by_cases hu : u ∈ E.domain
  · rw [E.energy_of_mem hu]
    refine iSup_le fun f => ?_
    have h := (hLUB f).1 ⟨u, hu, rfl⟩
    exact EReal.coe_le_coe_iff.2 (by linarith)
  · rw [E.energy_of_notMem hu]
    exact le_top

end Biconjugation

/-- A limit in measure of eventually `Rem`-measurable functions has a `Rem`-measurable
version, a.e. for the ambient measure. -/
lemma aux_lem_borel_weights_rem_version {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (Rem : MeasurableSpace Ω) (Xs : ℕ → Ω → ℝ) (Y : Ω → ℝ) (N0 : ℕ)
    (hX : ∀ n, N0 ≤ n → Measurable[Rem] (Xs n))
    (hconv : TendstoInMeasure P Xs atTop Y) :
    ∃ φ : Ω → ℝ, Measurable[Rem] φ ∧ φ =ᵐ[P] Y := by
  obtain ⟨ns, hns, hae⟩ := hconv.exists_seq_tendsto_ae
  refine ⟨fun om => limsup (fun k => Xs (ns (k + N0)) om) atTop, ?_, ?_⟩
  · refine @Measurable.limsup ℝ Ω _ _ _ Rem _ _ _ (fun k => Xs (ns (k + N0))) fun k => ?_
    exact hX _ ((Nat.le_add_left N0 k).trans (hns.id_le _))
  · filter_upwards [hae] with om hom
    exact (hom.comp (tendsto_add_atTop_nat N0)).limsup_eq

section OperatorVersion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A real sequence uniformly approximable by convergent sequences converges. -/
lemma aux_lem_borel_weights_limit_of_approx (a : ℕ → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ b : ℕ → ℝ, (∃ l, Tendsto b atTop (𝓝 l)) ∧
      ∀ n, |a n - b n| ≤ ε) :
    ∃ l, Tendsto a atTop (𝓝 l) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨b, ⟨l, hl⟩, hab⟩ := h (ε / 3) (by positivity)
  have hbc := hl.cauchySeq
  rw [Metric.cauchySeq_iff'] at hbc
  obtain ⟨N, hN⟩ := hbc (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq] at h1 ⊢
  have h2 := abs_le.1 (hab n)
  have h3 := abs_le.1 (hab N)
  have h1' := abs_lt.1 h1
  exact abs_lt.2 ⟨by linarith, by linarith⟩

omit [CompleteSpace H] in
/-- An operator is determined by its matrix on a dense sequence. -/
lemma aux_lem_borel_weights_ext_dense (e : ℕ → H) (he : DenseRange e)
    (T S : H →L[ℝ] H) (h : ∀ i j, inner ℝ (e i) (T (e j)) = inner ℝ (e i) (S (e j))) :
    T = S := by
  have hcol : ∀ j, T (e j) = S (e j) := by
    intro j
    have hz : ∀ y : H, inner ℝ y (T (e j) - S (e j)) = 0 := by
      intro y
      have hcl : IsClosed {y : H | inner ℝ y (T (e j) - S (e j)) = 0} :=
        isClosed_eq (continuous_id.inner continuous_const) continuous_const
      have hsub : range e ⊆ {y : H | inner ℝ y (T (e j) - S (e j)) = 0} := by
        rintro _ ⟨i, rfl⟩
        simp [inner_sub_right, h i j]
      have := hcl.closure_subset_iff.2 hsub
      rw [he.closure_range] at this
      exact this (mem_univ y)
    have := hz (T (e j) - S (e j))
    rw [real_inner_self_eq_norm_sq] at this
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))
  have hfun : (T : H → H) = S :=
    he.equalizer T.continuous S.continuous (funext fun j => hcol j)
  ext g
  exact congrFun hfun g

/-- Pointwise limits of uniformly bounded operator matrices on a dense sequence are
matrices of operators. -/
lemma aux_lem_borel_weights_closure_matrix (e : ℕ → H) (he : DenseRange e) (K : ℝ)
    (x : ℕ × ℕ → ℝ)
    (hx : x ∈ closure ((fun T : H →L[ℝ] H => fun p : ℕ × ℕ => inner ℝ (e p.1) (T (e p.2))) ''
      Metric.closedBall (0 : H →L[ℝ] H) K)) :
    ∃ T : H →L[ℝ] H, ∀ p : ℕ × ℕ, x p = inner ℝ (e p.1) (T (e p.2)) := by
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.1 hx
  choose T hTK hTy using hy
  have hTn : ∀ n, ‖T n‖ ≤ K := fun n => by simpa using hTK n
  have hK : 0 ≤ K := (norm_nonneg _).trans (hTn 0)
  have hcoord : ∀ i j, Tendsto (fun n => inner ℝ (e i) (T n (e j))) atTop (𝓝 (x (i, j))) := by
    intro i j
    have h := tendsto_pi_nhds.1 hlim (i, j)
    simpa [← hTy] using h
  have hbnd : ∀ n (f g : H), |inner ℝ f (T n g)| ≤ K * ‖f‖ * ‖g‖ := by
    intro n f g
    calc |inner ℝ f (T n g)| ≤ ‖f‖ * ‖T n g‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖f‖ * (K * ‖g‖) :=
          mul_le_mul_of_nonneg_left ((T n).le_of_opNorm_le (hTn n) g) (norm_nonneg _)
      _ = K * ‖f‖ * ‖g‖ := by ring
  have hstep1 : ∀ (f : H) (j : ℕ), ∃ l, Tendsto (fun n => inner ℝ f (T n (e j))) atTop (𝓝 l) := by
    intro f j
    apply aux_lem_borel_weights_limit_of_approx
    intro ε hε
    obtain ⟨i, hi⟩ := Metric.denseRange_iff.1 he f (ε / (K * ‖e j‖ + 1)) (by positivity)
    refine ⟨fun n => inner ℝ (e i) (T n (e j)), ⟨_, hcoord i j⟩, fun n => ?_⟩
    rw [← inner_sub_left]
    have hd : dist f (e i) * (K * ‖e j‖ + 1) < ε := (lt_div_iff₀ (by positivity)).1 hi
    rw [dist_eq_norm] at hd
    calc |inner ℝ (f - e i) (T n (e j))| ≤ K * ‖f - e i‖ * ‖e j‖ := hbnd n _ _
      _ = ‖f - e i‖ * (K * ‖e j‖) := by ring
      _ ≤ ‖f - e i‖ * (K * ‖e j‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ ≤ ε := hd.le
  have hstep2 : ∀ f g : H, ∃ l, Tendsto (fun n => inner ℝ f (T n g)) atTop (𝓝 l) := by
    intro f g
    apply aux_lem_borel_weights_limit_of_approx
    intro ε hε
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 he g (ε / (K * ‖f‖ + 1)) (by positivity)
    obtain ⟨l, hl⟩ := hstep1 f j
    refine ⟨fun n => inner ℝ f (T n (e j)), ⟨l, hl⟩, fun n => ?_⟩
    rw [← inner_sub_right, ← map_sub]
    have hd : dist g (e j) * (K * ‖f‖ + 1) < ε := (lt_div_iff₀ (by positivity)).1 hj
    rw [dist_eq_norm] at hd
    calc |inner ℝ f (T n (g - e j))| ≤ K * ‖f‖ * ‖g - e j‖ := hbnd n _ _
      _ = ‖g - e j‖ * (K * ‖f‖) := by ring
      _ ≤ ‖g - e j‖ * (K * ‖f‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ ≤ ε := hd.le
  choose b hb using hstep2
  have hbadd : ∀ f g g', b f (g + g') = b f g + b f g' := by
    intro f g g'
    refine tendsto_nhds_unique (hb f (g + g')) ?_
    simpa [map_add, inner_add_right] using (hb f g).add (hb f g')
  have hbsmul : ∀ (f g : H) (c : ℝ), b f (c • g) = c * b f g := by
    intro f g c
    refine tendsto_nhds_unique (hb f (c • g)) ?_
    simpa [map_smul, real_inner_smul_right] using (hb f g).const_mul c
  have hbabs : ∀ f g, |b f g| ≤ K * ‖f‖ * ‖g‖ := fun f g =>
    le_of_tendsto' (hb f g).abs fun n => hbnd n f g
  have hβ : ∀ g : H, ∃ β : H →L[ℝ] ℝ, ∀ f, β f = b f g := by
    intro g
    refine ⟨ContinuousLinearMap.ofTendstoOfBoundedRange (l := (atTop : Filter ℕ)) (fun f => b f g)
      (fun n => innerSL ℝ (T n g)) ?_ ?_, fun f => rfl⟩
    · rw [tendsto_pi_nhds]
      intro f
      simpa [innerSL_apply_apply, real_inner_comm] using hb f g
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨K * ‖g‖, ?_⟩
      rintro _ ⟨n, rfl⟩
      rw [innerSL_apply_norm]
      exact (T n).le_of_opNorm_le (hTn n) g
  choose β hβ using hβ
  set w : H → H := fun g => (InnerProductSpace.toDual ℝ H).symm (β g) with hw
  have hwinner : ∀ g f, inner ℝ (w g) f = b f g := by
    intro g f
    rw [hw]
    simp only
    rw [InnerProductSpace.toDual_symm_apply, hβ]
  have hwnorm : ∀ g, ‖w g‖ ≤ K * ‖g‖ := by
    intro g
    rw [hw]
    simp only
    rw [LinearIsometryEquiv.norm_map]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
    rw [hβ, Real.norm_eq_abs]
    have := hbabs f g
    linarith [this, mul_comm (K * ‖g‖) ‖f‖, show K * ‖f‖ * ‖g‖ = K * ‖g‖ * ‖f‖ by ring]
  let T0 : H →ₗ[ℝ] H :=
    { toFun := w
      map_add' := by
        intro g g'
        refine ext_inner_right ℝ fun f => ?_
        rw [hwinner, inner_add_left, hwinner, hwinner, hbadd]
      map_smul' := by
        intro c g
        refine ext_inner_right ℝ fun f => ?_
        rw [hwinner, RingHom.id_apply, real_inner_smul_left, hwinner, hbsmul] }
  refine ⟨T0.mkContinuous K hwnorm, fun p => ?_⟩
  rw [LinearMap.mkContinuous_apply]
  change x p = inner ℝ (e p.1) (w (e p.2))
  rw [real_inner_comm, hwinner]
  exact tendsto_nhds_unique (hcoord p.1 p.2) (hb _ _)

/-- A `Rem`-measurable operator version from `Rem`-measurable versions of the matrix of
`G` on a dense sequence.  The version is defined on the `Rem`-measurable set of matrices
that are matrices of operators (a countable union of closures of operator balls). -/
lemma aux_lem_borel_weights_operator_version {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (Rem : MeasurableSpace Ω) (G : Ω → H →L[ℝ] H) (e : ℕ → H) (he : DenseRange e)
    (ψ : ℕ × ℕ → Ω → ℝ) (hψ : ∀ p, Measurable[Rem] (ψ p))
    (hψG : ∀ p, ψ p =ᵐ[P] fun om => inner ℝ (e p.1) (G om (e p.2))) :
    ∃ Gv : Ω → H →L[ℝ] H, Gv =ᵐ[P] G ∧
      ∀ f g : H, Measurable[Rem] fun om => inner ℝ f (Gv om g) := by
  classical
  set Φ : (H →L[ℝ] H) → (ℕ × ℕ → ℝ) := fun T p => inner ℝ (e p.1) (T (e p.2)) with hΦ
  set Ψ : Ω → ℕ × ℕ → ℝ := fun om p => ψ p om with hΨ
  set R : Set Ω := {om | ∃ T : H →L[ℝ] H, ∀ p, Ψ om p = Φ T p} with hR
  have hRset : R = Ψ ⁻¹' ⋃ K : ℕ, closure (Φ '' Metric.closedBall 0 (K : ℝ)) := by
    ext om
    simp only [hR, mem_ofPred_eq, mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨T, hT⟩
      obtain ⟨K, hK⟩ := exists_nat_ge ‖T‖
      exact ⟨K, subset_closure ⟨T, by simpa using hK, funext fun p => (hT p).symm⟩⟩
    · rintro ⟨K, hK⟩
      exact aux_lem_borel_weights_closure_matrix e he K (Ψ om) hK
  have hΨmeas : Measurable[Rem] Ψ :=
    @Measurable.of_eval Ω (ℕ × ℕ) (fun _ => ℝ) Rem _ Ψ (fun p => hψ p)
  have hRmeas : MeasurableSet[Rem] R := by
    rw [hRset]
    exact hΨmeas (MeasurableSet.iUnion fun K => isClosed_closure.measurableSet)
  let Gv : Ω → H →L[ℝ] H := fun om =>
    if h : ∃ T : H →L[ℝ] H, ∀ p, Ψ om p = Φ T p then h.choose else 0
  have hGvR : ∀ om ∈ R, ∀ p, Ψ om p = Φ (Gv om) p := by
    intro om hom p
    show Ψ om p = Φ (if h : ∃ T : H →L[ℝ] H, ∀ p, Ψ om p = Φ T p then h.choose else 0) p
    have hom' : ∃ T : H →L[ℝ] H, ∀ p, Ψ om p = Φ T p := hom
    rw [dite_eq_left hom']
    exact hom'.choose_spec p
  have hGvnR : ∀ om ∉ R, Gv om = 0 := by
    intro om hom
    simp only [Gv]
    exact dite_eq_right hom
  have hentry : ∀ i j, (fun om => inner ℝ (e i) (Gv om (e j))) = R.indicator (ψ (i, j)) := by
    intro i j
    funext om
    by_cases hom : om ∈ R
    · rw [indicator_of_mem hom]
      exact (hGvR om hom (i, j)).symm
    · rw [indicator_of_notMem hom, hGvnR om hom]
      simp
  refine ⟨Gv, ?_, ?_⟩
  · have hall : ∀ᵐ om ∂P, ∀ p, ψ p om = inner ℝ (e p.1) (G om (e p.2)) := ae_all_iff.2 hψG
    filter_upwards [hall] with om hom
    have homR : om ∈ R := ⟨G om, hom⟩
    apply aux_lem_borel_weights_ext_dense e he
    intro i j
    rw [← hom (i, j)]
    exact (hGvR om homR (i, j)).symm
  · intro f g
    have hf : f ∈ closure (range e) := he.closure_range.symm ▸ mem_univ f
    have hg : g ∈ closure (range e) := he.closure_range.symm ▸ mem_univ g
    obtain ⟨xs, hxs, hxlim⟩ := mem_closure_iff_seq_limit.1 hf
    obtain ⟨ys, hys, hylim⟩ := mem_closure_iff_seq_limit.1 hg
    choose i hi using hxs
    choose j hj using hys
    have hmk : ∀ k, Measurable[Rem] fun om => inner ℝ (e (i k)) (Gv om (e (j k))) := by
      intro k
      rw [hentry]
      exact (hψ (i k, j k)).indicator hRmeas
    have hlim : Tendsto (fun k om => inner ℝ (e (i k)) (Gv om (e (j k)))) atTop
        (𝓝 fun om => inner ℝ f (Gv om g)) := by
      rw [tendsto_pi_nhds]
      intro om
      have h1 : Tendsto (fun k => e (i k)) atTop (𝓝 f) := by
        simpa only [hi] using hxlim
      have h2 : Tendsto (fun k => e (j k)) atTop (𝓝 g) := by
        simpa only [hj] using hylim
      exact h1.inner (((Gv om).continuous.tendsto g).comp h2)
    exact @measurable_of_tendsto_metrizable Ω ℝ Rem _ _ _ _ _ _ hmk hlim

end OperatorVersion

/-- Signed integrals only see where the signed measure lives: if `ν` vanishes on all
measurable subsets of `S`, integrands agreeing off `S` have equal signed integrals. -/
lemma aux_lem_borel_weights_signedIntegralOn_congr_off {X : Type*} [MeasurableSpace X]
    (ν : SignedMeasure X) (S : Set X) (hS : MeasurableSet S)
    (h0 : ∀ B, MeasurableSet B → B ⊆ S → ν B = 0) (f g : X → ℝ)
    (hfg : ∀ x ∉ S, f x = g x) (B : Set X) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B f = _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ν B g := by
  set j := ν.toJordanDecomposition with hj
  have hν : ∀ A, MeasurableSet A → ν A = (j.posPart A).toReal - (j.negPart A).toReal := by
    intro A hA
    conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition ν]
    rw [JordanDecomposition.toSignedMeasure, sub_apply,
      Measure.toSignedMeasure_apply_measurable hA, Measure.toSignedMeasure_apply_measurable hA]
    rfl
  obtain ⟨T, hT, hpT, hnT⟩ := j.mutuallySingular
  have hpos : j.posPart S = 0 := by
    have h1 : j.posPart (S ∩ T) = 0 := measure_mono_null inter_subset_right hpT
    have h2 : j.posPart (S \ T) = 0 := by
      have hn : j.negPart (S \ T) = 0 := measure_mono_null (fun x hx => hx.2) hnT
      have h := hν (S \ T) (hS.diff hT)
      rw [h0 _ (hS.diff hT) sdiff_subset, hn, ENNReal.toReal_zero, sub_zero] at h
      exact ((ENNReal.toReal_eq_zero_iff _).1 h.symm).resolve_right (measure_ne_top _ _)
    rw [← measure_inter_add_sdiff S hT, h1, h2, add_zero]
  have hneg : j.negPart S = 0 := by
    have h1 : j.negPart (S \ T) = 0 := measure_mono_null (fun x hx => hx.2) hnT
    have h2 : j.negPart (S ∩ T) = 0 := by
      have hp : j.posPart (S ∩ T) = 0 := measure_mono_null inter_subset_right hpT
      have h := hν (S ∩ T) (hS.inter hT)
      rw [h0 _ (hS.inter hT) inter_subset_left, hp, ENNReal.toReal_zero, zero_sub,
        zero_eq_neg] at h
      exact ((ENNReal.toReal_eq_zero_iff _).1 h).resolve_right (measure_ne_top _ _)
    rw [← measure_inter_add_sdiff S hT, h1, h2, add_zero]
  have hpae : ∀ᵐ x ∂j.posPart, f x = g x := by
    have : ∀ᵐ x ∂j.posPart, x ∉ S := measure_eq_zero_iff_ae_notMem.1 hpos
    filter_upwards [this] with x hx using hfg x hx
  have hnae : ∀ᵐ x ∂j.negPart, f x = g x := by
    have : ∀ᵐ x ∂j.negPart, x ∉ S := measure_eq_zero_iff_ae_notMem.1 hneg
    filter_upwards [this] with x hx using hfg x hx
  simp only [_root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn]
  rw [integral_congr_ae (ae_restrict_of_ae hpae), integral_congr_ae (ae_restrict_of_ae hnae)]




theorem lem_borel_weights
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (hg : Measurable g)
    (M : ℝ) (hgbdd : ∀ x : SpatialCoordinates d, |g x| ≤ M)
    (hreg : _root_.SubdiffusiveProcess.DirichletForm.IsRegular E.toClosedForm)
    (hloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal E.toClosedForm)
    (hcoreQ : ∃ C : Set (Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))),
      _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E.toClosedForm (Q : Set (SpatialCoordinates d)) C)
    (halg : _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra E.toClosedForm) :
    (∃ (Eg : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
        (Gammag : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Eg.toClosedForm),
        Eg.toClosedForm.domain = E.toClosedForm.domain ∧
        (∀ u ∈ E.toClosedForm.domain, ∀ v ∈ E.toClosedForm.domain,
          Eg.toClosedForm.form u v =
            _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
              (fun x => Real.exp (g x))) ∧
        _root_.SubdiffusiveProcess.DirichletForm.IsRegular Eg.toClosedForm ∧
        _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal Eg.toClosedForm ∧
        (∀ u ∈ E.toClosedForm.domain, ∀ v ∈ E.toClosedForm.domain,
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            Gammag.cross u v B =
              _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) B
                (fun x => Real.exp (g x)))) ∧
      (∀ (Omega : Type) [MeasurableSpace Omega]
        (P : Measure Omega) (_hP : IsProbabilityMeasure P)
        (Rem : MeasurableSpace Omega) (_hRem : Rem ≤ (inferInstance : MeasurableSpace Omega))
        (S : ResponseSpace Q) (_hS : S.space = killedSobolevGraph Q)
        (a aDeleted : ℕ → Omega → PositiveCoefficient Q)
        (seq : ℕ → ℕ) (_hseq : StrictMono seq)
        (Er : Omega → _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
        (GammaR : ∀ omega, _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure (Er omega).toClosedForm)
        (Gbase Gdeleted : Omega → DomainL2 Q →L[ℝ] DomainL2 Q)
        (ell : Omega → SpatialCoordinates d → ℝ)
        (_hell : ∀ omega, ContinuousOn (ell omega) (closure (Q : Set (SpatialCoordinates d))) ∧
          ∃ K : ℝ, ∀ x ∈ (Q : Set (SpatialCoordinates d)), |ell omega x| ≤ K)
        (_hdeleted : ∀ N omega, ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          (aDeleted N omega).val x = Real.exp (-ell omega x) * (a N omega).val x)
        (_hbase : ∀ᵐ omega ∂P, ∀ u,
          (Er omega).toClosedForm.energy u = limitFormEnergy (Gbase omega) u)
        (_hbaseconv : ∀ f : DomainL2 Q, TendstoInMeasure P
          (fun n omega => inverseResponse S (a (seq n) omega)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
          (fun omega => inner ℝ f (Gbase omega f)))
        (_hregular : ∀ᵐ omega ∂P,
          _root_.SubdiffusiveProcess.DirichletForm.IsRegular (Er omega).toClosedForm ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal (Er omega).toClosedForm ∧
          _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra (Er omega).toClosedForm ∧
          (∃ C : Set (DomainL2 Q),
            _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn (Er omega).toClosedForm (Q : Set (SpatialCoordinates d)) C) ∧
          (∀ u ∈ (Er omega).toClosedForm.domain,
            (GammaR omega).measure u (Q : Set (SpatialCoordinates d))ᶜ = 0))
        (_hweightedInverse : ∀ᵐ omega ∂P,
          (∀ f g : DomainL2 Q, inner ℝ f (Gdeleted omega g) =
            inner ℝ (Gdeleted omega f) g) ∧
          Function.Injective (Gdeleted omega) ∧
          (∀ f : DomainL2 Q, IsLUB {t : ℝ | ∃ u : DomainL2 Q,
            u ∈ (Er omega).toClosedForm.domain ∧
            t = 2 * inner ℝ f u - ∫ x in (Q : Set (SpatialCoordinates d)),
              Real.exp (-ell omega x) ∂((GammaR omega).measure u)}
            (inner ℝ f (Gdeleted omega f))))
        (_hweightedConv : ∀ f : DomainL2 Q, TendstoInMeasure P
          (fun n omega => inverseResponse S (aDeleted (seq n) omega)
            ((sobolevVolumeLoad f).comp S.space.subtypeL)) atTop
          (fun omega => inner ℝ f (Gdeleted omega f)))
        (N0 : ℕ)
        (_hfiniteRem : ∀ N, N0 ≤ N → ∀ f : DomainL2 Q,
          @Measurable Omega ℝ Rem _ (fun omega => inverseResponse S (aDeleted N omega)
            ((sobolevVolumeLoad f).comp S.space.subtypeL))),
        ∃ Gversion : Omega → DomainL2 Q →L[ℝ] DomainL2 Q,
          (Gversion =ᵐ[P] Gdeleted) ∧
          (∀ f g : DomainL2 Q, @Measurable Omega ℝ Rem _
            (fun omega => inner ℝ f (Gversion omega g))) ∧
          (∀ᵐ omega ∂P,
            ∃ (Edeleted : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
              (GammaDeleted : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure Edeleted.toClosedForm),
              Edeleted.toClosedForm.domain = (Er omega).toClosedForm.domain ∧
              (∀ u : DomainL2 Q,
                Edeleted.toClosedForm.energy u = limitFormEnergy (Gversion omega) u) ∧
              (∀ u ∈ (Er omega).toClosedForm.domain,
                ∀ v ∈ (Er omega).toClosedForm.domain,
                Edeleted.toClosedForm.form u v =
                  _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ((GammaR omega).cross u v) Set.univ
                    (fun x => Real.exp (-ell omega x))) ∧
              _root_.SubdiffusiveProcess.DirichletForm.IsRegular Edeleted.toClosedForm ∧
              _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal Edeleted.toClosedForm ∧
              (∀ u ∈ (Er omega).toClosedForm.domain,
                ∀ v ∈ (Er omega).toClosedForm.domain,
                ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
                  GammaDeleted.cross u v B =
                    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ((GammaR omega).cross u v) B
                      (fun x => Real.exp (-ell omega x))))) := by
  constructor
  · obtain ⟨Eg, Gammag, hdom, hform, hregg, _hcore, hlocg, hGamma⟩ :=
      lem_borel_weights_form E Gamma g hg M hgbdd hreg hcoreQ hloc halg
    exact ⟨Eg, Gammag, hdom, hform, hregg, hlocg, hGamma⟩
  · intro Omega _ P _hP Rem _hRem S _hS a aDeleted seq hseq Er GammaR _Gbase Gdeleted ell hell
      _hdeleted _hbase _hbaseconv hregular hweightedInverse hweightedConv N0 hfiniteRem
    -- Remaining-layer versions of the determining quadratic responses.
    have hver : ∀ h : DomainL2 Q, ∃ φ : Omega → ℝ, Measurable[Rem] φ ∧
        φ =ᵐ[P] fun om => inner ℝ h (Gdeleted om h) := by
      intro h
      refine aux_lem_borel_weights_rem_version P Rem _ _ N0 (fun n hn => ?_) (hweightedConv h)
      exact hfiniteRem (seq n) (hn.trans (hseq.id_le n)) h
    choose φ hφmeas hφae using hver
    have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
    obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq (DomainL2 Q)
    -- Polarization on the countable dense family.
    set ψ : ℕ × ℕ → Omega → ℝ := fun p om =>
      (φ (e p.1 + e p.2) om - φ (e p.1 - e p.2) om) / 4 with hψdef
    have hψmeas : ∀ p, Measurable[Rem] (ψ p) := fun p =>
      ((hφmeas _).sub (hφmeas _)).div_const 4
    have hsymm : ∀ᵐ om ∂P, ∀ f g : DomainL2 Q,
        inner ℝ f (Gdeleted om g) = inner ℝ (Gdeleted om f) g :=
      hweightedInverse.mono fun om h => h.1
    have hψae : ∀ p, ψ p =ᵐ[P] fun om => inner ℝ (e p.1) (Gdeleted om (e p.2)) := by
      intro p
      filter_upwards [hφae (e p.1 + e p.2), hφae (e p.1 - e p.2), hsymm] with om h1 h2 h3
      have hs : inner ℝ (e p.2) (Gdeleted om (e p.1)) = inner ℝ (e p.1) (Gdeleted om (e p.2)) := by
        rw [h3]
        exact real_inner_comm _ _
      simp only [hψdef]
      rw [h1, h2]
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right]
      rw [hs]
      ring
    obtain ⟨Gv, hGvae, hGvmeas⟩ :=
      aux_lem_borel_weights_operator_version P Rem Gdeleted e he ψ hψmeas hψae
    refine ⟨Gv, hGvae, hGvmeas, ?_⟩
    filter_upwards [hregular, hweightedInverse, hGvae] with om hreg hinv hGv
    obtain ⟨hregR, hlocR, halgR, hcoreR, hsuppR⟩ := hreg
    obtain ⟨-, -, hLUB⟩ := hinv
    classical
    obtain ⟨hcont, K, hK⟩ := hell om
    set gom : SpatialCoordinates d → ℝ :=
      (Q : Set (SpatialCoordinates d)).piecewise (fun x => -ell om x) (fun _ => 0) with hgomdef
    have hQmeas : MeasurableSet (Q : Set (SpatialCoordinates d)) := Q.isOpen.measurableSet
    have hgmeas : Measurable gom :=
      ContinuousOn.measurable_piecewise (hcont.mono subset_closure).neg continuousOn_const
        hQmeas
    have hgbdd : ∀ x, |gom x| ≤ |K| := by
      intro x
      by_cases hx : x ∈ (Q : Set (SpatialCoordinates d))
      · rw [hgomdef, piecewise_eq_of_mem _ _ _ hx, abs_neg]
        exact (hK x hx).trans (le_abs_self K)
      · rw [hgomdef, piecewise_eq_of_notMem _ _ _ hx, abs_zero]
        exact abs_nonneg K
    have hgQ : ∀ x ∈ (Q : Set (SpatialCoordinates d)), gom x = -ell om x := fun x hx => by
      rw [hgomdef, piecewise_eq_of_mem _ _ _ hx]
    obtain ⟨Ed, Gd, hdom, hform, hregd, _hcored, hlocd, hGamma⟩ :=
      lem_borel_weights_form (Er om) (GammaR om) gom hgmeas |K| hgbdd hregR hcoreR hlocR halgR
    -- The random energy measures live on `Q`.
    have hswap : ∀ u ∈ (Er om).toClosedForm.domain, ∀ v ∈ (Er om).toClosedForm.domain,
        ∀ B : Set (SpatialCoordinates d),
          _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ((GammaR om).cross u v) B (fun x => Real.exp (gom x)) =
            _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn ((GammaR om).cross u v) B
              (fun x => Real.exp (-ell om x)) := by
      intro u hu v hv B
      refine aux_lem_borel_weights_signedIntegralOn_congr_off _ _ hQmeas.compl ?_ _ _ ?_ B
      · intro A hA hAQ
        have hu0 : (GammaR om).measure u A = 0 := measure_mono_null hAQ (hsuppR u hu)
        have hv0 : (GammaR om).measure v A = 0 := measure_mono_null hAQ (hsuppR v hv)
        have h := (GammaR om).abs_cross_le u hu v hv A hA
        rw [hu0, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at h
        exact abs_nonpos_iff.1 h
      · intro x hx
        rw [hgQ x (not_not.1 hx)]
    have hdiag : ∀ u ∈ (Er om).toClosedForm.domain, Ed.toClosedForm.form u u =
        ∫ x in (Q : Set (SpatialCoordinates d)), Real.exp (-ell om x) ∂((GammaR om).measure u) := by
      intro u hu
      have : IsFiniteMeasure ((GammaR om).measure u) :=
        ⟨(GammaR om).measure_univ_lt_top u hu⟩
      have hcs : (GammaR om).cross u u = ((GammaR om).measure u).toSignedMeasure := by
        ext B hB
        rw [(GammaR om).cross_self u hu B hB, Measure.toSignedMeasure_apply_measurable hB]
        rfl
      have hexpb : ∀ x, |Real.exp (gom x)| ≤ Real.exp |K| := by
        intro x
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans (hgbdd x))
      have hae : ∀ᵐ x ∂((GammaR om).measure u), x ∈ (Q : Set (SpatialCoordinates d)) :=
        ae_iff.2 (hsuppR u hu)
      rw [hform u hu u hu, hcs,
        aux_lem_borel_weights_closed_core_signed_to_measure _ hgmeas.exp hexpb]
      have h1 : ∫ x, Real.exp (gom x) ∂((GammaR om).measure u) =
          ∫ x in (Q : Set (SpatialCoordinates d)), Real.exp (gom x) ∂((GammaR om).measure u) := by
        rw [Measure.restrict_eq_self_of_ae_mem hae]
      rw [h1]
      exact setIntegral_congr_fun hQmeas fun x hx => by
        show Real.exp (gom x) = Real.exp (-ell om x)
        rw [hgQ x hx]
    refine ⟨Ed, Gd, hdom, ?_, ?_, hregd, hlocd, ?_⟩
    · intro u
      rw [hGv]
      have hLUB' : ∀ f : DomainL2 Q, IsLUB {t : ℝ | ∃ w : DomainL2 Q,
          w ∈ Ed.toClosedForm.domain ∧ t = 2 * inner ℝ f w - Ed.toClosedForm.form w w}
          (inner ℝ f (Gdeleted om f)) := by
        intro f
        have hset : {t : ℝ | ∃ w : DomainL2 Q,
            w ∈ Ed.toClosedForm.domain ∧ t = 2 * inner ℝ f w - Ed.toClosedForm.form w w} =
            {t : ℝ | ∃ u : DomainL2 Q, u ∈ (Er om).toClosedForm.domain ∧
              t = 2 * inner ℝ f u - ∫ x in (Q : Set (SpatialCoordinates d)),
                Real.exp (-ell om x) ∂((GammaR om).measure u)} := by
          ext t
          simp only [mem_ofPred_eq, hdom]
          constructor
          · rintro ⟨w, hw, rfl⟩
            exact ⟨w, hw, by rw [hdiag w hw]⟩
          · rintro ⟨w, hw, rfl⟩
            exact ⟨w, hw, by rw [hdiag w hw]⟩
        rw [hset]
        exact hLUB f
      exact aux_lem_borel_weights_energy_eq_dual Ed.toClosedForm (Gdeleted om) hLUB' u
    · intro u hu v hv
      rw [hform u hu v hv, hswap u hu v hv]
    · intro u hu v hv B hB
      rw [hGamma u hu v hv B hB, hswap u hu v hv]

end SubdiffusiveProcess.Paper
