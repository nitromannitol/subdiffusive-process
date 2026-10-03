module

public import SubdiffusiveProcess.Paper.prop_speed_resolvent
public import SubdiffusiveProcess.Analysis.QuadraticMinimizerContinuity

@[expose] public section

/-! Supports: mfd_lem_killing.
Continuity of the full finite-energy minimizer, with the midpoint gap discharged
by the actual quadratic form algebra and coercivity. These are internal data
produced from the killed inverse, not premises of the paper lemma.
-/
open Filter MeasureTheory Topology
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_mfd_lem_killing_continuous_form_minimizer
    {X V W : Type*} [TopologicalSpace X] [SequentialSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (E : V → ℝ≥0∞) (A : V → W)
    (hE0 : E 0 = 0)
    (hclosed : ∀ (c : ℝ) (a b : V), E a ≠ ⊤ → E b ≠ ⊤ → E (c • a + b) ≠ ⊤)
    (hpara : ∀ a b, E a ≠ ⊤ → E b ≠ ⊤ →
      (E (a + b)).toReal + (E (a - b)).toReal = 2 * (E a).toReal + 2 * (E b).toReal)
    (hscale : ∀ (c : ℝ) (a : V), E a ≠ ⊤ → E (c • a) = ENNReal.ofReal (c ^ 2) * E a)
    (hAlin : ∀ (c : ℝ) (a b : V), E a ≠ ⊤ → E b ≠ ⊤ → A (c • a + b) = c • A a + A b)
    (C : ℝ) (hC : 0 < C)
    (hcoer : ∀ v, E v ≠ ⊤ → ‖v‖ ^ 2 ≤ C * (E v).toReal)
    (lam : X → ℝ) (g : X → W) (u : X → V)
    (hlam : ∀ x, 0 < lam x) (hlamc : Continuous lam) (hgc : Continuous g)
    (hu : ∀ x, E (u x) ≠ ⊤)
    (humin : ∀ x v, E v ≠ ⊤ →
      (E (u x)).toReal + lam x * ‖A (u x)‖ ^ 2 - 2 * ⟪g x, A (u x)⟫_ℝ ≤
        (E v).toReal + lam x * ‖A v‖ ^ 2 - 2 * ⟪g x, A v⟫_ℝ) : Continuous u := by
  have hz : E (0 : V) ≠ ⊤ := by rw [hE0]; exact ENNReal.zero_ne_top
  have hA0 : A 0 = 0 := by
    have h := hAlin 1 0 0 hz hz
    simp only [one_smul, zero_add] at h
    exact (add_left_cancel (show A 0 + 0 = A 0 + A 0 by rw [add_zero]; exact h)).symm
  let mid := fun x y => (1 / 2 : ℝ) • (u x + u y)
  have hsum (x y : X) : E (u x + u y) ≠ ⊤ := by simpa using hclosed 1 _ _ (hu x) (hu y)
  have hdiff (x y : X) : E (u x - u y) ≠ ⊤ := by
    simpa only [neg_one_smul, neg_add_eq_sub] using hclosed (-1) (u y) (u x) (hu y) (hu x)
  have hmid (x y : X) : E (mid x y) ≠ ⊤ := by
    simpa only [mid, add_zero] using hclosed (1 / 2) (u x + u y) 0 (hsum x y) hz
  have hgap (x y : X) : (1 / (4 * C)) * ‖u x - u y‖ ^ 2 ≤
      (((E (u x)).toReal + lam x * ‖A (u x)‖ ^ 2 - 2 * ⟪g x, A (u x)⟫_ℝ) +
        ((E (u y)).toReal + lam x * ‖A (u y)‖ ^ 2 - 2 * ⟪g x, A (u y)⟫_ℝ)) / 2 -
        ((E (mid x y)).toReal + lam x * ‖A (mid x y)‖ ^ 2 - 2 * ⟪g x, A (mid x y)⟫_ℝ) := by
    have hhalf : (E ((1 / 2 : ℝ) • (u x - u y))).toReal =
        (1 / 4 : ℝ) * (E (u x - u y)).toReal := by
      rw [hscale (1 / 2) _ (hdiff x y), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 / 2 : ℝ) ^ 2)]
      ring
    have hcb : ‖u x - u y‖ ^ 2 ≤ (4 * C) * (E ((1 / 2 : ℝ) • (u x - u y))).toReal := by
      rw [hhalf]
      nlinarith [hcoer (u x - u y) (hdiff x y)]
    have hcb' : (1 / (4 * C)) * ‖u x - u y‖ ^ 2 ≤
        (E ((1 / 2 : ℝ) • (u x - u y))).toReal := by
      rw [one_div_mul_eq_div]
      exact (div_le_iff₀ (by positivity : 0 < 4 * C)).mpr (by simpa only [mul_comm] using hcb)
    have hidentity := aux_prop_speed_resolvent_midpoint E A (g x) (lam x)
      hE0 hclosed hpara hscale hAlin (u x) (u y) (hu x) (hu y)
    change (E (mid x y)).toReal + lam x * ‖A (mid x y)‖ ^ 2 -
      2 * ⟪g x, A (mid x y)⟫_ℝ = _ at hidentity
    have hnon : 0 ≤ lam x * ‖A ((1 / 2 : ℝ) • (u x - u y))‖ ^ 2 :=
      mul_nonneg (hlam x).le (sq_nonneg _)
    linarith
  exact SubdiffusiveProcess.Analysis.continuous_minimizer_of_quadratic_gap
    (fun v => (E v).toReal) A {v | E v ≠ ⊤} lam g u mid
    (1 / (4 * C)) (by positivity) hlam hlamc hgc hz (by
      change (E 0).toReal = 0
      rw [hE0, ENNReal.toReal_zero]) hA0
    (fun v _ => ENNReal.toReal_nonneg) hu hmid humin hgap

end Paper
