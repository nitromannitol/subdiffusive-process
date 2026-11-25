module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Uniqueness of the Laplace transform

A function `f` that is continuous and bounded on `[0, ∞)` and whose Laplace transform vanishes at
every `λ = n + 1`, `n ∈ ℕ`, vanishes on `[0, ∞)`.

A smooth test function `g` with compact support in `(0, ∞)` is written as `g t = e^{-t} G(e^{-t})`
with `G` continuous on `[0, 1]`. Uniform approximation of `G` by polynomials (Weierstrass) and the
vanishing of the moments `∫ e^{-(n+1)t} f(t) dt` give `∫ g f = 0`, so `f = 0` almost everywhere on
`(0, ∞)` by the fundamental lemma of the calculus of variations, hence everywhere on `[0, ∞)` by
continuity.

## Main statements

* `integrableOn_exp_mul_of_abs_le`: integrability of `e^{-a t} f(t)` on `(0, ∞)`;
* `eqOn_zero_of_laplace_eq_zero`: the uniqueness theorem.
-/

@[expose] public section

namespace SubdiffusiveProcess.SDE

open MeasureTheory Set Filter Real Polynomial
open scoped Topology ContDiff

/-- A function bounded on `(0, ∞)` times a decaying exponential is integrable there. -/
theorem integrableOn_exp_mul_of_abs_le {f : ℝ → ℝ} {a C : ℝ} (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hC : ∀ t ∈ Ioi (0 : ℝ), |f t| ≤ C) :
    IntegrableOn (fun t => exp (-a * t) * f t) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 ha).const_mul C).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => exp (-a * t)).aestronglyMeasurable.mul hf
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC t ht) (exp_pos _).le

/-- For `q` continuous on `[0, 1]` and `f` bounded on `(0, ∞)`, the function
`t ↦ e^{-t} q(e^{-t}) f(t)` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_comp_mul {q f : ℝ → ℝ} (hq : ContinuousOn q (Icc 0 1)) {C : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hC : ∀ t ∈ Ioi (0 : ℝ), |f t| ≤ C) :
    IntegrableOn (fun t => exp (-t) * q (exp (-t)) * f t) (Ioi 0) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  have hmem : ∀ t ∈ Ioi (0 : ℝ), exp (-t) ∈ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨(exp_pos _).le, exp_le_one_iff.2 (by linarith only [ht.out])⟩
  have hqc : ContinuousOn (fun t => q (exp (-t))) (Ioi 0) :=
    hq.comp (by fun_prop : Continuous fun t : ℝ => exp (-t)).continuousOn fun t ht => hmem t ht
  refine ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul (M * C)).mono' ?_ ?_
  · exact ((by fun_prop : Continuous fun t : ℝ => exp (-t)).aestronglyMeasurable.mul
      (hqc.aestronglyMeasurable measurableSet_Ioi)).mul hf
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have hq' : |q (exp (-t))| ≤ M := by simpa only [Real.norm_eq_abs] using hM _ (hmem t ht)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos _), neg_one_mul]
    calc exp (-t) * |q (exp (-t))| * |f t| ≤ exp (-t) * M * C :=
          mul_le_mul (mul_le_mul_of_nonneg_left hq' (exp_pos _).le) (hC t ht) (abs_nonneg _)
            (mul_nonneg (exp_pos _).le ((abs_nonneg _).trans hq'))
      _ = M * C * exp (-t) := by ring

/-- **Uniqueness of the Laplace transform.** If `f` is continuous and bounded on `[0, ∞)` and
`∫₀^∞ e^{-(n+1)t} f(t) dt = 0` for every `n ∈ ℕ`, then `f = 0` on `[0, ∞)`. -/
theorem eqOn_zero_of_laplace_eq_zero {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {C : ℝ}
    (hC : ∀ t ∈ Ici (0 : ℝ), |f t| ≤ C)
    (h : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), exp (-((n : ℝ) + 1) * t) * f t = 0) :
    EqOn f 0 (Ici 0) := by
  have hfI : ContinuousOn f (Ioi 0) := hf.mono Ioi_subset_Ici_self
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    hfI.aestronglyMeasurable measurableSet_Ioi
  have hCI : ∀ t ∈ Ioi (0 : ℝ), |f t| ≤ C := fun t ht => hC t (le_of_lt ht)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 (mem_Ici.2 le_rfl))
  -- The polynomial moments vanish.
  have hpoly : ∀ p : ℝ[X], ∫ t in Ioi (0 : ℝ), exp (-t) * p.eval (exp (-t)) * f t = 0 := by
    intro p
    have e : ∀ t, exp (-t) * p.eval (exp (-t)) * f t =
        ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (exp (-((i : ℝ) + 1) * t) * f t) := by
      intro t
      rw [eval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hx : exp (-((i : ℝ) + 1) * t) = exp (-t) * exp (-t) ^ i := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rw [hx]
      ring
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ =>
      (integrableOn_exp_mul_of_abs_le (by positivity) hmeas hCI).const_mul _]
    exact Finset.sum_eq_zero fun i _ => by rw [integral_const_mul, h i, mul_zero]
  -- Smooth test functions supported in `(0, ∞)` integrate to zero against `f`.
  have htest : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ Ioi 0 →
      ∫ t, g t • f t = 0 := by
    intro g hg hgc hgs
    obtain ⟨b, hb⟩ := hgc.isCompact.bddAbove
    have hgzero : ∀ t, b < t → g t = 0 := fun t ht =>
      image_eq_zero_of_notMem_tsupport fun hmem => (lt_irrefl b) (ht.trans_le (hb hmem))
    have hgneg : ∀ t, t ≤ 0 → g t = 0 := fun t ht =>
      image_eq_zero_of_notMem_tsupport fun hmem => (not_lt.2 ht) (hgs hmem)
    set G : ℝ → ℝ := fun s => g (-log s) / s with hG
    have hGc : ContinuousOn G (Icc 0 1) := by
      intro s hs
      rcases eq_or_lt_of_le hs.1 with h0 | hpos
      · subst h0
        have hG0 : G 0 = 0 := by simp [hG]
        refine (continuousWithinAt_const.congr_of_eventuallyEq ?_ hG0 :
          ContinuousWithinAt G (Icc 0 1) 0)
        have hpos : (0 : ℝ) < exp (-(max b 0)) := exp_pos _
        filter_upwards [inter_mem_nhdsWithin (Icc 0 1) (Iio_mem_nhds hpos)] with s' hs'
        rcases eq_or_lt_of_le hs'.1.1 with h0' | hpos'
        · rw [← h0', hG0]
        · have hlt : b < -log s' := by
            have h1 : log s' < -(max b 0) := by
              rw [log_lt_iff_lt_exp hpos']
              exact hs'.2
            linarith only [h1, le_max_left b 0]
          simp only [hG, hgzero _ hlt, zero_div]
      · exact (ContinuousAt.div ((hg.continuous.continuousAt).comp
          (continuousAt_log hpos.ne').neg) continuousAt_id hpos.ne').continuousWithinAt
    have hrep : ∀ t, exp (-t) * G (exp (-t)) = g t := by
      intro t
      simp only [hG, log_exp, neg_neg]
      rw [mul_div_assoc', mul_div_cancel_left₀ _ (exp_pos _).ne']
    have hint : ∫ t, g t • f t = ∫ t in Ioi (0 : ℝ), exp (-t) * G (exp (-t)) * f t := by
      have hset := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) (s := Ioi (0 : ℝ))
        (f := fun t => g t • f t) fun t ht => by rw [hgneg t (not_lt.1 ht), zero_smul]
      rw [← hset]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [smul_eq_mul, hrep]
    rw [hint]
    have hmem : ∀ t ∈ Ioi (0 : ℝ), exp (-t) ∈ Icc (0 : ℝ) 1 := fun t ht =>
      ⟨(exp_pos _).le, exp_le_one_iff.2 (by linarith only [ht.out])⟩
    have hbound : ∀ ε : ℝ, 0 < ε →
        |∫ t in Ioi (0 : ℝ), exp (-t) * G (exp (-t)) * f t| ≤ ε * C := by
      intro ε hε
      obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 G hGc ε hε
      have hpc : ContinuousOn (fun s => p.eval s) (Icc 0 1) := p.continuous.continuousOn
      have hdiff : ∫ t in Ioi (0 : ℝ), exp (-t) * G (exp (-t)) * f t =
          ∫ t in Ioi (0 : ℝ), exp (-t) * (G (exp (-t)) - p.eval (exp (-t))) * f t := by
        have h1 := integrableOn_exp_comp_mul hGc hmeas hCI
        have h2 := integrableOn_exp_comp_mul hpc hmeas hCI
        rw [show (fun t => exp (-t) * (G (exp (-t)) - p.eval (exp (-t))) * f t) =
            fun t => exp (-t) * G (exp (-t)) * f t - exp (-t) * p.eval (exp (-t)) * f t from
          funext fun t => by ring, integral_sub h1 h2, hpoly p, sub_zero]
      rw [hdiff]
      calc |∫ t in Ioi (0 : ℝ), exp (-t) * (G (exp (-t)) - p.eval (exp (-t))) * f t|
          ≤ ∫ t in Ioi (0 : ℝ), ε * C * exp (-1 * t) := by
            rw [← Real.norm_eq_abs]
            refine norm_integral_le_of_norm_le
              ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul _) ?_
            refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
            have hpt := hp _ (hmem t ht)
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (exp_pos _), neg_one_mul,
              abs_sub_comm]
            calc exp (-t) * |p.eval (exp (-t)) - G (exp (-t))| * |f t| ≤ exp (-t) * ε * C :=
                  mul_le_mul (mul_le_mul_of_nonneg_left hpt.le (exp_pos _).le) (hCI t ht)
                    (abs_nonneg _) (mul_nonneg (exp_pos _).le hε.le)
              _ = ε * C * exp (-t) := by ring
        _ = ε * C := by
            simp only [neg_one_mul]
            rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
    by_contra hne
    have hxpos := abs_pos.2 hne
    have hC1 : 0 < C + 1 := by linarith only [hC0]
    have hb' := hbound (|∫ t in Ioi (0 : ℝ), exp (-t) * G (exp (-t)) * f t| / (2 * (C + 1)))
      (by positivity)
    have hlt : |∫ t in Ioi (0 : ℝ), exp (-t) * G (exp (-t)) * f t| / (2 * (C + 1)) * C <
        |∫ t in Ioi (0 : ℝ), exp (-t) * G (exp (-t)) * f t| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith only [hxpos, hC0]
    linarith only [hb', hlt]
  -- Conclusion.
  have hae := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hfI.locallyIntegrableOn measurableSet_Ioi) htest
  have hEq : EqOn f 0 (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) ((ae_restrict_iff' measurableSet_Ioi).2 hae)
      isOpen_Ioi hfI continuousOn_const
  intro t ht
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from ht) with h0 | hpos
  · subst h0
    have hcw : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
      ((hf 0 (mem_Ici.2 le_rfl)).mono Ioi_subset_Ici_self).tendsto
    have h2 : Tendsto f (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hEq hs).symm)
    exact tendsto_nhds_unique hcw h2
  · exact hEq hpos

end SubdiffusiveProcess.SDE
