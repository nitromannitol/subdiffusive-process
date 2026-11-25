module

public import SubdiffusiveProcess.SDE.StoppedResolvent
public import SubdiffusiveProcess.SDE.LaplaceUniqueness
public import MarkovProcess.Main
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# The Markov identity for a solution of the stochastic differential equation

Let `Q` be a sub-Markov kernel semigroup on `ℝ^d` whose resolvent `∫₀^∞ e^{-λ t} Q_t h dt` of a
smooth compactly supported `h` is, for `λ = n + 1`, a bounded `C²` solution of
`λ u − ((σ²/2) Δu + b·∇u) = h` (`HasClassicalResolvent`). If `X` solves `dX = σ dW + b(X) dt`, then
for all `s, q ≥ 0`, every `A ∈ ℱ_s` and every smooth compactly supported `h`,
`∫_A h(X_{s+q}) dP = ∫_A (Q_q h)(X_s) dP`.

The resolvent identity `setIntegral_resolvent_eq` and Fubini's theorem show that both sides have
the same Laplace transform in `q` at every `λ = n + 1`; both are continuous and bounded in `q`, so
they agree by `eqOn_zero_of_laplace_eq_zero`. This replaces the identification of killed
resolvents, Laplace inversion and the Markov property of the solution in `s.fixed.coefficient`.

## Main statements

* `integral_Ioi_eq_integral_Ioi_zero_add`: translation of an integral over `(s, ∞)`;
* `HasClassicalResolvent`: the resolvent hypothesis on `Q`;
* `setIntegral_comp_add_eq_setIntegral_kernel`: the Markov identity.
-/

@[expose] public section

noncomputable section

namespace SubdiffusiveProcess.SDE

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped NNReal ENNReal Topology ContDiff

variable {d : ℕ}

/-- Translation of an integral over `(s, ∞)` to an integral over `(0, ∞)`. -/
theorem integral_Ioi_eq_integral_Ioi_zero_add (f : ℝ → ℝ) (s : ℝ) :
    ∫ r in Ioi s, f r = ∫ q in Ioi 0, f (q + s) := by
  have h := (measurePreserving_add_right volume s).setIntegral_preimage_emb
    (measurableEmbedding_addRight s) f (Ioi s)
  rw [preimage_add_const_Ioi, sub_self] at h
  exact h.symm

/-- The resolvent of `Q` at `λ = n + 1` applied to a smooth compactly supported `h` is a bounded
`C²` solution of `λ u − ((σ²/2) Δu + b·∇u) = h`. -/
def HasClassicalResolvent (Q : MarkovProcess.SubMarkovKernelSemigroup (Vec d)) (σ : ℝ) (b : Vec d → Vec d) :
    Prop :=
  ∀ (n : ℕ) (h : Vec d → ℝ), ContDiff ℝ ∞ h → HasCompactSupport h →
    ∃ u : Vec d → ℝ, ContDiff ℝ 2 u ∧ (∃ B, ∀ x, |u x| ≤ B) ∧
      (∀ x, ((n : ℝ) + 1) * u x - spaceGenerator σ b u x = h x) ∧
      ∀ x, u x = ∫ t in Ioi (0 : ℝ), exp (-((n : ℝ) + 1) * t) * ∫ z, h z ∂(Q t.toNNReal x)

universe u

/-- **The Markov identity.** Under `HasClassicalResolvent Q σ b`, with `t ↦ Q_t h (y)` continuous
for smooth compactly supported `h`, a solution `X` of `dX = σ dW + b(X) dt` satisfies
`∫_A h(X_{s+q}) dP = ∫_A (Q_q h)(X_s) dP` for all `s, q ≥ 0`, `A ∈ ℱ_s` and smooth compactly
supported `h`. -/
theorem setIntegral_comp_add_eq_setIntegral_kernel (hIto : ItoFormulaStopped.{u} d)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P ℱ] {σ : ℝ} {b : Vec d → Vec d}
    (hb : Continuous b) {W X : ℝ≥0 → Ω → Vec d} (hW : IsBrownianMotion W ℱ P)
    (hX : IsStrongSolution σ b W X ℱ) {Q : MarkovProcess.SubMarkovKernelSemigroup (Vec d)}
    (hQ : HasClassicalResolvent Q σ b)
    (hQc : ∀ h : Vec d → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ y,
      Continuous fun t : ℝ≥0 => ∫ z, h z ∂(Q t y))
    {h : Vec d → ℝ} (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (s q : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ w in A, h (X (s + q) w) ∂P = ∫ w in A, (∫ z, h z ∂(Q q (X s w))) ∂P := by
  obtain ⟨H, hH⟩ : ∃ H, ∀ x, |h x| ≤ H := by
    obtain ⟨C, hC⟩ := hh.continuous.bounded_above_of_compact_support hhc
    exact ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x⟩
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
  have hhm : Measurable h := hh.continuous.measurable
  have hXm : ∀ t, Measurable (X t) := fun t => (hX.adapted t).mono (ℱ.le t) le_rfl
  have hAm : MeasurableSet A := ℱ.le s A hA
  haveI : ∀ t, IsFiniteKernel (Q t) := fun t =>
    ⟨⟨1, ENNReal.one_lt_top, fun y => Q.measure_univ_le_one t y⟩⟩
  have hQb : ∀ t y, |∫ z, h z ∂(Q t y)| ≤ H := by
    intro t y
    have h1 := norm_integral_le_of_norm_le_const (μ := Q t y) (C := H)
      (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hH z)
    rw [Real.norm_eq_abs] at h1
    have hle : (Q t y).real univ ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact Q.measure_univ_le_one t y)
    exact h1.trans (mul_le_of_le_one_right hH0 hle)
  have hKm : ∀ t, Measurable fun y => ∫ z, h z ∂(Q t y) := fun t =>
    (StronglyMeasurable.integral_kernel (κ := Q t) hh.continuous.stronglyMeasurable).measurable
  have hAle : (P.restrict A).real univ ≤ 1 := by
    rw [Measure.real, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have hsetb : ∀ f : Ω → ℝ, (∀ w, |f w| ≤ H) → |∫ w in A, f w ∂P| ≤ H := by
    intro f hf
    have h1 := norm_integral_le_of_norm_le_const (μ := P.restrict A) (C := H)
      (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hf w)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_of_le_one_right hH0 hAle)
  -- The two functions of the lag.
  set φ₁ : ℝ → ℝ := fun t => ∫ w in A, h (X (s + t.toNNReal) w) ∂P with hφ₁
  set φ₂ : ℝ → ℝ := fun t => ∫ w in A, (∫ z, h z ∂(Q t.toNNReal (X s w))) ∂P with hφ₂
  have hφ₁c : Continuous φ₁ :=
    continuous_of_dominated (bound := fun _ => H)
      (fun t => (hhm.comp (hXm _)).aestronglyMeasurable)
      (fun t => Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hH _)
      (integrable_const _)
      (Eventually.of_forall fun w => hh.continuous.comp
        ((hX.continuous w).comp (continuous_const.add continuous_real_toNNReal)))
  have hφ₂c : Continuous φ₂ :=
    continuous_of_dominated (bound := fun _ => H)
      (fun t => ((hKm _).comp (hXm s)).aestronglyMeasurable)
      (fun t => Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hQb _ _)
      (integrable_const _)
      (Eventually.of_forall fun w => (hQc h hh hhc (X s w)).comp continuous_real_toNNReal)
  have hφ₁b : ∀ t, |φ₁ t| ≤ H := fun t => hsetb _ fun w => hH _
  have hφ₂b : ∀ t, |φ₂ t| ≤ H := fun t => hsetb _ fun w => hQb _ _
  -- Laplace transforms.
  have hlap : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ), exp (-((n : ℝ) + 1) * t) * (φ₁ t - φ₂ t) = 0 := by
    intro n
    have hlam : (0 : ℝ) < n + 1 := by positivity
    obtain ⟨u, hu2, ⟨B, hB⟩, hueq, hurep⟩ := hQ n h hh hhc
    have hres := setIntegral_resolvent_eq hIto hb hW hX hu2 hB hh.continuous hH hlam hueq s hA
    have hexpi := exp_neg_integrableOn_Ioi 0 hlam
    -- Joint measurability of the two integrands.
    have hm1 : Measurable (Function.uncurry fun (w : Ω) (t : ℝ) =>
        exp (-((n : ℝ) + 1) * t) * h (X (s + t.toNNReal) w)) := by
      have : Measurable (Function.uncurry fun (t : ℝ) (w : Ω) =>
          exp (-((n : ℝ) + 1) * t) * h (X (s + t.toNNReal) w)) :=
        measurable_uncurry_of_continuous_of_measurable
          (fun w => (by fun_prop : Continuous fun t : ℝ => exp (-((n : ℝ) + 1) * t)).mul
            (hh.continuous.comp ((hX.continuous w).comp
              (continuous_const.add continuous_real_toNNReal))))
          (fun t => measurable_const.mul (hhm.comp (hXm _)))
      exact this.comp measurable_swap
    have hm2 : Measurable (Function.uncurry fun (w : Ω) (t : ℝ) =>
        exp (-((n : ℝ) + 1) * t) * ∫ z, h z ∂(Q t.toNNReal (X s w))) := by
      have : Measurable (Function.uncurry fun (t : ℝ) (w : Ω) =>
          exp (-((n : ℝ) + 1) * t) * ∫ z, h z ∂(Q t.toNNReal (X s w))) :=
        measurable_uncurry_of_continuous_of_measurable
          (fun w => (by fun_prop : Continuous fun t : ℝ => exp (-((n : ℝ) + 1) * t)).mul
            ((hQc h hh hhc (X s w)).comp continuous_real_toNNReal))
          (fun t => measurable_const.mul ((hKm _).comp (hXm s)))
      exact this.comp measurable_swap
    have hbound_int : Integrable (fun p : Ω × ℝ => H * exp (-((n : ℝ) + 1) * p.2))
        ((P.restrict A).prod (volume.restrict (Ioi 0))) :=
      (integrable_const H).mul_prod hexpi
    have hint1 : Integrable (Function.uncurry fun (w : Ω) (t : ℝ) =>
        exp (-((n : ℝ) + 1) * t) * h (X (s + t.toNNReal) w))
        ((P.restrict A).prod (volume.restrict (Ioi 0))) :=
      hbound_int.mono' hm1.aestronglyMeasurable (Eventually.of_forall fun p => by
        obtain ⟨w, t⟩ := p
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
          abs_of_pos (exp_pos _)]
        rw [mul_comm H]
        exact mul_le_mul_of_nonneg_left (hH _) (exp_pos _).le)
    have hint2 : Integrable (Function.uncurry fun (w : Ω) (t : ℝ) =>
        exp (-((n : ℝ) + 1) * t) * ∫ z, h z ∂(Q t.toNNReal (X s w)))
        ((P.restrict A).prod (volume.restrict (Ioi 0))) :=
      hbound_int.mono' hm2.aestronglyMeasurable (Eventually.of_forall fun p => by
        obtain ⟨w, t⟩ := p
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
          abs_of_pos (exp_pos _)]
        rw [mul_comm H]
        exact mul_le_mul_of_nonneg_left (hQb _ _) (exp_pos _).le)
    -- The left side of the resolvent identity.
    have hL : ∫ w in A, u (X s w) ∂P =
        ∫ t in Ioi (0 : ℝ), exp (-((n : ℝ) + 1) * t) * φ₂ t := by
      simp_rw [hurep]
      rw [integral_integral_swap hint2]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hφ₂]
      rw [integral_const_mul]
    -- The right side of the resolvent identity.
    have hR : ∫ w in A, (∫ r in Ioi (s : ℝ), exp (-((n : ℝ) + 1) * (r - s)) *
        h (X r.toNNReal w)) ∂P = ∫ t in Ioi (0 : ℝ), exp (-((n : ℝ) + 1) * t) * φ₁ t := by
      have hsub : ∀ w, ∫ r in Ioi (s : ℝ), exp (-((n : ℝ) + 1) * (r - s)) * h (X r.toNNReal w) =
          ∫ t in Ioi (0 : ℝ), exp (-((n : ℝ) + 1) * t) * h (X (s + t.toNNReal) w) := by
        intro w
        rw [integral_Ioi_eq_integral_Ioi_zero_add]
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [add_sub_cancel_right, Real.toNNReal_add (le_of_lt ht) s.coe_nonneg,
          Real.toNNReal_coe, add_comm t.toNNReal s]
      simp_rw [hsub]
      rw [integral_integral_swap hint1]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hφ₁]
      rw [integral_const_mul]
    have hφi : ∀ φ : ℝ → ℝ, Continuous φ → (∀ t, |φ t| ≤ H) →
        IntegrableOn (fun t => exp (-((n : ℝ) + 1) * t) * φ t) (Ioi 0) := fun φ hc hb =>
      integrableOn_exp_mul_of_abs_le hlam (hc.aestronglyMeasurable) fun t _ => hb t
    simp_rw [mul_sub]
    rw [integral_sub (hφi φ₁ hφ₁c hφ₁b) (hφi φ₂ hφ₂c hφ₂b), ← hL, ← hR, hres, sub_self]
  have hzero := eqOn_zero_of_laplace_eq_zero (f := fun t => φ₁ t - φ₂ t)
    (hφ₁c.sub hφ₂c).continuousOn (C := 2 * H)
    (fun t _ => (abs_sub _ _).trans (by linarith only [hφ₁b t, hφ₂b t])) hlap
    (show (0 : ℝ) ≤ q from q.coe_nonneg)
  simp only [Pi.zero_apply, sub_eq_zero, hφ₁, hφ₂, Real.toNNReal_coe] at hzero
  exact hzero

end SubdiffusiveProcess.SDE
