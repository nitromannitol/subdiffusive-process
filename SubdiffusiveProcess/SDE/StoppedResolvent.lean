module

public import SubdiffusiveProcess.SDE.Inputs
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The resolvent identity along a solution of the stochastic differential equation

Let `X` solve `dX = σ dW + b(X) dt` and let `u` be `C²` and bounded with
`λ u − ((σ²/2) Δu + b·∇u) = h`, `λ > 0`, `h` bounded and continuous. Itô's formula
(`ItoFormulaStopped`) applied to `g(t, x) = e^{-λ (t - s)} u(x)` at the exit times of growing balls,
followed by the limits `R → ∞` and `t → ∞`, gives for every `A ∈ ℱ_s`
`∫_A u(X_s) dℙ = ∫_A ∫_s^∞ e^{-λ (r - s)} h(X_r) dr dℙ`.
This is the step "Interior elliptic regularity and Itô's formula, stopped first strictly inside
the cube, give ... after exhaustion and letting the deterministic time horizon tend to infinity"
of `s.fixed.coefficient`, for the whole space and conditioned on `ℱ_s`.

## Main statements

* `spaceTimeGenerator_expMul`: the generator of `e^{-λ t + c} u(x)`;
* `eventually_stopAt_eq`: along a continuous path the stopped time is eventually `t`;
* `setIntegral_resolvent_eq`: the resolvent identity.
-/

@[expose] public section

noncomputable section

namespace SubdiffusiveProcess.SDE

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped NNReal ENNReal Topology

variable {d : ℕ}

/-! ### The generator of `e^{-λ t + c} φ(x)` -/

theorem hasFDerivAt_expMul {φ : Vec d → ℝ} {p : ℝ × Vec d} (hφ : DifferentiableAt ℝ φ p.2)
    (lam c : ℝ) :
    HasFDerivAt (fun q : ℝ × Vec d => exp (-lam * q.1 + c) * φ q.2)
      (exp (-lam * p.1 + c) • ((fderiv ℝ φ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (Vec d))) +
        φ p.2 • ((exp (-lam * p.1 + c) * -lam) • ContinuousLinearMap.fst ℝ ℝ (Vec d))) p := by
  have h1 : HasFDerivAt (fun q : ℝ × Vec d => exp (-lam * q.1 + c))
      ((exp (-lam * p.1 + c) * -lam) • ContinuousLinearMap.fst ℝ ℝ (Vec d)) p := by
    have hd : HasDerivAt (fun t : ℝ => exp (-lam * t + c)) (exp (-lam * p.1 + c) * -lam) p.1 := by
      have := ((hasDerivAt_id p.1).const_mul (-lam)).add_const c
      simpa using this.exp
    exact hd.comp_hasFDerivAt p (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun q : ℝ × Vec d => φ q.2)
      ((fderiv ℝ φ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (Vec d))) p :=
    hφ.hasFDerivAt.comp p hasFDerivAt_snd
  exact h1.mul h2

theorem fderiv_expMul_apply {φ : Vec d → ℝ} {p : ℝ × Vec d} (hφ : DifferentiableAt ℝ φ p.2)
    (lam c a : ℝ) (v : Vec d) :
    fderiv ℝ (fun q : ℝ × Vec d => exp (-lam * q.1 + c) * φ q.2) p (a, v) =
      exp (-lam * p.1 + c) * fderiv ℝ φ p.2 v - lam * exp (-lam * p.1 + c) * φ p.2 * a := by
  rw [(hasFDerivAt_expMul hφ lam c).fderiv]
  simp
  ring

/-- The partial derivatives of a `C²` function are differentiable. -/
theorem differentiable_partialDeriv {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (i : Fin d) :
    Differentiable ℝ (partialDeriv i u) := by
  have h : ContDiff ℝ 1 (fun x => fderiv ℝ u x (Pi.single i 1)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact h.differentiable one_ne_zero

/-- The space-time generator of `e^{-λ t + c} u(x)` is `e^{-λ t + c} (L u − λ u)`. -/
theorem spaceTimeGenerator_expMul {σ : ℝ} {b : Vec d → Vec d} {u : Vec d → ℝ}
    (hu : ContDiff ℝ 2 u) (lam c : ℝ) (p : ℝ × Vec d) :
    spaceTimeGenerator σ b (fun q => exp (-lam * q.1 + c) * u q.2) p =
      exp (-lam * p.1 + c) * (spaceGenerator σ b u p.2 - lam * u p.2) := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hfirst : ∀ i, spacePartial i (fun q : ℝ × Vec d => exp (-lam * q.1 + c) * u q.2) =
      fun q => exp (-lam * q.1 + c) * partialDeriv i u q.2 := by
    intro i
    funext q
    simp only [spacePartial, fderiv_expMul_apply (hu1 q.2), partialDeriv]
    ring
  have hsecond : ∀ i, spacePartial i (spacePartial i
      (fun q : ℝ × Vec d => exp (-lam * q.1 + c) * u q.2)) p =
      exp (-lam * p.1 + c) * partialDeriv i (partialDeriv i u) p.2 := by
    intro i
    rw [hfirst i]
    show fderiv ℝ (fun q : ℝ × Vec d => exp (-lam * q.1 + c) * partialDeriv i u q.2) p
      (0, Pi.single i 1) = _
    rw [fderiv_expMul_apply (differentiable_partialDeriv hu i p.2)]
    simp only [partialDeriv]
    ring
  have htime : timeDeriv (fun q : ℝ × Vec d => exp (-lam * q.1 + c) * u q.2) p =
      -(lam * exp (-lam * p.1 + c) * u p.2) := by
    simp only [timeDeriv, fderiv_expMul_apply (hu1 p.2), map_zero]
    ring
  have hS1 : ∑ i, spacePartial i (spacePartial i
      (fun q : ℝ × Vec d => exp (-lam * q.1 + c) * u q.2)) p =
      exp (-lam * p.1 + c) * ∑ i, partialDeriv i (partialDeriv i u) p.2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hsecond i
  have hS2 : ∑ i, b p.2 i * spacePartial i
      (fun q : ℝ × Vec d => exp (-lam * q.1 + c) * u q.2) p =
      exp (-lam * p.1 + c) * ∑ i, b p.2 i * partialDeriv i u p.2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfirst i]
    ring
  rw [spaceTimeGenerator, htime, hS1, hS2, spaceGenerator]
  ring

theorem contDiff_expMul {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (lam c : ℝ) :
    ContDiff ℝ 2 (fun q : ℝ × Vec d => exp (-lam * q.1 + c) * u q.2) :=
  (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_fst).add contDiff_const)).mul
    (hu.comp contDiff_snd)

/-! ### Exit times along a continuous path -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem stopAt_of_le {τ : ℝ≥0∞} {t : ℝ≥0} (h : (t : ℝ≥0∞) ≤ τ) : stopAt τ t = t := by
  simp [stopAt, min_eq_left h]

/-- Along a continuous path, the exit time from the ball of radius `R` eventually exceeds any
given time. -/
theorem eventually_le_exitTime {X : ℝ≥0 → Ω → Vec d} {ω : Ω}
    (hX : Continuous fun t => X t ω) (T : ℝ≥0) :
    ∀ᶠ R : ℝ in atTop, (T : ℝ≥0∞) ≤ exitTime X R ω := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
    hX.continuousOn
  filter_upwards [eventually_gt_atTop M] with R hR
  refine le_iInf₂ fun t ht => ?_
  by_contra hlt
  have htT : t ≤ T := by exact_mod_cast (not_le.1 hlt).le
  have := hM t ⟨zero_le, htT⟩
  linarith only [this, ht, hR]

/-- Along a continuous path, the stopped time is eventually `t`. -/
theorem eventually_stopAt_eq {X : ℝ≥0 → Ω → Vec d} {ω : Ω}
    (hX : Continuous fun t => X t ω) (t : ℝ≥0) :
    ∀ᶠ R : ℝ in atTop, stopAt (exitTime X R ω) t = t := by
  filter_upwards [eventually_le_exitTime hX t] with R hR
  exact stopAt_of_le hR

theorem stopAt_le (τ : ℝ≥0∞) (t : ℝ≥0) : stopAt τ t ≤ t := by
  unfold stopAt
  calc (min (t : ℝ≥0∞) τ).toNNReal ≤ (t : ℝ≥0∞).toNNReal :=
        ENNReal.toNNReal_mono ENNReal.coe_ne_top (min_le_left _ _)
    _ = t := ENNReal.toNNReal_coe t

/-! ### The resolvent identity -/

universe u

/-- **The resolvent identity along a solution.** Let `X` solve `dX = σ dW + b(X) dt` with `b`
continuous, and let `u` be `C²` and bounded, `h` continuous and bounded, `λ > 0`, with
`λ u − ((σ²/2) Δu + b·∇u) = h`. Then for every `s` and every `A ∈ ℱ_s`,
`∫_A u(X_s) dP = ∫_A ∫_s^∞ e^{-λ (r - s)} h(X_r) dr dP`. -/
theorem setIntegral_resolvent_eq (hIto : ItoFormulaStopped.{u} d) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P ℱ] {σ : ℝ} {b : Vec d → Vec d}
    (hb : Continuous b) {W X : ℝ≥0 → Ω → Vec d} (hW : IsBrownianMotion W ℱ P)
    (hX : IsStrongSolution σ b W X ℱ) {u h : Vec d → ℝ} (hu : ContDiff ℝ 2 u) {B H : ℝ}
    (huB : ∀ x, |u x| ≤ B) (hh : Continuous h) (hhH : ∀ x, |h x| ≤ H) {lam : ℝ}
    (hlam : 0 < lam) (heq : ∀ x, lam * u x - spaceGenerator σ b u x = h x)
    (s : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, u (X s ω) ∂P =
      ∫ ω in A, (∫ r in Ioi (s : ℝ), exp (-lam * (r - s)) * h (X r.toNNReal ω)) ∂P := by
  set c : ℝ := lam * s with hc
  set g : ℝ × Vec d → ℝ := fun q => exp (-lam * q.1 + c) * u q.2 with hg
  set F : Ω → ℝ → ℝ := fun ω r => exp (-lam * r + c) * h (X r.toNNReal ω) with hF
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (huB 0)
  have hH0 : 0 ≤ H := (abs_nonneg _).trans (hhH 0)
  have huc : Continuous u := hu.continuous
  have hXm : ∀ t, Measurable (X t) := fun t => (hX.adapted t).mono (ℱ.le t) le_rfl
  -- The generator of `g` along the path.
  have hgen : ∀ ω (r : ℝ), spaceTimeGenerator σ b g (r, X r.toNNReal ω) = -F ω r := by
    intro ω r
    rw [hg, spaceTimeGenerator_expMul hu lam c]
    simp only [hF, ← heq (X r.toNNReal ω)]
    ring
  -- Bounds.
  have hgB : ∀ (r : ℝ) (y : Vec d), 0 ≤ r → |g (r, y)| ≤ exp c * B := by
    intro r y hr
    simp only [hg, abs_mul, abs_of_pos (exp_pos _)]
    have hle : -lam * r + c ≤ c := by nlinarith only [mul_nonneg hlam.le hr]
    exact mul_le_mul (exp_le_exp.2 hle) (huB y) (abs_nonneg _) (exp_pos _).le
  have hFB : ∀ ω (r : ℝ), |F ω r| ≤ exp c * H * exp (-lam * r) := by
    intro ω r
    simp only [hF, abs_mul, abs_of_pos (exp_pos _)]
    rw [show -lam * r + c = c + -lam * r by ring, exp_add]
    calc exp c * exp (-lam * r) * |h (X r.toNNReal ω)| ≤ exp c * exp (-lam * r) * H :=
          mul_le_mul_of_nonneg_left (hhH _) (by positivity)
      _ = exp c * H * exp (-lam * r) := by ring
  have hFB' : ∀ ω (r : ℝ), 0 ≤ r → |F ω r| ≤ exp c * H := by
    intro ω r hr
    refine (hFB ω r).trans ?_
    have : exp (-lam * r) ≤ 1 := exp_le_one_iff.2 (by nlinarith only [mul_nonneg hlam.le hr])
    calc exp c * H * exp (-lam * r) ≤ exp c * H * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = exp c * H := mul_one _
  have hFc : ∀ ω, Continuous (F ω) := fun ω => by
    simp only [hF]
    exact (by fun_prop : Continuous fun r : ℝ => exp (-lam * r + c)).mul
      (hh.comp ((hX.continuous ω).comp continuous_real_toNNReal))
  have hFint : ∀ ω, IntegrableOn (F ω) (Ioi 0) := fun ω =>
    ((exp_neg_integrableOn_Ioi 0 hlam).const_mul (exp c * H)).mono'
      (hFc ω).aestronglyMeasurable
      (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hFB ω r)
  -- The stopped martingales and their limit as `R → ∞`.
  set M : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω =>
    g ((stopAt (exitTime X n ω) t : ℝ), X (stopAt (exitTime X n ω) t) ω) - g (0, X 0 ω) -
      ∫ r in (0 : ℝ)..(stopAt (exitTime X n ω) t : ℝ), spaceTimeGenerator σ b g (r, X r.toNNReal ω)
    with hMdef
  have hM : ∀ n : ℕ, Martingale (M n) ℱ P := fun n =>
    hIto P ℱ σ b hb W X hW hX g (contDiff_expMul hu lam c) n
  set Ψ : ℝ≥0 → Ω → ℝ := fun t ω => g (t, X t ω) - g (0, X 0 ω) + ∫ r in (0 : ℝ)..(t : ℝ), F ω r
    with hΨ
  have hint_gen : ∀ ω (a : ℝ), ∫ r in (0 : ℝ)..a, spaceTimeGenerator σ b g (r, X r.toNNReal ω) =
      -∫ r in (0 : ℝ)..a, F ω r := by
    intro ω a
    rw [intervalIntegral.integral_congr (g := fun r => -F ω r) fun r _ => hgen ω r,
      intervalIntegral.integral_neg]
  have hev : ∀ (t : ℝ≥0) (ω : Ω), ∀ᶠ n : ℕ in atTop, M n t ω = Ψ t ω := by
    intro t ω
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_stopAt_eq (hX.continuous ω) t)] with n hn
    simp only [hMdef, hΨ, hn, hint_gen]
    ring
  have hIabs : ∀ ω (a : ℝ), 0 ≤ a → |∫ r in (0 : ℝ)..a, F ω r| ≤ exp c * H * a := by
    intro ω a ha
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := a)
      (C := exp c * H) (f := F ω) fun r hr => by
        rw [Real.norm_eq_abs]
        have hr' : r ∈ Ioc 0 a := by rwa [uIoc_of_le ha] at hr
        exact hFB' ω r hr'.1.le
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg ha] at this
  have hMbound : ∀ n (t : ℝ≥0) ω, |M n t ω| ≤ 2 * (exp c * B) + exp c * H * t := by
    intro n t ω
    have hS := stopAt_le (exitTime X n ω) t
    have hS' : ((stopAt (exitTime X n ω) t : ℝ≥0) : ℝ) ≤ t := by exact_mod_cast hS
    have h1 := hgB _ (X (stopAt (exitTime X n ω) t) ω) (stopAt (exitTime X n ω) t).2
    have h2 := hgB 0 (X 0 ω) le_rfl
    have h3 := hIabs ω _ (stopAt (exitTime X n ω) t).2
    have h3' : exp c * H * ((stopAt (exitTime X n ω) t : ℝ≥0) : ℝ) ≤ exp c * H * t :=
      mul_le_mul_of_nonneg_left hS' (by positivity)
    simp only [hMdef, hint_gen, sub_neg_eq_add]
    calc |g ((stopAt (exitTime X n ω) t : ℝ), X (stopAt (exitTime X n ω) t) ω) - g (0, X 0 ω) +
          ∫ r in (0 : ℝ)..(stopAt (exitTime X n ω) t : ℝ), F ω r|
        ≤ |g ((stopAt (exitTime X n ω) t : ℝ), X (stopAt (exitTime X n ω) t) ω)| +
            |g (0, X 0 ω)| + |∫ r in (0 : ℝ)..(stopAt (exitTime X n ω) t : ℝ), F ω r| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ exp c * B + exp c * B + exp c * H * t := add_le_add (add_le_add h1 h2) (h3.trans h3')
      _ = 2 * (exp c * B) + exp c * H * t := by ring
  have hlim : ∀ t : ℝ≥0, Tendsto (fun n => ∫ ω in A, M n t ω ∂P) atTop
      (𝓝 (∫ ω in A, Ψ t ω ∂P)) := by
    intro t
    refine tendsto_integral_of_dominated_convergence
      (fun _ => 2 * (exp c * B) + exp c * H * t) (fun n => ?_) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · exact (((hM n).1 t).mono (ℱ.le t)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact hMbound n t ω
    · exact tendsto_const_nhds.congr' (by
        filter_upwards [hev t ω] with n hn
        exact hn.symm)
  have hΨeq : ∀ t : ℝ≥0, s ≤ t → ∫ ω in A, Ψ t ω ∂P = ∫ ω in A, Ψ s ω ∂P := by
    intro t hst
    have heqn : ∀ n, ∫ ω in A, M n s ω ∂P = ∫ ω in A, M n t ω ∂P := fun n =>
      (hM n).setIntegral_eq hst hA
    exact tendsto_nhds_unique ((hlim t).congr fun n => (heqn n).symm) (hlim s)
  -- The limit `t → ∞`.
  set J : ℝ := ∫ r in Ioi (0 : ℝ), exp c * H * exp (-lam * r) with hJ
  have hJint : IntegrableOn (fun r : ℝ => exp c * H * exp (-lam * r)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hlam).const_mul _
  have hIJ : ∀ ω (a : ℝ), 0 ≤ a → |∫ r in (0 : ℝ)..a, F ω r| ≤ J := by
    intro ω a ha
    rw [intervalIntegral.integral_of_le ha, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hJint.mono_set Ioc_subset_Ioi_self)
      (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hFB ω r)).trans ?_
    exact setIntegral_mono_set hJint
      (Eventually.of_forall fun r => by positivity) Ioc_subset_Ioi_self.eventuallyLE
  have hIinfJ : ∀ ω, |∫ r in Ioi (0 : ℝ), F ω r| ≤ J := by
    intro ω
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hJint
      (Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hFB ω r)
  have hΨbound : ∀ (t : ℝ≥0) ω, |Ψ t ω| ≤ 2 * (exp c * B) + J := by
    intro t ω
    have h1 := hgB t (X t ω) t.2
    have h2 := hgB 0 (X 0 ω) le_rfl
    have h3 := hIJ ω t t.2
    simp only [hΨ]
    calc |g (t, X t ω) - g (0, X 0 ω) + ∫ r in (0 : ℝ)..(t : ℝ), F ω r|
        ≤ |g (t, X t ω)| + |g (0, X 0 ω)| + |∫ r in (0 : ℝ)..(t : ℝ), F ω r| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ exp c * B + exp c * B + J := add_le_add (add_le_add h1 h2) h3
      _ = 2 * (exp c * B) + J := by ring
  have hΨmeas : ∀ t : ℝ≥0, AEStronglyMeasurable (Ψ t) (P.restrict A) := fun t =>
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (((hM n).1 t).mono (ℱ.le t)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => tendsto_const_nhds.congr' (by
        filter_upwards [hev t ω] with n hn
        exact hn.symm))
  set Ψinf : Ω → ℝ := fun ω => -g (0, X 0 ω) + ∫ r in Ioi (0 : ℝ), F ω r with hΨinf
  have hexp0 : Tendsto (fun n : ℕ => exp (-lam * n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => lam * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hlam
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply, neg_mul]
  have hlimΨ : ∀ ω, Tendsto (fun n : ℕ => Ψ n ω) atTop (𝓝 (Ψinf ω)) := by
    intro ω
    have hg0 : Tendsto (fun n : ℕ => g (((n : ℝ≥0) : ℝ), X n ω)) atTop (𝓝 0) := by
      have hb : Tendsto (fun n : ℕ => exp c * B * exp (-lam * n)) atTop (𝓝 0) := by
        simpa using hexp0.const_mul (exp c * B)
      refine squeeze_zero_norm (fun n => ?_) hb
      rw [Real.norm_eq_abs]
      simp only [hg, abs_mul, abs_of_pos (exp_pos _), NNReal.coe_natCast]
      rw [show -lam * (n : ℝ) + c = c + -lam * n by ring, exp_add]
      calc exp c * exp (-lam * n) * |u (X n ω)| ≤ exp c * exp (-lam * n) * B :=
            mul_le_mul_of_nonneg_left (huB _) (by positivity)
        _ = exp c * B * exp (-lam * n) := by ring
    have hI : Tendsto (fun n : ℕ => ∫ r in (0 : ℝ)..((n : ℝ≥0) : ℝ), F ω r) atTop
        (𝓝 (∫ r in Ioi (0 : ℝ), F ω r)) :=
      intervalIntegral_tendsto_integral_Ioi 0 (hFint ω)
        (by simpa only [NNReal.coe_natCast] using tendsto_natCast_atTop_atTop)
    have := (hg0.sub (tendsto_const_nhds (x := g (0, X 0 ω)))).add hI
    simpa only [hΨ, hΨinf, zero_sub] using this
  have hΨinfmeas : AEStronglyMeasurable Ψinf (P.restrict A) :=
    aestronglyMeasurable_of_tendsto_ae atTop (f := fun n : ℕ => Ψ n) (fun n => hΨmeas n)
      (Eventually.of_forall hlimΨ)
  have hΨinf_eq : ∫ ω in A, Ψinf ω ∂P = ∫ ω in A, Ψ s ω ∂P := by
    have hl : Tendsto (fun n : ℕ => ∫ ω in A, Ψ n ω ∂P) atTop (𝓝 (∫ ω in A, Ψinf ω ∂P)) :=
      tendsto_integral_of_dominated_convergence (fun _ => 2 * (exp c * B) + J)
        (fun n => hΨmeas n) (integrable_const _)
        (fun n => Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hΨbound n ω)
        (Eventually.of_forall hlimΨ)
    refine tendsto_nhds_unique hl (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop ⌈s⌉₊] with n hn
    refine (hΨeq n ?_).symm
    exact (Nat.le_ceil s).trans (by exact_mod_cast hn)
  -- The pointwise identity and the conclusion.
  have hsplit : ∀ ω, ∫ r in Ioi (0 : ℝ), F ω r =
      (∫ r in (0 : ℝ)..(s : ℝ), F ω r) + ∫ r in Ioi (s : ℝ), F ω r := by
    intro ω
    have hu := setIntegral_union (μ := volume) (f := F ω) (s := Ioc 0 (s : ℝ))
      (t := Ioi (s : ℝ)) (Set.disjoint_left.2 fun x hx1 hx2 => (not_lt.2 hx1.2) hx2)
      measurableSet_Ioi ((hFint ω).mono_set Ioc_subset_Ioi_self)
      ((hFint ω).mono_set (Ioi_subset_Ioi s.coe_nonneg))
    rw [Ioc_union_Ioi_eq_Ioi s.coe_nonneg] at hu
    rw [intervalIntegral.integral_of_le s.coe_nonneg, hu]
  have hpt : ∀ ω, ∫ r in Ioi (s : ℝ), exp (-lam * (r - s)) * h (X r.toNNReal ω) =
      Ψinf ω - Ψ s ω + u (X s ω) := by
    intro ω
    have hgs : g (s, X s ω) = u (X s ω) := by
      simp only [hg, hc]
      rw [show -lam * (s : ℝ) + lam * s = 0 by ring, exp_zero, one_mul]
    have hint : ∫ r in Ioi (s : ℝ), exp (-lam * (r - s)) * h (X r.toNNReal ω) =
        ∫ r in Ioi (s : ℝ), F ω r :=
      setIntegral_congr_fun measurableSet_Ioi fun r _ => by
        simp only [hF, hc]
        congr 2
        ring
    rw [hint]
    simp only [hΨinf, hΨ, hgs, hsplit ω]
    ring
  have hiu : Integrable (fun ω => u (X s ω)) (P.restrict A) :=
    Integrable.of_bound (huc.measurable.comp (hXm s)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact huB _)
  have hiΨs : Integrable (Ψ s) (P.restrict A) :=
    Integrable.of_bound (hΨmeas s) _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hΨbound s ω)
  have hiΨinf : Integrable Ψinf (P.restrict A) :=
    Integrable.of_bound hΨinfmeas (exp c * B + J) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      have h2 := hgB 0 (X 0 ω) le_rfl
      have h3 := hIinfJ ω
      simp only [hΨinf]
      calc |-g (0, X 0 ω) + ∫ r in Ioi (0 : ℝ), F ω r|
          ≤ |-g (0, X 0 ω)| + |∫ r in Ioi (0 : ℝ), F ω r| := abs_add_le _ _
        _ ≤ exp c * B + J := by rw [abs_neg]; linarith only [h2, h3])
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  have h1 := integral_add (hiΨinf.sub hiΨs) hiu
  have h2 := integral_sub hiΨinf hiΨs
  simp only [Pi.sub_apply] at h1 h2
  rw [h1, h2, hΨinf_eq, sub_self, zero_add]

end SubdiffusiveProcess.SDE
