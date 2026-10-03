module

public import Mathlib.Analysis.ODE.Gronwall
public import MarkovProcess.Trajectory.Dynkin
public import MarkovProcess.Semigroup.Generator

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Filter Topology MeasureTheory MarkovProcess MarkovProcess.Semigroup
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ZeroAtInfty

theorem le_exp_mul_of_right_deriv_le {f fprime : ℝ → ℝ} {C T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt f (fprime t) (Set.Ici t) t)
    (hb : ∀ t ∈ Set.Ico 0 T, fprime t ≤ C * f t) :
    f T ≤ Real.exp (C * T) * f 0 := by
  have h := le_gronwallBound_of_liminf_deriv_right_le (δ := f 0) (K := C) (ε := 0) hf
    (fun x hx r hr => (hd x hx).liminf_right_slope_le hr)
    le_rfl (fun x hx => by simpa using hb x hx)
  have hT' := h T ⟨hT, le_rfl⟩
  simpa [gronwallBound_ε0, mul_comm] using hT'

theorem integral_affine_c0 {alpha : Type*} [TopologicalSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha] (mu : Measure alpha) [IsProbabilityMeasure mu]
    (f : C₀(alpha, ℝ)) (A C : ℝ) :
    (∫ y, C * (A + f y) ∂mu) = C * (A + ∫ y, f y ∂mu) := by
  have hf : Integrable (fun y ↦ f y) mu := f.toBCF.integrable mu
  rw [integral_const_mul, integral_add (integrable_const A) hf]
  simp

theorem hasDerivWithinAt_affine_c0Orbit {alpha : Type*} [TopologicalSpace alpha]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup C₀(alpha, ℝ))
    (f : S.generatorDomain) (A : ℝ) (x : alpha) (t : NNReal) :
    HasDerivWithinAt (fun s : ℝ ↦ A + S (Real.toNNReal s) f x)
      (S t (S.generator f) x) (Set.Ici (t : ℝ)) t := by
  have hd := S.hasDerivWithinAt_Ici f t
  have h2 := (MarkovProcess.SubMarkovKernelSemigroup.evalC0CLM x).hasFDerivAt.comp_hasDerivWithinAt
    (t : ℝ) hd
  simpa only [Function.comp_def,
    MarkovProcess.SubMarkovKernelSemigroup.evalC0CLM_apply] using h2.const_add A

/-- A constant plus a generator-domain function obeys the exponential
comparison whenever its generator has the corresponding pointwise upper bound. -/
theorem affine_c0Semigroup_le_exp {alpha : Type*} [TopologicalSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hF : P.IsFellerKernelSemigroup) (f : hF.c0Semigroup.generatorDomain) (A C : ℝ)
    (hLf : ∀ y, hF.c0Semigroup.generator f y ≤ C * (A + (f : C₀(alpha, ℝ)) y))
    (t : NNReal) (x : alpha) :
    A + hF.c0Semigroup t f x ≤ Real.exp (C * (t : ℝ)) * (A + (f : C₀(alpha, ℝ)) x) := by
  let S := hF.c0Semigroup
  let u : ℝ → ℝ := fun s ↦ A + S (Real.toNNReal s) f x
  let du : ℝ → ℝ := fun s ↦ S (Real.toNNReal s) (S.generator f) x
  have hcont : Continuous u :=
    continuous_const.add ((evalC0CLM x).continuous.comp (S.continuous_operator_toNNReal f))
  have hderiv : ∀ s ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt u (du s) (Set.Ici s) s := by
    intro s hs
    have h := hasDerivWithinAt_affine_c0Orbit S f A x (Real.toNNReal s)
    rw [Real.coe_toNNReal s hs.1] at h
    exact h
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t, du s ≤ C * u s := by
    intro s _
    let tS := Real.toNNReal s
    letI : IsProbabilityMeasure (P tS x) := ⟨hP tS x⟩
    have hiL : Integrable (fun y ↦ S.generator f y) (P tS x) :=
      (S.generator f).toBCF.integrable (P tS x)
    have hiF : Integrable (fun y ↦ (f : C₀(alpha, ℝ)) y) (P tS x) :=
      (f : C₀(alpha, ℝ)).toBCF.integrable (P tS x)
    change (∫ y, S.generator f y ∂P tS x) ≤
      C * (A + ∫ y, (f : C₀(alpha, ℝ)) y ∂P tS x)
    exact (integral_mono hiL (((integrable_const A).add hiF).const_mul C) hLf).trans_eq
      (integral_affine_c0 (P tS x) (f : C₀(alpha, ℝ)) A C)
  have h := le_exp_mul_of_right_deriv_le t.coe_nonneg hcont.continuousOn hderiv hbound
  simpa only [u, Real.toNNReal_zero, Real.toNNReal_coe, S.zero_apply] using! h

theorem lintegral_ofReal_le_of_approximation {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (f : ℕ → alpha → ℝ) (F : alpha → ℝ) (A : ℝ)
    (hi : ∀ n, Integrable (f n) mu) (hn : ∀ n x, 0 ≤ f n x)
    (hlim : ∀ x, Tendsto (fun n ↦ f n x) atTop (nhds (F x)))
    (hb : ∀ n, (∫ x, f n x ∂mu) ≤ A) :
    (∫⁻ x, ENNReal.ofReal (F x) ∂mu) ≤ ENNReal.ofReal A := by
  have key : ∀ n, (∫⁻ x, ENNReal.ofReal (f n x) ∂mu) ≤ ENNReal.ofReal A := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (fun x => hn n x))]
    exact ENNReal.ofReal_le_ofReal (hb n)
  calc ∫⁻ x, ENNReal.ofReal (F x) ∂mu
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal (f n x)) atTop ∂mu := by
        simp only [fun x => (ENNReal.tendsto_ofReal (hlim x)).liminf_eq]
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂mu) atTop :=
        lintegral_liminf_le' (fun n => (hi n).aemeasurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal A :=
        liminf_le_of_frequently_le (Eventually.of_forall key).frequently

theorem exp_sub_one_le_mul_exp (t : ℝ) : Real.exp t - 1 ≤ t*Real.exp t := by
  have h1 := Real.add_one_le_exp (-t)
  have h2 : 0 < Real.exp t := Real.exp_pos t
  have h3 : Real.exp (-t) * Real.exp t = 1 := by
    rw [Real.exp_neg, inv_mul_cancel₀ h2.ne']
  have h4 : (-t + 1) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
    mul_le_mul_of_nonneg_right h1 h2.le
  nlinarith [h4, h3]

theorem gronwallBound_zero_le {K eps t : ℝ} (hK : 0 ≤ K) (heps : 0 ≤ eps) (ht : 0 ≤ t) :
    gronwallBound 0 K eps t ≤ eps*t*Real.exp (K*t) := by
  have _ := ht
  by_cases hk : K = 0
  · simp [hk, gronwallBound_K0]
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hk)
    rw [gronwallBound_of_K_ne_0 hk]
    simp only [zero_mul, zero_add]
    have hexp : 0 ≤ Real.exp (K*t) := Real.exp_pos (K*t) |>.le
    calc eps/K*(Real.exp (K*t)-1) ≤ eps/K*(K*t*Real.exp (K*t)) :=
          mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp (K*t)) (div_nonneg heps hKpos.le)
      _ = eps*t*Real.exp (K*t) := by field_simp

theorem integral_affine_c0_pair {alpha : Type*} [TopologicalSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha] (mu : Measure alpha) [IsProbabilityMeasure mu]
    (f g : C₀(alpha, ℝ)) (A B a D : ℝ) :
    (∫ y, D*(a*(A+f y)+(B+g y)) ∂mu) =
      D*(a*(A+∫ y, f y ∂mu)+(B+∫ y, g y ∂mu)) := by
  have hf : Integrable (fun y : alpha => f y) mu := f.toBCF.integrable mu
  have hg : Integrable (fun y : alpha => g y) mu := g.toBCF.integrable mu
  have h1 : Integrable (fun y : alpha => a*(A+f y)) mu :=
    ((integrable_const A).add hf).const_mul a
  have h2 : Integrable (fun y : alpha => B+g y) mu :=
    (integrable_const B).add hg
  have hB : (∫ y : alpha, B+g y ∂mu) = B+∫ y : alpha, g y ∂mu := by
    simpa only [one_mul] using integral_affine_c0 mu g B 1
  have h3 : Integrable (fun y : alpha => a*(A+f y)+(B+g y)) mu := h1.add h2
  rw [integral_const_mul, integral_add h1 h2, integral_affine_c0 mu f A a, hB]

theorem le_mul_time_exp_of_right_deriv_le {f fprime : ℝ → ℝ} {K eps T : ℝ}
    (hK : 0 ≤ K) (heps : 0 ≤ eps) (hT : 0 ≤ T) (hf : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ s ∈ Set.Ico 0 T, HasDerivWithinAt f (fprime s) (Set.Ici s) s)
    (h0 : f 0 ≤ 0) (hb : ∀ s ∈ Set.Ico 0 T, fprime s ≤ K*f s+eps) :
    f T ≤ eps*T*Real.exp (K*T) := by
  have hg := le_gronwallBound_of_liminf_deriv_right_le (a := 0) (b := T) (δ := 0)
    (K := K) (ε := eps) hf (fun x hx r hr => (hd x hx).liminf_right_slope_le hr) h0 hb
  have hTle : gronwallBound 0 K eps (T - 0) ≤ eps * T * Real.exp (K * T) := by
    simpa only [sub_zero] using gronwallBound_zero_le hK heps hT
  exact (hg T ⟨hT, le_rfl⟩).trans hTle

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
