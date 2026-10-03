module

public import SubdiffusiveProcess.Frozen.Assumptions.OGammaLE
@[expose] public section




set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.OGamma

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- The Orlicz integrand of `OGammaLE`, named so the lemmas below can talk about it. -/
def integrand (sigma A : ℝ) (X : Omega → ℝ) : Omega → ℝ :=
  fun omega => Real.exp ((A⁻¹ * max (X omega) 0) ^ sigma)

/-- `OGammaLE` folded through `integrand`. -/
theorem ogammaLE_iff (sigma A : ℝ) (X : Omega → ℝ) :
    SubdiffusiveProcess.OGammaLE mu sigma A X ↔
      Integrable (integrand sigma A X) mu ∧ ∫ omega, integrand sigma A X omega ∂mu ≤ 2 :=
  Iff.rfl

omit [MeasurableSpace Omega] in
theorem integrand_pos (sigma A : ℝ) (X : Omega → ℝ) (omega : Omega) :
    0 < integrand sigma A X omega := Real.exp_pos _

theorem aemeasurable_integrand (sigma A : ℝ) {X : Omega → ℝ} (hX : AEMeasurable X mu) :
    AEMeasurable (integrand sigma A X) mu := by
  unfold integrand; fun_prop

omit [MeasurableSpace Omega] in
/-- The integrand is monotone in `X`: it sees only the positive part. -/
theorem integrand_mono {sigma A : ℝ} (hA : 0 < A) (hsigma : 0 ≤ sigma)
    {X Y : Omega → ℝ} {omega : Omega} (h : X omega ≤ Y omega) :
    integrand sigma A X omega ≤ integrand sigma A Y omega := by
  refine Real.exp_le_exp.mpr (Real.rpow_le_rpow (by positivity) ?_ hsigma)
  exact mul_le_mul_of_nonneg_left (max_le_max h le_rfl) (le_of_lt (inv_pos.mpr hA))

omit [MeasurableSpace Omega] in
/-- The integrand is antitone in the scale `A`. -/
theorem integrand_antitone_scale {sigma A A' : ℝ} (hA : 0 < A) (hAA : A ≤ A')
    (hsigma : 0 ≤ sigma) {X : Omega → ℝ} (omega : Omega) :
    integrand sigma A' X omega ≤ integrand sigma A X omega := by
  have hA' : 0 < A' := lt_of_lt_of_le hA hAA
  refine Real.exp_le_exp.mpr (Real.rpow_le_rpow (by positivity) ?_ hsigma)
  exact mul_le_mul_of_nonneg_right (by rwa [inv_le_inv₀ hA' hA]) (le_max_right _ _)

/-- The zero variable satisfies `OGammaLE` at every exponent and every scale: the integrand
collapses to `1`, and a probability measure integrates that to `1 ≤ 2`. -/
theorem ogammaLE_zero [IsProbabilityMeasure mu] (sigma A : ℝ) (hsigma : sigma ≠ 0) :
    SubdiffusiveProcess.OGammaLE mu sigma A (fun _ : Omega => (0 : ℝ)) := by
  have h0 : integrand sigma A (fun _ : Omega => (0:ℝ)) = fun _ : Omega => (1 : ℝ) := by
    funext omega
    simp only [integrand, max_self, mul_zero]
    rw [Real.zero_rpow hsigma, Real.exp_zero]
  rw [ogammaLE_iff, h0]
  exact ⟨integrable_const 1, by rw [integral_const, probReal_univ]; norm_num⟩

/-- A constant qualifies once the scale is large enough. -/
theorem ogammaLE_const [IsProbabilityMeasure mu] {sigma A c : ℝ}
    (hbound : (A⁻¹ * max c 0) ^ sigma ≤ Real.log 2) :
    SubdiffusiveProcess.OGammaLE mu sigma A (fun _ : Omega => c) := by
  have h0 : integrand sigma A (fun _ : Omega => c)
      = fun _ : Omega => Real.exp ((A⁻¹ * max c 0) ^ sigma) := rfl
  rw [ogammaLE_iff, h0]
  refine ⟨integrable_const _, ?_⟩
  rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  calc Real.exp ((A⁻¹ * max c 0) ^ sigma) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr hbound
    _ = 2 := Real.exp_log (by norm_num)

/-- **`OGammaLE` is monotone in the variable.** -/
theorem ogammaLE_of_ae_le {sigma A : ℝ} (hA : 0 < A) (hsigma : 0 ≤ sigma)
    {X Y : Omega → ℝ} (hX : AEMeasurable X mu) (hle : ∀ᵐ omega ∂mu, X omega ≤ Y omega)
    (hY : SubdiffusiveProcess.OGammaLE mu sigma A Y) :
    SubdiffusiveProcess.OGammaLE mu sigma A X := by
  rw [ogammaLE_iff] at hY ⊢
  have hdom : ∀ᵐ omega ∂mu, ‖integrand sigma A X omega‖ ≤ integrand sigma A Y omega := by
    filter_upwards [hle] with omega h
    rw [Real.norm_eq_abs, abs_of_pos (integrand_pos _ _ _ _)]
    exact integrand_mono hA hsigma h
  have hint : Integrable (integrand sigma A X) mu :=
    Integrable.mono' hY.1 (aemeasurable_integrand sigma A hX).aestronglyMeasurable hdom
  refine ⟨hint, le_trans (integral_mono_ae hint hY.1 ?_) hY.2⟩
  filter_upwards [hle] with omega h using integrand_mono hA hsigma h

/-- **`OGammaLE` is antitone in the scale**: a larger `A` is a weaker requirement. -/
theorem ogammaLE_mono_scale {sigma A A' : ℝ} (hA : 0 < A) (hAA : A ≤ A') (hsigma : 0 ≤ sigma)
    {X : Omega → ℝ} (hX : AEMeasurable X mu) (h : SubdiffusiveProcess.OGammaLE mu sigma A X) :
    SubdiffusiveProcess.OGammaLE mu sigma A' X := by
  rw [ogammaLE_iff] at h ⊢
  have hdom : ∀ᵐ omega ∂mu, ‖integrand sigma A' X omega‖ ≤ integrand sigma A X omega := by
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_pos (integrand_pos _ _ _ _)]
    exact integrand_antitone_scale hA hAA hsigma omega
  have hint : Integrable (integrand sigma A' X) mu :=
    Integrable.mono' h.1 (aemeasurable_integrand sigma A' hX).aestronglyMeasurable hdom
  exact ⟨hint, le_trans (integral_mono hint h.1
    (fun omega => integrand_antitone_scale hA hAA hsigma omega)) h.2⟩

/-- **An `OGammaLE` bound is a tail estimate.**  `μ{X ≥ λ} ≤ 2 exp(-(λ/A)^σ)` for `λ ≥ 0`,
by Markov's inequality applied to the exponential moment.  This is the direction every
consumer of a `StoppingTailBound` needs. -/
theorem measureReal_ge_le_of_ogammaLE [IsFiniteMeasure mu] {sigma A : ℝ} {X : Omega → ℝ}
    (h : SubdiffusiveProcess.OGammaLE mu sigma A X) (hA : 0 < A) (hsigma : 0 ≤ sigma)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    mu.real {omega | lam ≤ X omega} ≤ 2 * Real.exp (-((A⁻¹ * lam) ^ sigma)) := by
  rw [ogammaLE_iff] at h
  set eps : ℝ := Real.exp ((A⁻¹ * lam) ^ sigma) with heps
  have hepspos : 0 < eps := Real.exp_pos _
  have hsub : {omega | lam ≤ X omega} ⊆ {omega | eps ≤ integrand sigma A X omega} := by
    intro omega homega
    have hmax : lam ≤ max (X omega) 0 := le_max_of_le_left homega
    refine Real.exp_le_exp.mpr (Real.rpow_le_rpow (by positivity) ?_ hsigma)
    exact mul_le_mul_of_nonneg_left hmax (le_of_lt (inv_pos.mpr hA))
  have hmono : mu.real {omega | lam ≤ X omega}
      ≤ mu.real {omega | eps ≤ integrand sigma A X omega} :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun omega => (integrand_pos sigma A X omega).le) h.1 eps
  have hchain : eps * mu.real {omega | lam ≤ X omega} ≤ 2 :=
    le_trans (le_trans (mul_le_mul_of_nonneg_left hmono hepspos.le) hmarkov) h.2
  have hdiv : mu.real {omega | lam ≤ X omega} ≤ 2 / Real.exp ((A⁻¹ * lam) ^ sigma) := by
    rw [le_div_iff₀ hepspos, mul_comm]
    exact hchain
  rwa [div_eq_mul_inv, ← Real.exp_neg] at hdiv

omit [MeasurableSpace Omega] in
/-- The pointwise heart of `ogammaLE_add`: at `A = A₁ + A₂` the integrand of the sum is
dominated by the `θ`-average of the two integrands, `θ = A₁ / (A₁ + A₂)`. -/
theorem integrand_add_le {sigma A1 A2 : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2) (hsigma : 1 ≤ sigma)
    {X Y : Omega → ℝ} (omega : Omega) :
    integrand sigma (A1 + A2) (fun w => X w + Y w) omega
      ≤ (A1 / (A1 + A2)) * integrand sigma A1 X omega
        + (A2 / (A1 + A2)) * integrand sigma A2 Y omega := by
  have hA : 0 < A1 + A2 := by linarith
  set u : ℝ := A1⁻¹ * max (X omega) 0 with hu
  set v : ℝ := A2⁻¹ * max (Y omega) 0 with hv
  have hu0 : 0 ≤ u := by positivity
  have hv0 : 0 ≤ v := by positivity
  set th : ℝ := A1 / (A1 + A2) with hth
  have hth0 : 0 ≤ th := by positivity
  have hth1 : 0 ≤ A2 / (A1 + A2) := by positivity
  have hAne : A1 + A2 ≠ 0 := ne_of_gt hA
  have hthsum : th + A2 / (A1 + A2) = 1 := by rw [hth]; field_simp
  -- the argument of the outer exponential is a convex combination
  have harg : (A1 + A2)⁻¹ * max (X omega + Y omega) 0 ≤ th * u + (A2 / (A1 + A2)) * v := by
    have hmax : max (X omega + Y omega) 0 ≤ max (X omega) 0 + max (Y omega) 0 :=
      max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
        (by positivity)
    have hcomb : th * u + (A2 / (A1 + A2)) * v
        = (A1 + A2)⁻¹ * (max (X omega) 0 + max (Y omega) 0) := by
      rw [hth, hu, hv]
      field_simp
    rw [hcomb]
    exact mul_le_mul_of_nonneg_left hmax (by positivity)
  -- convexity of `t ^ sigma` on `[0, ∞)`
  have hrpow : (th * u + (A2 / (A1 + A2)) * v) ^ sigma ≤ th * u ^ sigma
      + (A2 / (A1 + A2)) * v ^ sigma :=
    (convexOn_rpow hsigma).2 (Set.mem_Ici.mpr hu0) (Set.mem_Ici.mpr hv0)
      hth0 hth1 hthsum
  -- convexity of `exp`
  have hexp : Real.exp (th * u ^ sigma + (A2 / (A1 + A2)) * v ^ sigma)
      ≤ th * Real.exp (u ^ sigma) + (A2 / (A1 + A2)) * Real.exp (v ^ sigma) :=
    convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) hth0 hth1 hthsum
  refine le_trans (Real.exp_le_exp.mpr (le_trans (Real.rpow_le_rpow (by positivity) harg
    (by linarith)) hrpow)) hexp

/-- **The scales add.**  No constant is lost: `A₁ + A₂` is the right scale for `X + Y`.
Requires `σ ≥ 1`, which is where the convexity of `t ↦ t^σ` is used; both exponents occurring
in `StoppingTailBound` (`σ = 1` and `σ = 2`) qualify. -/
theorem ogammaLE_add {sigma A1 A2 : ℝ} (hA1 : 0 < A1) (hA2 : 0 < A2) (hsigma : 1 ≤ sigma)
    {X Y : Omega → ℝ} (hX : AEMeasurable X mu) (hY : AEMeasurable Y mu)
    (hXo : SubdiffusiveProcess.OGammaLE mu sigma A1 X) (hYo : SubdiffusiveProcess.OGammaLE mu sigma A2 Y) :
    SubdiffusiveProcess.OGammaLE mu sigma (A1 + A2) (fun omega => X omega + Y omega) := by
  rw [ogammaLE_iff] at hXo hYo ⊢
  have hA : 0 < A1 + A2 := by linarith
  set th : ℝ := A1 / (A1 + A2) with hth
  set th' : ℝ := A2 / (A1 + A2) with hth'
  have hth0 : 0 ≤ th := by positivity
  have hth'0 : 0 ≤ th' := by positivity
  have hAne : A1 + A2 ≠ 0 := ne_of_gt hA
  have hthsum : th + th' = 1 := by rw [hth, hth']; field_simp
  have hbound : Integrable
      (fun omega => th * integrand sigma A1 X omega + th' * integrand sigma A2 Y omega) mu :=
    (hXo.1.const_mul th).add (hYo.1.const_mul th')
  have hdom : ∀ omega, integrand sigma (A1 + A2) (fun w => X w + Y w) omega
      ≤ th * integrand sigma A1 X omega + th' * integrand sigma A2 Y omega :=
    fun omega => integrand_add_le hA1 hA2 hsigma omega
  have hmeas : AEMeasurable (integrand sigma (A1 + A2) (fun w => X w + Y w)) mu :=
    aemeasurable_integrand _ _ (hX.add hY)
  have hint : Integrable (integrand sigma (A1 + A2) (fun w => X w + Y w)) mu := by
    refine Integrable.mono' hbound hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (integrand_pos _ _ _ _)]
    exact hdom omega
  refine ⟨hint, ?_⟩
  calc ∫ omega, integrand sigma (A1 + A2) (fun w => X w + Y w) omega ∂mu
      ≤ ∫ omega, (th * integrand sigma A1 X omega + th' * integrand sigma A2 Y omega) ∂mu :=
        integral_mono hint hbound hdom
    _ = th * (∫ omega, integrand sigma A1 X omega ∂mu)
          + th' * ∫ omega, integrand sigma A2 Y omega ∂mu := by
        rw [integral_add (hXo.1.const_mul th) (hYo.1.const_mul th'),
          integral_const_mul, integral_const_mul]
    _ ≤ th * 2 + th' * 2 := by
        exact add_le_add (mul_le_mul_of_nonneg_left hXo.2 hth0)
          (mul_le_mul_of_nonneg_left hYo.2 hth'0)
    _ = 2 := by rw [← add_mul, hthsum, one_mul]

/-! ### First moments -/

omit [MeasurableSpace Omega] in
/-- `y ≤ exp (y ^ σ)` for `y ≥ 0` and `σ ≥ 1`: below `1` the exponential is already at least
`1`, and above it `y ≤ y ^ σ ≤ exp (y ^ σ)`. -/
theorem le_exp_rpow {y sigma : ℝ} (hy : 0 ≤ y) (hsigma : 1 ≤ sigma) :
    y ≤ Real.exp (y ^ sigma) := by
  rcases le_or_gt y 1 with h | h
  · exact h.trans (Real.one_le_exp (Real.rpow_nonneg hy sigma))
  · have h1 : y ≤ y ^ sigma := by
      calc y = y ^ (1:ℝ) := (Real.rpow_one y).symm
        _ ≤ y ^ sigma := Real.rpow_le_rpow_of_exponent_le h.le hsigma
    exact h1.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))

/-- **A nonnegative variable with an `OGammaLE` bound has first moment at most `2A`.**

`Section6Discharge`, `Section5Support/CellSupMoment`, `CutoffMoments` and `ShellSensitivity`
each derive this by hand from `M.G2.regularity_expectation`; this is the general statement
they are instances of. -/
theorem integral_le_of_ogammaLE_nonneg {sigma A : ℝ} {X : Omega → ℝ}
    (h : SubdiffusiveProcess.OGammaLE mu sigma A X) (hA : 0 < A) (hsigma : 1 ≤ sigma)
    (hXm : AEMeasurable X mu) (hXnn : ∀ omega, 0 ≤ X omega) :
    Integrable X mu ∧ ∫ omega, X omega ∂mu ≤ 2 * A := by
  rw [ogammaLE_iff] at h
  have hpoint : ∀ omega, X omega ≤ A * integrand sigma A X omega := by
    intro omega
    have hy : 0 ≤ A⁻¹ * X omega := mul_nonneg (inv_nonneg.mpr hA.le) (hXnn omega)
    have hexp := le_exp_rpow hy hsigma
    have hxy : X omega = A * (A⁻¹ * X omega) := by field_simp
    rw [hxy]
    refine mul_le_mul_of_nonneg_left ?_ hA.le
    simpa [integrand, max_eq_left (hXnn omega)] using hexp
  have hint : Integrable X mu := by
    refine (h.1.const_mul A).mono' hXm.aestronglyMeasurable ?_
    filter_upwards with omega
    rw [Real.norm_of_nonneg (hXnn omega)]
    exact hpoint omega
  refine ⟨hint, ?_⟩
  calc ∫ omega, X omega ∂mu ≤ ∫ omega, A * integrand sigma A X omega ∂mu :=
        integral_mono hint (h.1.const_mul A) hpoint
    _ = A * ∫ omega, integrand sigma A X omega ∂mu := integral_const_mul _ _
    _ ≤ A * 2 := mul_le_mul_of_nonneg_left h.2 hA.le
    _ = 2 * A := by ring

/-! ### Scale arithmetic

`ogammaLE_add` returns the *sum* of the two scales, and the anchors ask for a single square
root of a sum.  These are the conversions. -/

omit [MeasurableSpace Omega] in
/-- `√a + √b ≤ √2 √(a+b)`. -/
theorem sqrt_add_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a + Real.sqrt b ≤ Real.sqrt 2 * Real.sqrt (a + b) := by
  have hsum : (0:ℝ) ≤ a + b := by linarith
  have hsq : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ (Real.sqrt 2 * Real.sqrt (a + b)) ^ 2 := by
    have h1 : (Real.sqrt a + Real.sqrt b) ^ 2
        = a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
      rw [add_pow_two, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
    have h2 : (Real.sqrt 2 * Real.sqrt (a + b)) ^ 2 = 2 * (a + b) := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sq_sqrt hsum]
    have h3 : 2 * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
      have := sq_nonneg (Real.sqrt a - Real.sqrt b)
      have hA := Real.sq_sqrt ha
      have hB := Real.sq_sqrt hb
      nlinarith [this, hA, hB]
    rw [h1, h2]; linarith
  have hnn : 0 ≤ Real.sqrt a + Real.sqrt b := by positivity
  have hy : 0 ≤ Real.sqrt 2 * Real.sqrt (a + b) := by positivity
  calc Real.sqrt a + Real.sqrt b
      = Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Real.sqrt 2 * Real.sqrt (a + b)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt 2 * Real.sqrt (a + b) := Real.sqrt_sq hy

omit [MeasurableSpace Omega] in
/-- A constant is below any square root that is at least one, so an additive constant term is
absorbed by the anchors' `√(m+1+…)` shape. -/
theorem le_sqrt_of_one_le {a : ℝ} (ha : 1 ≤ a) : (1:ℝ) ≤ Real.sqrt a := by
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt ha

end SubdiffusiveProcess.CoarseGrainingVocab.OGamma
