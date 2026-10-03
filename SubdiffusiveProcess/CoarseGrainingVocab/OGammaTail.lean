module

public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaToolkit
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Homogenization.Probability.IndependentSums.GammaSigma.Basic
@[expose] public section




set_option autoImplicit false

open MeasureTheory Set Filter Topology ProbabilityTheory

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.OGamma

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

omit [MeasurableSpace Omega] in
theorem rpow_two (y : ℝ) : y ^ (2:ℝ) = y ^ (2:ℕ) := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

omit [MeasurableSpace Omega] in
/-- The level set of `integrand 2 (2A) X - 1` above `s` sits inside the tail of `X` at
`2A √(log (1+s))`.  This is the substitution that turns the layer cake into the hypothesis. -/
theorem level_subset {B : ℝ} (hB : 0 < B) {X : Omega → ℝ} {s : ℝ} (hs : 0 < s) :
    {omega : Omega | s < integrand 2 B X omega - 1}
      ⊆ {omega : Omega | B * Real.sqrt (Real.log (1+s)) ≤ X omega} := by
  have hL : (0:ℝ) < Real.log (1+s) := Real.log_pos (by linarith)
  intro omega homega
  simp only [Set.mem_setOf_eq, integrand] at homega ⊢
  set u : ℝ := B⁻¹ * max (X omega) 0 with hu
  have hunn : 0 ≤ u := by positivity
  have h1 : Real.log (1+s) < u ^ (2:ℕ) := by
    have h2 : 1 + s < Real.exp (u ^ (2:ℝ)) := by linarith
    have h3 := Real.log_lt_log (by linarith) h2
    rw [Real.log_exp, rpow_two] at h3
    exact h3
  have h4 : Real.sqrt (Real.log (1+s)) < u := by
    have := Real.sqrt_lt_sqrt hL.le h1
    rwa [Real.sqrt_sq hunn] at this
  have h5 : B * Real.sqrt (Real.log (1+s)) < max (X omega) 0 := by
    have h6 := mul_lt_mul_of_pos_left h4 hB
    rwa [hu, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hB), one_mul] at h6
  have h7 : (0:ℝ) < max (X omega) 0 := lt_of_le_of_lt (by positivity) h5
  rcases le_or_gt (X omega) 0 with hx | hx
  · rw [max_eq_right hx] at h7; exact absurd h7 (lt_irrefl 0)
  · rw [max_eq_left hx.le] at h5; exact h5.le

/-! ### The comparison integral `∫₀^∞ 2 (1+s)^{-4} ds = 2/3` -/

omit [MeasurableSpace Omega] in
theorem hasDerivAt_tailPrimitive {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun s : ℝ => -(2/3 : ℝ) / (1+s)^3) (2 / (1+x)^4) x := by
  have hpos : (0:ℝ) < 1 + x := by linarith
  have hu : HasDerivAt (fun s : ℝ => (1+s)^3) (3 * (1+x)^2) x := by
    simpa using! ((hasDerivAt_id x).const_add (1:ℝ)).pow 3
  have h := (hasDerivAt_const x (-(2/3):ℝ)).div hu (by positivity)
  convert h using 1
  field_simp
  ring

omit [MeasurableSpace Omega] in
theorem tendsto_tailPrimitive :
    Tendsto (fun s : ℝ => -(2/3 : ℝ) / (1+s)^3) atTop (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => 1 + s) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_id
  have h2 : Tendsto (fun s : ℝ => (1+s)^3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3:ℕ) ≠ 0)).comp h1
  have h3 := (h2.inv_tendsto_atTop).const_mul (-(2/3 : ℝ))
  rw [mul_zero] at h3
  simpa [div_eq_mul_inv] using h3

omit [MeasurableSpace Omega] in
theorem integrableOn_tail : IntegrableOn (fun s : ℝ => 2 / (1+s)^4) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg
    ((hasDerivAt_tailPrimitive le_rfl).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_tailPrimitive (le_of_lt hx))
    (fun x hx => by
      have : (0:ℝ) < 1 + x := by simp at hx; linarith
      positivity)
    tendsto_tailPrimitive

omit [MeasurableSpace Omega] in
theorem integral_tail : ∫ s in Ioi (0:ℝ), 2 / (1+s)^4 = 2/3 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (a := (0:ℝ)) (f := fun s : ℝ => -(2/3 : ℝ) / (1+s)^3) (f' := fun s : ℝ => 2 / (1+s)^4)
    (m := 0) ((hasDerivAt_tailPrimitive le_rfl).continuousAt.continuousWithinAt)
    (fun x hx => hasDerivAt_tailPrimitive (le_of_lt hx)) integrableOn_tail
    tendsto_tailPrimitive
  simpa using h

omit [MeasurableSpace Omega] in
theorem lintegral_tail :
    ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (2 / (1+s)^4) = ENNReal.ofReal (2/3) := by
  rw [← integral_tail]
  refine (ofReal_integral_eq_lintegral_ofReal integrableOn_tail ?_).symm
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  have : (0:ℝ) < 1 + s := by simp at hs; linarith
  positivity






theorem ogammaLE_of_layercake [IsProbabilityMeasure mu] {B : ℝ} (hB : 0 < B)
    {X : Omega → ℝ} (hXm : AEMeasurable X mu) {g : ℝ → ℝ}
    (hgnn : ∀ᵐ s ∂(volume.restrict (Ioi (0:ℝ))), 0 ≤ g s)
    (hgint : IntegrableOn g (Ioi 0)) (hgle : ∫ s in Ioi (0:ℝ), g s ≤ 1)
    (htail : ∀ s ∈ Ioi (0:ℝ),
      mu {omega | B * Real.sqrt (Real.log (1+s)) ≤ X omega} ≤ ENNReal.ofReal (g s)) :
    SubdiffusiveProcess.OGammaLE mu 2 B X := by
  set Z : Omega → ℝ := fun omega => integrand 2 B X omega - 1 with hZdef
  have hZnn : ∀ omega, 0 ≤ Z omega := by
    intro omega
    have h1 : (1:ℝ) ≤ integrand 2 B X omega :=
      Real.one_le_exp (Real.rpow_nonneg (by positivity) 2)
    simp only [hZdef]; linarith
  have hZm : AEMeasurable Z mu := (aemeasurable_integrand 2 B hXm).sub aemeasurable_const
  have hgL : ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (g s)
      = ENNReal.ofReal (∫ s in Ioi (0:ℝ), g s) :=
    (ofReal_integral_eq_lintegral_ofReal hgint hgnn).symm
  have hbound : ∫⁻ omega, ENNReal.ofReal (Z omega) ∂mu
      ≤ ENNReal.ofReal (∫ s in Ioi (0:ℝ), g s) := by
    rw [lintegral_eq_lintegral_meas_lt mu (Filter.Eventually.of_forall hZnn) hZm, ← hgL]
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact le_trans (measure_mono (level_subset hB hs)) (htail s hs)
  have hgnn' : 0 ≤ ∫ s in Ioi (0:ℝ), g s := integral_nonneg_of_ae hgnn
  have hZint : Integrable Z mu := by
    refine ⟨hZm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hZnn)]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hZle : ∫ omega, Z omega ∂mu ≤ ∫ s in Ioi (0:ℝ), g s := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hZnn)
      hZm.aestronglyMeasurable]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rwa [ENNReal.toReal_ofReal hgnn'] at h
  rw [ogammaLE_iff]
  have hsplit : integrand 2 B X = fun omega => Z omega + 1 := by
    funext omega; simp [hZdef]
  rw [hsplit]
  refine ⟨hZint.add (integrable_const 1), ?_⟩
  rw [integral_add hZint (integrable_const 1), integral_const, probReal_univ, smul_eq_mul,
    one_mul]
  linarith

/-- **A tail estimate gives back an `OGammaLE` bound**, at twice the scale.  The instance of
`ogammaLE_of_layercake` with `g s = 2 (1+s)^{-4}`, whose integral is `2/3 ≤ 1`. -/
theorem ogammaLE_of_tail [IsProbabilityMeasure mu] {A : ℝ} (hA : 0 < A) {X : Omega → ℝ}
    (hXm : AEMeasurable X mu)
    (htail : ∀ lam : ℝ, 0 < lam →
      mu {omega | lam ≤ X omega} ≤ ENNReal.ofReal (2 * Real.exp (-((lam / A) ^ (2:ℕ))))) :
    SubdiffusiveProcess.OGammaLE mu 2 (2 * A) X := by
  have hB : (0:ℝ) < 2 * A := by linarith
  refine ogammaLE_of_layercake hB hXm ?_ integrableOn_tail
    (by rw [integral_tail]; norm_num) ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have : (0:ℝ) < 1 + s := by simp at hs; linarith
    positivity
  · intro s hs
    have hs0 : (0:ℝ) < s := hs
    have hL : (0:ℝ) < Real.log (1+s) := Real.log_pos (by linarith)
    have hsq : (0:ℝ) < Real.sqrt (Real.log (1+s)) := Real.sqrt_pos.mpr hL
    have hlam : (0:ℝ) < (2*A) * Real.sqrt (Real.log (1+s)) := by positivity
    have hconv : 2 * Real.exp (-(((2*A) * Real.sqrt (Real.log (1+s)) / A) ^ (2:ℕ)))
        = 2 / (1+s)^4 := by
      have hratio : (2*A) * Real.sqrt (Real.log (1+s)) / A
          = 2 * Real.sqrt (Real.log (1+s)) := by field_simp
      rw [hratio, mul_pow, Real.sq_sqrt hL.le]
      have hlog : Real.log ((1+s)^(4:ℕ)) = 4 * Real.log (1+s) := by
        rw [Real.log_pow]; norm_num
      have hkey : (2:ℝ)^(2:ℕ) * Real.log (1+s) = Real.log ((1+s)^(4:ℕ)) := by
        rw [hlog]; norm_num
      rw [hkey, Real.exp_neg, Real.exp_log (by positivity)]
      ring
    rw [← hconv]
    exact htail _ hlam

/-- The same, from a tail estimate stated with `Measure.real` — the form Mathlib's Chernoff
bounds produce. -/
theorem ogammaLE_of_measureReal_tail [IsProbabilityMeasure mu] {A : ℝ} (hA : 0 < A)
    {X : Omega → ℝ} (hXm : AEMeasurable X mu)
    (htail : ∀ lam : ℝ, 0 < lam →
      mu.real {omega | lam ≤ X omega} ≤ 2 * Real.exp (-((lam / A) ^ (2:ℕ)))) :
    SubdiffusiveProcess.OGammaLE mu 2 (2 * A) X := by
  refine ogammaLE_of_tail hA hXm fun lam hlam => ?_
  have hfin : mu {omega | lam ≤ X omega} ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal (htail lam hlam)

/-- **Mathlib's sub-Gaussian variables satisfy `OGammaLE`.** -/
theorem ogammaLE_of_hasSubgaussianMGF [IsProbabilityMeasure mu] {X : Omega → ℝ} {c : NNReal}
    (hc : 0 < (c : ℝ)) (h : HasSubgaussianMGF X c mu) :
    SubdiffusiveProcess.OGammaLE mu 2 (2 * Real.sqrt (2 * c)) X := by
  have hA : 0 < Real.sqrt (2 * (c:ℝ)) := Real.sqrt_pos.mpr (by linarith)
  refine ogammaLE_of_measureReal_tail hA h.aemeasurable fun lam hlam => ?_
  have hsq : (lam / Real.sqrt (2 * (c:ℝ))) ^ (2:ℕ) = lam ^ (2:ℕ) / (2 * (c:ℝ)) := by
    rw [div_pow, Real.sq_sqrt (by linarith)]
  have hch := h.measure_ge_le hlam.le
  rw [hsq]
  calc mu.real {omega | lam ≤ X omega} ≤ Real.exp (-lam ^ 2 / (2 * (c:ℝ))) := hch
    _ = Real.exp (-(lam ^ (2:ℕ) / (2 * (c:ℝ)))) := by rw [neg_div]
    _ ≤ 2 * Real.exp (-(lam ^ (2:ℕ) / (2 * (c:ℝ)))) := by
        nlinarith [Real.exp_pos (-(lam ^ (2:ℕ) / (2 * (c:ℝ))))]

/-- **The `√n`.**  A sum of `n` independent variables, each sub-Gaussian with proxy `c`,
satisfies `OGammaLE` at scale `2√(2nc)` — growing like `√n`, not like `n`.  This is the shape
of the paper's random-factor tails, and it is *not* reachable from `ogammaLE_add`, which gives
only the triangle inequality; independence is what buys the square root. -/
theorem ogammaLE_sum_range_of_iIndepFun [IsProbabilityMeasure mu] {X : ℕ → Omega → ℝ}
    (h_indep : iIndepFun X mu) {c : NNReal} {n : ℕ} (hn : 0 < n) (hc : 0 < (c : ℝ))
    (h_subG : ∀ i < n, HasSubgaussianMGF (X i) c mu) :
    SubdiffusiveProcess.OGammaLE mu 2 (2 * Real.sqrt (2 * n * c)) (fun omega => ∑ i ∈ Finset.range n, X i omega) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hprod : (0:ℝ) < 2 * n * (c:ℝ) := by positivity
  have hA : 0 < Real.sqrt (2 * n * (c:ℝ)) := Real.sqrt_pos.mpr hprod
  have hmeas : AEMeasurable (fun omega => ∑ i ∈ Finset.range n, X i omega) mu :=
    (HasSubgaussianMGF.sum_of_iIndepFun h_indep
      (fun i hi => h_subG i (Finset.mem_range.mp hi))).aemeasurable
  refine ogammaLE_of_measureReal_tail hA hmeas fun lam hlam => ?_
  have hsq : (lam / Real.sqrt (2 * n * (c:ℝ))) ^ (2:ℕ) = lam ^ (2:ℕ) / (2 * n * (c:ℝ)) := by
    rw [div_pow, Real.sq_sqrt hprod.le]
  have hch := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun h_indep h_subG hlam.le
  rw [hsq]
  calc mu.real {omega | lam ≤ ∑ i ∈ Finset.range n, X i omega}
      ≤ Real.exp (-lam ^ 2 / (2 * n * (c:ℝ))) := hch
    _ = Real.exp (-(lam ^ (2:ℕ) / (2 * n * (c:ℝ)))) := by rw [neg_div]
    _ ≤ 2 * Real.exp (-(lam ^ (2:ℕ) / (2 * n * (c:ℝ)))) := by
        nlinarith [Real.exp_pos (-(lam ^ (2:ℕ) / (2 * n * (c:ℝ))))]




theorem ogammaLE_of_isBigO_gammaTwo_aemeasurable [IsProbabilityMeasure mu] {A : ℝ}
    (hA : 0 < A) {X : Omega → ℝ} (hXm : AEMeasurable X mu)
    (h : Homogenization.IndependentSums.IsBigO mu
      (Homogenization.IndependentSums.gammaSigma 2) X A) :
    SubdiffusiveProcess.OGammaLE mu 2 (6 * A) X := by
  have h3A : (0:ℝ) < 3 * A := by linarith
  have hiff := Homogenization.IndependentSums.isBigO_gammaSigma_iff.mp h
  have hlog2 : (4:ℝ)/9 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hmain : ∀ lam : ℝ, 0 < lam →
      mu.real {omega | lam ≤ X omega} ≤ 2 * Real.exp (-((lam / (3 * A)) ^ (2:ℕ))) := by
    intro lam hlam
    by_cases hcase : lam ≤ 2 * A
    · have hratio : (lam / (3 * A)) ^ (2:ℕ) ≤ (4:ℝ)/9 := by
        have h1 : lam / (3 * A) ≤ 2/3 := by rw [div_le_iff₀ h3A]; linarith
        have h2 : (0:ℝ) ≤ lam / (3 * A) := by positivity
        nlinarith [h1, h2]
      have hexp : (1:ℝ)/2 ≤ Real.exp (-((lam / (3 * A)) ^ (2:ℕ))) := by
        calc (1:ℝ)/2 = Real.exp (-Real.log 2) := by
              rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
          _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
      have hone : mu.real {omega | lam ≤ X omega} ≤ 1 := measureReal_le_one
      linarith
    · push_neg at hcase
      have ht1 : (1:ℝ) ≤ lam / (2 * A) := by rw [le_div_iff₀ (by linarith)]; linarith
      have hsub : {omega | lam ≤ X omega}
          ⊆ Homogenization.IndependentSums.absTailEvent X (A * (lam / (2 * A))) := by
        intro omega homega
        have hval : A * (lam / (2 * A)) = lam / 2 := by field_simp
        have hx : lam / 2 < |X omega| := by
          have : lam ≤ |X omega| := le_trans homega (le_abs_self _)
          linarith
        simpa [Homogenization.IndependentSums.absTailEvent,
          Homogenization.IndependentSums.upperTailEvent, hval] using hx
      have hge : (lam / (3 * A)) ^ (2:ℕ) ≤ (lam / (2 * A)) ^ (2:ℕ) := by
        have h1 : lam / (3 * A) ≤ lam / (2 * A) :=
          div_le_div_of_nonneg_left hlam.le (by linarith) (by linarith)
        have h2 : (0:ℝ) ≤ lam / (3 * A) := by positivity
        nlinarith [h1, h2]
      calc mu.real {omega | lam ≤ X omega}
          ≤ mu.real (Homogenization.IndependentSums.absTailEvent X (A * (lam / (2 * A)))) :=
            measureReal_mono hsub (measure_ne_top _ _)
        _ ≤ Real.exp (-((lam / (2 * A)) ^ (2:ℝ))) := hiff ht1
        _ = Real.exp (-((lam / (2 * A)) ^ (2:ℕ))) := by rw [rpow_two]
        _ ≤ Real.exp (-((lam / (3 * A)) ^ (2:ℕ))) :=
            Real.exp_le_exp.mpr (by linarith)
        _ ≤ 2 * Real.exp (-((lam / (3 * A)) ^ (2:ℕ))) := by
            nlinarith [Real.exp_pos (-((lam / (3 * A)) ^ (2:ℕ)))]
  have hfin := ogammaLE_of_measureReal_tail h3A hXm hmain
  simpa [show (2:ℝ) * (3 * A) = 6 * A by ring] using hfin

end SubdiffusiveProcess.CoarseGrainingVocab.OGamma
