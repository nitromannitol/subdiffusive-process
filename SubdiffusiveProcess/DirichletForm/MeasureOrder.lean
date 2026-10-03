/-
# From an order of forms to an order of energy measures: the sine/cosine identity
-/
module

public import SubdiffusiveProcess.DirichletForm.SinCos
public import SubdiffusiveProcess.DirichletForm.Weighted
public import SubdiffusiveProcess.DirichletForm.MeasureComparison

@[expose] public section

/-!
# The sine/cosine identity for energy measures

The comparison of energy measures from a comparison of forms rests on one
identity.  For core functions `u, v` and `k > 0`, applying the Leibniz rule to
`v Φ_k^s(u)` and to `v Φ_k^c(u)` and adding, the derivative squares sum to `1`,
the cross terms cancel, and the last terms sum to `k⁻²`:

`Γ(vΦ_k^s(u))(B) + Γ(vΦ_k^c(u))(B) = ∫_B v² dΓ(u) + k⁻² Γ(v)(B)`.

Taking `B = X` this is
`E(vΦ_k^s(u)) + E(vΦ_k^c(u)) = ∫ v² dΓ_E(u) + k⁻² E(v)`, which is the display in
the proof of the paper's `mfd:lem-sincos`.  Applying a form bound to both
functions and letting `k → ∞` then gives `∫ v² dΓ_F(u) ≤ C ∫ v² dΓ_E(u)`.

This file proves the identity (all three terms separately, then the sum) and the
`k → ∞` step.  Everything is stated over the library carriers; nothing here is a
paper conclusion.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  {m : Measure X}

namespace DirichletForm

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
/-- A continuous compactly supported real function is bounded. -/
theorem exists_bound_of_hasCompactSupport {f : X → ℝ} (hcs : HasCompactSupport f)
    (hf : Continuous f) : ∃ C : ℝ, ∀ x : X, |f x| ≤ C := by
  simpa using hcs.exists_bound_of_continuous hf

/-- A product of squares of bounded continuous functions is integrable against a
finite measure. -/
theorem integrable_sq_mul_sq {μ : Measure X} [IsFiniteMeasure μ] {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) {C D : ℝ}
    (hC : ∀ x : X, |f x| ≤ C) (hD : ∀ x : X, |g x| ≤ D) :
    Integrable (fun x => f x ^ 2 * g x ^ 2) μ := by
  refine integrable_of_continuous_of_bound (by fun_prop) (C := C ^ 2 * D ^ 2) fun x => ?_
  have h1 : f x ^ 2 ≤ C ^ 2 := by nlinarith [abs_nonneg (f x), hC x, sq_abs (f x)]
  have h2 : g x ^ 2 ≤ D ^ 2 := by nlinarith [abs_nonneg (g x), hD x, sq_abs (g x)]
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (f x), sq_nonneg (g x), sq_nonneg C, sq_nonneg D]

namespace EnergyMeasure

variable {E : ClosedForm m} (Γ : EnergyMeasure E)

/-- The first terms of the two Leibniz expansions add up to `∫_B v² dΓ(u)`:
`(Φ_k^s)'² + (Φ_k^c)'² = 1`. -/
theorem setIntegral_sq_mul_sq_deriv_sinCos_add {u : Lp ℝ 2 m} (hu : u ∈ E.domain)
    {uc vc : X → ℝ} (hucont : Continuous uc) (hvcont : Continuous vc)
    {Cv : ℝ} (hCv : ∀ x : X, |vc x| ≤ Cv) {k : ℝ} (hk : k ≠ 0) (B : Set X) :
    (∫ x in B, vc x ^ 2 * deriv (sinScaled k) (uc x) ^ 2 ∂(Γ.measure u)) +
        (∫ x in B, vc x ^ 2 * deriv (cosScaled k) (uc x) ^ 2 ∂(Γ.measure u)) =
      ∫ x in B, vc x ^ 2 ∂(Γ.measure u) := by
  haveI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.measure_univ_lt_top u hu⟩
  simp only [deriv_sinScaled hk, deriv_cosScaled hk]
  have hcos : ∀ x : X, |Real.cos (k * uc x)| ≤ 1 := fun x =>
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hsin : ∀ x : X, |(-Real.sin (k * uc x))| ≤ 1 := fun x => by
    rw [abs_neg]
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have h1 : Integrable (fun x => vc x ^ 2 * Real.cos (k * uc x) ^ 2)
      ((Γ.measure u).restrict B) := integrable_sq_mul_sq hvcont (by fun_prop) hCv hcos
  have h2 : Integrable (fun x => vc x ^ 2 * (-Real.sin (k * uc x)) ^ 2)
      ((Γ.measure u).restrict B) := integrable_sq_mul_sq hvcont (by fun_prop) hCv hsin
  rw [← integral_add h1 h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h := Real.sin_sq_add_cos_sq (k * uc x)
  simp only []
  linear_combination (vc x ^ 2) * h

omit [TopologicalSpace X] [OpensMeasurableSpace X] in
/-- The cross terms of the two Leibniz expansions cancel:
`Φ_k^s (Φ_k^s)' + Φ_k^c (Φ_k^c)' = 0`. -/
theorem signedIntegralOn_sinCos_cross_add (ν : SignedMeasure X) (B : Set X)
    (uc vc : X → ℝ) {k : ℝ} (hk : k ≠ 0) :
    signedIntegralOn ν B
        (fun x => vc x * sinScaled k (uc x) * deriv (sinScaled k) (uc x)) +
      signedIntegralOn ν B
        (fun x => vc x * cosScaled k (uc x) * deriv (cosScaled k) (uc x)) = 0 := by
  refine signedIntegralOn_add_eq_zero ν B fun x => ?_
  have h := sinScaled_mul_deriv_add_cosScaled_mul_deriv hk (uc x)
  linear_combination (vc x) * h

/-- The last terms of the two Leibniz expansions add up to `k⁻² Γ(v)(B)`:
`(Φ_k^s)² + (Φ_k^c)² = k⁻²`. -/
theorem setIntegral_sq_sinCos_add {v : Lp ℝ 2 m} (hv : v ∈ E.domain) {uc : X → ℝ}
    (hucont : Continuous uc) {k : ℝ} (hk : 0 < k) (B : Set X) :
    (∫ x in B, sinScaled k (uc x) ^ 2 ∂(Γ.measure v)) +
        (∫ x in B, cosScaled k (uc x) ^ 2 ∂(Γ.measure v)) =
      (k ^ 2)⁻¹ * (Γ.measure v B).toReal := by
  haveI : IsFiniteMeasure (Γ.measure v) := ⟨Γ.measure_univ_lt_top v hv⟩
  have hcont : Continuous fun x : X => sinScaled k (uc x) := by
    unfold sinScaled; fun_prop
  have hcont' : Continuous fun x : X => cosScaled k (uc x) := by
    unfold cosScaled; fun_prop
  have h1 : Integrable (fun x => sinScaled k (uc x) ^ 2) ((Γ.measure v).restrict B) := by
    simpa using integrable_sq_mul_sq (μ := (Γ.measure v).restrict B) hcont continuous_const
      (fun x => abs_sinScaled_le hk (uc x)) (fun _ => le_of_eq (abs_one))
  have h2 : Integrable (fun x => cosScaled k (uc x) ^ 2) ((Γ.measure v).restrict B) := by
    simpa using integrable_sq_mul_sq (μ := (Γ.measure v).restrict B) hcont' continuous_const
      (fun x => abs_cosScaled_le hk (uc x)) (fun _ => le_of_eq (abs_one))
  rw [← integral_add h1 h2]
  have hconst : (∫ x in B, (sinScaled k (uc x) ^ 2 + cosScaled k (uc x) ^ 2) ∂(Γ.measure v))
      = ∫ _x in B, (k ^ 2)⁻¹ ∂(Γ.measure v) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact sq_sinScaled_add_sq_cosScaled k (uc x)
  rw [hconst, setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]

/-- **The sine/cosine identity** (`mfd:lem-sincos`).  Adding
the Leibniz expansions of `v Φ_k^s(u)` and `v Φ_k^c(u)` collapses to
`∫_B v² dΓ(u) + k⁻² Γ(v)(B)`. -/
theorem toReal_measure_sinCos_add {u v : Lp ℝ 2 m} (hu : E.MemCore u) (hv : E.MemCore v)
    {uc vc : X → ℝ} (hucont : Continuous uc) (hvcont : Continuous vc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc)
    {Cv : ℝ} (hCv : ∀ x : X, |vc x| ≤ Cv) {k : ℝ} (hk : 0 < k)
    {ws wc : Lp ℝ 2 m} (hws : ws ∈ E.domain) (hwc : wc ∈ E.domain)
    (hwsrep : ⇑ws =ᵐ[m] fun x => vc x * sinScaled k (uc x))
    (hwcrep : ⇑wc =ᵐ[m] fun x => vc x * cosScaled k (uc x))
    {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure ws B).toReal + (Γ.measure wc B).toReal =
      (∫ x in B, vc x ^ 2 ∂(Γ.measure u)) + (k ^ 2)⁻¹ * (Γ.measure v B).toReal := by
  have hk' : k ≠ 0 := ne_of_gt hk
  rw [Γ.leibniz u v hu hv uc vc hucont hvcont huae hvae (sinScaled k)
      (contDiff_sinScaled k) ws hws hwsrep B hB,
    Γ.leibniz u v hu hv uc vc hucont hvcont huae hvae (cosScaled k)
      (contDiff_cosScaled k) wc hwc hwcrep B hB]
  have h1 := Γ.setIntegral_sq_mul_sq_deriv_sinCos_add hu.mem_domain hucont hvcont hCv hk' B
  have h2 := signedIntegralOn_sinCos_cross_add (Γ.cross u v) B uc vc hk'
  have h3 := Γ.setIntegral_sq_sinCos_add hv.mem_domain hucont hk B
  linarith [h1, h2, h3]

/-- The sine/cosine identity on the whole space, in terms of the form
(`mfd:lem-sincos`):
`E(vΦ_k^s(u)) + E(vΦ_k^c(u)) = ∫ v² dΓ_E(u) + k⁻² E(v)`. -/
theorem form_sinCos_add {u v : Lp ℝ 2 m} (hu : E.MemCore u) (hv : E.MemCore v)
    {uc vc : X → ℝ} (hucont : Continuous uc) (hvcont : Continuous vc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc)
    {Cv : ℝ} (hCv : ∀ x : X, |vc x| ≤ Cv) {k : ℝ} (hk : 0 < k)
    {ws wc : Lp ℝ 2 m} (hws : ws ∈ E.domain) (hwc : wc ∈ E.domain)
    (hwsrep : ⇑ws =ᵐ[m] fun x => vc x * sinScaled k (uc x))
    (hwcrep : ⇑wc =ᵐ[m] fun x => vc x * cosScaled k (uc x)) :
    E.form ws ws + E.form wc wc =
      (∫ x, vc x ^ 2 ∂(Γ.measure u)) + (k ^ 2)⁻¹ * E.form v v := by
  have h := Γ.toReal_measure_sinCos_add hu hv hucont hvcont huae hvae hCv hk hws hwc
    hwsrep hwcrep MeasurableSet.univ
  rw [Γ.measure_univ ws hws, Γ.measure_univ wc hwc, Γ.measure_univ v hv.mem_domain,
    Measure.restrict_univ] at h
  exact h

end EnergyMeasure

/-- If `a + k⁻² b ≤ c + k⁻² d` for every `k > 0` then `a ≤ c`: the `k → ∞` step
of the sine/cosine argument. -/
theorem le_of_forall_inv_sq_le {a b c d : ℝ}
    (h : ∀ k : ℝ, 0 < k → a + (k ^ 2)⁻¹ * b ≤ c + (k ^ 2)⁻¹ * d) : a ≤ c := by
  have key : ∀ n : ℕ, a - c ≤ (((n : ℝ) + 1) ^ 2)⁻¹ * (d - b) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h' := h ((n : ℝ) + 1) hn
    nlinarith [h']
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) atTop (𝓝 0) := by
    have h2 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
      simpa using h0.pow 2
    refine h2.congr fun n => ?_
    rw [div_pow, one_pow, one_div]
  have hlim : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹ * (d - b)) atTop (𝓝 0) := by
    simpa using h1.mul_const (d - b)
  have hle : a - c ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim key
  linarith

namespace EnergyMeasure

variable {E F : ClosedForm m} (ΓE : EnergyMeasure E) (ΓF : EnergyMeasure F)

/-- If `f ≤ g + ε` pointwise then the integrals differ by at most `ε` times the
total mass. -/
theorem integral_le_add_of_le_add {μ : Measure X} [IsFiniteMeasure μ] {f g : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) {ε : ℝ} (h : ∀ x : X, f x ≤ g x + ε) :
    (∫ x, f x ∂μ) ≤ (∫ x, g x ∂μ) + (μ Set.univ).toReal * ε := by
  have hmono := integral_mono hf (hg.add (integrable_const ε)) h
  simp only [Pi.add_apply] at hmono
  rw [integral_add hg (integrable_const ε), integral_const, measureReal_def, smul_eq_mul]
    at hmono
  exact hmono



theorem integral_le_of_unifApprox {ν μ : Measure X} [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {C : ℝ} (hC : 0 ≤ C) {φ : X → ℝ} (hφ : Continuous φ) {Mφ : ℝ}
    (hφb : ∀ x : X, |φ x| ≤ Mφ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ g : X → ℝ, Continuous g ∧ (∃ M : ℝ, ∀ x : X, |g x| ≤ M) ∧
      (∀ x : X, |g x - φ x| ≤ ε) ∧ (∫ x, g x ∂ν) ≤ C * ∫ x, g x ∂μ) :
    (∫ x, φ x ∂ν) ≤ C * ∫ x, φ x ∂μ := by
  have hφν : Integrable φ ν := integrable_of_continuous_of_bound hφ hφb
  have hφμ : Integrable φ μ := integrable_of_continuous_of_bound hφ hφb
  set A : ℝ := (ν Set.univ).toReal + C * (μ Set.univ).toReal with hAdef
  have hA : 0 ≤ A := by
    have h1 : (0 : ℝ) ≤ (ν Set.univ).toReal := ENNReal.toReal_nonneg
    have h2 : (0 : ℝ) ≤ (μ Set.univ).toReal := ENNReal.toReal_nonneg
    have := mul_nonneg hC h2
    rw [hAdef]; linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨g, hgc, ⟨Mg, hgb⟩, hclose, hle⟩ := h (δ / (A + 1)) (by positivity)
  have hgν : Integrable g ν := integrable_of_continuous_of_bound hgc hgb
  have hgμ : Integrable g μ := integrable_of_continuous_of_bound hgc hgb
  have h1 : (∫ x, φ x ∂ν) ≤ (∫ x, g x ∂ν) + (ν Set.univ).toReal * (δ / (A + 1)) :=
    integral_le_add_of_le_add hφν hgν fun x => by
      have := abs_le.mp (hclose x); linarith [this.1, this.2]
  have h2 : (∫ x, g x ∂μ) ≤ (∫ x, φ x ∂μ) + (μ Set.univ).toReal * (δ / (A + 1)) :=
    integral_le_add_of_le_add hgμ hφμ fun x => by
      have := abs_le.mp (hclose x); linarith [this.1, this.2]
  have h3 : C * (∫ x, g x ∂μ) ≤
      C * (∫ x, φ x ∂μ) + C * ((μ Set.univ).toReal * (δ / (A + 1))) := by
    have := mul_le_mul_of_nonneg_left h2 hC; linarith [this]
  have hfin : A * (δ / (A + 1)) ≤ δ := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ (by positivity : (0:ℝ) < A + 1)]
    nlinarith [hδ.le, hA]
  calc (∫ x, φ x ∂ν) ≤ (∫ x, g x ∂ν) + (ν Set.univ).toReal * (δ / (A + 1)) := h1
    _ ≤ C * (∫ x, g x ∂μ) + (ν Set.univ).toReal * (δ / (A + 1)) := by linarith [hle]
    _ ≤ C * (∫ x, φ x ∂μ) + A * (δ / (A + 1)) := by rw [hAdef]; nlinarith [h3]
    _ ≤ C * (∫ x, φ x ∂μ) + δ := by linarith [hfin]

/-- The cutoff estimate behind the core-square approximation
(`mfd:lem-sincos`).  If `w` approximates `√f` uniformly to
`δ` and the plateau `ϑ` is `1` wherever `f` does not vanish, then `(wϑ)²`
approximates `f` uniformly to `δ(δ + 2√M)`.

Off `supp f` the plateau may cut `w` down, but there `√f = 0`, so `|w| ≤ δ` and
the square is at most `δ²`; on `supp f` the plateau is `1` and the estimate is
the algebraic identity `|w² − f| = |w − √f| · |w + √f|`. -/
theorem abs_sq_mul_sub_le {f ϑ w : X → ℝ} {δ M : ℝ} (hδ : 0 ≤ δ)
    (hf0 : ∀ x : X, 0 ≤ f x) (hfM : ∀ x : X, f x ≤ M)
    (hϑ0 : ∀ x : X, 0 ≤ ϑ x) (hϑ1 : ∀ x : X, ϑ x ≤ 1)
    (hplateau : ∀ x : X, f x ≠ 0 → ϑ x = 1)
    (hw : ∀ x : X, |w x - Real.sqrt (f x)| ≤ δ) (x : X) :
    |(w x * ϑ x) ^ 2 - f x| ≤ δ * (δ + 2 * Real.sqrt M) := by
  have hsq : Real.sqrt (f x) ^ 2 = f x := Real.sq_sqrt (hf0 x)
  have hsnn : 0 ≤ Real.sqrt (f x) := Real.sqrt_nonneg _
  have hsM : Real.sqrt (f x) ≤ Real.sqrt M := Real.sqrt_le_sqrt (hfM x)
  have hMnn : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hd := abs_le.mp (hw x)
  by_cases hfx : f x = 0
  · have hs0 : Real.sqrt (f x) = 0 := by rw [hfx, Real.sqrt_zero]
    have hwb : |w x| ≤ δ := by rw [← sub_zero (w x), ← hs0]; exact hw x
    have hwd := abs_le.mp hwb
    have h1 : w x ^ 2 ≤ δ ^ 2 := sq_le_sq' hwd.1 hwd.2
    have h2 : ϑ x ^ 2 ≤ 1 := by nlinarith [hϑ0 x, hϑ1 x]
    have h3 : (w x * ϑ x) ^ 2 = w x ^ 2 * ϑ x ^ 2 := by ring
    have h4 : w x ^ 2 * ϑ x ^ 2 ≤ δ ^ 2 := by
      nlinarith [sq_nonneg (w x), sq_nonneg (ϑ x), h1, h2]
    rw [hfx, sub_zero, abs_of_nonneg (sq_nonneg _), h3]
    nlinarith [h4, mul_nonneg hδ hMnn]
  · have hϑx : ϑ x = 1 := hplateau x hfx
    rw [hϑx, mul_one, abs_le]
    constructor <;> nlinarith [hd.1, hd.2, hsq, hsnn, hsM, hδ, hMnn]

/-- **Step 7(a) of `mfd:lem-sincos`**: a
bound on the integrals of squares of core functions passes to any bounded
continuous `φ` that those squares approximate uniformly. -/
theorem integral_le_of_sq_approx {ν μ : Measure X} [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {C : ℝ} (hC : 0 ≤ C) {φ : X → ℝ} (hφ : Continuous φ) {Mφ : ℝ}
    (hφb : ∀ x : X, |φ x| ≤ Mφ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ vc : X → ℝ, Continuous vc ∧
      (∃ M : ℝ, ∀ x : X, |vc x| ≤ M) ∧ (∀ x : X, |vc x ^ 2 - φ x| ≤ ε) ∧
      (∫ x, vc x ^ 2 ∂ν) ≤ C * ∫ x, vc x ^ 2 ∂μ) :
    (∫ x, φ x ∂ν) ≤ C * ∫ x, φ x ∂μ := by
  refine integral_le_of_unifApprox hC hφ hφb fun ε hε => ?_
  obtain ⟨vc, hvc, ⟨M, hM⟩, hclose, hle⟩ := happrox ε hε
  refine ⟨fun x => vc x ^ 2, by fun_prop, ⟨M ^ 2, fun x => ?_⟩, hclose, hle⟩
  rw [abs_of_nonneg (sq_nonneg (vc x))]
  nlinarith [abs_nonneg (vc x), hM x, sq_abs (vc x)]

/-- **Step 6 of `mfd:lem-sincos`.**  If the
form bound `F ≤ C E` holds on the two core functions `vΦ_k^s(u)`, `vΦ_k^c(u)` for
every `k > 0`, then `∫ v² dΓ_F(u) ≤ C ∫ v² dΓ_E(u)`. -/
theorem integral_sq_measure_le_of_form_le (hdom : E.domain = F.domain) {C : ℝ}
    {u v : Lp ℝ 2 m} (hu : E.MemCore u) (hv : E.MemCore v)
    {uc vc : X → ℝ} (hucont : Continuous uc) (hvcont : Continuous vc)
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc)
    {Cv : ℝ} (hCv : ∀ x : X, |vc x| ≤ Cv)
    (hprod : ∀ k : ℝ, 0 < k → ∃ ws wc : Lp ℝ 2 m, ws ∈ E.domain ∧ wc ∈ E.domain ∧
      (⇑ws =ᵐ[m] fun x => vc x * sinScaled k (uc x)) ∧
      (⇑wc =ᵐ[m] fun x => vc x * cosScaled k (uc x)) ∧
      F.form ws ws ≤ C * E.form ws ws ∧ F.form wc wc ≤ C * E.form wc wc) :
    (∫ x, vc x ^ 2 ∂(ΓF.measure u)) ≤ C * ∫ x, vc x ^ 2 ∂(ΓE.measure u) := by
  refine le_of_forall_inv_sq_le (b := F.form v v) (d := C * E.form v v) fun k hk => ?_
  obtain ⟨ws, wc, hws, hwc, hwsrep, hwcrep, hFs, hFc⟩ := hprod k hk
  have huF : F.MemCore u := ⟨hdom ▸ hu.mem_domain, hu.hasCoreRep⟩
  have hvF : F.MemCore v := ⟨hdom ▸ hv.mem_domain, hv.hasCoreRep⟩
  have hE := ΓE.form_sinCos_add hu hv hucont hvcont huae hvae hCv hk hws hwc hwsrep hwcrep
  have hF := ΓF.form_sinCos_add huF hvF hucont hvcont huae hvae hCv hk
    (hdom ▸ hws) (hdom ▸ hwc) hwsrep hwcrep
  have hsum : F.form ws ws + F.form wc wc ≤ C * (E.form ws ws + E.form wc wc) := by linarith
  rw [hF, hE] at hsum
  exact hsum.trans (le_of_eq (by ring))



theorem measure_le_of_sq_approx [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    {E F : ClosedForm m} (ΓE : EnergyMeasure E) (ΓF : EnergyMeasure F)
    {C : ℝ≥0} {U : Set X} (hU : IsOpen U) {u : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (huF : u ∈ F.domain)
    (happrox : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      (∀ x : X, 0 ≤ f x) → (∀ x : X, f x ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ∃ vc : X → ℝ, Continuous vc ∧
        (∃ M : ℝ, ∀ x : X, |vc x| ≤ M) ∧ (∀ x : X, |vc x ^ 2 - f x| ≤ ε) ∧
        (∫ x, vc x ^ 2 ∂(ΓF.measure u)) ≤ (C : ℝ) * ∫ x, vc x ^ 2 ∂(ΓE.measure u))
    {B : Set X} (hBU : B ⊆ U) :
    ΓF.measure u B ≤ (C : ℝ≥0∞) * ΓE.measure u B := by
  haveI : IsFiniteMeasure (ΓE.measure u) := ⟨ΓE.measure_univ_lt_top u hu⟩
  haveI : IsFiniteMeasure (ΓF.measure u) := ⟨ΓF.measure_univ_lt_top u huF⟩
  haveI : (ΓE.measure u).Regular := ΓE.regular u hu
  haveI : (ΓF.measure u).Regular := ΓF.regular u huF
  refine measure_le_of_integral_le hU (fun f hf hcs hsupp hf0 hf1 => ?_) hBU
  refine integral_le_of_sq_approx C.coe_nonneg hf (Mφ := 1) (fun x => ?_) ?_
  · rw [abs_of_nonneg (hf0 x)]; exact hf1 x
  · intro ε hε; exact happrox f hf hcs hsupp hf0 hf1 ε hε

/-- **The partition-of-unity step of `mfd:prop-21`**
(`eq:mfd-21`).  If `φ i` is a continuous partition of
unity and on each piece `∫ φ i dν ≤ ∫ (ρ + ε) φ i dμ`, then summing gives
`ν(X) ≤ ∫ ρ dμ + ε μ(X)`.

Applied with `ν = Γ_F(u)`, `μ = Γ_E(u)` and `ρ` the weight, this is the display
`F(u) = Σᵢ ∫ φᵢ dΓ_F(u) ≤ ∫ ρ dΓ_E(u) + ε E(u)`; the symmetric inequality is the
same lemma with the roles exchanged. -/
theorem measure_univ_le_of_partition {ν μ : Measure X} [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι) (φ : ι → X → ℝ) (ρ : X → ℝ) {ε M : ℝ}
    (hφ0 : ∀ i : ι, ∀ x : X, 0 ≤ φ i x) (hφc : ∀ i : ι, Continuous (φ i))
    (hsum : ∀ x : X, ∑ i ∈ s, φ i x = 1)
    (hρc : Continuous ρ) (hρb : ∀ x : X, |ρ x| ≤ M) (hε : 0 ≤ ε)
    (hpiece : ∀ i ∈ s, (∫ x, φ i x ∂ν) ≤ ∫ x, (ρ x + ε) * φ i x ∂μ) :
    (ν Set.univ).toReal ≤ (∫ x, ρ x ∂μ) + ε * (μ Set.univ).toReal := by
  have hφ1 : ∀ i ∈ s, ∀ x : X, |φ i x| ≤ 1 := by
    intro i hi x
    rw [abs_of_nonneg (hφ0 i x)]
    have := hsum x
    have hnn : ∀ j ∈ s, 0 ≤ φ j x := fun j _ => hφ0 j x
    calc φ i x ≤ ∑ j ∈ s, φ j x := Finset.single_le_sum hnn hi
      _ = 1 := this
  have hiν : ∀ i ∈ s, Integrable (φ i) ν := fun i hi =>
    integrable_of_continuous_of_bound (hφc i) (hφ1 i hi)
  have hiμ : ∀ i ∈ s, Integrable (fun x => (ρ x + ε) * φ i x) μ := by
    intro i hi
    refine integrable_of_continuous_of_bound (by fun_prop) (C := (M + ε) * 1) fun x => ?_
    rw [abs_mul]
    have h1 : |ρ x + ε| ≤ M + ε := by
      have := abs_le.mp (hρb x)
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    have h2 : |φ i x| ≤ 1 := hφ1 i hi x
    have hMe : (0 : ℝ) ≤ M + ε := le_trans (abs_nonneg _) h1
    exact mul_le_mul h1 h2 (abs_nonneg _) hMe
  have hone : (∫ x, (1 : ℝ) ∂ν) = (ν Set.univ).toReal := by
    rw [integral_const, measureReal_def, smul_eq_mul, mul_one]
  have hleft : (ν Set.univ).toReal = ∑ i ∈ s, ∫ x, φ i x ∂ν := by
    rw [← hone, ← integral_finset_sum s hiν]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hsum x).symm)
  have hright : (∑ i ∈ s, ∫ x, (ρ x + ε) * φ i x ∂μ) = ∫ x, (ρ x + ε) ∂μ := by
    rw [← integral_finset_sum s hiμ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ∑ i ∈ s, (ρ x + ε) * φ i x = ρ x + ε
    rw [← Finset.mul_sum, hsum x, mul_one]
  have hsplit : (∫ x, (ρ x + ε) ∂μ) = (∫ x, ρ x ∂μ) + ε * (μ Set.univ).toReal := by
    rw [integral_add (integrable_of_continuous_of_bound hρc hρb) (integrable_const ε),
      integral_const, measureReal_def, smul_eq_mul, mul_comm]
  rw [hleft, ← hsplit, ← hright]
  exact Finset.sum_le_sum hpiece

/-- **`mfd:lem-sincos`, packaged.**  Form
order implies energy-measure order: if `F ≤ C E` on the core functions supported
in the open set `q`, then `Γ_F(u) ≤ C Γ_E(u)` on every subset of `q`.

The single hypothesis `happrox` bundles the paper's three inputs at the point
where they are used together: regularity (`mfd:prop-regularity`, lines
2214-2216) supplies a core function `v` whose continuous representative `vc`
approximates `φ` uniformly, and for that `v` the core-algebra input
(Fukushima–Oshima–Takeda Theorem 1.4.2, lines 2202-2205) supplies the products
`v·Φ(u)` in `D(E)`, on which the displayed form order gives `F ≤ C E`.

`happrox` must NOT require `Φ 0 = 0`: the argument applies it to
`Φ_c = k⁻¹cos(k·)`, whose value at the origin is `k⁻¹`, and the Leibniz cross
terms `ΦΦ'` of the pair cancel only for the true cosine — with
`k⁻¹(cos(k·) − 1)` they sum to `k⁻¹sin(ku)`.  Fukushima–Oshima–Takeda Theorem
1.4.2 needs no condition at the origin for the product `v·Φ(u)`: it is the
compactly supported factor `v` that puts the product in the core, and `Φ(0) = 0`
is needed only for `Φ(u)` alone to lie in the domain.

Everything else is proved: the sine/cosine identity, the `k → ∞` step, the
uniform approximation, and the passage from test functions to Borel sets. -/
theorem measure_le_of_form_le_core [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    (hdom : E.domain = F.domain) {C : ℝ≥0} {q : Set X} (hq : IsOpen q)
    {u : Lp ℝ 2 m} (hu : E.MemCore u) {uc : X → ℝ} (hucont : Continuous uc)
    (huae : ⇑u =ᵐ[m] uc)
    (happrox : ∀ φ : X → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ q →
      ∀ ε : ℝ, 0 < ε → ∃ (v : Lp ℝ 2 m) (vc : X → ℝ), E.MemCore v ∧
        Continuous vc ∧ (⇑v =ᵐ[m] vc) ∧ (∀ x : X, |vc x - φ x| ≤ ε) ∧
        ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ → (∃ L : ℝ, ∀ s : ℝ, |deriv Φ s| ≤ L) →
          ∃ p : Lp ℝ 2 m, p ∈ E.domain ∧ F.form p p ≤ (C : ℝ) * E.form p p ∧
            (⇑p =ᵐ[m] fun x => vc x * Φ (uc x)))
    {B : Set X} (hBq : B ⊆ q) :
    ΓF.measure u B ≤ (C : ℝ≥0∞) * ΓE.measure u B := by
  have huE : u ∈ E.domain := hu.mem_domain
  have huF : u ∈ F.domain := hdom ▸ huE
  refine measure_le_of_sq_approx ΓE ΓF hq huE huF ?_ hBq
  intro f hf hcs hsupp hf0 hf1 ε hε
  -- a uniform error `δ` in `√f` costs `δ(δ + 2)` in `f`
  set δ : ℝ := min 1 (ε / 3) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ3 : δ ≤ ε / 3 := min_le_right _ _
  have hsqrtc : Continuous fun x => Real.sqrt (f x) := Real.continuous_sqrt.comp hf
  have hsqrtcs : HasCompactSupport fun x => Real.sqrt (f x) :=
    hcs.comp_left (g := Real.sqrt) Real.sqrt_zero
  have hsqrtsupp : tsupport (fun x => Real.sqrt (f x)) ⊆ q := by
    refine (closure_mono (fun x hx => ?_)).trans hsupp
    simp only [Function.mem_support] at hx ⊢
    intro hfx
    exact hx (by rw [hfx, Real.sqrt_zero])
  obtain ⟨v, vc, hv, hvc, hvae, hclose, hmul⟩ :=
    happrox _ hsqrtc hsqrtcs hsqrtsupp δ hδ0
  have hvcb : ∀ x : X, |vc x| ≤ 1 + δ := by
    intro x
    have h1 : Real.sqrt (f x) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (hf1 x)
    have h2 := abs_le.mp (hclose x)
    have h3 : 0 ≤ Real.sqrt (f x) := Real.sqrt_nonneg _
    rw [abs_le]; constructor <;> linarith [h2.1, h2.2]
  refine ⟨vc, hvc, ⟨1 + δ, hvcb⟩, fun x => ?_, ?_⟩
  · have hplat := abs_sq_mul_sub_le (f := f) (ϑ := fun _ => (1 : ℝ)) (w := vc)
      hδ0.le hf0 hf1 (fun _ => zero_le_one) (fun _ => le_rfl) (fun _ _ => rfl) hclose x
    simp only [mul_one, Real.sqrt_one] at hplat
    have : δ * (δ + 2) ≤ ε := by nlinarith [hδ1, hδ3, hδ0.le]
    exact hplat.trans this
  · -- step 6, with the sine/cosine products supplied by the core algebra
    refine ΓE.integral_sq_measure_le_of_form_le ΓF hdom hu hv hucont hvc huae hvae
      hvcb ?_
    intro k hk
    have hkne : k ≠ 0 := ne_of_gt hk
    obtain ⟨ps, hpsdom, hpsle, hpsrep⟩ := hmul (sinScaled k) (contDiff_sinScaled k)
      ⟨1, fun s => by rw [deriv_sinScaled hkne]; exact Real.abs_cos_le_one _⟩
    obtain ⟨pc, hpcdom, hpcle, hpcrep⟩ := hmul (cosScaled k) (contDiff_cosScaled k)
      ⟨1, fun s => by rw [deriv_cosScaled hkne, abs_neg]; exact Real.abs_sin_le_one _⟩
    exact ⟨ps, pc, hpsdom, hpcdom, hpsrep, hpcrep, hpsle, hpcle⟩

end EnergyMeasure

end DirichletForm
