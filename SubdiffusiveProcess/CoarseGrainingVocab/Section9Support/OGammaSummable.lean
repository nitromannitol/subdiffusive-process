module

public import SubdiffusiveProcess.Model.OGammaLE
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ProviderSupport

@[expose] public section




set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-! ### The two elementary convexity steps -/

theorem sq_convex_comb {theta a b : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    (theta * a + (1 - theta) * b) ^ 2 ≤ theta * a ^ 2 + (1 - theta) * b ^ 2 := by
  nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : (0:ℝ) ≤ 1 - theta))
    (sq_nonneg (a - b))]

theorem exp_sq_convex_comb {theta a b : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    Real.exp ((theta * a + (1 - theta) * b) ^ 2) ≤
      theta * Real.exp (a ^ 2) + (1 - theta) * Real.exp (b ^ 2) := by
  refine le_trans (Real.exp_le_exp.mpr (sq_convex_comb h0 h1)) ?_
  have hconv := convexOn_exp.2 (mem_univ (a ^ 2)) (mem_univ (b ^ 2)) h0
    (by linarith : (0:ℝ) ≤ 1 - theta) (by ring)
  simpa only [smul_eq_mul] using hconv

/-! ### The `σ = 2` bound in natural-power form -/

theorem ogammaLE_two_iff_of_nonneg {A : ℝ} (hA : 0 < A) {X : Omega → ℝ}
    (hX : ∀ omega, 0 ≤ X omega) :
    SubdiffusiveProcess.OGammaLE mu 2 A X ↔
      (Integrable (fun omega => Real.exp ((X omega / A) ^ 2)) mu ∧
        ∫ omega, Real.exp ((X omega / A) ^ 2) ∂mu ≤ 2) := by
  have hfun : (fun omega => Real.exp ((A⁻¹ * max (X omega) 0) ^ (2:ℝ)))
      = fun omega => Real.exp ((X omega / A) ^ 2) := by
    funext omega
    rw [max_eq_left (hX omega), show ((2:ℝ)) = ((2:ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    congr 1
    field_simp
  constructor
  · rintro ⟨hi, hb⟩
    exact ⟨by rw [← hfun]; exact hi, by rw [← hfun]; exact hb⟩
  · rintro ⟨hi, hb⟩
    exact ⟨by rw [hfun]; exact hi, by rw [hfun]; exact hb⟩

/-! ### Adding two scales, with no loss -/

/-- **Two nonnegative `Γ₂` variables add at the sum of their scales**, with no constant.
The convex combination `(X+Y)/(A+B) = θ (X/A) + (1-θ)(Y/B)` with `θ = A/(A+B)` and the
convexity of `t ↦ exp (t ^ 2)` give the pointwise bound; the two expectations are each at
most `2`, and `θ · 2 + (1-θ) · 2 = 2`. -/
theorem ogammaLE_two_add {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {X Y : Omega → ℝ}
    (hXm : AEMeasurable X mu) (hYm : AEMeasurable Y mu)
    (hX0 : ∀ omega, 0 ≤ X omega) (hY0 : ∀ omega, 0 ≤ Y omega)
    (hX : SubdiffusiveProcess.OGammaLE mu 2 A X) (hY : SubdiffusiveProcess.OGammaLE mu 2 B Y) :
    SubdiffusiveProcess.OGammaLE mu 2 (A + B) (fun omega => X omega + Y omega) := by
  have hAB : 0 < A + B := by linarith
  obtain ⟨hXi, hXb⟩ := (ogammaLE_two_iff_of_nonneg hA hX0).mp hX
  obtain ⟨hYi, hYb⟩ := (ogammaLE_two_iff_of_nonneg hB hY0).mp hY
  set theta : ℝ := A / (A + B) with htheta
  have h0 : 0 ≤ theta := by rw [htheta]; positivity
  have h1 : theta ≤ 1 := by
    rw [htheta, div_le_one hAB]; linarith
  have hone : 1 - theta = B / (A + B) := by
    rw [htheta]; field_simp; ring
  have hpoint : ∀ omega, Real.exp (((X omega + Y omega) / (A + B)) ^ 2) ≤
      theta * Real.exp ((X omega / A) ^ 2) + (1 - theta) * Real.exp ((Y omega / B) ^ 2) := by
    intro omega
    have hrw : (X omega + Y omega) / (A + B)
        = theta * (X omega / A) + (1 - theta) * (Y omega / B) := by
      rw [htheta, hone]; field_simp
    rw [hrw]
    exact exp_sq_convex_comb h0 h1
  have hmaj : Integrable (fun omega =>
      theta * Real.exp ((X omega / A) ^ 2) + (1 - theta) * Real.exp ((Y omega / B) ^ 2)) mu :=
    (hXi.const_mul theta).add (hYi.const_mul (1 - theta))
  have hmeas : AEStronglyMeasurable
      (fun omega => Real.exp (((X omega + Y omega) / (A + B)) ^ 2)) mu :=
    ((((hXm.add hYm).div_const (A + B)).pow_const 2).exp).aestronglyMeasurable
  have hint : Integrable (fun omega =>
      Real.exp (((X omega + Y omega) / (A + B)) ^ 2)) mu := by
    refine Integrable.mono' hmaj hmeas ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpoint omega
  refine (ogammaLE_two_iff_of_nonneg hAB (fun omega => by
    have := hX0 omega; have := hY0 omega; linarith)).mpr ⟨hint, ?_⟩
  have hle : ∫ omega, Real.exp (((X omega + Y omega) / (A + B)) ^ 2) ∂mu ≤
      ∫ omega, (theta * Real.exp ((X omega / A) ^ 2) +
        (1 - theta) * Real.exp ((Y omega / B) ^ 2)) ∂mu :=
    integral_mono hint hmaj hpoint
  rw [integral_add (hXi.const_mul theta) (hYi.const_mul (1 - theta)),
    integral_const_mul, integral_const_mul] at hle
  nlinarith [hle, hXb, hYb, h0, h1]


/-! ### Finite sums -/

theorem ogammaLE_two_finset_sum {iota : Type*} [DecidableEq iota] (X : iota → Omega → ℝ)
    (A : iota → ℝ) (hA : ∀ i, 0 < A i) (hXm : ∀ i, AEMeasurable (X i) mu)
    (hX0 : ∀ i omega, 0 ≤ X i omega) (h : ∀ i, SubdiffusiveProcess.OGammaLE mu 2 (A i) (X i))
    {s : Finset iota} (hs : s.Nonempty) :
    SubdiffusiveProcess.OGammaLE mu 2 (∑ i ∈ s, A i) (fun omega => ∑ i ∈ s, X i omega) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simpa using h i
  | cons i t hit ht ih =>
      rw [Finset.sum_cons]
      have hrw : (fun omega => ∑ k ∈ Finset.cons i t hit, X k omega)
          = fun omega => X i omega + ∑ k ∈ t, X k omega := by
        funext omega; rw [Finset.sum_cons]
      rw [hrw]
      refine ogammaLE_two_add (hA i) ?_ (hXm i)
        (by
          have := Finset.aemeasurable_sum (μ := mu) t fun k (_ : k ∈ t) => hXm k
          refine this.congr ?_
          filter_upwards with omega
          simp) (hX0 i)
        (fun omega => Finset.sum_nonneg fun k _ => hX0 k omega) (h i) ih
      exact Finset.sum_pos (fun k _ => hA k) ht

/-! ### Countable sums with summable scales -/

/-- **A summable family of nonnegative `Γ₂` variables sums at the sum of its scales.**
Each partial sum is `O_{Γ₂}` at its own partial scale by `ogammaLE_two_finset_sum`, hence at
the full scale by monotonicity, and Fatou passes the uniform bound `2` to the limit.  This is
the step the source performs with `∑ 3^{-k} ≤ 3/2`, and the one the tree's
`Section9.FiniteShellSum` cannot do: its constant is linear in the number of terms. -/
theorem ogammaLE_two_tsum (X : ℕ → Omega → ℝ) (A : ℕ → ℝ)
    (hA : ∀ k, 0 < A k) (hsum : Summable A)
    (hXm : ∀ k, Measurable (X k)) (hX0 : ∀ k omega, 0 ≤ X k omega)
    (h : ∀ k, SubdiffusiveProcess.OGammaLE mu 2 (A k) (X k))
    (hconv : ∀ omega, Summable fun k => X k omega) :
    SubdiffusiveProcess.OGammaLE mu 2 (∑' k, A k) (fun omega => ∑' k, X k omega) := by
  classical
  set C : ℝ := ∑' k, A k with hCdef
  have hC : 0 < C := by
    rw [hCdef]
    exact hsum.tsum_pos (fun k => (hA k).le) 0 (hA 0)
  set S : ℕ → Omega → ℝ := fun N omega => ∑ k ∈ Finset.range (N + 1), X k omega with hSdef
  have hS0 : ∀ N omega, 0 ≤ S N omega := fun N omega =>
    Finset.sum_nonneg fun k _ => hX0 k omega
  have hSmeas : ∀ N, Measurable (S N) := fun N =>
    Finset.measurable_sum _ fun k _ => hXm k
  have hlimit0 : ∀ omega, 0 ≤ ∑' k, X k omega := fun omega =>
    tsum_nonneg fun k => hX0 k omega
  -- each partial sum, at the full scale
  have hpart : ∀ N, SubdiffusiveProcess.OGammaLE mu 2 C (S N) := by
    intro N
    have hne : (Finset.range (N + 1)).Nonempty := Finset.nonempty_range_add_one
    have hbase := ogammaLE_two_finset_sum (mu := mu) X A hA (fun k => (hXm k).aemeasurable)
      hX0 h hne
    refine SubdiffusiveProcess.CoarseGrainingVocab.Section6CutoffRegularity.ogammaLE_mono_scale'
      two_pos (Finset.sum_pos (fun k _ => hA k) hne) ?_ hbase
    rw [hCdef]
    exact hsum.sum_le_tsum _ (fun k _ => (hA k).le)
  -- the integrand of the limit, and of the partial sums
  set g : ℕ → Omega → ℝ := fun N omega => Real.exp ((S N omega / C) ^ 2) with hgdef
  set glim : Omega → ℝ := fun omega => Real.exp (((∑' k, X k omega) / C) ^ 2) with hglim
  have hgmeas : ∀ N, Measurable fun omega => ENNReal.ofReal (g N omega) := by
    intro N
    exact (((hSmeas N).div_const C).pow_const 2).exp.ennreal_ofReal
  have hglintle : ∀ N, ∫⁻ omega, ENNReal.ofReal (g N omega) ∂mu ≤ 2 := by
    intro N
    obtain ⟨hi, hb⟩ := (ogammaLE_two_iff_of_nonneg hC (hS0 N)).mp (hpart N)
    have hrw := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le)
    rw [← hrw]
    calc ENNReal.ofReal (∫ omega, Real.exp ((S N omega / C) ^ 2) ∂mu)
        ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hb
      _ = 2 := by norm_num
  -- Fatou
  have htend : ∀ omega, Filter.Tendsto (fun N => ENNReal.ofReal (g N omega))
      Filter.atTop (nhds (ENNReal.ofReal (glim omega))) := by
    intro omega
    have hsum' : Filter.Tendsto (fun N => S N omega) Filter.atTop
        (nhds (∑' k, X k omega)) :=
      (hconv omega).hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have hcont : Filter.Tendsto (fun N => g N omega) Filter.atTop (nhds (glim omega)) := by
      rw [hgdef, hglim]
      exact (Real.continuous_exp.tendsto _).comp
        (((continuous_pow 2).tendsto _).comp ((hsum'.div_const C)))
    exact (ENNReal.continuous_ofReal.tendsto _).comp hcont
  have hfatou : ∫⁻ omega, ENNReal.ofReal (glim omega) ∂mu ≤ 2 := by
    have hle : ∫⁻ omega, Filter.liminf (fun N => ENNReal.ofReal (g N omega))
        Filter.atTop ∂mu ≤
        Filter.liminf (fun N => ∫⁻ omega, ENNReal.ofReal (g N omega) ∂mu) Filter.atTop :=
      lintegral_liminf_le hgmeas
    have heq : (fun omega => Filter.liminf (fun N => ENNReal.ofReal (g N omega))
        Filter.atTop) = fun omega => ENNReal.ofReal (glim omega) := by
      funext omega
      exact (htend omega).liminf_eq
    rw [heq] at hle
    refine le_trans hle ?_
    exact Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall hglintle)
  -- conclude
  have htsummeas : Measurable fun omega => ∑' k, X k omega := by
    refine measurable_of_tendsto_metrizable hSmeas ?_
    rw [tendsto_pi_nhds]
    intro omega
    exact (hconv omega).hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hglimmeas : Measurable glim := by
    rw [hglim]
    exact ((htsummeas.div_const C).pow_const 2).exp
  have hint : Integrable glim mu := by
    refine ⟨hglimmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hfatou (by norm_num)
  refine (ogammaLE_two_iff_of_nonneg hC hlimit0).mpr ⟨hint, ?_⟩
  have hrw := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le)
  have h2 : ENNReal.ofReal (∫ omega, glim omega ∂mu) ≤ ENNReal.ofReal 2 := by
    rw [hrw]
    simpa using hfatou
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h2

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
