import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderCarrierOps
import Mathlib.MeasureTheory.Function.ContinuousMapDense




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped CompactlySupported RealInnerProductSpace

noncomputable section

variable {d : ℕ}

/-! ### The squared `L²` norm as an integral -/

/-- The integral of a square is the squared `L²` norm of the associated
element of `L²`. -/
theorem integral_sq_eq_norm_toLp_sq {h : Vec d → ℝ} (hmem : MemLp h 2 volume) :
    ∫ x, h x ^ 2 ∂volume = ‖hmem.toLp h‖ ^ 2 := by
  have hinner : ⟪hmem.toLp h, hmem.toLp h⟫ =
      ∫ x, (hmem.toLp h) x * (hmem.toLp h) x ∂volume :=
    MeasureTheory.L2.inner_def _ _
  rw [real_inner_self_eq_norm_sq] at hinner
  rw [hinner]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp] with x hx
  rw [hx, sq]

/-- The elementary triangle bound for squared `L²` distances. -/
theorem integral_sq_sub_le_two_mul_add {p q r : Vec d → ℝ}
    (hp : MemLp p 2 volume) (hq : MemLp q 2 volume) (hr : MemLp r 2 volume) :
    ∫ x, (p x - q x) ^ 2 ∂volume ≤
      2 * ∫ x, (p x - r x) ^ 2 ∂volume +
        2 * ∫ x, (r x - q x) ^ 2 ∂volume := by
  have hpq : Integrable (fun x ↦ (p x - q x) ^ 2) volume :=
    (hp.sub hq).integrable_sq
  have hpr : Integrable (fun x ↦ (p x - r x) ^ 2) volume :=
    (hp.sub hr).integrable_sq
  have hrq : Integrable (fun x ↦ (r x - q x) ^ 2) volume :=
    (hr.sub hq).integrable_sq
  have hsum : Integrable
      (fun x ↦ 2 * (p x - r x) ^ 2 + 2 * (r x - q x) ^ 2) volume :=
    (hpr.const_mul 2).add (hrq.const_mul 2)
  have hmono : ∫ x, (p x - q x) ^ 2 ∂volume ≤
      ∫ x, (2 * (p x - r x) ^ 2 + 2 * (r x - q x) ^ 2) ∂volume := by
    refine integral_mono hpq hsum fun x ↦ ?_
    nlinarith [sq_nonneg (p x - 2 * r x + q x)]
  refine hmono.trans (le_of_eq ?_)
  rw [integral_add (hpr.const_mul 2) (hrq.const_mul 2), integral_const_mul,
    integral_const_mul]

/-! ### Completeness -/

/-- An `L²`-Cauchy sequence of square-integrable functions has an `L²` limit,
in the squared-integral normalization. -/
theorem exists_l2_limit_of_cauchy {h : ℕ → Vec d → ℝ}
    (hmem : ∀ n, MemLp (h n) 2 volume)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      ∫ x, (h n x - h m x) ^ 2 ∂volume ≤ ε) :
    ∃ H : Vec d → ℝ, MemLp H 2 volume ∧
      Tendsto (fun n ↦ ∫ x, (h n x - H x) ^ 2 ∂volume) atTop (𝓝 0) := by
  set F : ℕ → Lp ℝ 2 volume := fun n ↦ (hmem n).toLp (h n) with hF
  have hdiff : ∀ n m, ∫ x, (h n x - h m x) ^ 2 ∂volume = ‖F n - F m‖ ^ 2 := by
    intro n m
    have hid := integral_sq_eq_norm_toLp_sq ((hmem n).sub (hmem m))
    simp only [Pi.sub_apply] at hid
    rw [hid, MemLp.toLp_sub (hmem n) (hmem m)]
  have hCS : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ε ^ 2 / 2) (by positivity)
    refine ⟨N, fun n hn m hm ↦ ?_⟩
    have h1 : ‖F n - F m‖ ^ 2 ≤ ε ^ 2 / 2 := by
      rw [← hdiff]; exact hN n hn m hm
    have h2 : (0 : ℝ) ≤ ‖F n - F m‖ := norm_nonneg _
    have h3 : ‖F n - F m‖ < ε := by nlinarith
    simpa only [dist_eq_norm] using h3
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hCS
  refine ⟨fun x ↦ L x, Lp.memLp L, ?_⟩
  have hrepr : ∀ n, ∫ x, (h n x - L x) ^ 2 ∂volume = ‖F n - L‖ ^ 2 := by
    intro n
    have hid := integral_sq_eq_norm_toLp_sq ((hmem n).sub (Lp.memLp L))
    simp only [Pi.sub_apply] at hid
    rw [hid, MemLp.toLp_sub (hmem n) (Lp.memLp L), Lp.toLp_coeFn]
  simp only [hrepr]
  have hnorm : Tendsto (fun n ↦ ‖F n - L‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hL
  simpa using hnorm.pow 2

/-! ### Cauchy--Schwarz and continuity of the `L²` pairing -/

section Pairing

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}

/-- The integral of a square is the squared `L²` norm, on an arbitrary
measure space. -/
theorem integral_sq_eq_norm_toLp_sq' {h : X → ℝ} (hmem : MemLp h 2 mu) :
    ∫ x, h x ^ 2 ∂mu = ‖hmem.toLp h‖ ^ 2 := by
  have hinner : ⟪hmem.toLp h, hmem.toLp h⟫ =
      ∫ x, (hmem.toLp h) x * (hmem.toLp h) x ∂mu :=
    MeasureTheory.L2.inner_def _ _
  rw [real_inner_self_eq_norm_sq] at hinner
  rw [hinner]
  refine integral_congr_ae ?_
  filter_upwards [hmem.coeFn_toLp] with x hx
  rw [hx, sq]

/-- Cauchy--Schwarz for the `L²` pairing, in the squared-integral
normalization. -/
theorem abs_integral_mul_le_sqrt_mul_sqrt {p q : X → ℝ}
    (hp : MemLp p 2 mu) (hq : MemLp q 2 mu) :
    |∫ x, p x * q x ∂mu| ≤
      Real.sqrt (∫ x, p x ^ 2 ∂mu) * Real.sqrt (∫ x, q x ^ 2 ∂mu) := by
  have hinner : ⟪hp.toLp p, hq.toLp q⟫ = ∫ x, p x * q x ∂mu := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hp.coeFn_toLp, hq.coeFn_toLp] with x hx hy
    simp [hx, hy, RCLike.inner_apply, mul_comm]
  have hnormP : Real.sqrt (∫ x, p x ^ 2 ∂mu) = ‖hp.toLp p‖ := by
    rw [integral_sq_eq_norm_toLp_sq' hp, Real.sqrt_sq (norm_nonneg _)]
  have hnormQ : Real.sqrt (∫ x, q x ^ 2 ∂mu) = ‖hq.toLp q‖ := by
    rw [integral_sq_eq_norm_toLp_sq' hq, Real.sqrt_sq (norm_nonneg _)]
  rw [← hinner, hnormP, hnormQ]
  exact abs_real_inner_le_norm _ _

/-- The `L²` pairing is continuous in its first argument along an `L²`
convergent sequence. -/
theorem tendsto_integral_mul_of_l2_tendsto {p : ℕ → X → ℝ} {P q : X → ℝ}
    (hp : ∀ n, MemLp (p n) 2 mu) (hP : MemLp P 2 mu) (hq : MemLp q 2 mu)
    (hconv : Tendsto (fun n ↦ ∫ x, (p n x - P x) ^ 2 ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, p n x * q x ∂mu) atTop
      (𝓝 (∫ x, P x * q x ∂mu)) := by
  have hint : ∀ n, Integrable (fun x ↦ p n x * q x) mu := fun n ↦
    (hp n).integrable_mul hq
  have hintP : Integrable (fun x ↦ P x * q x) mu := hP.integrable_mul hq
  have hdiff : ∀ n, ∫ x, p n x * q x ∂mu - ∫ x, P x * q x ∂mu =
      ∫ x, (p n x - P x) * q x ∂mu := by
    intro n
    rw [← integral_sub (hint n) hintP]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    ring
  have hbound : ∀ n, |∫ x, (p n x - P x) * q x ∂mu| ≤
      Real.sqrt (∫ x, (p n x - P x) ^ 2 ∂mu) *
        Real.sqrt (∫ x, q x ^ 2 ∂mu) := by
    intro n
    have hpn : MemLp (fun x ↦ p n x - P x) 2 mu := (hp n).sub hP
    simpa only [Pi.sub_apply] using
      abs_integral_mul_le_sqrt_mul_sqrt hpn hq
  have hsqrt : Tendsto
      (fun n ↦ Real.sqrt (∫ x, (p n x - P x) ^ 2 ∂mu) *
        Real.sqrt (∫ x, q x ^ 2 ∂mu)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ Real.sqrt (∫ x, (p n x - P x) ^ 2 ∂mu))
        atTop (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0).comp hconv
    simpa using h1.mul_const (Real.sqrt (∫ x, q x ^ 2 ∂mu))
  have hzero : Tendsto
      (fun n ↦ ∫ x, p n x * q x ∂mu - ∫ x, P x * q x ∂mu) atTop (𝓝 0) := by
    simp only [hdiff]
    refine squeeze_zero_norm ?_ hsqrt
    intro n
    simpa only [Real.norm_eq_abs] using hbound n
  exact (tendsto_sub_nhds_zero_iff).1 hzero

/-- The squared `L²` norm is continuous along an `L²` convergent sequence. -/
theorem tendsto_integral_sq_of_l2_tendsto {p : ℕ → X → ℝ} {P : X → ℝ}
    (hp : ∀ n, MemLp (p n) 2 mu) (hP : MemLp P 2 mu)
    (hconv : Tendsto (fun n ↦ ∫ x, (p n x - P x) ^ 2 ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, p n x ^ 2 ∂mu) atTop (𝓝 (∫ x, P x ^ 2 ∂mu)) := by
  set F : ℕ → Lp ℝ 2 mu := fun n ↦ (hp n).toLp (p n) with hF
  set L : Lp ℝ 2 mu := hP.toLp P with hL
  have hdiff : ∀ n, ∫ x, (p n x - P x) ^ 2 ∂mu = ‖F n - L‖ ^ 2 := by
    intro n
    have hid := integral_sq_eq_norm_toLp_sq' ((hp n).sub hP)
    simp only [Pi.sub_apply] at hid
    rw [hid, MemLp.toLp_sub (hp n) hP]
  have hnorm : Tendsto (fun n ↦ ‖F n - L‖) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n ↦ ‖F n - L‖ ^ 2) atTop (𝓝 0) := by
      simpa only [hdiff] using hconv
    have hcomp := (Real.continuous_sqrt.tendsto 0).comp hsq
    have hfun : ((fun x ↦ Real.sqrt x) ∘ fun n ↦ ‖F n - L‖ ^ 2) =
        fun n ↦ ‖F n - L‖ := by
      funext n
      simp only [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
    rw [hfun] at hcomp
    simpa using hcomp
  have hconvF : Tendsto F atTop (𝓝 L) := tendsto_iff_norm_sub_tendsto_zero.2 hnorm
  have hnormsq : Tendsto (fun n ↦ ‖F n‖ ^ 2) atTop (𝓝 (‖L‖ ^ 2)) :=
    (hconvF.norm).pow 2
  have hrepr : ∀ n, ∫ x, p n x ^ 2 ∂mu = ‖F n‖ ^ 2 := fun n ↦
    integral_sq_eq_norm_toLp_sq' (hp n)
  have hreprL : ∫ x, P x ^ 2 ∂mu = ‖L‖ ^ 2 := integral_sq_eq_norm_toLp_sq' hP
  simpa only [hrepr, hreprL] using hnormsq

end Pairing

/-! ### Compactly supported continuous approximation -/

/-- Every square-integrable function is the `L²` limit of a sequence of
continuous compactly supported functions, in the squared-integral
normalization. -/
theorem exists_compactSupport_l2_approx {f : Vec d → ℝ}
    (hf : MemLp f 2 volume) :
    ∃ g : ℕ → C_c(Vec d, ℝ),
      Tendsto (fun n ↦ ∫ x, (f x - g n x) ^ 2 ∂volume) atTop (𝓝 0) := by
  classical
  have hstep : ∀ n : ℕ, ∃ g : C_c(Vec d, ℝ),
      ∫ x, (f x - g x) ^ 2 ∂volume ≤ ((n : ℝ) + 1)⁻¹ := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    set eps : ℝ := Real.sqrt (((n : ℝ) + 1)⁻¹) with heps
    have hepspos : 0 < eps := Real.sqrt_pos.2 hpos
    obtain ⟨g, hgsupp, hgle, hgcont, hgmem⟩ :=
      hf.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by norm_num)
        (ε := ENNReal.ofReal eps)
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hepspos)
    refine ⟨⟨⟨g, hgcont⟩, hgsupp⟩, ?_⟩
    have hid := integral_sq_eq_norm_toLp_sq (hf.sub hgmem)
    simp only [Pi.sub_apply] at hid
    have hnorm : ‖(hf.sub hgmem).toLp (f - g)‖ ≤ eps := by
      rw [Lp.norm_toLp]
      have hlt : eLpNorm (f - g) 2 volume ≠ ⊤ := (hf.sub hgmem).2.ne
      calc (eLpNorm (f - g) 2 volume).toReal
          ≤ (ENNReal.ofReal eps).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hgle
        _ = eps := ENNReal.toReal_ofReal hepspos.le
    have hsq : ‖(hf.sub hgmem).toLp (f - g)‖ ^ 2 ≤ eps ^ 2 := by
      have := norm_nonneg ((hf.sub hgmem).toLp (f - g))
      nlinarith
    calc ∫ x, (f x - g x) ^ 2 ∂volume
        = ‖(hf.sub hgmem).toLp (f - g)‖ ^ 2 := hid
      _ ≤ eps ^ 2 := hsq
      _ = ((n : ℝ) + 1)⁻¹ := Real.sq_sqrt hpos.le
  choose g hg using hstep
  refine ⟨g, ?_⟩
  have hzero : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have htop : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp htop
  exact squeeze_zero (fun n ↦ integral_nonneg fun x ↦ sq_nonneg _) hg hzero

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
