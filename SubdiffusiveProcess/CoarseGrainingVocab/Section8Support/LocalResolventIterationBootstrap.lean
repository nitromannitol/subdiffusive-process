import MarkovProcess.Kernel.LpFinite
import MarkovProcess.Kernel.LpTop
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Kernel estimates for finite resolvent iteration

The helpers in this file use the real-valued kernel integral and its raw
`eLpNorm`, retaining the carriers used by the local resolvent statement.
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationBootstrap

variable {α : Type*} [MeasurableSpace α]

/-- Rectangle symmetry is symmetry of the joint kernel measure. -/
theorem compProd_symm {μ : Measure α} [IsFiniteMeasure μ]
    {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hs : ∀ C D : Set α, MeasurableSet C → MeasurableSet D →
      (∫⁻ x in C, κ x D ∂μ) = ∫⁻ x in D, κ x C ∂μ) :
    (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ := by
  letI : IsFiniteKernel κ := hκ.isFiniteKernel
  apply Measure.ext_prod
  intro C D hC hD
  rw [Measure.map_apply measurable_swap (hC.prod hD)]
  rw [Set.preimage_swap_prod]
  rw [Measure.compProd_apply_prod hD hC, Measure.compProd_apply_prod hC hD]
  exact hs D C hD hC

/-- Nonnegative kernel pairing under rectangle symmetry. -/
theorem lintegral_pair {μ : Measure α} [IsFiniteMeasure μ]
    {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hs : (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ)
    {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, g x * (∫⁻ y, f y ∂κ x) ∂μ) =
      ∫⁻ x, f x * (∫⁻ y, g y ∂κ x) ∂μ := by
  letI : IsFiniteKernel κ := hκ.isFiniteKernel
  calc
    (∫⁻ x, g x * (∫⁻ y, f y ∂κ x) ∂μ) =
        ∫⁻ x, ∫⁻ y, g x * f y ∂κ x ∂μ := by
      apply lintegral_congr
      intro x
      rw [lintegral_const_mul _ hf]
    _ = ∫⁻ z, g z.1 * f z.2 ∂(μ ⊗ₘ κ) :=
      (Measure.lintegral_compProd ((hg.comp measurable_fst).mul
        (hf.comp measurable_snd))).symm
    _ = ∫⁻ z, g z.1 * f z.2 ∂(μ ⊗ₘ κ).map Prod.swap := by rw [hs]
    _ = ∫⁻ z, g z.2 * f z.1 ∂(μ ⊗ₘ κ) :=
      lintegral_map ((hg.comp measurable_fst).mul
        (hf.comp measurable_snd)) measurable_swap
    _ = ∫⁻ x, ∫⁻ y, g y * f x ∂κ x ∂μ :=
      Measure.lintegral_compProd ((hg.comp measurable_snd).mul
        (hf.comp measurable_fst))
    _ = ∫⁻ x, f x * (∫⁻ y, g y ∂κ x) ∂μ := by
      apply lintegral_congr
      intro x
      simp only [mul_comm (g _) (f x), lintegral_const_mul _ hg]

/-- Subinvariance supplies the integrability needed for fibrewise Jensen. -/
theorem memLp_fiber {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    {p : NNReal} (hp : 1 ≤ p) {f : α → ℝ} (hf : MemLp f p μ) :
    ∀ᵐ x ∂μ, MemLp f p (κ x) := by
  have hfk : IsFiniteKernel κ := hκ.isFiniteKernel
  letI := hfk
  have hfComp : MemLp f p (κ ∘ₘ μ) := hf.mono_measure hκμ
  have hFiberEq : ∀ᵐ x ∂μ, f =ᵐ[κ x] hfComp.1.mk f :=
    Measure.ae_ae_of_ae_comp hfComp.1.ae_eq_mk
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast ne_of_gt (zero_lt_one.trans_le hp)
  have hpowInt : Integrable (fun x => ‖f x‖ ^ (p : ℝ)) (κ ∘ₘ μ) :=
    hfComp.integrable_norm_rpow hp0 ENNReal.coe_ne_top
  have hFiberInt : ∀ᵐ x ∂μ, Integrable (fun y => ‖f y‖ ^ (p : ℝ)) (κ x) :=
    Measure.ae_integrable_of_integrable_comp hpowInt
  filter_upwards [hFiberEq, hFiberInt] with x hxEq hxInt
  have hxMeas : AEStronglyMeasurable f (κ x) :=
    hfComp.1.stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq.symm
  exact (integrable_norm_rpow_iff hxMeas hp0 ENNReal.coe_ne_top).mp hxInt

/-- Jensen's inequality with its power integral retained as a real kernel integral. -/
theorem fiber_power {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    {p : NNReal} (hp : 1 ≤ p) {f : α → ℝ} (hf : MemLp f p μ) :
    ∀ᵐ x ∂μ, ‖kernelIntegral κ f x‖ₑ ^ (p : ℝ) ≤
      ‖kernelIntegral κ (fun y => ‖f y‖ ^ (p : ℝ)) x‖ₑ := by
  letI : IsFiniteKernel κ := hκ.isFiniteKernel
  filter_upwards [memLp_fiber hκ hκμ hp hf] with x hx
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast ne_of_gt (zero_lt_one.trans_le hp)
  have hxInt : Integrable (fun y => ‖f y‖ ^ (p : ℝ)) (κ x) :=
    hx.integrable_norm_rpow hp0 ENNReal.coe_ne_top
  have hnonneg : ∀ y, 0 ≤ ‖f y‖ ^ (p : ℝ) :=
    fun y => Real.rpow_nonneg (norm_nonneg _) _
  have heq : ‖kernelIntegral κ (fun y => ‖f y‖ ^ (p : ℝ)) x‖ₑ =
      ∫⁻ y, ‖f y‖ₑ ^ (p : ℝ) ∂κ x := by
    rw [kernelIntegral, Real.enorm_eq_ofReal (integral_nonneg hnonneg),
      ofReal_integral_eq_lintegral_ofReal hxInt (Filter.Eventually.of_forall hnonneg)]
    apply lintegral_congr
    intro y
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) p.coe_nonneg,
      ofReal_norm_eq_enorm]
  rw [heq]
  exact enorm_integral_rpow_le_lintegral_enorm_rpow hp (hκ x) hx

/-- Jensen lifts an endpoint estimate by the same factor on both exponents. -/
theorem gain_power {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    {a b : ℝ≥0∞} {p : NNReal} (hp : 1 ≤ p) (K : ℝ≥0∞)
    (hbound : ∀ g : α → ℝ, MemLp g a μ →
      eLpNorm (kernelIntegral κ g) b μ ≤ K * eLpNorm g a μ)
    {f : α → ℝ} (hf : MemLp f (a * p) μ) (hfp : MemLp f p μ) :
    eLpNorm (kernelIntegral κ f) (b * p) μ ≤
      K ^ (1 / (p : ℝ)) * eLpNorm f (a * p) μ := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast zero_lt_one.trans_le hp
  have hpE : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hpR.ne'
  have hg : MemLp (fun x => ‖f x‖ ^ (p : ℝ)) a μ := by
    have hdiv : (a * (p : ℝ≥0∞)) / p = a := by
      rw [div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hpE ENNReal.coe_ne_top,
        mul_one]
    simpa only [ENNReal.coe_toReal, hdiv] using hf.norm_rpow_div (p : ℝ≥0∞)
  have hmono : eLpNorm (fun x => ‖kernelIntegral κ f x‖ₑ ^ (p : ℝ)) b μ ≤
      eLpNorm (kernelIntegral κ (fun y => ‖f y‖ ^ (p : ℝ))) b μ := by
    apply eLpNorm_mono_enorm_ae
    simpa only [enorm_eq_self] using fiber_power hκ hκμ hp hfp
  have hpow : eLpNorm (kernelIntegral κ f) (b * p) μ ^ (p : ℝ) ≤
      K * eLpNorm f (a * p) μ ^ (p : ℝ) := by
    simpa only [eLpNorm_enorm_rpow _ hpR, eLpNorm_norm_rpow _ hpR,
      ENNReal.ofReal_coe_nnreal] using hmono.trans (hbound _ hg)
  have hroot : (eLpNorm (kernelIntegral κ f) (b * p) μ ^ (p : ℝ)) ^
      (1 / (p : ℝ)) ≤ (K * eLpNorm f (a * p) μ ^ (p : ℝ)) ^
      (1 / (p : ℝ)) :=
    ENNReal.rpow_le_rpow hpow (by positivity)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / (p : ℝ)),
    ← ENNReal.rpow_mul, mul_one_div_cancel hpR.ne', ENNReal.rpow_one] using hroot

/-- An `L¹` endpoint estimate yields the finite gain used at each iteration. -/
theorem gain {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    {r p : NNReal} (hp : 1 ≤ p) (K : ℝ≥0∞)
    (hdual : ∀ g : α → ℝ, MemLp g 1 μ →
      eLpNorm (kernelIntegral κ g) r μ ≤ K * eLpNorm g 1 μ)
    {f : α → ℝ} (hf : MemLp f p μ) :
    eLpNorm (kernelIntegral κ f) (p * r) μ ≤
      K ^ (1 / (p : ℝ)) * eLpNorm f p μ := by
  simpa only [one_mul, NNReal.coe_mul, mul_comm (r : ℝ≥0∞) (p : ℝ≥0∞)] using
    gain_power hκ hκμ (a := 1) (b := r) hp K hdual (by simpa only [one_mul] using hf) hf

/-- A high-exponent estimate finishes the iteration with its exact power of the bound. -/
theorem finish {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    {q a : NNReal} (ha : 1 ≤ a) (K : ℝ≥0∞)
    (hhigh : ∀ g : α → ℝ, MemLp g q μ →
      eLpNorm (kernelIntegral κ g) ∞ μ ≤ K * eLpNorm g q μ)
    {f : α → ℝ} (hf : MemLp f (a * q) μ) (hfa : MemLp f a μ) :
    eLpNorm (kernelIntegral κ f) ∞ μ ≤
      K ^ (1 / (a : ℝ)) * eLpNorm f (a * q) μ := by
  have haE : (a : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast ne_of_gt (zero_lt_one.trans_le ha)
  simpa only [ENNReal.top_mul haE, NNReal.coe_mul,
    mul_comm (q : ℝ≥0∞) (a : ℝ≥0∞)] using
    gain_power hκ hκμ (a := q) (b := ∞) ha K hhigh
      (by simpa only [NNReal.coe_mul, mul_comm] using hf) hfa

/-- Finite composition of estimates along a prescribed exponent sequence. -/
theorem iterate_norm {μ : Measure α} {T : (α → ℝ) → α → ℝ}
    (p : ℕ → ℝ≥0∞) (C : ℕ → ℝ≥0∞)
    (hstep : ∀ n f, MemLp f (p n) μ →
      MemLp (T f) (p (n+1)) μ ∧
        eLpNorm (T f) (p (n+1)) μ ≤ C n * eLpNorm f (p n) μ)
    {f : α → ℝ} (hf : MemLp f (p 0) μ) (n : ℕ) :
    MemLp (T^[n] f) (p n) μ ∧
      eLpNorm (T^[n] f) (p n) μ ≤
        (∏ i ∈ Finset.range n, C i) * eLpNorm f (p 0) μ := by
  induction n with
  | zero =>
    refine ⟨hf, ?_⟩
    simp only [Function.iterate_zero_apply, Finset.prod_range_zero, one_mul, le_refl]
  | succ n ih =>
    have hnext : MemLp (T (T^[n] f)) (p (n+1)) μ ∧
        eLpNorm (T (T^[n] f)) (p (n+1)) μ ≤
          C n * eLpNorm (T^[n] f) (p n) μ := hstep n (T^[n] f) ih.1
    rw [Function.iterate_succ_apply']
    refine ⟨hnext.1, ?_⟩
    calc
      eLpNorm (T (T^[n] f)) (p (n+1)) μ ≤
          C n * eLpNorm (T^[n] f) (p n) μ := hnext.2
      _ ≤ C n * ((∏ i ∈ Finset.range n, C i) * eLpNorm f (p 0) μ) :=
        mul_le_mul_right ih.2 (C n)
      _ = (∏ i ∈ Finset.range (n+1), C i) * eLpNorm f (p 0) μ := by
        rw [Finset.prod_range_succ]
        ac_rfl

/-- The powers paid in the finite gain and final endpoint add to the high exponent. -/
theorem geometric (r q : ℝ) (hr : 1 < r) (_hq : 0 < q)
    (hrq : q * (r - 1) = r) (k : ℕ) :
    (∑ i ∈ Finset.range k, 1 / r ^ i) + q / r ^ k = q := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  induction k with
  | zero => simp only [Finset.sum_range_zero, pow_zero, div_one, zero_add]
  | succ k ih =>
    have hstep : 1 / r ^ k + q / r ^ (k+1) = q / r ^ k := by
      rw [pow_succ]
      field_simp
      nlinarith [hrq]
    rw [Finset.sum_range_succ, add_assoc, hstep]
    exact ih

/-- Cancellation of a finite power integral in the duality test. -/
theorem power_absorb {a M : ℝ≥0∞} {r q : ℝ}
    (ha : a ≠ ∞) (hr : 0 < r) (hq : 1 < q)
    (hrq : 1 / r + 1 / q = 1)
    (h : a ≤ M * a ^ (1 / q)) : a ^ (1 / r) ≤ M := by
  by_cases ha0 : a = 0
  · rw [ha0, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hr)]
    exact zero_le _
  have haq0 : a ^ (1 / q) ≠ 0 := by
    intro hzero
    rcases ENNReal.rpow_eq_zero_iff.mp hzero with hz | ht
    · exact ha0 hz.1
    · exact ha ht.1
  have haqTop : a ^ (1 / q) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ha
  apply (ENNReal.mul_le_mul_iff_left haq0 haqTop).mp
  rw [← ENNReal.rpow_add _ _ ha0 ha, hrq, ENNReal.rpow_one]
  exact h

/-- Bounded nonnegative dual tests detect the full finite exponent norm. -/
theorem finite_dual_test {μ : Measure α} [IsFiniteMeasure μ]
    {r q : ℝ} (hr : 1 < r) (hq : 1 < q) (hrq : (r - 1) * q = r)
    {u : α → ℝ≥0∞} (hu : Measurable u) {M : ℝ≥0∞} (_hM : M ≠ ∞)
    (htest : ∀ g : α → ℝ≥0∞, Measurable g →
      (∃ B : ℝ≥0, ∀ x, g x ≤ B) →
      (∫⁻ x, u x * g x ∂μ) ≤ M * (∫⁻ x, g x ^ q ∂μ) ^ (1 / q)) :
    (∫⁻ x, u x ^ r ∂μ) ^ (1 / r) ≤ M := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hrm : 0 ≤ r - 1 := sub_nonneg.mpr hr.le
  have hconj : 1 / r + 1 / q = 1 := by
    field_simp
    nlinarith [hrq]
  let v : ℕ → α → ℝ≥0∞ := fun n x => min (u x) (n : ℝ≥0∞)
  have hvmeas : ∀ n, Measurable (v n) := fun n => hu.min measurable_const
  have hvbound : ∀ n, (∫⁻ x, v n x ^ r ∂μ) ≤ M ^ r := by
    intro n
    let g : α → ℝ≥0∞ := fun x => v n x ^ (r - 1)
    have hgmeas : Measurable g := (hvmeas n).pow_const _
    have hgbdd : ∃ B : ℝ≥0, ∀ x, g x ≤ B := by
      refine ⟨(n : ℝ≥0) ^ (r - 1), ?_⟩
      intro x
      change (min (u x) (n : ℝ≥0∞)) ^ (r-1) ≤ _
      simpa only [ENNReal.coe_rpow_of_nonneg _ hrm, ENNReal.coe_natCast] using
        ENNReal.rpow_le_rpow (min_le_right (u x) (n : ℝ≥0∞)) hrm
    have hgpow : ∀ x, g x ^ q = v n x ^ r := by
      intro x
      change (v n x ^ (r - 1)) ^ q = v n x ^ r
      rw [← ENNReal.rpow_mul, hrq]
    have hfinite : (∫⁻ x, v n x ^ r ∂μ) ≠ ∞ := by
      apply ne_top_of_le_ne_top (b := (n : ℝ≥0∞) ^ r * μ univ)
      · exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg hr0.le (ENNReal.natCast_ne_top n))
          (measure_ne_top μ univ)
      · calc
          (∫⁻ x, v n x ^ r ∂μ) ≤ ∫⁻ _x : α, (n : ℝ≥0∞) ^ r ∂μ :=
            lintegral_mono fun x => ENNReal.rpow_le_rpow (min_le_right _ _) hr0.le
          _ = (n : ℝ≥0∞) ^ r * μ univ := lintegral_const _
    have hineq : (∫⁻ x, v n x ^ r ∂μ) ≤
        M * (∫⁻ x, v n x ^ r ∂μ) ^ (1 / q) := by
      calc
        (∫⁻ x, v n x ^ r ∂μ) ≤ ∫⁻ x, u x * g x ∂μ := by
          apply lintegral_mono
          intro x
          calc
            v n x ^ r = v n x * g x := by
              change v n x ^ r = v n x * v n x ^ (r - 1)
              calc
                v n x ^ r = v n x ^ (1 + (r - 1)) := by congr 1; ring
                _ = v n x * v n x ^ (r - 1) := by
                  rw [ENNReal.rpow_add_of_nonneg 1 (r - 1) zero_le_one hrm,
                    ENNReal.rpow_one]
            _ ≤ u x * g x := mul_le_mul_left (min_le_left _ _) _
        _ ≤ M * (∫⁻ x, g x ^ q ∂μ) ^ (1 / q) := htest g hgmeas hgbdd
        _ = M * (∫⁻ x, v n x ^ r ∂μ) ^ (1 / q) := by simp only [hgpow]
    have hroot : (∫⁻ x, v n x ^ r ∂μ) ^ (1 / r) ≤ M :=
      power_absorb hfinite hr0 hq hconj hineq
    exact (ENNReal.rpow_inv_le_iff hr0).mp (by simpa only [one_div] using hroot)
  have hsup : ∀ x, (⨆ n, v n x ^ r) = u x ^ r := by
    intro x
    have htrunc : (⨆ n, v n x) = u x := by
      simp only [v, ← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    have hiso : (ENNReal.orderIsoRpow r hr0) (⨆ n, v n x) =
        ⨆ n, (ENNReal.orderIsoRpow r hr0) (v n x) :=
      (ENNReal.orderIsoRpow r hr0).map_iSup _
    change (⨆ n, v n x) ^ r = ⨆ n, v n x ^ r at hiso
    rw [htrunc] at hiso
    exact hiso.symm
  rw [one_div]
  apply (ENNReal.rpow_inv_le_iff hr0).mpr
  calc
    (∫⁻ x, u x ^ r ∂μ) = ∫⁻ x, ⨆ n, v n x ^ r ∂μ := by simp only [hsup]
    _ = ⨆ n, ∫⁻ x, v n x ^ r ∂μ := by
      apply lintegral_iSup (fun n => (hvmeas n).pow_const _)
      intro n m hnm x
      exact ENNReal.rpow_le_rpow (min_le_min_left _ (by exact_mod_cast hnm)) hr0.le
    _ ≤ M ^ r := iSup_le hvbound

/-- Symmetry turns the high-exponent estimate into its `L¹` dual endpoint. -/
theorem endpoint_duality {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : Kernel α α} (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    (hs : ∀ C D : Set α, MeasurableSet C → MeasurableSet D →
      (∫⁻ x in C, κ x D ∂μ) = ∫⁻ x in D, κ x C ∂μ)
    (q r : NNReal) (hq : 1 < q) (hr : 1 < r)
    (hqr : (q : ℝ)⁻¹ + (r : ℝ)⁻¹ = 1)
    {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hhigh : ∀ g : α → ℝ, MemLp g q μ →
      eLpNorm (kernelIntegral κ g) ∞ μ ≤ K * eLpNorm g q μ)
    {f : α → ℝ} (hf : MemLp f 1 μ) :
    eLpNorm (kernelIntegral κ f) r μ ≤ K * eLpNorm f 1 μ := by
  letI : IsFiniteKernel κ := hκ.isFiniteKernel
  have hqR : 1 < (q : ℝ) := by exact_mod_cast hq
  have hrR : 1 < (r : ℝ) := by exact_mod_cast hr
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  have hpowers : ((r : ℝ) - 1) * (q : ℝ) = (r : ℝ) := by
    have hqR0 : (q : ℝ) ≠ 0 := (zero_lt_one.trans hqR).ne'
    have hrR0 : (r : ℝ) ≠ 0 := (zero_lt_one.trans hrR).ne'
    field_simp [hqR0, hrR0] at hqr
    nlinarith [hqr]
  have hsymm : (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ := compProd_symm hκ hs
  have hmeas_case : ∀ f₀ : α → ℝ, Measurable f₀ → MemLp f₀ 1 μ →
      eLpNorm (kernelIntegral κ f₀) r μ ≤ K * eLpNorm f₀ 1 μ := by
    intro f₀ hf₀m hf₀
    let u : α → ℝ≥0∞ := fun x => ∫⁻ y, ‖f₀ y‖ₑ ∂κ x
    have hum : Measurable u := hf₀m.enorm.lintegral_kernel
    have hM : K * eLpNorm f₀ 1 μ ≠ ∞ := ENNReal.mul_ne_top hK hf₀.2.ne
    have htests : ∀ g : α → ℝ≥0∞, Measurable g →
        (∃ B : ℝ≥0, ∀ x, g x ≤ B) →
        (∫⁻ x, u x * g x ∂μ) ≤
          (K * eLpNorm f₀ 1 μ) * (∫⁻ x, g x ^ (q : ℝ) ∂μ) ^ (1 / (q : ℝ)) := by
      intro g hgm hgb
      obtain ⟨B, hB⟩ := hgb
      let g₀ : α → ℝ := fun x => (g x).toReal
      have hg₀m : Measurable g₀ := hgm.ennreal_toReal
      have hgfin : ∀ x, g x ≠ ∞ := fun x => ne_top_of_le_ne_top ENNReal.coe_ne_top (hB x)
      have hgenorm : ∀ x, ‖g₀ x‖ₑ = g x := by
        intro x
        change ‖(g x).toReal‖ₑ = g x
        rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hgfin x)]
      have hgmem : MemLp g₀ q μ :=
        MemLp.of_enorm_bound hg₀m.aestronglyMeasurable ENNReal.coe_ne_top
          (Filter.Eventually.of_forall fun x => (hgenorm x).le.trans (hB x))
      have hgnorm : eLpNorm g₀ q μ =
          (∫⁻ x, g x ^ (q : ℝ) ∂μ) ^ (1 / (q : ℝ)) := by
        rw [eLpNorm_nnreal_eq_lintegral hq0]
        simp only [hgenorm]
      have hG : ∀ x, (∫⁻ y, g y ∂κ x) = ‖kernelIntegral κ g₀ x‖ₑ := by
        intro x
        have hgxmem : MemLp g₀ 1 (κ x) :=
          MemLp.of_enorm_bound hg₀m.aestronglyMeasurable ENNReal.coe_ne_top
            (Filter.Eventually.of_forall fun y => (hgenorm y).le.trans (hB y))
        have hgxint : Integrable g₀ (κ x) := memLp_one_iff_integrable.mp hgxmem
        have hnonneg : ∀ y, 0 ≤ g₀ y := fun y => ENNReal.toReal_nonneg
        rw [kernelIntegral, Real.enorm_eq_ofReal (integral_nonneg hnonneg),
          ofReal_integral_eq_lintegral_ofReal hgxint (Filter.Eventually.of_forall hnonneg)]
        apply lintegral_congr
        intro y
        exact (ENNReal.ofReal_toReal (hgfin y)).symm
      have hGbound : ∀ᵐ x ∂μ, (∫⁻ y, g y ∂κ x) ≤ K * eLpNorm g₀ q μ := by
        filter_upwards [enorm_ae_le_eLpNormEssSup (kernelIntegral κ g₀) μ] with x hx
        rw [hG]
        exact hx.trans (hhigh g₀ hgmem)
      calc
        (∫⁻ x, u x * g x ∂μ) =
            ∫⁻ x, ‖f₀ x‖ₑ * (∫⁻ y, g y ∂κ x) ∂μ := by
          simpa only [u, mul_comm (g _) _] using lintegral_pair hκ hsymm hf₀m.enorm hgm
        _ ≤ ∫⁻ x, ‖f₀ x‖ₑ * (K * eLpNorm g₀ q μ) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hGbound] with x hx
          exact mul_le_mul_right hx _
        _ = (K * eLpNorm f₀ 1 μ) *
            (∫⁻ x, g x ^ (q : ℝ) ∂μ) ^ (1 / (q : ℝ)) := by
          rw [lintegral_mul_const _ hf₀m.enorm, ← eLpNorm_one_eq_lintegral_enorm, hgnorm]
          ac_rfl
    have hnormu : (∫⁻ x, u x ^ (r : ℝ) ∂μ) ^ (1 / (r : ℝ)) ≤
        K * eLpNorm f₀ 1 μ := finite_dual_test hrR hqR hpowers hum hM htests
    calc
      eLpNorm (kernelIntegral κ f₀) r μ ≤ eLpNorm u r μ := by
        apply eLpNorm_mono_enorm
        intro x
        exact enorm_integral_le_lintegral_enorm f₀
      _ = (∫⁻ x, u x ^ (r : ℝ) ∂μ) ^ (1 / (r : ℝ)) := by
        rw [eLpNorm_nnreal_eq_lintegral hr0]
        simp only [enorm_eq_self]
      _ ≤ K * eLpNorm f₀ 1 μ := hnormu
  have hfm : Measurable (hf.1.mk f) := hf.1.stronglyMeasurable_mk.measurable
  have hfmem : MemLp (hf.1.mk f) 1 μ :=
    (memLp_congr_ae hf.1.ae_eq_mk).mp hf
  have heq : kernelIntegral κ f =ᵐ[μ] kernelIntegral κ (hf.1.mk f) :=
    kernelIntegral_congr_ae hκμ hf.1.ae_eq_mk
  calc
    eLpNorm (kernelIntegral κ f) r μ = eLpNorm (kernelIntegral κ (hf.1.mk f)) r μ :=
      eLpNorm_congr_ae heq
    _ ≤ K * eLpNorm (hf.1.mk f) 1 μ := hmeas_case _ hfm hfmem
    _ = K * eLpNorm f 1 μ := congrArg (K * ·) (eLpNorm_congr_ae hf.1.ae_eq_mk).symm

/-- A geometric sequence of finite gains reaches the high exponent after
a number of steps fixed independently of the kernel and its bound. -/
theorem iteration_count (q r : NNReal) (hr : 1 < r) :
    ∃ k : ℕ, q ≤ r ^ k := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt q hr
  exact ⟨k, hk.le⟩

/-- A symmetric sub-Markov kernel with one finite-to-infinity estimate has
an `L¹`-to-infinity bound after `k+1` iterations. The precise exponent on the
endpoint constant is independent of the integer `k`. -/
theorem iterate_bound {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : Kernel α α} (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    (hs : ∀ C D : Set α, MeasurableSet C → MeasurableSet D →
      (∫⁻ x in C, κ x D ∂μ) = ∫⁻ x in D, κ x C ∂μ)
    (q r : NNReal) (hq : 1 < q) (hr : 1 < r)
    (hqr : (q : ℝ)⁻¹ + (r : ℝ)⁻¹ = 1)
    (k : ℕ) (hk : q ≤ r ^ k) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hhigh : ∀ g : α → ℝ, MemLp g q μ →
      eLpNorm (kernelIntegral κ g) ∞ μ ≤ K * eLpNorm g q μ)
    {f : α → ℝ} (hf : MemLp f 1 μ) :
    eLpNorm ((kernelIntegral κ)^[k+1] f) ∞ μ ≤ K ^ (q : ℝ) * eLpNorm f 1 μ := by
  have hrR : 1 < (r : ℝ) := by exact_mod_cast hr
  have hqR : 1 < (q : ℝ) := by exact_mod_cast hq
  have hrR0 : 0 < (r : ℝ) := zero_lt_one.trans hrR
  have hqR0 : 0 < (q : ℝ) := zero_lt_one.trans hqR
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  have hgeom : (q : ℝ) * ((r : ℝ) - 1) = (r : ℝ) := by
    field_simp [hrR0.ne', hqR0.ne'] at hqr
    nlinarith [hqr]
  have hdual : ∀ g : α → ℝ, MemLp g 1 μ →
      eLpNorm (kernelIntegral κ g) r μ ≤ K * eLpNorm g 1 μ :=
    fun g hg => endpoint_duality hκ hκμ hs q r hq hr hqr hK hhigh hg
  let p : ℕ → ℝ≥0∞ := fun n => (r ^ n : NNReal)
  let C : ℕ → ℝ≥0∞ := fun n => K ^ (1 / (r : ℝ) ^ n)
  have hstep : ∀ n g, MemLp g (p n) μ →
      MemLp (kernelIntegral κ g) (p (n+1)) μ ∧
        eLpNorm (kernelIntegral κ g) (p (n+1)) μ ≤ C n * eLpNorm g (p n) μ := by
    intro n g hg
    have hpn : 1 ≤ r ^ n := one_le_pow₀ hr.le
    have hgain : eLpNorm (kernelIntegral κ g) (p (n+1)) μ ≤
        C n * eLpNorm g (p n) μ := by
      simpa only [p, C, pow_succ, NNReal.coe_pow] using
        gain hκ hκμ hpn K hdual hg
    have hfinite : C n * eLpNorm g (p n) μ < ∞ := by
      exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by positivity) hK) hg.2
    exact ⟨⟨AEStronglyMeasurable.kernelIntegral hg.1 hκμ, hgain.trans_lt hfinite⟩, hgain⟩
  have hiter : MemLp ((kernelIntegral κ)^[k] f) (p k) μ ∧
      eLpNorm ((kernelIntegral κ)^[k] f) (p k) μ ≤
        (∏ i ∈ Finset.range k, C i) * eLpNorm f 1 μ := by
    simpa only [p, pow_zero, ENNReal.coe_one] using
      iterate_norm p C hstep (by simpa only [p, pow_zero, ENNReal.coe_one] using hf) k
  have hprod : ∀ n, (∏ i ∈ Finset.range n, C i) =
      K ^ (∑ i ∈ Finset.range n, 1 / (r : ℝ) ^ i) := by
    intro n
    induction n with
    | zero => simp only [Finset.prod_range_zero, Finset.sum_range_zero, ENNReal.rpow_zero]
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]
      exact (ENNReal.rpow_add_of_nonneg _ _
        (Finset.sum_nonneg fun i hi => by positivity) (by positivity)).symm
  let a : NNReal := r ^ k / q
  have ha : 1 ≤ a := (one_le_div (zero_lt_one.trans hq)).mpr hk
  have haq : a * q = r ^ k := div_mul_cancel₀ _ hq0
  have haqE : (a : ℝ≥0∞) * q = p k := by
    change (a : ℝ≥0∞) * q = (r ^ k : NNReal)
    exact_mod_cast haq
  have hale : a ≤ r ^ k := div_le_self (zero_le _) hq.le
  have hfak : MemLp ((kernelIntegral κ)^[k] f) (a * q) μ := by
    simpa only [haqE] using hiter.1
  have hfa : MemLp ((kernelIntegral κ)^[k] f) a μ :=
    hiter.1.mono_exponent (by
      change (a : ℝ≥0∞) ≤ (r ^ k : NNReal)
      exact_mod_cast hale)
  have hfinish : eLpNorm ((kernelIntegral κ)^[k+1] f) ∞ μ ≤
      K ^ ((q : ℝ) / (r : ℝ) ^ k) * eLpNorm ((kernelIntegral κ)^[k] f) (p k) μ := by
    simpa only [haqE, Function.iterate_succ_apply', a, NNReal.coe_div, NNReal.coe_pow,
      one_div_div] using
      finish hκ hκμ ha K hhigh hfak hfa
  calc
    eLpNorm ((kernelIntegral κ)^[k+1] f) ∞ μ ≤
        K ^ ((q : ℝ) / (r : ℝ) ^ k) *
          eLpNorm ((kernelIntegral κ)^[k] f) (p k) μ := hfinish
    _ ≤ K ^ ((q : ℝ) / (r : ℝ) ^ k) *
        ((∏ i ∈ Finset.range k, C i) * eLpNorm f 1 μ) :=
      mul_le_mul_right hiter.2 _
    _ = (K ^ (∑ i ∈ Finset.range k, 1 / (r : ℝ) ^ i) *
        K ^ ((q : ℝ) / (r : ℝ) ^ k)) * eLpNorm f 1 μ := by rw [hprod]; ac_rfl
    _ = K ^ ((∑ i ∈ Finset.range k, 1 / (r : ℝ) ^ i) +
        (q : ℝ) / (r : ℝ) ^ k) * eLpNorm f 1 μ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _
        (Finset.sum_nonneg fun i hi => by positivity) (by positivity)]
    _ = K ^ (q : ℝ) * eLpNorm f 1 μ := by rw [geometric _ _ hrR hqR0 hgeom k]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationBootstrap
