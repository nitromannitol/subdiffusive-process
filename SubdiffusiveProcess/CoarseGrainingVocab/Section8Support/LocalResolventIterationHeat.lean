import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationBootstrap
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal ProbabilityTheory
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationHeat
variable {α : Type*} [MeasurableSpace α]
def positiveIntegral (κ : Kernel α α) (f : α → ENNReal) (x : α) : ENNReal := ∫⁻ y, f y ∂κ x
def pairing (μ : Measure α) (κ : Kernel α α) (f g : α → ENNReal) : ENNReal := ∫⁻ x, f x * positiveIntegral κ g x ∂μ
def timeAverage (ν : Measure ℝ) (h : NNReal → ENNReal) (t : NNReal) : ENNReal := ∫⁻ s : ℝ, h (t + Real.toNNReal s) ∂ν

open LocalResolventIterationBootstrap

@[fun_prop] theorem measurable_positiveIntegral {κ : Kernel α α}
    {f : α → ENNReal} (hf : Measurable f) : Measurable (positiveIntegral κ f) :=
  hf.lintegral_kernel

theorem positive_comp (η κ : Kernel α α) {f : α → ENNReal} (hf : Measurable f) :
    positiveIntegral (η ∘ₖ κ) f = positiveIntegral κ (positiveIntegral η f) := by
  funext x
  exact Kernel.lintegral_comp η κ x hf

theorem positive_jensen {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    {f : α → ENNReal} (hf : Measurable f) (x : α) :
    (positiveIntegral κ f x) ^ 2 ≤ positiveIntegral κ (fun y => (f y)^2) x := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hh : (∫⁻ y, f y ∂κ x) ≤
      (∫⁻ y, (f y)^2 ∂κ x) ^ (1/2 : ℝ) * (κ x univ) ^ (1/2 : ℝ) := by
    simpa only [Pi.mul_apply, mul_one, ENNReal.one_rpow, one_pow, lintegral_one,
      ENNReal.rpow_two] using
      ENNReal.lintegral_mul_le_Lp_mul_Lq (κ x) hpq hf.aemeasurable
        (measurable_const.aemeasurable (f := fun _ : α => (1 : ENNReal)))
  have hb : (κ x univ) ^ (1/2 : ℝ) ≤ 1 := by
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow (hκ x) (by norm_num : (0 : ℝ) ≤ 1/2)
  have hh' : (∫⁻ y, f y ∂κ x) ≤ (∫⁻ y, (f y)^2 ∂κ x) ^ (1/2 : ℝ) :=
    hh.trans ((mul_le_mul_right hb _).trans_eq (mul_one _))
  have hh2 : (∫⁻ y, f y ∂κ x) ^ (2 : ℝ) ≤
      ((∫⁻ y, (f y)^2 ∂κ x) ^ (1/2 : ℝ)) ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow hh' (by norm_num)
  rw [← ENNReal.rpow_mul, show (1/2 : ℝ)*2 = 1 by norm_num, ENNReal.rpow_one] at hh2
  simpa only [ENNReal.rpow_two, positiveIntegral] using hh2

theorem positive_contraction {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    {f : α → ENNReal} (hf : Measurable f) :
    (∫⁻ x, (positiveIntegral κ f x)^2 ∂μ) ≤ ∫⁻ x, (f x)^2 ∂μ := by
  calc
    (∫⁻ x, (positiveIntegral κ f x)^2 ∂μ) ≤
        ∫⁻ x, positiveIntegral κ (fun y => (f y)^2) x ∂μ :=
      lintegral_mono (positive_jensen hκ hf)
    _ = ∫⁻ x, (f x)^2 ∂κ ∘ₘ μ :=
      (Measure.lintegral_bind (Kernel.aemeasurable κ) (hf.pow_const 2).aemeasurable).symm
    _ ≤ ∫⁻ x, (f x)^2 ∂μ := lintegral_mono' hκμ le_rfl

theorem pairing_factor {μ : Measure α} [IsFiniteMeasure μ]
    {Q : NNReal → Kernel α α} (hsub : ∀ t, IsSubMarkovKernel (Q t))
    (hsym : ∀ t, (μ ⊗ₘ Q t).map Prod.swap = μ ⊗ₘ Q t)
    (hsem : ∀ t s, Q (t+s) = Q s ∘ₖ Q t)
    {f g : α → ENNReal} (hf : Measurable f) (hg : Measurable g) (t : NNReal) :
    pairing μ (Q (t+t)) f g =
      ∫⁻ x, positiveIntegral (Q t) f x * positiveIntegral (Q t) g x ∂μ := by
  unfold pairing
  rw [hsem t t, positive_comp _ _ hg]
  exact (lintegral_pair (hsub t) (hsym t) (measurable_positiveIntegral hg) hf).trans
    (lintegral_congr (fun x => mul_comm _ _))

theorem diagonal_antitone {μ : Measure α} [IsFiniteMeasure μ]
    {Q : NNReal → Kernel α α} (hsub : ∀ t, IsSubMarkovKernel (Q t))
    (hμ : ∀ t, Q t ∘ₘ μ ≤ μ)
    (hsym : ∀ t, (μ ⊗ₘ Q t).map Prod.swap = μ ⊗ₘ Q t)
    (hsem : ∀ t s, Q (t+s) = Q s ∘ₖ Q t)
    {f : α → ENNReal} (hf : Measurable f) :
    Antitone (fun t => pairing μ (Q t) f f) := by
  intro t u htu
  have ht : t = t/2 + t/2 := by ring
  have hu : u = u/2 + u/2 := by ring
  have hsplit : u/2 = (u-t)/2 + t/2 := by
    rw [← add_div, tsub_add_cancel_of_le htu]
  calc
    pairing μ (Q u) f f = ∫⁻ x, (positiveIntegral (Q (u/2)) f x)^2 ∂μ := by
      conv_lhs => rw [hu]
      rw [pairing_factor hsub hsym hsem hf hf]
      simp only [pow_two]
    _ = ∫⁻ x, (positiveIntegral (Q ((u-t)/2)) (positiveIntegral (Q (t/2)) f) x)^2 ∂μ := by
      rw [hsplit, hsem, positive_comp _ _ hf]
    _ ≤ ∫⁻ x, (positiveIntegral (Q (t/2)) f x)^2 ∂μ :=
      positive_contraction (hsub _) (hμ _) (measurable_positiveIntegral hf)
    _ = pairing μ (Q t) f f := by
      conv_rhs => rw [ht]
      rw [pairing_factor hsub hsym hsem hf hf]
      simp only [pow_two]

theorem measurable_positive_joint {Q : NNReal → Kernel α α}
    (hjoint : ∀ B : Set α, MeasurableSet B →
      Measurable (fun p : NNReal × α => Q p.1 p.2 B))
    {f : α → ENNReal} (hf : Measurable f) :
    Measurable (fun p : NNReal × α => positiveIntegral (Q p.1) f p.2) := by
  let K : Kernel (NNReal × α) α :=
    ⟨fun p => Q p.1 p.2, Measure.measurable_of_measurable_coe _ hjoint⟩
  exact hf.lintegral_kernel (κ := K)

theorem positive_mixture {R : Kernel α α} {Q : NNReal → Kernel α α}
    {ν : Measure ℝ} [SFinite ν]
    (hjoint : ∀ B : Set α, MeasurableSet B → Measurable (fun p : NNReal × α => Q p.1 p.2 B))
    (hmix : ∀ x B, MeasurableSet B → R x B = ∫⁻ s : ℝ, Q (Real.toNNReal s) x B ∂ν)
    {f : α → ENNReal} (hf : Measurable f) (x : α) :
    positiveIntegral R f x = ∫⁻ s : ℝ, positiveIntegral (Q (Real.toNNReal s)) f x ∂ν := by
  have hmeas : Measurable (fun s : ℝ => Q (Real.toNNReal s) x) :=
    (Measure.measurable_of_measurable_coe _ hjoint).comp
      (measurable_real_toNNReal.prodMk measurable_const)
  have hR : R x = ν.bind (fun s : ℝ => Q (Real.toNNReal s) x) := by
    apply Measure.ext
    intro B hB
    rw [Measure.bind_apply hB hmeas.aemeasurable]
    exact hmix x B hB
  unfold positiveIntegral
  rw [hR]
  exact Measure.lintegral_bind hmeas.aemeasurable hf.aemeasurable

theorem positive_commute {R : Kernel α α} {Q : NNReal → Kernel α α}
    {ν : Measure ℝ} [SFinite ν] (hsub : ∀ t, IsSubMarkovKernel (Q t))
    (hjoint : ∀ B : Set α, MeasurableSet B → Measurable (fun p : NNReal × α => Q p.1 p.2 B))
    (hmix : ∀ x B, MeasurableSet B → R x B = ∫⁻ s : ℝ, Q (Real.toNNReal s) x B ∂ν)
    (hsem : ∀ t s, Q (t+s) = Q s ∘ₖ Q t)
    {f : α → ENNReal} (hf : Measurable f) (t : NNReal) (x : α) :
    positiveIntegral (Q t) (positiveIntegral R f) x =
      ∫⁻ s : ℝ, positiveIntegral (Q (t + Real.toNNReal s)) f x ∂ν := by
  letI : IsFiniteKernel (Q t) := (hsub t).isFiniteKernel
  have hmeas : Measurable (fun p : α × ℝ =>
      positiveIntegral (Q (Real.toNNReal p.2)) f p.1) :=
    (measurable_positive_joint hjoint hf).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  calc
    positiveIntegral (Q t) (positiveIntegral R f) x =
        ∫⁻ y, ∫⁻ s : ℝ, positiveIntegral (Q (Real.toNNReal s)) f y ∂ν ∂Q t x := by
      exact lintegral_congr (positive_mixture hjoint hmix hf)
    _ = ∫⁻ s : ℝ, positiveIntegral (Q t) (positiveIntegral (Q (Real.toNNReal s)) f) x ∂ν :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ s : ℝ, positiveIntegral (Q (t + Real.toNNReal s)) f x ∂ν := by
      apply lintegral_congr
      intro s
      rw [hsem, positive_comp _ _ hf]

theorem time_average_lower {ν : Measure ℝ} {a : NNReal} {m : ENNReal}
    (hm : m ≤ ν {s : ℝ | Real.toNNReal s ≤ a})
    {h : NNReal → ENNReal} (hh : Antitone h) (n : ℕ) (t : NNReal) :
    m^n * h (t + n*a) ≤ (timeAverage ν)^[n] h t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    let S : Set ℝ := {s : ℝ | Real.toNNReal s ≤ a}
    have hS : MeasurableSet S := measurableSet_le measurable_real_toNNReal measurable_const
    have heq : t + (n+1:ℕ)*a = (t+a) + n*a := by push_cast; ring
    calc
      m^(n+1) * h (t+(n+1:ℕ)*a) =
          m * (m^n * h (t+(n+1:ℕ)*a)) := by rw [pow_succ]; ac_rfl
      _ ≤ ν S * (m^n * h (t+(n+1:ℕ)*a)) := mul_le_mul_left hm _
      _ = ∫⁻ s in S, m^n * h (t+(n+1:ℕ)*a) ∂ν := by
        simp only [lintegral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
        ac_rfl
      _ ≤ ∫⁻ s in S, (timeAverage ν)^[n] h (t+Real.toNNReal s) ∂ν := by
        apply setLIntegral_mono' hS
        intro s hs
        have htime : t + Real.toNNReal s + n*a ≤ t + (n+1:ℕ)*a := by
          rw [heq]
          exact add_le_add (add_le_add le_rfl hs) le_rfl
        exact (mul_le_mul_right (hh htime) _).trans (ih (t+Real.toNNReal s))
      _ ≤ ∫⁻ s : ℝ, (timeAverage ν)^[n] h (t+Real.toNNReal s) ∂ν :=
        setLIntegral_le_lintegral _ _
      _ = (timeAverage ν)^[n+1] h t := by rw [Function.iterate_succ_apply']; rfl

theorem exponential_half_mass {a : NNReal} (ha : 0 < a) :
    (1/2 : ENNReal) ≤ expMeasure ((a : ℝ)⁻¹) {s : ℝ | Real.toNNReal s ≤ a} := by
  have haR : 0 < (a : ℝ) := ha
  letI : IsProbabilityMeasure (expMeasure ((a : ℝ)⁻¹)) :=
    isProbabilityMeasure_expMeasure (inv_pos.mpr haR)
  have hset : {s : ℝ | Real.toNNReal s ≤ a} = Iic (a : ℝ) := by
    ext s
    exact Real.toNNReal_le_iff_le_coe
  rw [hset, ← ofReal_cdf, cdf_expMeasure_eq (inv_pos.mpr haR), if_pos haR.le,
    inv_mul_cancel₀ haR.ne']
  have he : Real.exp (-1) ≤ (1/2 : ℝ) := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by
      have haux : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      linarith)
  have he' : (1/2 : ℝ) ≤ 1 - Real.exp (-1) := by linarith
  exact (by simp : (1/2 : ENNReal) = ENNReal.ofReal (1/2 : ℝ)).trans_le
    (ENNReal.ofReal_le_ofReal he')

theorem measurable_positive_iterate (R : Kernel α α)
    {f : α → ENNReal} (hf : Measurable f) (n : ℕ) :
    Measurable ((positiveIntegral R)^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact measurable_positiveIntegral ih

theorem shifted_iteration_mixture {μ : Measure α} [IsFiniteMeasure μ]
    {R : Kernel α α} {Q : NNReal → Kernel α α} {ν : Measure ℝ} [SFinite ν]
    (hsub : ∀ t, IsSubMarkovKernel (Q t))
    (hjoint : ∀ B : Set α, MeasurableSet B → Measurable (fun p : NNReal × α => Q p.1 p.2 B))
    (hmix : ∀ x B, MeasurableSet B → R x B = ∫⁻ s : ℝ, Q (Real.toNNReal s) x B ∂ν)
    (hsem : ∀ t s, Q (t+s) = Q s ∘ₖ Q t)
    {f g : α → ENNReal} (hf : Measurable f) (hg : Measurable g) (n : ℕ) (t : NNReal) :
    pairing μ (Q t) f ((positiveIntegral R)^[n] g) =
      (timeAverage ν)^[n] (fun u => pairing μ (Q u) f g) t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    have hgn : Measurable ((positiveIntegral R)^[n] g) := measurable_positive_iterate R hg n
    have hmeas : Measurable (fun p : α × ℝ =>
        positiveIntegral (Q (t+Real.toNNReal p.2)) ((positiveIntegral R)^[n] g) p.1) :=
      (measurable_positive_joint hjoint hgn).comp
        ((measurable_const.add (measurable_real_toNNReal.comp measurable_snd)).prodMk measurable_fst)
    rw [Function.iterate_succ_apply']
    calc
      pairing μ (Q t) f (positiveIntegral R ((positiveIntegral R)^[n] g)) =
          ∫⁻ x, ∫⁻ s : ℝ, f x *
            positiveIntegral (Q (t+Real.toNNReal s)) ((positiveIntegral R)^[n] g) x ∂ν ∂μ := by
        apply lintegral_congr
        intro x
        rw [positive_commute hsub hjoint hmix hsem hgn]
        exact (lintegral_const_mul _ (hmeas.comp measurable_prodMk_left)).symm
      _ = ∫⁻ s : ℝ, pairing μ (Q (t+Real.toNNReal s)) f ((positiveIntegral R)^[n] g) ∂ν :=
        lintegral_lintegral_swap ((hf.comp measurable_fst).mul hmeas).aemeasurable
      _ = ∫⁻ s : ℝ, (timeAverage ν)^[n] (fun u => pairing μ (Q u) f g)
          (t+Real.toNNReal s) ∂ν := lintegral_congr (fun s => ih _)
      _ = (timeAverage ν)^[n+1] (fun u => pairing μ (Q u) f g) t := by
        rw [Function.iterate_succ_apply']; rfl

theorem iteration_mixture {μ : Measure α} [IsFiniteMeasure μ]
    {R : Kernel α α} {Q : NNReal → Kernel α α} {ν : Measure ℝ} [SFinite ν]
    (hsub : ∀ t, IsSubMarkovKernel (Q t))
    (hjoint : ∀ B : Set α, MeasurableSet B → Measurable (fun p : NNReal × α => Q p.1 p.2 B))
    (hmix : ∀ x B, MeasurableSet B → R x B = ∫⁻ s : ℝ, Q (Real.toNNReal s) x B ∂ν)
    (hsem : ∀ t s, Q (t+s) = Q s ∘ₖ Q t)
    {f g : α → ENNReal} (hf : Measurable f) (hg : Measurable g) (n : ℕ) :
    (∫⁻ x, f x * ((positiveIntegral R)^[n+1] g) x ∂μ) =
      (timeAverage ν)^[n+1] (fun u => pairing μ (Q u) f g) 0 := by
  have hgn : Measurable ((positiveIntegral R)^[n] g) := measurable_positive_iterate R hg n
  have hmeas : Measurable (fun p : α × ℝ =>
      positiveIntegral (Q (Real.toNNReal p.2)) ((positiveIntegral R)^[n] g) p.1) :=
    (measurable_positive_joint hjoint hgn).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  rw [Function.iterate_succ_apply']
  calc
    (∫⁻ x, f x * positiveIntegral R ((positiveIntegral R)^[n] g) x ∂μ) =
        ∫⁻ x, ∫⁻ s : ℝ, f x *
          positiveIntegral (Q (Real.toNNReal s)) ((positiveIntegral R)^[n] g) x ∂ν ∂μ := by
      apply lintegral_congr
      intro x
      rw [positive_mixture hjoint hmix hgn]
      exact (lintegral_const_mul _ (hmeas.comp measurable_prodMk_left)).symm
    _ = ∫⁻ s : ℝ, pairing μ (Q (Real.toNNReal s)) f ((positiveIntegral R)^[n] g) ∂ν :=
      lintegral_lintegral_swap ((hf.comp measurable_fst).mul hmeas).aemeasurable
    _ = ∫⁻ s : ℝ, (timeAverage ν)^[n] (fun u => pairing μ (Q u) f g)
        (Real.toNNReal s) ∂ν :=
      lintegral_congr (fun s => shifted_iteration_mixture hsub hjoint hmix hsem hf hg n _)
    _ = (timeAverage ν)^[n+1] (fun u => pairing μ (Q u) f g) 0 := by
      rw [Function.iterate_succ_apply']
      simp only [timeAverage, zero_add]

theorem positive_bound_of_rectangle {μ : Measure α} [IsFiniteMeasure μ]
    {κ : Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hsym : (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ) {C : ENNReal}
    (hrect : ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      (∫⁻ x in A, κ x B ∂μ) ≤ C * μ A * μ B)
    {f : α → ENNReal} (hf : Measurable f) :
    ∀ᵐ x ∂μ, positiveIntegral κ f x ≤ C * ∫⁻ y, f y ∂μ := by
  have hB : ∀ B : Set α, MeasurableSet B → ∀ᵐ x ∂μ, κ x B ≤ C * μ B := by
    intro B hB
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (κ.measurable_coe hB)
    intro A hA _hfin
    simpa only [lintegral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter,
      mul_assoc, mul_left_comm, mul_comm] using hrect A B hA hB
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (measurable_positiveIntegral hf)
  intro A hA _hfin
  have hind : Measurable (A.indicator (fun _ : α => (1 : ENNReal))) := measurable_const.indicator hA
  calc
    (∫⁻ x in A, positiveIntegral κ f x ∂μ) =
        ∫⁻ x, A.indicator (fun _ => (1 : ENNReal)) x * positiveIntegral κ f x ∂μ := by
      rw [← lintegral_indicator hA]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ A <;> simp [hx]
    _ = ∫⁻ x, f x * positiveIntegral κ (A.indicator (fun _ => (1 : ENNReal))) x ∂μ :=
      lintegral_pair hκ hsym hf hind
    _ = ∫⁻ x, f x * κ x A ∂μ := by
      simp only [positiveIntegral, lintegral_indicator hA, lintegral_one,
        Measure.restrict_apply, MeasurableSet.univ, univ_inter]
    _ ≤ ∫⁻ x, f x * (C * μ A) ∂μ := lintegral_mono_ae ((hB A hA).mono fun x hx => mul_le_mul_right hx _)
    _ = ∫⁻ x in A, C * ∫⁻ y, f y ∂μ ∂μ := by
      rw [lintegral_mul_const _ hf]
      simp only [lintegral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
      ac_rfl

theorem rectangle_endpoint {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : Kernel α α} (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    (hsym : (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ) {C : ENNReal}
    (hrect : ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      (∫⁻ x in A, κ x B ∂μ) ≤ C * μ A * μ B)
    {f : α → ℝ} (hf : MemLp f 1 μ) :
    eLpNorm (kernelIntegral κ f) ∞ μ ≤ C * eLpNorm f 1 μ := by
  let g : α → ℝ := hf.1.mk f
  have hg : StronglyMeasurable g := hf.1.stronglyMeasurable_mk
  have hfg : f =ᵐ[μ] g := hf.1.ae_eq_mk
  have hb : ∀ᵐ x ∂μ, positiveIntegral κ (fun y => ‖g y‖ₑ) x ≤ C * ∫⁻ y, ‖g y‖ₑ ∂μ :=
    positive_bound_of_rectangle hκ hsym hrect hg.enorm
  have hbound : eLpNorm (kernelIntegral κ g) ∞ μ ≤ C * eLpNorm g 1 μ := by
    rw [eLpNorm_exponent_top, eLpNorm_one_eq_lintegral_enorm]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    filter_upwards [hb] with x hx
    exact (enorm_integral_le_lintegral_enorm g).trans hx
  rw [eLpNorm_congr_ae (kernelIntegral_congr_ae hκμ hfg), eLpNorm_congr_ae hfg]
  exact hbound

theorem iterate_ofReal {R : Kernel α α} (hR : IsSubMarkovKernel R)
    {f : α → ℝ} (hf : StronglyMeasurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (n : ℕ) :
    StronglyMeasurable ((kernelIntegral R)^[n] f) ∧
    (∀ x, 0 ≤ ((kernelIntegral R)^[n] f) x ∧ ((kernelIntegral R)^[n] f) x ≤ 1) ∧
    ((positiveIntegral R)^[n] (fun x => ENNReal.ofReal (f x))) =
      (fun x => ENNReal.ofReal (((kernelIntegral R)^[n] f) x)) := by
  letI : IsFiniteKernel R := hR.isFiniteKernel
  induction n with
  | zero => exact ⟨hf, fun x => ⟨h0 x, h1 x⟩, rfl⟩
  | succ n ih =>
    have hi : ∀ x, Integrable ((kernelIntegral R)^[n] f) (R x) := by
      intro x
      exact (integrable_const (1 : ℝ)).mono' ih.1.aestronglyMeasurable
        (ae_of_all _ (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (ih.2.1 y).1]; exact (ih.2.1 y).2))
    have hn : ∀ x, 0 ≤ kernelIntegral R ((kernelIntegral R)^[n] f) x :=
      fun x => integral_nonneg (fun y => (ih.2.1 y).1)
    have hle : ∀ x, kernelIntegral R ((kernelIntegral R)^[n] f) x ≤ 1 := by
      intro x
      have hnorm : ‖kernelIntegral R ((kernelIntegral R)^[n] f) x‖ₑ ≤ 1 :=
        enorm_kernelIntegral_le_of_ae hR (ae_of_all _ (fun y => by
          rw [Real.enorm_eq_ofReal (ih.2.1 y).1, ENNReal.ofReal_le_one]
          exact (ih.2.1 y).2))
      rwa [Real.enorm_eq_ofReal (hn x), ENNReal.ofReal_le_one] at hnorm
    simp only [Function.iterate_succ_apply']
    refine ⟨ih.1.integral_kernel, fun x => ⟨hn x, hle x⟩, ?_⟩
    rw [ih.2.2]
    funext x
    exact (ofReal_integral_eq_lintegral_ofReal (hi x)
      (ae_of_all _ (fun y => (ih.2.1 y).1))).symm

theorem pairing_cauchy {μ : Measure α} [IsFiniteMeasure μ]
    {Q : NNReal → Kernel α α} (hsub : ∀ t, IsSubMarkovKernel (Q t))
    (hsym : ∀ t, (μ ⊗ₘ Q t).map Prod.swap = μ ⊗ₘ Q t)
    (hsem : ∀ t s, Q (t+s) = Q s ∘ₖ Q t)
    {f g : α → ENNReal} (hf : Measurable f) (hg : Measurable g) (t : NNReal) :
    (pairing μ (Q t) f g)^2 ≤ pairing μ (Q t) f f * pairing μ (Q t) g g := by
  have ht : t = t/2+t/2 := by ring
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder : (∫⁻ x, positiveIntegral (Q (t/2)) f x * positiveIntegral (Q (t/2)) g x ∂μ) ≤
      (∫⁻ x, (positiveIntegral (Q (t/2)) f x)^2 ∂μ) ^ (1/2 : ℝ) *
      (∫⁻ x, (positiveIntegral (Q (t/2)) g x)^2 ∂μ) ^ (1/2 : ℝ) := by
    simpa only [Pi.mul_apply, ENNReal.rpow_two] using
      ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (measurable_positiveIntegral hf).aemeasurable
        (measurable_positiveIntegral hg).aemeasurable
  have hpow : (∫⁻ x, positiveIntegral (Q (t/2)) f x * positiveIntegral (Q (t/2)) g x ∂μ) ^ (2 : ℝ) ≤
      ((∫⁻ x, (positiveIntegral (Q (t/2)) f x)^2 ∂μ) ^ (1/2 : ℝ) *
      (∫⁻ x, (positiveIntegral (Q (t/2)) g x)^2 ∂μ) ^ (1/2 : ℝ)) ^ (2 : ℝ) :=
    ENNReal.rpow_le_rpow hholder (by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (1/2 : ℝ)*2 = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.rpow_one, ENNReal.rpow_two] at hpow
  conv_lhs => rw [ht, pairing_factor hsub hsym hsem hf hg]
  conv_rhs => rw [ht, pairing_factor hsub hsym hsem hf hf, pairing_factor hsub hsym hsem hg hg]
  simpa only [pow_two] using hpow

theorem pairing_indicator {μ : Measure α} {κ : Kernel α α}
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    pairing μ κ (A.indicator (fun _ => (1 : ENNReal)))
      (B.indicator (fun _ => (1 : ENNReal))) = ∫⁻ x in A, κ x B ∂μ := by
  unfold pairing positiveIntegral
  simp only [lintegral_indicator hB, lintegral_one,
    Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A <;> simp [hx]

theorem rectangle_of_diagonal {μ : Measure α} [IsFiniteMeasure μ]
    {Q : NNReal → Kernel α α} (hsub : ∀ t, IsSubMarkovKernel (Q t))
    (hsym : ∀ t, (μ ⊗ₘ Q t).map Prod.swap = μ ⊗ₘ Q t)
    (hsem : ∀ t s, Q (t+s) = Q s ∘ₖ Q t) {t : NNReal} {C : ENNReal}
    (hdiag : ∀ A : Set α, MeasurableSet A →
      pairing μ (Q t) (A.indicator (fun _ => (1 : ENNReal)))
        (A.indicator (fun _ => (1 : ENNReal))) ≤ C * (μ A)^2)
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ x in A, Q t x B ∂μ) ≤ C * μ A * μ B := by
  have hcs : (∫⁻ x in A, Q t x B ∂μ)^2 ≤ (C * μ A * μ B)^2 := by
    calc
      (∫⁻ x in A, Q t x B ∂μ)^2 =
          (pairing μ (Q t) (A.indicator (fun _ => (1 : ENNReal)))
            (B.indicator (fun _ => (1 : ENNReal))))^2 := by rw [pairing_indicator A B hA hB]
      _ ≤ pairing μ (Q t) (A.indicator (fun _ => (1 : ENNReal)))
            (A.indicator (fun _ => (1 : ENNReal))) *
          pairing μ (Q t) (B.indicator (fun _ => (1 : ENNReal)))
            (B.indicator (fun _ => (1 : ENNReal))) :=
        pairing_cauchy hsub hsym hsem (measurable_const.indicator hA) (measurable_const.indicator hB) t
      _ ≤ (C * (μ A)^2) * (C * (μ B)^2) := mul_le_mul' (hdiag A hA) (hdiag B hB)
      _ = (C * μ A * μ B)^2 := by simp only [pow_two]; ac_rfl
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
    (by simpa only [ENNReal.rpow_two] using hcs)

/-- A finite resolvent iterate bounds heat-kernel rectangles at the sum of the mean times. -/
theorem heat_rectangle {μ : Measure α} [IsProbabilityMeasure μ]
    {R : Kernel α α} (hR : IsSubMarkovKernel R)
    {Q : NNReal → Kernel α α} (hsub : ∀ t, IsSubMarkovKernel (Q t))
    (hμ : ∀ t, Q t ∘ₘ μ ≤ μ)
    (hsym : ∀ t, (μ ⊗ₘ Q t).map Prod.swap = μ ⊗ₘ Q t)
    (hsem : ∀ t s, Q (t+s) = Q s ∘ₖ Q t)
    (hjoint : ∀ B : Set α, MeasurableSet B → Measurable (fun p : NNReal × α => Q p.1 p.2 B))
    {a : NNReal} (ha : 0 < a)
    (hmix : ∀ x B, MeasurableSet B → R x B =
      ∫⁻ s : ℝ, Q (Real.toNNReal s) x B ∂expMeasure ((a : ℝ)⁻¹))
    (n : ℕ) {M : ENNReal}
    (hbound : ∀ f : α → ℝ, MemLp f 1 μ →
      eLpNorm ((kernelIntegral R)^[n+1] f) ∞ μ ≤ M * eLpNorm f 1 μ)
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ x in A, Q ((n+1:ℕ)*a) x B ∂μ) ≤
      (2 : ENNReal)^(n+1) * M * μ A * μ B := by
  letI : IsProbabilityMeasure (expMeasure ((a : ℝ)⁻¹)) :=
    isProbabilityMeasure_expMeasure (inv_pos.mpr ha)
  apply rectangle_of_diagonal hsub hsym hsem (A := A) (B := B) (hA := hA) (hB := hB)
  intro D hD
  let f : α → ℝ := D.indicator (fun _ => 1)
  let F : α → ENNReal := D.indicator (fun _ => 1)
  have hf : StronglyMeasurable f := stronglyMeasurable_const.indicator hD
  have hF : Measurable F := measurable_const.indicator hD
  have hf0 : ∀ x, 0 ≤ f x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hf1 : ∀ x, f x ≤ 1 := fun x => by by_cases hx : x ∈ D <;> simp [f, hx]
  have hmem : MemLp f 1 μ := (memLp_const (1 : ℝ)).indicator hD
  have hnorm : eLpNorm f 1 μ = μ D := by
    have henorm : (fun x => ‖f x‖ₑ) = D.indicator (fun _ => (1 : ENNReal)) := by
      funext x
      by_cases hx : x ∈ D <;> simp [f, hx]
    rw [eLpNorm_one_eq_lintegral_enorm, show (∫⁻ x, ‖f x‖ₑ ∂μ) = ∫⁻ x, D.indicator
      (fun _ => (1 : ENNReal)) x ∂μ from by rw [henorm], lintegral_indicator hD]
    simp
  have hof : (fun x => ENNReal.ofReal (f x)) = F := by
    funext x
    by_cases hx : x ∈ D <;> simp [f, F, hx]
  have hiter : StronglyMeasurable ((kernelIntegral R)^[n+1] f) ∧
      (∀ x, 0 ≤ ((kernelIntegral R)^[n+1] f) x ∧ ((kernelIntegral R)^[n+1] f) x ≤ 1) ∧
      ((positiveIntegral R)^[n+1] (fun x => ENNReal.ofReal (f x))) =
        (fun x => ENNReal.ofReal (((kernelIntegral R)^[n+1] f) x)) :=
    iterate_ofReal hR hf hf0 hf1 (n+1)
  have hboundF : ∀ᵐ x ∂μ, ((positiveIntegral R)^[n+1] F) x ≤ M * μ D := by
    have hb : eLpNorm ((kernelIntegral R)^[n+1] f) ∞ μ ≤ M * μ D := by
      simpa only [hnorm] using hbound f hmem
    filter_upwards [enorm_ae_le_eLpNormEssSup ((kernelIntegral R)^[n+1] f) μ] with x hx
    have hval : ((positiveIntegral R)^[n+1] F) x
        = ENNReal.ofReal (((kernelIntegral R)^[n+1] f) x) := by
      rw [← hof, hiter.2.2]
    rw [hval, ← Real.enorm_eq_ofReal (hiter.2.1 x).1]
    exact hx.trans hb
  have hres : (∫⁻ x, F x * ((positiveIntegral R)^[n+1] F) x ∂μ) ≤ M * (μ D)^2 := by
    calc
      (∫⁻ x, F x * ((positiveIntegral R)^[n+1] F) x ∂μ) ≤ ∫⁻ x, F x * (M * μ D) ∂μ :=
        lintegral_mono_ae (hboundF.mono (fun x hx => mul_le_mul_right hx _))
      _ = M * (μ D)^2 := by
        rw [lintegral_mul_const _ hF]
        simp only [F, lintegral_indicator hD, lintegral_one,
          Measure.restrict_apply, MeasurableSet.univ, univ_inter, pow_two]
        ac_rfl
  have hlow : (1/2 : ENNReal)^(n+1) * pairing μ (Q ((n+1:ℕ)*a)) F F ≤
      ∫⁻ x, F x * ((positiveIntegral R)^[n+1] F) x ∂μ := by
    rw [iteration_mixture hsub hjoint hmix hsem hF hF n]
    simpa only [zero_add] using time_average_lower (exponential_half_mass ha)
      (diagonal_antitone hsub hμ hsym hsem hF) (n+1) 0
  calc
    pairing μ (Q ((n+1:ℕ)*a)) F F =
        (2 : ENNReal)^(n+1) * ((1/2 : ENNReal)^(n+1) * pairing μ (Q ((n+1:ℕ)*a)) F F) := by
      have h2 : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
        rw [one_div, ENNReal.mul_inv_cancel (by simp) (by simp)]
      rw [← mul_assoc, ← mul_pow, h2, one_pow, one_mul]
    _ ≤ (2 : ENNReal)^(n+1) * (M * (μ D)^2) := mul_le_mul_right (hlow.trans hres) _
    _ = (2 : ENNReal)^(n+1) * M * (μ D)^2 := (mul_assoc _ _ _).symm

/-- The same finite-iteration estimate in the raw real-valued `L¹ → L∞` carriers. -/
theorem heat_bound {μ : Measure α} [IsProbabilityMeasure μ]
    {R : Kernel α α} (hR : IsSubMarkovKernel R)
    {Q : NNReal → Kernel α α} (hsub : ∀ t, IsSubMarkovKernel (Q t))
    (hμ : ∀ t, Q t ∘ₘ μ ≤ μ)
    (hsym : ∀ t, (μ ⊗ₘ Q t).map Prod.swap = μ ⊗ₘ Q t)
    (hsem : ∀ t s, Q (t+s) = Q s ∘ₖ Q t)
    (hjoint : ∀ B : Set α, MeasurableSet B → Measurable (fun p : NNReal × α => Q p.1 p.2 B))
    {a : NNReal} (ha : 0 < a)
    (hmix : ∀ x B, MeasurableSet B → R x B =
      ∫⁻ s : ℝ, Q (Real.toNNReal s) x B ∂expMeasure ((a : ℝ)⁻¹))
    (n : ℕ) {M : ENNReal}
    (hbound : ∀ f : α → ℝ, MemLp f 1 μ →
      eLpNorm ((kernelIntegral R)^[n+1] f) ∞ μ ≤ M * eLpNorm f 1 μ)
    {f : α → ℝ} (hf : MemLp f 1 μ) :
    eLpNorm (kernelIntegral (Q ((n+1:ℕ)*a)) f) ∞ μ ≤
      (2 : ENNReal)^(n+1) * M * eLpNorm f 1 μ :=
  rectangle_endpoint (hsub _) (hμ _) (hsym _)
    (heat_rectangle hR hsub hμ hsym hsem hjoint ha hmix n hbound) hf

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationHeat
