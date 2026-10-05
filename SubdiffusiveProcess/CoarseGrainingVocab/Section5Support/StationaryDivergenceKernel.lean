module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationarySolenoidalStream
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-!
# Explicit divergence kernel for two smoothing scales

The elementary tensor-density construction writes
the difference of two product mollifiers as the divergence of a smooth,
compactly supported vector field.  Together with `StationaryKernelStream`,
this removes the analytic stream-existence assumption from the solenoidal
approximation argument.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ} {r : ℝ}

def streamLineBump (hr : 0 < r) : ContDiffBump (0 : ℝ) :=
  ⟨r / 2, r, by linarith, by linarith⟩

@[simp] theorem streamLineBump_rIn (hr : 0 < r) :
    (streamLineBump hr).rIn = r / 2 := rfl

@[simp] theorem streamLineBump_rOut (hr : 0 < r) :
    (streamLineBump hr).rOut = r := rfl

def streamScaledBump (hr : 0 < r) : ℝ → ℝ :=
  (streamLineBump hr).normed volume

theorem streamScaledBump_nonneg (hr : 0 < r) (t : ℝ) :
    0 ≤ streamScaledBump hr t := ContDiffBump.nonneg_normed _ t

theorem contDiff_streamScaledBump (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (streamScaledBump hr) :=
  ContDiffBump.contDiff_normed _

theorem continuous_streamScaledBump (hr : 0 < r) :
    Continuous (streamScaledBump hr) := (contDiff_streamScaledBump hr).continuous

theorem support_streamScaledBump (hr : 0 < r) :
    Function.support (streamScaledBump hr) = Metric.ball (0 : ℝ) r := by
  have h := ContDiffBump.support_normed_eq
    (μ := (volume : Measure ℝ)) (f := streamLineBump hr)
  rwa [streamLineBump_rOut] at h

theorem integral_streamScaledBump (hr : 0 < r) :
    ∫ t, streamScaledBump hr t = 1 := ContDiffBump.integral_normed _

theorem streamScaledBump_eq_zero (hr : 0 < r) {t : ℝ}
    (ht : r ≤ |t|) : streamScaledBump hr t = 0 := by
  by_contra hne
  have hmem : t ∈ Metric.ball (0 : ℝ) r := by
    rw [← support_streamScaledBump hr]
    exact hne
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
  linarith

theorem streamScaledBump_le (hr : 0 < r) (t : ℝ) :
    streamScaledBump hr t ≤ 1 / r := by
  have hval : volume.real (Metric.closedBall (0 : ℝ) (r / 2)) = r := by
    rw [measureReal_def, Real.volume_closedBall,
      ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 2 * (r / 2))]
    ring
  have h := ContDiffBump.normed_le_div_measure_closedBall_rIn
    (streamLineBump hr) (μ := (volume : Measure ℝ)) t
  rw [streamLineBump_rIn, hval] at h
  exact h

theorem streamUpdate_eq_add_smul_basisVec (x : Vec d) (k : Fin d) (t : ℝ) :
    Function.update x k t = x + (t - x k) • basisVec k := by
  funext i
  by_cases h : i = k
  · subst h
    simp
  · simp [h]

theorem streamCoordDeriv_eq_of_hasDerivAt_update
    {F : Vec d → ℝ} {h : ℝ → ℝ} {x : Vec d} {k : Fin d} {c : ℝ}
    (hF : DifferentiableAt ℝ F x)
    (hupd : ∀ t : ℝ, F (Function.update x k t) = h t)
    (hh : HasDerivAt h c (x k)) : streamCoordDeriv F k x = c := by
  have hline : HasDerivAt
      (fun t : ℝ => x + (t - x k) • basisVec k) (basisVec k) (x k) := by
    have h1 : HasDerivAt (fun t : ℝ => t - x k) (1 : ℝ) (x k) :=
      (hasDerivAt_id (x k)).sub_const (x k)
    have h2 := HasDerivAt.const_add x (h1.smul_const (basisVec k))
    rwa [one_smul] at h2
  have hcomp : HasDerivAt
      (F ∘ fun t : ℝ => x + (t - x k) • basisVec k)
      (fderiv ℝ F x (basisVec k)) (x k) := by
    have hFA : HasFDerivAt F (fderiv ℝ F x)
        ((fun t : ℝ => x + (t - x k) • basisVec k) (x k)) := by
      show HasFDerivAt F (fderiv ℝ F x) (x + (x k - x k) • basisVec k)
      rw [show x + (x k - x k) • basisVec k = x by simp]
      exact hF.hasFDerivAt
    exact hFA.comp_hasDerivAt (x k) hline
  have hfun : (F ∘ fun t : ℝ => x + (t - x k) • basisVec k) = h := by
    funext t
    rw [Function.comp_apply, ← streamUpdate_eq_add_smul_basisVec, hupd]
  rw [hfun] at hcomp
  exact hcomp.unique hh

def streamProductDensity (d : ℕ) (hr : 0 < r) : Vec d → ℝ :=
  fun x => ∏ i : Fin d, streamScaledBump hr (x i)

theorem streamProductDensity_nonneg (d : ℕ) (hr : 0 < r) (x : Vec d) :
    0 ≤ streamProductDensity d hr x :=
  Finset.prod_nonneg fun i _ => streamScaledBump_nonneg hr (x i)

theorem contDiff_streamProductDensity (d : ℕ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (streamProductDensity d hr) :=
  contDiff_prod fun i _ =>
    (contDiff_streamScaledBump hr).comp (contDiff_apply ℝ ℝ i)

theorem continuous_streamProductDensity (d : ℕ) (hr : 0 < r) :
    Continuous (streamProductDensity d hr) :=
  (contDiff_streamProductDensity d hr).continuous

theorem streamProductDensity_eq_zero_of_le (d : ℕ) (hr : 0 < r)
    {x : Vec d} (hx : r ≤ ‖x‖) : streamProductDensity d hr x = 0 := by
  classical
  by_contra hne
  have hall : ∀ i : Fin d, ‖x i‖ < r := by
    intro i
    by_contra hi
    push Not at hi
    refine hne (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    exact streamScaledBump_eq_zero hr (by rwa [Real.norm_eq_abs] at hi)
  have hlt : ‖x‖ < r := (pi_norm_lt_iff hr).2 hall
  linarith

theorem hasCompactSupport_streamProductDensity (d : ℕ) (hr : 0 < r) :
    HasCompactSupport (streamProductDensity d hr) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) r)
    fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  push Not at hx
  exact streamProductDensity_eq_zero_of_le d hr hx.le

theorem support_streamProductDensity_subset (d : ℕ) (hr : 0 < r) :
    Function.support (streamProductDensity d hr) ⊆
      Metric.ball (0 : Vec d) r := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  by_contra hnot
  exact hx (streamProductDensity_eq_zero_of_le d hr (not_lt.mp hnot))

theorem integrable_streamProductDensity (d : ℕ) (hr : 0 < r) :
    Integrable (streamProductDensity d hr) volume :=
  (continuous_streamProductDensity d hr).integrable_of_hasCompactSupport
    (hasCompactSupport_streamProductDensity d hr)

theorem integral_streamProductDensity (d : ℕ) (hr : 0 < r) :
    ∫ x, streamProductDensity d hr x = 1 := by
  have h : ∫ x : Fin d → ℝ, ∏ i : Fin d, streamScaledBump hr (x i) =
      (∫ t, streamScaledBump hr t) ^ Fintype.card (Fin d) :=
    integral_fintype_prod_volume_eq_pow
      (𝕜 := ℝ) (ι := Fin d) (streamScaledBump hr)
  calc
    ∫ x, streamProductDensity d hr x =
        ∫ x : Fin d → ℝ, ∏ i : Fin d, streamScaledBump hr (x i) := rfl
    _ = (∫ t, streamScaledBump hr t) ^ Fintype.card (Fin d) := h
    _ = 1 := by rw [integral_streamScaledBump hr, one_pow]

theorem streamProductDensity_le (d : ℕ) (hr : 0 < r) (x : Vec d) :
    streamProductDensity d hr x ≤ 1 / r ^ d := by
  classical
  have h : ∏ i : Fin d, streamScaledBump hr (x i) ≤
      ∏ _i : Fin d, (1 / r) :=
    Finset.prod_le_prod₀
      (fun i _ => streamScaledBump_nonneg hr (x i))
      (fun i _ => streamScaledBump_le hr (x i))
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  calc
    streamProductDensity d hr x ≤ (1 / r) ^ d := h
    _ = 1 / r ^ d := by rw [div_pow, one_pow]

/-- The product density packaged for the stationary Hilbert mollifier. -/
def Stationary.L2Mollifier.ofStreamProduct (d : ℕ) (hr : 0 < r) :
    Stationary.L2Mollifier d where
  toFun := streamProductDensity d hr
  radius := r
  nonneg := streamProductDensity_nonneg d hr
  smooth := contDiff_streamProductDensity d hr
  compactSupport := hasCompactSupport_streamProductDensity d hr
  integral_eq_one := integral_streamProductDensity d hr
  support_subset := support_streamProductDensity_subset d hr

def streamIdxBelow (d m : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun i : Fin d => (i : ℕ) < m

def streamIdxAbove (d m : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun i : Fin d => m ≤ (i : ℕ)

@[simp] theorem mem_streamIdxBelow {m : ℕ} {i : Fin d} :
    i ∈ streamIdxBelow d m ↔ (i : ℕ) < m := by simp [streamIdxBelow]

@[simp] theorem mem_streamIdxAbove {m : ℕ} {i : Fin d} :
    i ∈ streamIdxAbove d m ↔ m ≤ (i : ℕ) := by simp [streamIdxAbove]

theorem streamIdxBelow_zero (d : ℕ) :
    streamIdxBelow d 0 = (∅ : Finset (Fin d)) := by ext i; simp

theorem streamIdxAbove_zero (d : ℕ) :
    streamIdxAbove d 0 = (Finset.univ : Finset (Fin d)) := by ext i; simp

theorem streamIdxBelow_self (d : ℕ) :
    streamIdxBelow d d = (Finset.univ : Finset (Fin d)) := by ext i; simp

theorem streamIdxAbove_self (d : ℕ) :
    streamIdxAbove d d = (∅ : Finset (Fin d)) := by ext i; simp

theorem streamIdxAbove_val_eq_insert (k : Fin d) :
    streamIdxAbove d (k : ℕ) =
      insert k (streamIdxAbove d ((k : ℕ) + 1)) := by
  classical
  ext i
  simp only [Finset.mem_insert, mem_streamIdxAbove]
  constructor
  · intro hi
    rcases Nat.lt_or_ge (i : ℕ) ((k : ℕ) + 1) with hlt | hge
    · exact Or.inl (Fin.val_injective (by omega))
    · exact Or.inr hge
  · rintro (rfl | hge)
    · exact le_rfl
    · omega

theorem streamIdxBelow_succ_eq_insert (k : Fin d) :
    streamIdxBelow d ((k : ℕ) + 1) =
      insert k (streamIdxBelow d (k : ℕ)) := by
  classical
  ext i
  simp only [Finset.mem_insert, mem_streamIdxBelow]
  constructor
  · intro hi
    rcases Nat.lt_or_ge (i : ℕ) (k : ℕ) with hlt | hge
    · exact Or.inr hlt
    · exact Or.inl (Fin.val_injective (by omega))
  · rintro (rfl | hlt) <;> omega

def streamKernelPrimitive (a b : ℝ → ℝ) (T t : ℝ) : ℝ :=
  ∫ s in (-T)..t, (a s - b s)

theorem hasDerivAt_streamKernelPrimitive {a b : ℝ → ℝ} {T : ℝ}
    (ha : Continuous a) (hb : Continuous b) (t : ℝ) :
    HasDerivAt (streamKernelPrimitive a b T) (a t - b t) t := by
  have hc : Continuous fun s => a s - b s := ha.sub hb
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (-T) t)
    (hc.stronglyMeasurableAtFilter volume (nhds t)) hc.continuousAt

theorem differentiable_streamKernelPrimitive {a b : ℝ → ℝ} {T : ℝ}
    (ha : Continuous a) (hb : Continuous b) :
    Differentiable ℝ (streamKernelPrimitive a b T) := fun t =>
  (hasDerivAt_streamKernelPrimitive ha hb t).differentiableAt

theorem deriv_streamKernelPrimitive {a b : ℝ → ℝ} {T : ℝ}
    (ha : Continuous a) (hb : Continuous b) :
    deriv (streamKernelPrimitive a b T) = fun t => a t - b t := by
  funext t
  exact (hasDerivAt_streamKernelPrimitive ha hb t).deriv

theorem contDiff_streamKernelPrimitive {a b : ℝ → ℝ} {T : ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (streamKernelPrimitive a b T) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨differentiable_streamKernelPrimitive ha.continuous hb.continuous, ?_⟩
  rw [deriv_streamKernelPrimitive ha.continuous hb.continuous]
  exact ha.sub hb

private theorem integrable_streamKernelFactor_of_zero_outside
    {a : ℝ → ℝ} {T : ℝ} (ha : Continuous a)
    (haT : ∀ s : ℝ, T ≤ |s| → a s = 0) : Integrable a volume := by
  refine ha.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (K := Set.Icc (-T) T) isCompact_Icc
      fun s hs => ?_)
  rw [Set.mem_Icc] at hs
  push Not at hs
  rcases le_or_gt (-T) s with hle | hlt
  · exact haT s (le_trans (hs hle).le (le_abs_self s))
  · exact haT s (le_trans (by linarith : T ≤ -s) (neg_le_abs s))

theorem streamKernelPrimitive_eq_zero_of_le
    {a b : ℝ → ℝ} {T : ℝ}
    (ha : Continuous a) (hb : Continuous b)
    (haT : ∀ s : ℝ, T ≤ |s| → a s = 0)
    (hbT : ∀ s : ℝ, T ≤ |s| → b s = 0)
    (ha1 : ∫ s, a s = 1) (hb1 : ∫ s, b s = 1)
    {t : ℝ} (ht : T ≤ |t|) : streamKernelPrimitive a b T t = 0 := by
  have hzero : ∀ s : ℝ, T ≤ |s| → a s - b s = 0 := fun s hs => by
    rw [haT s hs, hbT s hs, sub_zero]
  have hc : Continuous fun s => a s - b s := ha.sub hb
  unfold streamKernelPrimitive
  rcases le_abs.mp ht with hpos | hneg
  · have hsplit : (∫ s in (-T)..T, (a s - b s)) +
        ∫ s in T..t, (a s - b s) = ∫ s in (-T)..t, (a s - b s) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable (-T) T) (hc.intervalIntegrable T t)
    have hfull : (∫ s in (-T)..T, (a s - b s)) = 0 := by
      have hsupp : Function.support (fun s => a s - b s) ⊆ Set.Ioc (-T) T := by
        intro s hs
        by_contra hmem
        rw [Set.mem_Ioc] at hmem
        push Not at hmem
        rcases lt_or_ge (-T) s with hlt | hge
        · exact hs (hzero s (le_trans (hmem hlt).le (le_abs_self s)))
        · exact hs (hzero s (le_trans (by linarith : T ≤ -s) (neg_le_abs s)))
      rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp,
        integral_sub
          (integrable_streamKernelFactor_of_zero_outside ha haT)
          (integrable_streamKernelFactor_of_zero_outside hb hbT),
        ha1, hb1, sub_self]
    have htail : (∫ s in T..t, (a s - b s)) = 0 := by
      have hcongr : (∫ s in T..t, (a s - b s)) =
          ∫ _s in T..t, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [Set.uIcc_of_le hpos, Set.mem_Icc] at hs
        exact hzero s (le_trans hs.1 (le_abs_self s))
      rw [hcongr, intervalIntegral.integral_zero]
    rw [← hsplit, hfull, htail, add_zero]
  · have hle : t ≤ -T := by linarith
    have hcongr : (∫ s in (-T)..t, (a s - b s)) =
        ∫ _s in (-T)..t, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_ge hle, Set.mem_Icc] at hs
      exact hzero s (le_trans (by linarith [hs.2] : T ≤ -s) (neg_le_abs s))
    rw [hcongr, intervalIntegral.integral_zero]

def streamTensorDensity (a : ℝ → ℝ) (x : Vec d) : ℝ :=
  ∏ i : Fin d, a (x i)

def streamMixedDensity (a b : ℝ → ℝ) (m : ℕ) (x : Vec d) : ℝ :=
  (∏ i ∈ streamIdxBelow d m, b (x i)) *
    (∏ i ∈ streamIdxAbove d m, a (x i))

def streamDivKernel (a b : ℝ → ℝ) (T : ℝ) (x : Vec d) : Vec d :=
  fun k => streamKernelPrimitive a b T (x k) *
    (∏ i ∈ streamIdxBelow d (k : ℕ), b (x i)) *
    (∏ i ∈ streamIdxAbove d ((k : ℕ) + 1), a (x i))

theorem contDiff_streamDivKernel_apply {a b : ℝ → ℝ} {T : ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (k : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => streamDivKernel a b T x k) := by
  exact (((contDiff_streamKernelPrimitive ha hb).comp (contDiff_apply ℝ ℝ k)).mul
    (contDiff_prod fun i _ => hb.comp (contDiff_apply ℝ ℝ i))).mul
      (contDiff_prod fun i _ => ha.comp (contDiff_apply ℝ ℝ i))

theorem streamDivKernel_apply_eq_zero_of_le
    {a b : ℝ → ℝ} {T : ℝ}
    (ha : Continuous a) (hb : Continuous b)
    (haT : ∀ s : ℝ, T ≤ |s| → a s = 0)
    (hbT : ∀ s : ℝ, T ≤ |s| → b s = 0)
    (ha1 : ∫ s, a s = 1) (hb1 : ∫ s, b s = 1)
    (hT : 0 < T) {x : Vec d} (hx : T ≤ ‖x‖) (k : Fin d) :
    streamDivKernel a b T x k = 0 := by
  classical
  have hex : ∃ i : Fin d, T ≤ |x i| := by
    by_contra hcon
    push Not at hcon
    have hlt : ‖x‖ < T := (pi_norm_lt_iff hT).2 fun i => by
      rw [Real.norm_eq_abs]
      exact hcon i
    linarith
  obtain ⟨i, hi⟩ := hex
  unfold streamDivKernel
  rcases lt_trichotomy (i : ℕ) (k : ℕ) with hlt | heq | hgt
  · rw [Finset.prod_eq_zero (mem_streamIdxBelow.mpr hlt) (hbT (x i) hi)]
    ring
  · have hik : i = k := Fin.val_injective heq
    subst hik
    rw [streamKernelPrimitive_eq_zero_of_le ha hb haT hbT ha1 hb1 hi]
    ring
  · rw [Finset.prod_eq_zero (mem_streamIdxAbove.mpr (by omega)) (haT (x i) hi)]
    ring

theorem hasCompactSupport_streamDivKernel_apply
    {a b : ℝ → ℝ} {T : ℝ}
    (ha : Continuous a) (hb : Continuous b)
    (haT : ∀ s : ℝ, T ≤ |s| → a s = 0)
    (hbT : ∀ s : ℝ, T ≤ |s| → b s = 0)
    (ha1 : ∫ s, a s = 1) (hb1 : ∫ s, b s = 1)
    (hT : 0 < T) (k : Fin d) :
    HasCompactSupport (fun x : Vec d => streamDivKernel a b T x k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) T)
    fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  push Not at hx
  exact streamDivKernel_apply_eq_zero_of_le ha hb haT hbT ha1 hb1 hT hx.le k

private theorem streamCoordDeriv_streamDivKernel_apply
    {a b : ℝ → ℝ} {T : ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (k : Fin d) (x : Vec d) :
    streamCoordDeriv (fun y : Vec d => streamDivKernel a b T y k) k x =
      (a (x k) - b (x k)) *
        (∏ i ∈ streamIdxBelow d (k : ℕ), b (x i)) *
        (∏ i ∈ streamIdxAbove d ((k : ℕ) + 1), a (x i)) := by
  classical
  have hdiff : DifferentiableAt ℝ
      (fun y : Vec d => streamDivKernel a b T y k) x :=
    ((contDiff_streamDivKernel_apply ha hb k).differentiable
      (by simp)).differentiableAt
  have hupd : ∀ t : ℝ,
      streamDivKernel a b T (Function.update x k t) k =
        streamKernelPrimitive a b T t *
        (∏ i ∈ streamIdxBelow d (k : ℕ), b (x i)) *
        (∏ i ∈ streamIdxAbove d ((k : ℕ) + 1), a (x i)) := by
    intro t
    have hP : (∏ i ∈ streamIdxBelow d (k : ℕ),
        b (Function.update x k t i)) =
        ∏ i ∈ streamIdxBelow d (k : ℕ), b (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [mem_streamIdxBelow] at hi
      have hne : i ≠ k := fun hik => by rw [hik] at hi; omega
      rw [Function.update_of_ne hne]
    have hQ : (∏ i ∈ streamIdxAbove d ((k : ℕ) + 1),
        a (Function.update x k t i)) =
        ∏ i ∈ streamIdxAbove d ((k : ℕ) + 1), a (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [mem_streamIdxAbove] at hi
      have hne : i ≠ k := fun hik => by rw [hik] at hi; omega
      rw [Function.update_of_ne hne]
    unfold streamDivKernel
    rw [Function.update_self, hP, hQ]
  have htarget : HasDerivAt
      (fun t : ℝ => streamKernelPrimitive a b T t *
        (∏ i ∈ streamIdxBelow d (k : ℕ), b (x i)) *
        (∏ i ∈ streamIdxAbove d ((k : ℕ) + 1), a (x i)))
      ((a (x k) - b (x k)) *
        (∏ i ∈ streamIdxBelow d (k : ℕ), b (x i)) *
        (∏ i ∈ streamIdxAbove d ((k : ℕ) + 1), a (x i))) (x k) :=
    ((hasDerivAt_streamKernelPrimitive ha.continuous hb.continuous (x k)
      ).mul_const _).mul_const _
  exact streamCoordDeriv_eq_of_hasDerivAt_update hdiff hupd htarget

theorem streamCoordDeriv_sum_streamDivKernel
    {a b : ℝ → ℝ} {T : ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (x : Vec d) :
    ∑ k : Fin d,
        streamCoordDeriv (fun y : Vec d => streamDivKernel a b T y k) k x =
      streamTensorDensity a x - streamTensorDensity b x := by
  classical
  have hstep : ∀ k : Fin d,
      streamCoordDeriv (fun y : Vec d => streamDivKernel a b T y k) k x =
        streamMixedDensity a b (k : ℕ) x -
          streamMixedDensity a b ((k : ℕ) + 1) x := by
    intro k
    rw [streamCoordDeriv_streamDivKernel_apply ha hb k x]
    unfold streamMixedDensity
    rw [streamIdxAbove_val_eq_insert k,
      Finset.prod_insert (by simp : k ∉ streamIdxAbove d ((k : ℕ) + 1)),
      streamIdxBelow_succ_eq_insert k,
      Finset.prod_insert (by simp : k ∉ streamIdxBelow d (k : ℕ))]
    ring
  calc
    ∑ k : Fin d,
        streamCoordDeriv (fun y : Vec d => streamDivKernel a b T y k) k x =
      ∑ k : Fin d, (streamMixedDensity a b (k : ℕ) x -
        streamMixedDensity a b ((k : ℕ) + 1) x) :=
          Finset.sum_congr rfl fun k _ => hstep k
    _ = ∑ m ∈ Finset.range d,
        (streamMixedDensity a b m x - streamMixedDensity a b (m + 1) x) :=
      Fin.sum_univ_eq_sum_range
        (fun m => streamMixedDensity a b m x -
          streamMixedDensity a b (m + 1) x) d
    _ = streamMixedDensity a b 0 x - streamMixedDensity a b d x :=
      Finset.sum_range_sub' (fun m => streamMixedDensity a b m x) d
    _ = streamTensorDensity a x - streamTensorDensity b x := by
      unfold streamMixedDensity streamTensorDensity
      rw [streamIdxBelow_zero, streamIdxAbove_zero, streamIdxBelow_self,
        streamIdxAbove_self]
      simp

theorem contDiff_twoScaleStreamKernel
    {epsilon R : ℝ} (hepsilon : 0 < epsilon) (hR : 0 < R)
    (k : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d =>
      streamDivKernel (streamScaledBump hepsilon) (streamScaledBump hR)
        (epsilon + R) x k) :=
  contDiff_streamDivKernel_apply
    (contDiff_streamScaledBump hepsilon) (contDiff_streamScaledBump hR) k

theorem hasCompactSupport_twoScaleStreamKernel
    {epsilon R : ℝ} (hepsilon : 0 < epsilon) (hR : 0 < R)
    (k : Fin d) :
    HasCompactSupport (fun x : Vec d =>
      streamDivKernel (streamScaledBump hepsilon) (streamScaledBump hR)
        (epsilon + R) x k) := by
  refine hasCompactSupport_streamDivKernel_apply
    (continuous_streamScaledBump hepsilon) (continuous_streamScaledBump hR)
    (fun s hs => streamScaledBump_eq_zero hepsilon (by linarith))
    (fun s hs => streamScaledBump_eq_zero hR (by linarith))
    (integral_streamScaledBump hepsilon) (integral_streamScaledBump hR)
    (by linarith) k

theorem streamCoordDeriv_sum_twoScaleStreamKernel
    {epsilon R : ℝ} (hepsilon : 0 < epsilon) (hR : 0 < R)
    (x : Vec d) :
    ∑ k : Fin d, streamCoordDeriv
      (fun y : Vec d =>
        streamDivKernel (streamScaledBump hepsilon) (streamScaledBump hR)
          (epsilon + R) y k) k x =
      streamProductDensity d hepsilon x - streamProductDensity d hR x := by
  simpa only [streamProductDensity, streamTensorDensity] using
    streamCoordDeriv_sum_streamDivKernel
      (contDiff_streamScaledBump hepsilon) (contDiff_streamScaledBump hR) x

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
