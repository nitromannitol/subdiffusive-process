module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section




set_option autoImplicit false

open MeasureTheory Set Filter Metric
open scoped RealInnerProductSpace ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity

/-! ## Symmetric bounded operators -/

section Symm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A bounded operator on a real inner product space is *symmetric* when it agrees
with its adjoint on the whole space.  Stated as a pairing identity so that no
`CompleteSpace`/`star` machinery is needed. -/
def IsSymmetricOp (T : E →L[ℝ] E) : Prop := ∀ f g : E, ⟪T f, g⟫ = ⟪f, T g⟫

theorem IsSymmetricOp.comp {S T : E →L[ℝ] E} (hS : IsSymmetricOp S) (hT : IsSymmetricOp T)
    (hcomm : ∀ f, S (T f) = T (S f)) : IsSymmetricOp (S.comp T) := fun f g => by
  simp only [ContinuousLinearMap.comp_apply]
  rw [hS, hT, hcomm]

end Symm

/-! ## Upgrading almost-everywhere statements to every point of the carrier

A measure of full support on an open set turns an almost-everywhere inequality
between functions continuous on that set into a pointwise one.  This is the
manuscript's "continuity and full support extend them to every spatial point". -/

section Upgrade

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {mu : Measure X} {Om : Set X}

/-- **Full support on `Om`**: every nonempty open subset of `Om` has positive mass. -/
def FullSupportOn (mu : Measure X) (Om : Set X) : Prop :=
  ∀ V : Set X, IsOpen V → V ⊆ Om → V.Nonempty → mu V ≠ 0

/-- An almost-everywhere upper bound on a function continuous on `Om` holds at
every point of `Om`. -/
theorem le_of_ae_le (hOm : IsOpen Om) (hsupp : FullSupportOn mu Om)
    {f : X → ℝ} (hf : ContinuousOn f Om) {c : ℝ}
    (hae : ∀ᵐ x ∂mu, x ∈ Om → f x ≤ c) : ∀ x ∈ Om, f x ≤ c := by
  intro x hx
  by_contra hlt
  push Not at hlt
  have hnull : mu (Om ∩ f ⁻¹' Ioi c) = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.mp hae)
    exact fun hcon => absurd (hcon hy.1) (not_le.mpr hy.2)
  exact hsupp _ (hf.isOpen_inter_preimage hOm isOpen_Ioi) inter_subset_left ⟨x, hx, hlt⟩ hnull

/-- An almost-everywhere lower bound on a function continuous on `Om` holds at
every point of `Om`. -/
theorem le_of_ae_ge (hOm : IsOpen Om) (hsupp : FullSupportOn mu Om)
    {f : X → ℝ} (hf : ContinuousOn f Om) {c : ℝ}
    (hae : ∀ᵐ x ∂mu, x ∈ Om → c ≤ f x) : ∀ x ∈ Om, c ≤ f x := by
  intro x hx
  by_contra hlt
  push Not at hlt
  have hnull : mu (Om ∩ f ⁻¹' Iio c) = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.mp hae)
    exact fun hcon => absurd (hcon hy.1) (not_le.mpr hy.2)
  exact hsupp _ (hf.isOpen_inter_preimage hOm isOpen_Iio) inter_subset_left ⟨x, hx, hlt⟩ hnull

/-- Two functions continuous on `Om` that agree almost everywhere on `Om` agree at
every point of `Om`. -/
theorem eqOn_of_ae_eq_of_fullSupport (hOm : IsOpen Om) (hsupp : FullSupportOn mu Om)
    {f g : X → ℝ} (hf : ContinuousOn f Om) (hg : ContinuousOn g Om)
    (hae : ∀ᵐ x ∂mu, x ∈ Om → f x = g x) : EqOn f g Om := by
  have hsub : ContinuousOn (fun x => f x - g x) Om := hf.sub hg
  have h1 : ∀ x ∈ Om, f x - g x ≤ 0 := by
    refine le_of_ae_le hOm hsupp hsub ?_
    filter_upwards [hae] with y hy hyOm
    simp [hy hyOm]
  have h2 : ∀ x ∈ Om, (0 : ℝ) ≤ f x - g x := by
    refine le_of_ae_ge hOm hsupp hsub ?_
    filter_upwards [hae] with y hy hyOm
    simp [hy hyOm]
  intro x hx
  have := le_antisymm (h1 x hx) (h2 x hx)
  linarith

end Upgrade

/-! ## Two facts about real `L²` -/

section L2Basic

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}

/-- A nonnegative function whose integral over every finite-measure set is at most
one has total lower integral at most one. -/
theorem lintegral_le_one_of_setIntegral_le_one [SigmaFinite mu] {h : X → ℝ}
    (hmeas : AEMeasurable h mu) (hnn : 0 ≤ᵐ[mu] h)
    (hint : ∀ s : Set X, MeasurableSet s → mu s ≠ ∞ → IntegrableOn h s mu)
    (hle : ∀ s : Set X, MeasurableSet s → mu s ≠ ∞ → (∫ z in s, h z ∂mu) ≤ 1) :
    (∫⁻ z, ENNReal.ofReal (h z) ∂mu) ≤ 1 := by
  classical
  set F : ℕ → X → ℝ≥0∞ :=
    fun n => (spanningSets mu n).indicator (fun z => ENNReal.ofReal (h z)) with hF
  have hFm : ∀ n, AEMeasurable (F n) mu :=
    fun n => hmeas.ennreal_ofReal.indicator (measurableSet_spanningSets mu n)
  have hmono : ∀ᵐ z ∂mu, Monotone fun n => F n z := by
    filter_upwards with z
    intro n m hnm
    by_cases hz : z ∈ spanningSets mu n
    · simp only [hF, Set.indicator_of_mem hz,
        Set.indicator_of_mem (monotone_spanningSets mu hnm hz), le_refl]
    · simp only [hF, Set.indicator_of_notMem hz, zero_le]
  have hsup : ∀ z, ⨆ n, F n z = ENNReal.ofReal (h z) := by
    intro z
    have hmem : z ∈ ⋃ n, spanningSets mu n := by rw [iUnion_spanningSets mu]; exact Set.mem_univ z
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    refine le_antisymm (iSup_le fun m => ?_) (le_iSup_of_le n ?_)
    · simp only [hF, Set.indicator_apply]
      split
      · exact le_rfl
      · exact zero_le
    · simp only [hF, Set.indicator_of_mem hn, le_refl]
  calc (∫⁻ z, ENNReal.ofReal (h z) ∂mu) = ∫⁻ z, ⨆ n, F n z ∂mu := by simp only [hsup]
    _ = ⨆ n, ∫⁻ z, F n z ∂mu := lintegral_iSup' hFm hmono
    _ ≤ 1 := by
        refine iSup_le fun n => ?_
        have hS := measurableSet_spanningSets mu n
        have hfin := (measure_spanningSets_lt_top mu n).ne
        rw [hF]
        simp only
        rw [lintegral_indicator hS,
          ← ofReal_integral_eq_lintegral_ofReal (hint _ hS hfin) (ae_restrict_of_ae hnn)]
        exact ENNReal.ofReal_le_one.mpr (hle _ hS hfin)

/-- The real `L²` inner product is the integral of the product. -/
theorem inner_eq_integral (f g : Lp ℝ 2 mu) : ⟪f, g⟫ = ∫ z, f z * g z ∂mu := by
  rw [L2.inner_def]
  simp [RCLike.inner_apply, mul_comm]

theorem indicatorConstLp_nonneg {s : Set X} (hs : MeasurableSet s) (hstop : mu s ≠ ∞) :
    (0 : X → ℝ) ≤ᵐ[mu] fun z => (indicatorConstLp 2 hs hstop (1 : ℝ)) z := by
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hstop) (c := (1 : ℝ))]
    with z hz
  rw [hz]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) z

theorem indicatorConstLp_le_one {s : Set X} (hs : MeasurableSet s) (hstop : mu s ≠ ∞) :
    ∀ᵐ z ∂mu, (indicatorConstLp 2 hs hstop (1 : ℝ)) z ≤ 1 := by
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hstop) (c := (1 : ℝ))]
    with z hz
  rw [hz]
  by_cases hzs : z ∈ s <;> simp [hzs]

theorem inner_indicatorConstLp_one (h : Lp ℝ 2 mu) {s : Set X} (hs : MeasurableSet s)
    (hstop : mu s ≠ ∞) :
    ⟪h, indicatorConstLp 2 hs hstop (1 : ℝ)⟫ = ∫ z in s, h z ∂mu := by
  rw [real_inner_comm, L2.inner_indicatorConstLp_eq_setIntegral_inner ℝ h hs (1 : ℝ) hstop]
  simp [RCLike.inner_apply]

end L2Basic

/-! ## The resolvent-regularity datum -/

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]

/-- **The data supplied by hypothesis (RRK)**, `s.fixed.coefficient` and `mfd:sec-speed`.

`Om` is the open carrier, `mu` a measure of full support concentrated on it,
`semigroup t = e^{-tH}`, `resolvent = (I+sH)^{-N}`, `smoothing t = (I+sH)^N e^{-tH/2}`
and `repr x = g_x` the Riesz representative of `f ↦ ((I+sH)^{-N}f)(x)`. -/
structure ResolventRegularityDatum (mu : Measure X) (Om : Set X) where
  /-- The carrier is open. -/
  isOpen_carrier : IsOpen Om
  /-- The measure is concentrated on the carrier. -/
  measure_compl : mu Omᶜ = 0
  /-- The measure has full support on the carrier. -/
  fullSupport : FullSupportOn mu Om
  /-- `e^{-tH}`, for `t > 0`. -/
  semigroup : ℝ → (Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
  /-- `(I + sH)^{-N}`. -/
  resolvent : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu
  /-- `(I + sH)^N e^{-tH/2}`, for `t > 0`. -/
  smoothing : ℝ → (Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
  /-- `g_x`, the Riesz representative of evaluation at `x` of `(I+sH)^{-N}`. -/
  repr : X → Lp ℝ 2 mu
  /-- `e^{-tH}` is self-adjoint. -/
  isSymmetricOp_semigroup : ∀ t, 0 < t → IsSymmetricOp (semigroup t)
  /-- `e^{-tH}e^{-uH} = e^{-(t+u)H}`. -/
  semigroup_comp : ∀ t u, 0 < t → 0 < u →
    (semigroup t).comp (semigroup u) = semigroup (t + u)
  /-- `e^{-tH}` preserves positivity. -/
  semigroup_nonneg : ∀ t, 0 < t → ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun x => f x) →
    0 ≤ᵐ[mu] fun x => (semigroup t f) x
  /-- `e^{-tH}` is sub-Markov. -/
  semigroup_le_one : ∀ t, 0 < t → ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun x => f x) →
    (∀ᵐ x ∂mu, f x ≤ 1) → ∀ᵐ x ∂mu, (semigroup t f) x ≤ 1
  /-- `(I+sH)^{-N}` is self-adjoint. -/
  isSymmetricOp_resolvent : IsSymmetricOp resolvent
  /-- `(I+sH)^{-N}` is injective. -/
  injective_resolvent : Function.Injective resolvent
  /-- `(I+sH)^N e^{-tH/2}` is self-adjoint. -/
  isSymmetricOp_smoothing : ∀ t, 0 < t → IsSymmetricOp (smoothing t)
  /-- `(I+sH)^{-N}(I+sH)^N e^{-tH/2} = e^{-tH/2}`. -/
  resolvent_comp_smoothing : ∀ t, 0 < t →
    resolvent.comp (smoothing t) = semigroup (t / 2)
  /-- `t ↦ (I+sH)^N e^{-tH/2}` is norm-continuous on `(0,∞)`.  This is the
  manuscript's "scalar functional calculus bounds `B_t` and `∂_t B_t` locally
  uniformly for `t > 0`". -/
  continuousOn_smoothing : ContinuousOn smoothing (Ioi 0)
  /-- **Riesz representation**: `g_x` represents evaluation at `x` of
  `(I+sH)^{-N}f`. -/
  resolvent_apply_ae : ∀ f : Lp ℝ 2 mu,
    (fun x => (resolvent f) x) =ᵐ[mu] fun x => ⟪repr x, f⟫
  /-- **(RRK)**: on every compact subset of the carrier, `x ↦ g_x` is Hölder. -/
  holder_repr : ∀ K : Set X, K ⊆ Om → IsCompact K → ∃ C a : ℝ, 0 < a ∧
    ∀ x ∈ K, ∀ y ∈ K, ‖repr x - repr y‖ ≤ C * dist x y ^ a

namespace ResolventRegularityDatum

variable {mu : Measure X} {Om : Set X} (D : ResolventRegularityDatum mu Om)

/-! ### The operator algebra

The manuscript's step 2 is entirely algebraic once `B_t` is a bounded operator:
the relation `R B_t = P_{t/2}` plus self-adjointness of `R`, `B_t` and `P_t`
generates every identity the kernel needs. -/

theorem resolvent_smoothing {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 mu) :
    D.resolvent ((D.smoothing t) f) = D.semigroup (t / 2) f := by
  have h := D.resolvent_comp_smoothing t ht
  calc D.resolvent ((D.smoothing t) f)
      = (D.resolvent.comp (D.smoothing t)) f := rfl
    _ = D.semigroup (t / 2) f := by rw [h]

/-- `B_t (I+sH)^{-N} = e^{-tH/2}`: the mirror of `resolvent_comp_smoothing`,
obtained by taking adjoints. -/
theorem smoothing_resolvent {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 mu) :
    (D.smoothing t) (D.resolvent f) = D.semigroup (t / 2) f := by
  refine ext_inner_left ℝ fun v => ?_
  rw [← D.isSymmetricOp_smoothing t ht, ← D.isSymmetricOp_resolvent,
    D.resolvent_smoothing ht v, D.isSymmetricOp_semigroup (t / 2) (by positivity)]

/-- `(I+sH)^{-N}` and `(I+sH)^N e^{-tH/2}` commute. -/
theorem resolvent_smoothing_comm {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 mu) :
    D.resolvent ((D.smoothing t) f) = (D.smoothing t) (D.resolvent f) := by
  rw [D.resolvent_smoothing ht, D.smoothing_resolvent ht]

/-- `A_t := (I+sH)^{2N} e^{-tH}`, the square of the smoothing operator. -/
def sq (t : ℝ) : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu := (D.smoothing t).comp (D.smoothing t)

theorem sq_apply (t : ℝ) (f : Lp ℝ 2 mu) :
    D.sq t f = (D.smoothing t) ((D.smoothing t) f) := rfl

theorem isSymmetricOp_sq {t : ℝ} (ht : 0 < t) : IsSymmetricOp (D.sq t) :=
  (D.isSymmetricOp_smoothing t ht).comp (D.isSymmetricOp_smoothing t ht) fun _ => rfl

theorem semigroup_semigroup {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (f : Lp ℝ 2 mu) :
    D.semigroup t (D.semigroup u f) = D.semigroup (t + u) f := by
  have h := D.semigroup_comp t u ht hu
  calc D.semigroup t (D.semigroup u f)
      = ((D.semigroup t).comp (D.semigroup u)) f := rfl
    _ = D.semigroup (t + u) f := by rw [h]

/-- `(I+sH)^{-2N} A_t = e^{-tH}`: the resolvent powers cancel the smoothing
squared, leaving the semigroup. -/
theorem resolvent_resolvent_sq {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 mu) :
    D.resolvent (D.resolvent (D.sq t f)) = D.semigroup t f := by
  have h1 : D.resolvent (D.sq t f) = (D.smoothing t) (D.semigroup (t / 2) f) := by
    rw [sq_apply, D.resolvent_smoothing_comm ht ((D.smoothing t) f), D.resolvent_smoothing ht f]
  rw [h1, D.resolvent_smoothing ht (D.semigroup (t / 2) f),
    D.semigroup_semigroup (half_pos ht) (half_pos ht), add_halves]

/-- `(I+sH)^{-N} A_t (I+sH)^{-N} = e^{-tH}`. -/
theorem resolvent_sq_resolvent {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 mu) :
    D.resolvent (D.sq t (D.resolvent f)) = D.semigroup t f := by
  have h : D.sq t (D.resolvent f) = D.resolvent (D.sq t f) := by
    rw [sq_apply, sq_apply, ← D.resolvent_smoothing_comm ht f,
      ← D.resolvent_smoothing_comm ht ((D.smoothing t) f)]
  rw [h, D.resolvent_resolvent_sq ht]

/-- `A_t e^{-uH} = A_{t+u}`, from injectivity of the resolvent. -/
theorem sq_semigroup {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (f : Lp ℝ 2 mu) :
    D.sq t (D.semigroup u f) = D.sq (t + u) f := by
  refine D.injective_resolvent (D.injective_resolvent ?_)
  rw [D.resolvent_resolvent_sq ht, D.resolvent_resolvent_sq (by positivity),
    D.semigroup_semigroup ht hu]

/-- `e^{-uH} A_t = A_{t+u}`, the adjoint form of `sq_semigroup`. -/
theorem semigroup_sq {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (f : Lp ℝ 2 mu) :
    D.semigroup u (D.sq t f) = D.sq (t + u) f := by
  refine ext_inner_left ℝ fun v => ?_
  rw [← D.isSymmetricOp_semigroup u hu, ← D.isSymmetricOp_sq ht, D.sq_semigroup ht hu v]
  exact D.isSymmetricOp_sq (by positivity : (0:ℝ) < t + u) v f

/-! ### Step 1: the Riesz representatives are locally Hölder, hence continuous -/

theorem continuousAt_repr [LocallyCompactSpace X] {x : X} (hx : x ∈ Om) :
    ContinuousAt D.repr x := by
  obtain ⟨K, hKnhds, hKsub, hKcpt⟩ := local_compact_nhds (D.isOpen_carrier.mem_nhds hx)
  obtain ⟨C, a, ha, hbd⟩ := D.holder_repr K hKsub hKcpt
  have hxK : x ∈ K := mem_of_mem_nhds hKnhds
  have hsq : Tendsto (fun y : X => C * dist y x ^ a) (nhds x) (nhds 0) := by
    have hd : Tendsto (fun y : X => dist y x) (nhds x) (nhds 0) :=
      tendsto_iff_dist_tendsto_zero.mp tendsto_id
    have hr : Tendsto (fun r : ℝ => r ^ a) (nhds 0) (nhds 0) := by
      have hc := Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
      rwa [ContinuousAt, Real.zero_rpow ha.ne'] at hc
    have := (hr.comp hd).const_mul C
    rwa [mul_zero] at this
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hsq
  filter_upwards [hKnhds] with y hy
  simpa [dist_eq_norm] using hbd y hy x hxK

theorem continuousOn_repr [LocallyCompactSpace X] : ContinuousOn D.repr Om :=
  fun _ hx => (D.continuousAt_repr hx).continuousWithinAt

/-! ### The kernel -/

/-- **The heat kernel**, `p_t(x,y) = ⟪B_t g_x, B_t g_y⟫_{L²(μ)}`,
`s.fixed.coefficient` and `mfd:sec-speed`. -/
def kernel (t : ℝ) (x y : X) : ℝ := ⟪(D.smoothing t) (D.repr x), (D.smoothing t) (D.repr y)⟫

/-- **The kernel is symmetric.** -/
theorem kernel_symm (t : ℝ) (x y : X) : D.kernel t x y = D.kernel t y x :=
  real_inner_comm _ _

theorem kernel_eq_inner_sq {t : ℝ} (ht : 0 < t) (x y : X) :
    D.kernel t x y = ⟪D.repr x, D.sq t (D.repr y)⟫ :=
  D.isSymmetricOp_smoothing t ht (D.repr x) ((D.smoothing t) (D.repr y))

/-- **Joint continuity**, `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem continuousOn_kernel [LocallyCompactSpace X] :
    ContinuousOn (fun z : ℝ × X × X => D.kernel z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ Om ×ˢ Om) := by
  have hB : ContinuousOn (fun z : ℝ × X × X => D.smoothing z.1) (Ioi 0 ×ˢ Om ×ˢ Om) :=
    D.continuousOn_smoothing.comp continuousOn_fst fun z hz => hz.1
  have hg1 : ContinuousOn (fun z : ℝ × X × X => D.repr z.2.1) (Ioi 0 ×ˢ Om ×ˢ Om) :=
    D.continuousOn_repr.comp (continuousOn_fst.comp continuousOn_snd fun _ hz => hz.2)
      fun z hz => hz.2.1
  have hg2 : ContinuousOn (fun z : ℝ × X × X => D.repr z.2.2) (Ioi 0 ×ˢ Om ×ˢ Om) :=
    D.continuousOn_repr.comp (continuousOn_snd.comp continuousOn_snd fun _ hz => hz.2)
      fun z hz => hz.2.2
  have happ : ∀ h : ℝ × X × X → Lp ℝ 2 mu, ContinuousOn h (Ioi 0 ×ˢ Om ×ˢ Om) →
      ContinuousOn (fun z : ℝ × X × X => D.smoothing z.1 (h z)) (Ioi 0 ×ˢ Om ×ˢ Om) :=
    fun _ hh => isBoundedBilinearMap_apply.continuous.comp_continuousOn (hB.prodMk hh)
  exact continuous_inner.comp_continuousOn ((happ _ hg1).prodMk (happ _ hg2))

/-- Joint continuity in the space variables, at a fixed time. -/
theorem continuousOn_kernel_pair [LocallyCompactSpace X] (t : ℝ) :
    ContinuousOn (fun z : X × X => D.kernel t z.1 z.2) (Om ×ˢ Om) := by
  have h1 : ContinuousOn (fun z : X × X => (D.smoothing t) (D.repr z.1)) (Om ×ˢ Om) :=
    ((D.smoothing t).continuous.comp_continuousOn D.continuousOn_repr).comp
      continuousOn_fst fun z hz => hz.1
  have h2 : ContinuousOn (fun z : X × X => (D.smoothing t) (D.repr z.2)) (Om ×ˢ Om) :=
    ((D.smoothing t).continuous.comp_continuousOn D.continuousOn_repr).comp
      continuousOn_snd fun z hz => hz.2
  exact continuous_inner.comp_continuousOn (h1.prodMk h2)

/-- Separate continuity of `y ↦ p_t(x,y)`. -/
theorem continuousOn_kernel_right [LocallyCompactSpace X] (t : ℝ) (x : X) :
    ContinuousOn (fun z : X => D.kernel t x z) Om := by
  have h : ContinuousOn (fun z : X => (D.smoothing t) (D.repr z)) Om :=
    (D.smoothing t).continuous.comp_continuousOn D.continuousOn_repr
  exact continuous_inner.comp_continuousOn (continuousOn_const.prodMk h)

/-! ### The kernel represents the semigroup -/

/-- `z ↦ p_t(x,z)` is, almost everywhere, the `L²` function `(I+sH)^{-N}A_t g_x`. -/
theorem kernel_ae_eq {t : ℝ} (ht : 0 < t) (x : X) :
    (fun z => (D.resolvent (D.sq t (D.repr x))) z) =ᵐ[mu] fun z => D.kernel t x z := by
  filter_upwards [D.resolvent_apply_ae (D.sq t (D.repr x))] with z hz
  rw [hz, D.kernel_symm t x z, D.kernel_eq_inner_sq ht z x]

/-- The pairing of `z ↦ p_t(x,z)` with `f`, as a function of `x`. -/
def pairing (t : ℝ) (f : Lp ℝ 2 mu) (x : X) : ℝ := ⟪D.resolvent (D.sq t (D.repr x)), f⟫

theorem continuousOn_pairing [LocallyCompactSpace X] (t : ℝ) (f : Lp ℝ 2 mu) :
    ContinuousOn (D.pairing t f) Om := by
  have h : ContinuousOn (fun x => D.resolvent (D.sq t (D.repr x))) Om :=
    (D.resolvent.comp (D.sq t)).continuous.comp_continuousOn D.continuousOn_repr
  exact continuous_inner.comp_continuousOn (h.prodMk continuousOn_const)

/-- **The semigroup is represented by the pairing**, almost everywhere. -/
theorem pairing_ae_eq {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 mu) :
    (fun x => (D.semigroup t f) x) =ᵐ[mu] D.pairing t f := by
  have hkey : ∀ x : X, D.pairing t f x = ⟪D.repr x, D.sq t (D.resolvent f)⟫ := by
    intro x
    rw [pairing, D.isSymmetricOp_resolvent, D.isSymmetricOp_sq ht]
  filter_upwards [D.resolvent_apply_ae (D.sq t (D.resolvent f))] with x hx
  rw [hkey x, ← hx, D.resolvent_sq_resolvent ht f]

theorem pairing_eq_integral {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 mu) (x : X) :
    D.pairing t f x = ∫ z, D.kernel t x z * f z ∂mu := by
  rw [pairing, inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [D.kernel_ae_eq ht x] with z hz
  rw [hz]

/-- **The kernel represents the semigroup**, `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem semigroup_ae_eq_integral {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 mu) :
    (fun x => (D.semigroup t f) x) =ᵐ[mu] fun x => ∫ z, D.kernel t x z * f z ∂mu := by
  filter_upwards [D.pairing_ae_eq ht f] with x hx
  rw [hx, D.pairing_eq_integral ht f x]

/-! ### Indicator pairings -/

theorem pairing_indicator {t : ℝ} (ht : 0 < t) (x : X) {s : Set X} (hs : MeasurableSet s)
    (hstop : mu s ≠ ∞) :
    D.pairing t (indicatorConstLp 2 hs hstop (1 : ℝ)) x = ∫ z in s, D.kernel t x z ∂mu := by
  rw [pairing, inner_indicatorConstLp_one _ hs hstop]
  refine setIntegral_congr_ae hs ?_
  filter_upwards [D.kernel_ae_eq ht x] with z hz _
  exact hz

/-! ### Positivity -/

theorem integrableOn_resolvent_sq {t : ℝ} (x : X) {s : Set X} (hstop : mu s ≠ ∞) :
    IntegrableOn (fun z => (D.resolvent (D.sq t (D.repr x))) z) s mu := by
  have : IsFiniteMeasure (mu.restrict s) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  exact memLp_one_iff_integrable.mp
    (((Lp.memLp (D.resolvent (D.sq t (D.repr x)))).restrict s).mono_exponent one_le_two)

/-- **The kernel is nonnegative at every point of the carrier**: the positivity of
the semigroup gives it almost everywhere, and continuity plus full support give
it everywhere.  `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem kernel_nonneg [LocallyCompactSpace X] [SigmaFinite mu] {t : ℝ} (ht : 0 < t)
    {x : X} (hx : x ∈ Om) {y : X} (hy : y ∈ Om) : 0 ≤ D.kernel t x y := by
  -- Step 1: pairing against a nonnegative `f` is nonnegative at *every* point of `Om`.
  have hpair : ∀ f : Lp ℝ 2 mu, (0 ≤ᵐ[mu] fun z => f z) → ∀ z ∈ Om, 0 ≤ D.pairing t f z := by
    intro f hf
    refine le_of_ae_ge D.isOpen_carrier D.fullSupport (D.continuousOn_pairing t f) ?_
    filter_upwards [D.pairing_ae_eq ht f, D.semigroup_nonneg t ht f hf] with z hz hz'
    exact fun _ => hz ▸ hz'
  -- Step 2: hence `(I+sH)^{-N}A_t g_x ≥ 0` almost everywhere.
  have hae : 0 ≤ᵐ[mu] fun z => (D.resolvent (D.sq t (D.repr x))) z := by
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun s _ hs => D.integrableOn_resolvent_sq x hs.ne) (fun s hs hstop => ?_)
    have hval := hpair (indicatorConstLp 2 hs hstop.ne (1 : ℝ))
      (indicatorConstLp_nonneg hs hstop.ne) x hx
    rwa [pairing, inner_indicatorConstLp_one _ hs hstop.ne] at hval
  -- Step 3: transfer to `p_t(x,·)` and upgrade by continuity.
  refine le_of_ae_ge D.isOpen_carrier D.fullSupport (D.continuousOn_kernel_right t x) ?_ y hy
  filter_upwards [hae, D.kernel_ae_eq ht x] with z hz hz'
  exact fun _ => hz' ▸ hz

/-! ### The sub-Markov mass bound -/

/-- The kernel mass of any finite-measure set is at most one, at **every** point of
the carrier. -/
theorem setIntegral_kernel_le_one [LocallyCompactSpace X] {t : ℝ} (ht : 0 < t)
    {x : X} (hx : x ∈ Om) {s : Set X} (hs : MeasurableSet s) (hstop : mu s ≠ ∞) :
    (∫ z in s, D.kernel t x z ∂mu) ≤ 1 := by
  rw [← D.pairing_indicator ht x hs hstop]
  refine le_of_ae_le D.isOpen_carrier D.fullSupport
    (D.continuousOn_pairing t (indicatorConstLp 2 hs hstop (1 : ℝ))) ?_ x hx
  filter_upwards [D.pairing_ae_eq ht (indicatorConstLp 2 hs hstop (1 : ℝ)),
    D.semigroup_le_one t ht (indicatorConstLp 2 hs hstop (1 : ℝ))
      (indicatorConstLp_nonneg hs hstop) (indicatorConstLp_le_one hs hstop)] with z hz hz'
  exact fun _ => hz ▸ hz'

/-- **`∫ p_t(x,z) dμ(z) ≤ 1` at every point of the carrier**,
`s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem lintegral_kernel_le_one [LocallyCompactSpace X] [SigmaFinite mu] {t : ℝ} (ht : 0 < t)
    {x : X} (hx : x ∈ Om) : (∫⁻ z, ENNReal.ofReal (D.kernel t x z) ∂mu) ≤ 1 := by
  have hOm : ∀ᵐ z ∂mu, z ∈ Om := by
    rw [ae_iff]
    simpa only [Set.compl_def] using D.measure_compl
  have hcongr : (∫⁻ z, ENNReal.ofReal (D.kernel t x z) ∂mu)
      = ∫⁻ z, ENNReal.ofReal ((D.resolvent (D.sq t (D.repr x))) z) ∂mu :=
    (lintegral_congr_ae (by
      filter_upwards [D.kernel_ae_eq ht x] with z hz
      rw [hz])).symm
  rw [hcongr]
  refine lintegral_le_one_of_setIntegral_le_one
    (Lp.aestronglyMeasurable _).aemeasurable ?_
    (fun s _ hs => D.integrableOn_resolvent_sq x hs) (fun s hs hstop => ?_)
  · filter_upwards [D.kernel_ae_eq ht x, hOm] with z hz hzOm
    exact hz ▸ D.kernel_nonneg ht hx hzOm
  · rw [setIntegral_congr_ae hs (by
      filter_upwards [D.kernel_ae_eq ht x] with z hz _
      exact hz)]
    exact D.setIntegral_kernel_le_one ht hx hs hstop

/-! ### Chapman–Kolmogorov -/

/-- **Pointwise Chapman–Kolmogorov**, `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem chapmanKolmogorov {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (x y : X) :
    (∫ z, D.kernel t x z * D.kernel u z y ∂mu) = D.kernel (t + u) x y := by
  have h1 : (fun z => D.kernel t x z * D.kernel u z y)
      =ᵐ[mu] fun z => (D.resolvent (D.sq t (D.repr x))) z
        * (D.resolvent (D.sq u (D.repr y))) z := by
    filter_upwards [D.kernel_ae_eq ht x, D.kernel_ae_eq hu y] with z hz hz'
    rw [hz, hz', D.kernel_symm u z y]
  rw [integral_congr_ae h1, ← inner_eq_integral, D.isSymmetricOp_resolvent,
    D.resolvent_resolvent_sq hu, ← D.isSymmetricOp_semigroup u hu, D.semigroup_sq ht hu,
    D.isSymmetricOp_sq (by positivity : (0:ℝ) < t + u), ← D.kernel_eq_inner_sq
      (by positivity : (0:ℝ) < t + u)]

/-! ### Uniqueness -/

/-- **Uniqueness of the continuous kernel**: any function continuous on the
carrier that agrees almost everywhere with `p_t(x,·)` agrees with it at every
point.  `s.fixed.coefficient` and `mfd:sec-speed`. -/
theorem kernel_unique [LocallyCompactSpace X] (t : ℝ) (x : X) {q : X → ℝ}
    (hq : ContinuousOn q Om) (hqae : ∀ᵐ z ∂mu, z ∈ Om → q z = D.kernel t x z) :
    EqOn q (fun z => D.kernel t x z) Om :=
  eqOn_of_ae_eq_of_fullSupport D.isOpen_carrier D.fullSupport hq
    (D.continuousOn_kernel_right t x) hqae

end ResolventRegularityDatum

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
