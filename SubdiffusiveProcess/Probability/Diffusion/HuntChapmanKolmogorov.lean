module

public import SubdiffusiveProcess.Probability.Diffusion.HuntContinuityRoute
public import SubdiffusiveProcess.Probability.Diffusion.Packet445Checks

@[expose] public section

/-!
# B1 of the continuity route: killed Chapman-Kolmogorov in density form

The
`Packet445Checks.killedKernel_laplacianLaw_add` is an identity of **kernels**; what the smoothing
step B4-B5 consumes is the corresponding identity of **densities**, pointwise on the interior:

```text
huntDensity U (s+t) x y = ∫ z in U, huntDensity U s x z * huntDensity U t z y   (x, y ∈ U)
```

together with the integrability that makes the right-hand side a Bochner integral.

The argument uses the following steps:

* `killedKernel_eq_withDensity` — at a positive time and an interior start the killed kernel *is*
  the restricted Lebesgue measure weighted by the Hunt density.  This is
  `lintegral_huntDensity_eq_killed` (already proved from the Hunt identity) read as a `Measure.ext`
  rather than as a family of set integrals, and it is what lets the kernel composition be unfolded
  by `lintegral_withDensity_eq_lintegral_mul`.
* `huntDensity_chapmanKolmogorov_ae` — the identity in `ℝ≥0∞`, almost everywhere in the terminal
  point: kernel composition, then Tonelli (`lintegral_lintegral_swap`), then
  `withDensity_eq_iff_of_sigmaFinite` to strip the density off both sides.  `Real.toNNReal` is
  additive on nonnegatives, which is where `0 < s` and `0 < t` first enter.
* `gaussianPDFReal_le_sup`, `laplacianDensity_le_const` — the uniform Gaussian bound
  `laplacianDensity t x y ≤ (√(4πt))⁻¹ ^ d`.  It follows
  from the one-dimensional bound `exp(-·) ≤ 1` and the product formula.
* `integrableOn_huntDensity_row`, `integrableOn_huntDensity_mul` — integrability.  On a **bounded**
  domain the restricted measure is finite, so Gaussian domination against a *constant* suffices and
  no killed-mass argument is needed.
* `continuousAt_huntDensity_end`, `continuousOn_huntDensity_end`,
  `continuousOn_huntDensity_convolution` — continuity in the terminal point of both sides, the
  second by fixed-measure dominated convergence with the constant bound above.
* `huntDensity_chapmanKolmogorov_ae_real`, then **`huntDensity_chapmanKolmogorov`** — the a.e.
  identity transported to `ℝ` through `ofReal_integral_eq_lintegral_ofReal`, then promoted to every
  interior point by `Measure.eqOn_open_of_ae_eq`, exactly as in B0.

Nothing here uses continuity in the **starting** point; that remains the target of B4-B7.

One Lean note worth recording, because it cost two rounds: `(measurable_uncurry_huntDensity …).comp
measurable_prodMk_left` makes the unifier prove `(fun z => f x z) = uncurry f ∘ Prod.mk x` against a
fully determined expected type, and that runs past `maxHeartbeats` on this carrier.
`Measurable.of_uncurry_left` / `Measurable.of_uncurry_right` state the same fact with nothing left
to unify and elaborate instantly.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- The one-dimensional Gaussian density is bounded by its value at the mean. -/
theorem gaussianPDFReal_le_sup (m : ℝ) (v : NNReal) (u : ℝ) :
    gaussianPDFReal m v u ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  unfold gaussianPDFReal
  have hexp : Real.exp (-(u - m) ^ 2 / (2 * v)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    rcases eq_or_lt_of_le (v.coe_nonneg) with hv | hv
    · rw [← hv]; norm_num
    · exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (u - m)]) (by linarith)
  have hpos : (0:ℝ) ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  nlinarith [Real.exp_pos (-(u - m) ^ 2 / (2 * v))]

/-- **The uniform Gaussian bound.**  At a positive time the free density is bounded by a
constant depending only on the time and the dimension. -/
theorem laplacianDensity_le_const {t : ℝ} (ht : 0 < t) (x y : Vec d) :
    laplacianDensity t x y ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ ^ d := by
  have hval : (Real.sqrt (2 * Real.pi * (2 * Real.toNNReal t : NNReal)))⁻¹
      = (Real.sqrt (4 * Real.pi * t))⁻¹ := by
    congr 2
    push_cast [Real.coe_toNNReal t ht.le]
    ring
  have hle : ∀ i : Fin d, gaussianPDFReal (x i) (2 * Real.toNNReal t) (y i)
      ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ := fun i => hval ▸ gaussianPDFReal_le_sup _ _ _
  have hnn : ∀ i : Fin d, (0:ℝ) ≤ gaussianPDFReal (x i) (2 * Real.toNNReal t) (y i) :=
    fun i => gaussianPDFReal_nonneg _ _ _
  calc laplacianDensity t x y = ∏ _i : Fin d, gaussianPDFReal (x _i) (2 * Real.toNNReal t) (y _i) :=
        rfl
    _ ≤ ∏ _i : Fin d, (Real.sqrt (4 * Real.pi * t))⁻¹ :=
        Finset.prod_le_prod₀ (fun i _ => hnn i) (fun i _ => hle i)
    _ = (Real.sqrt (4 * Real.pi * t))⁻¹ ^ d := by simp

/-- The killed kernel, at a positive time and an interior start, is the restricted Lebesgue
measure weighted by the Hunt density. -/
theorem killedKernel_eq_withDensity {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    killedKernel (laplacianLaw d) U hU (Real.toNNReal t) x
      = (volume.restrict U).withDensity (fun y => ENNReal.ofReal (huntDensity U t x y)) := by
  refine Measure.ext fun B hB => ?_
  rw [withDensity_apply _ hB, Measure.restrict_restrict hB,
    ← lintegral_huntDensity_eq_killed (brownian_hunt_identity d) hU hUb ht hx B hB]

/-- The two-variable Hunt density kernel is jointly measurable. -/
theorem measurable_huntDensity_prod {U : Set (Vec d)} (hU : IsOpen U) {s t : ℝ} (x : Vec d) :
    Measurable (fun p : Vec d × Vec d =>
      ENNReal.ofReal (huntDensity U s x p.1) * ENNReal.ofReal (huntDensity U t p.1 p.2)) := by
  have h1 : Measurable (fun p : Vec d × Vec d => ENNReal.ofReal (huntDensity U s x p.1)) :=
    ((((measurable_uncurry_huntDensity U hU s).comp measurable_prodMk_left).ennreal_ofReal).comp
      measurable_fst)
  have h2 : Measurable (fun p : Vec d × Vec d => ENNReal.ofReal (huntDensity U t p.1 p.2)) :=
    (measurable_uncurry_huntDensity U hU t).ennreal_ofReal
  exact h1.mul h2

/-- **B1 in `ℝ≥0∞`, almost everywhere.**  The killed Chapman-Kolmogorov identity, read on the
densities. -/
theorem huntDensity_chapmanKolmogorov_ae {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {x : Vec d} (hx : x ∈ U) :
    (fun y => ENNReal.ofReal (huntDensity U (s + t) x y))
      =ᵐ[volume.restrict U]
      fun y => ∫⁻ z in U, ENNReal.ofReal (huntDensity U s x z) *
        ENNReal.ofReal (huntDensity U t z y) := by
  classical
  have hst : 0 < s + t := by linarith
  set F : Vec d → ℝ≥0∞ := fun y => ∫⁻ z in U, ENNReal.ofReal (huntDensity U s x z) *
    ENNReal.ofReal (huntDensity U t z y) with hF
  have hFmeas : Measurable F := by
    have := (measurable_huntDensity_prod (U := U) hU (s := s) (t := t) x).lintegral_prod_left'
      (μ := volume.restrict U)
    exact this
  have hLmeas : Measurable (fun y => ENNReal.ofReal (huntDensity U (s + t) x y)) :=
    (((measurable_uncurry_huntDensity U hU (s + t)).comp measurable_prodMk_left)).ennreal_ofReal
  have hmeas_s : Measurable (fun y : Vec d => ENNReal.ofReal (huntDensity U s x y)) :=
    (((measurable_uncurry_huntDensity U hU s).comp measurable_prodMk_left)).ennreal_ofReal
  have hmeas_t : ∀ z : Vec d, Measurable (fun y : Vec d => ENNReal.ofReal (huntDensity U t z y)) :=
    fun z => (((measurable_uncurry_huntDensity U hU t).comp measurable_prodMk_left)).ennreal_ofReal
  have hmeasure : killedKernel (laplacianLaw d) U hU (Real.toNNReal (s + t)) x
      = (volume.restrict U).withDensity F := by
    refine Measure.ext fun B hB => ?_
    rw [withDensity_apply _ hB, Measure.restrict_restrict hB]
    have hadd : Real.toNNReal (s + t) = Real.toNNReal s + Real.toNNReal t :=
      Real.toNNReal_add hs.le ht.le
    rw [hadd, Packet445Checks.killedKernel_laplacianLaw_add U hU (Real.toNNReal s)
      (Real.toNNReal t), Kernel.comp_apply' _ _ _ hB,
      killedKernel_eq_withDensity hU hUb hs hx]
    rw [lintegral_withDensity_eq_lintegral_mul _ hmeas_s
      ((killedKernel (laplacianLaw d) U hU (Real.toNNReal t)).measurable_coe hB)]
    simp only [Pi.mul_apply]
    have hcongr : ∫⁻ z in U, ENNReal.ofReal (huntDensity U s x z) *
          killedKernel (laplacianLaw d) U hU (Real.toNNReal t) z B
        = ∫⁻ z in U, ∫⁻ y in B ∩ U, ENNReal.ofReal (huntDensity U s x z) *
            ENNReal.ofReal (huntDensity U t z y) := by
      refine setLIntegral_congr_fun hU.measurableSet (fun z hz => ?_)
      rw [← lintegral_huntDensity_eq_killed (brownian_hunt_identity d) hU hUb ht hz B hB]
      exact (lintegral_const_mul _ (hmeas_t z)).symm
    rw [hcongr]
    refine lintegral_lintegral_swap ?_
    exact (measurable_huntDensity_prod (U := U) hU (s := s) (t := t) x).aemeasurable
  have hL := killedKernel_eq_withDensity hU hUb hst hx
  rw [hL] at hmeasure
  exact (withDensity_eq_iff_of_sigmaFinite hLmeas.aemeasurable hFmeas.aemeasurable).mp hmeasure

/-- On a bounded domain the restricted Lebesgue measure is finite. -/
theorem isFiniteMeasure_restrict_of_isBounded {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) : IsFiniteMeasure (volume.restrict U) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact hUb.measure_lt_top

/-- The Hunt density row at a positive time is integrable on a bounded domain: Gaussian
domination bounds it by a constant, and the measure is finite. -/
theorem integrableOn_huntDensity_row {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {t : ℝ} (ht : 0 < t) (x : Vec d) :
    IntegrableOn (fun z => huntDensity U t x z) U := by
  have := isFiniteMeasure_restrict_of_isBounded hUb
  have hmeas : Measurable (fun z : Vec d => huntDensity U t x z) :=
    (measurable_uncurry_huntDensity U hU t).of_uncurry_left (x := x)
  refine Integrable.mono' (μ := volume.restrict U)
    (g := fun _ : Vec d => (Real.sqrt (4 * Real.pi * t))⁻¹ ^ d)
    (integrable_const _) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (huntDensity_nonneg U t x z)]
  exact le_trans (Packet445Checks.huntDensity_le_laplacianDensity U t x z)
    (laplacianDensity_le_const ht x z)

/-- The product of two Hunt density rows is integrable on a bounded domain. -/
theorem integrableOn_huntDensity_mul {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : Vec d) :
    IntegrableOn (fun z => huntDensity U s x z * huntDensity U t z y) U := by
  have := isFiniteMeasure_restrict_of_isBounded hUb
  have hmeas : Measurable (fun z : Vec d => huntDensity U s x z * huntDensity U t z y) :=
    Measurable.mul ((measurable_uncurry_huntDensity U hU s).of_uncurry_left (x := x))
      ((measurable_uncurry_huntDensity U hU t).of_uncurry_right (y := y))
  refine Integrable.mono' (μ := volume.restrict U)
    (g := fun _ : Vec d =>
      (Real.sqrt (4 * Real.pi * s))⁻¹ ^ d * (Real.sqrt (4 * Real.pi * t))⁻¹ ^ d)
    (integrable_const _) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (huntDensity_nonneg U s x z)
    (huntDensity_nonneg U t z y))]
  refine mul_le_mul ?_ ?_ (huntDensity_nonneg U t z y) (by positivity)
  · exact le_trans (Packet445Checks.huntDensity_le_laplacianDensity U s x z)
      (laplacianDensity_le_const hs x z)
  · exact le_trans (Packet445Checks.huntDensity_le_laplacianDensity U t z y)
      (laplacianDensity_le_const ht z y)

/-- The Hunt density is continuous at an interior terminal point. -/
theorem continuousAt_huntDensity_end {U : Set (Vec d)} (hU : IsOpen U)
    {x : Vec d} (hx : x ∈ U) {t : ℝ} (ht : 0 < t) {y : Vec d} (hy : y ∈ U) :
    ContinuousAt (fun w : Vec d => huntDensity U t x w) y := by
  have hopen : IsOpen (Ioi (0:ℝ) ×ˢ U) := isOpen_Ioi.prod hU
  have hAt : ContinuousAt (fun v : ℝ × Vec d => huntDensity U v.1 x v.2) (t, y) :=
    (Packet445Checks.continuousOn_huntDensity_time_end hU hx).continuousAt
      (hopen.mem_nhds ⟨ht, hy⟩)
  have hpair : ContinuousAt (fun w : Vec d => ((t, w) : ℝ × Vec d)) y := by fun_prop
  simpa [Function.comp_def] using hAt.comp hpair

/-- The Hunt density is continuous in the terminal point at a fixed positive time and interior
start. -/
theorem continuousOn_huntDensity_end {U : Set (Vec d)} (hU : IsOpen U)
    {x : Vec d} (hx : x ∈ U) {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun y : Vec d => huntDensity U t x y) U :=
  fun _y hy => (continuousAt_huntDensity_end hU hx ht hy).continuousWithinAt

/-- **B1, real-valued, almost everywhere.** -/
theorem huntDensity_chapmanKolmogorov_ae_real {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {x : Vec d} (hx : x ∈ U) :
    (fun y => huntDensity U (s + t) x y) =ᵐ[volume.restrict U]
      fun y => ∫ z in U, huntDensity U s x z * huntDensity U t z y := by
  filter_upwards [huntDensity_chapmanKolmogorov_ae hU hUb hs ht hx] with y hy
  have hprod : ∀ z : Vec d, ENNReal.ofReal (huntDensity U s x z) *
      ENNReal.ofReal (huntDensity U t z y)
      = ENNReal.ofReal (huntDensity U s x z * huntDensity U t z y) :=
    fun z => (ENNReal.ofReal_mul (huntDensity_nonneg U s x z)).symm
  simp only [hprod] at hy
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_huntDensity_mul hU hUb hs ht x y)
    (Filter.Eventually.of_forall fun z =>
      mul_nonneg (huntDensity_nonneg U s x z) (huntDensity_nonneg U t z y))] at hy
  exact (ENNReal.ofReal_eq_ofReal_iff (huntDensity_nonneg U (s + t) x y)
    (integral_nonneg fun z => mul_nonneg (huntDensity_nonneg U s x z)
      (huntDensity_nonneg U t z y))).mp hy

/-- The Chapman-Kolmogorov integral is continuous in the terminal point. -/
theorem continuousOn_huntDensity_convolution {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Vec d) :
    ContinuousOn (fun y : Vec d => ∫ z in U, huntDensity U s x z * huntDensity U t z y) U := by
  have := isFiniteMeasure_restrict_of_isBounded hUb
  intro y₀ hy₀
  refine ContinuousAt.continuousWithinAt ?_
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun _ : Vec d =>
      (Real.sqrt (4 * Real.pi * s))⁻¹ ^ d * (Real.sqrt (4 * Real.pi * t))⁻¹ ^ d)
    (Filter.Eventually.of_forall fun y => ?_) (Filter.Eventually.of_forall fun y => ?_)
    (integrable_const _) ?_
  · exact (Measurable.mul ((measurable_uncurry_huntDensity U hU s).of_uncurry_left (x := x))
      ((measurable_uncurry_huntDensity U hU t).of_uncurry_right (y := y))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (huntDensity_nonneg U s x z)
      (huntDensity_nonneg U t z y))]
    refine mul_le_mul ?_ ?_ (huntDensity_nonneg U t z y) (by positivity)
    · exact le_trans (Packet445Checks.huntDensity_le_laplacianDensity U s x z)
        (laplacianDensity_le_const hs x z)
    · exact le_trans (Packet445Checks.huntDensity_le_laplacianDensity U t z y)
        (laplacianDensity_le_const ht z y)
  · filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact (continuousAt_huntDensity_end hU hz ht hy₀).const_mul _

/-- **B1 of the continuity route.**  The killed Chapman-Kolmogorov identity in pointwise
density form, on the interior. -/
theorem huntDensity_chapmanKolmogorov {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {x : Vec d} (hx : x ∈ U) {y : Vec d} (hy : y ∈ U) :
    IntegrableOn (fun z => huntDensity U s x z * huntDensity U t z y) U ∧
      huntDensity U (s + t) x y = ∫ z in U, huntDensity U s x z * huntDensity U t z y := by
  refine ⟨integrableOn_huntDensity_mul hU hUb hs ht x y, ?_⟩
  refine Measure.eqOn_open_of_ae_eq
    (huntDensity_chapmanKolmogorov_ae_real hU hUb hs ht hx) hU
    (continuousOn_huntDensity_end hU hx (by linarith))
    (continuousOn_huntDensity_convolution hU hUb hs ht x) hy

end SubdiffusiveProcess.Probability.Diffusion
