module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

/-!
# `C¹` compactly supported functions lie in `H¹₀`

`H10Function U` demands a sequence of **smooth** compactly supported approximants, and
all three constructors in the dependency (`ofContDiff` and its two face-zero variants)
require `ContDiff ℝ ⊤` of the function itself. That leaves no way to admit a merely `C¹`
test function.

This is exactly what blocks the reduction of `l.weighted.local.harmonic` v4 to a Poisson
equation: `WeakHarmonic a` tests against `H10Function`, and the natural test function
`φ / a` is only `C¹`, because the coefficient is `C^{1,1}` and no better.

`ConvexApproxSmoothing` does not help — its operator dilates toward an interior point
before mollifying, which is the construction for density in `W^{1,p}(U)` by functions
*defined on* `U`. It produces no compactly supported approximants.

Here the dilation is unnecessary: the function already has compact support strictly
inside `U`, so plain mollification below the margin keeps the support inside. The file
builds that: the mollifier, its convolution's smoothness and support, the identity
`∇(ρ ⋆ u) = ρ ⋆ ∇u`, uniform convergence from uniform continuity, and the `L²`
consequence.

Main result: `memH10_of_contDiffOne`.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Set Filter
open scoped Convolution Pointwise ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Density

variable {d : ℕ}

/-- The standard bump of outer radius `ε`. -/
def bump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : Vec d) :=
  { rIn := ε / 2, rOut := ε, rIn_pos := by linarith, rIn_lt_rOut := by linarith }

/-- The normalized mollifier at scale `ε`. -/
def moll (ε : ℝ) (hε : 0 < ε) : Vec d → ℝ := (bump (d := d) ε hε).normed volume

theorem moll_smooth (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (moll (d := d) ε hε) :=
  (bump (d := d) ε hε).contDiff_normed

theorem moll_tsupport (ε : ℝ) (hε : 0 < ε) :
    tsupport (moll (d := d) ε hε) = Metric.closedBall (0 : Vec d) ε := by
  simpa [moll, bump] using! (bump (d := d) ε hε).tsupport_normed_eq (μ := volume)

theorem moll_integral (ε : ℝ) (hε : 0 < ε) :
    ∫ x, moll (d := d) ε hε x = 1 :=
  (bump (d := d) ε hε).integral_normed (μ := volume)

theorem moll_nonneg (ε : ℝ) (hε : 0 < ε) (x : Vec d) : 0 ≤ moll (d := d) ε hε x :=
  (bump (d := d) ε hε).nonneg_normed x

theorem moll_compactSupport (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (moll (d := d) ε hε) :=
  (bump (d := d) ε hε).hasCompactSupport_normed

/-- Mollification of `u` at scale `ε`. -/
def mollify (ε : ℝ) (hε : 0 < ε) (u : Vec d → ℝ) : Vec d → ℝ :=
  (moll (d := d) ε hε) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u

theorem mollify_smooth {u : Vec d → ℝ} (hu : Continuous u) (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (mollify (d := d) ε hε u) :=
  (moll_compactSupport (d := d) ε hε).contDiff_convolution_left _
    (moll_smooth (d := d) ε hε) hu.locallyIntegrable

theorem mollify_compactSupport {u : Vec d → ℝ} (hu : HasCompactSupport u)
    (ε : ℝ) (hε : 0 < ε) : HasCompactSupport (mollify (d := d) ε hε u) :=
  (moll_compactSupport (d := d) ε hε).convolution _ hu

theorem mollify_tsupport_subset {u : Vec d → ℝ} (ε : ℝ) (hε : 0 < ε) :
    tsupport (mollify (d := d) ε hε u) ⊆ Metric.cthickening ε (tsupport u) := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_cthickening
  obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset _ hx
  have haball : a ∈ Metric.closedBall (0 : Vec d) ε := by
    have : a ∈ tsupport (moll (d := d) ε hε) := subset_tsupport _ ha
    rwa [moll_tsupport (d := d) ε hε] at this
  refine Metric.mem_cthickening_of_dist_le _ b ε _ (subset_tsupport u hb) ?_
  simpa [dist_eq_norm] using! (mem_closedBall_zero_iff.mp haball)

/-- **Mollification commutes with the gradient.** -/
theorem fderiv_mollify_apply {u : Vec d → ℝ} (hu : ContDiff ℝ 1 u)
    (hcu : HasCompactSupport u) (ε : ℝ) (hε : 0 < ε) (x : Vec d) (i : Fin d) :
    (fderiv ℝ (mollify (d := d) ε hε u) x) (basisVec i)
      = mollify (d := d) ε hε (fun y => (fderiv ℝ u y) (basisVec i)) x := by
  have hloc : LocallyIntegrable (moll (d := d) ε hε) volume :=
    ((moll_smooth (d := d) ε hε).continuous).locallyIntegrable
  have hd := (hcu.hasFDerivAt_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hloc hu x).fderiv
  rw [mollify, hd]
  exact convolution_precompR_apply _ hloc (hcu.fderiv ℝ)
    (hu.continuous_fderiv one_ne_zero) x (basisVec i)

/-- Mollification converges uniformly for a continuous compactly supported function. -/
theorem exists_mollify_uniform_bound {u : Vec d → ℝ} (hu : Continuous u)
    (hcu : HasCompactSupport u) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ δ →
      ∀ x, |mollify (d := d) ε hε u x - u x| ≤ η := by
  have huc : UniformContinuous u := hcu.uniformContinuous_of_continuous hu
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc η hη
  refine ⟨δ, hδ, fun ε hε hεδ x => ?_⟩
  have hball : ∀ y ∈ Metric.ball x (bump (d := d) ε hε).rOut, dist (u y) (u x) ≤ η := by
    intro y hy
    have : dist y x < δ := lt_of_lt_of_le (Metric.mem_ball.mp hy) hεδ
    exact (hδ' this).le
  have := (bump (d := d) ε hε).dist_normed_convolution_le
    (μ := volume) (g := u) (x₀ := x) hu.aestronglyMeasurable hball
  simpa [mollify, moll, Real.dist_eq] using! this

/-- A uniformly small function supported in a fixed set has small `L²` norm. -/
theorem eLpNorm_le_of_bound_of_support {f : Vec d → ℝ} {K : Set (Vec d)}
    (hK : MeasurableSet K) {η : ℝ} (hη : 0 ≤ η)
    (hsupp : ∀ x, x ∉ K → f x = 0) (hbd : ∀ x, |f x| ≤ η) (U : Set (Vec d)) :
    SubdiffusiveProcess.RawLp.eLpNorm f 2 (volume.restrict U) ≤
      ENNReal.ofReal η * volume K ^ (1 / (2 : ℝ)) := by
  have hmono : SubdiffusiveProcess.RawLp.eLpNorm f 2 (volume.restrict U) ≤
      SubdiffusiveProcess.RawLp.eLpNorm f 2 volume := by
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num) (by norm_num),
      SubdiffusiveProcess.RawLp.eLpNorm_eq_raw_integral (by norm_num) (by norm_num)]
    exact ENNReal.rpow_le_rpow (lintegral_mono' Measure.restrict_le_self le_rfl)
      (by positivity)
  have hpt : ∀ x, ‖f x‖ ≤ ‖K.indicator (fun _ => η) x‖ := by
    intro x
    by_cases hx : x ∈ K
    · simpa [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hη] using! hbd x
    · simp [Set.indicator_of_notMem hx, hsupp x hx]
  have hind : AEStronglyMeasurable (K.indicator (fun _ => η)) volume :=
    aestronglyMeasurable_const.indicator hK
  calc
    SubdiffusiveProcess.RawLp.eLpNorm f 2 (volume.restrict U) ≤ SubdiffusiveProcess.RawLp.eLpNorm f 2 volume := hmono
    _ ≤ SubdiffusiveProcess.RawLp.eLpNorm (K.indicator (fun _ => η)) 2 volume :=
      SubdiffusiveProcess.RawLp.eLpNorm_mono_ae (Filter.Eventually.of_forall hpt)
    _ = MeasureTheory.eLpNorm (K.indicator (fun _ => η)) 2 volume :=
      SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hind
    _ = ENNReal.ofReal η * volume K ^ (1 / (2 : ℝ)) := by
      rw [eLpNorm_indicator_const hK.nullMeasurableSet (by norm_num) (by norm_num)]
      simp [Real.enorm_eq_ofReal hη]

/-- The `L²` convergence of mollification, along any scale sequence tending to `0`
that stays below the margin. -/
theorem tendsto_eLpNorm_mollify_sub {u : Vec d → ℝ} (hu : Continuous u)
    (hcu : HasCompactSupport u) {delta : ℝ} (_hdelta : 0 < delta)
    {eps : ℕ → ℝ} (hpos : ∀ n, 0 < eps n) (hle : ∀ n, eps n ≤ delta)
    (hto : Filter.Tendsto eps Filter.atTop (nhds 0)) (U : Set (Vec d)) :
    Filter.Tendsto
      (fun n => eLpNorm (fun x => mollify (d := d) (eps n) (hpos n) u x - u x) 2
        (volume.restrict U)) Filter.atTop (nhds 0) := by
  set K : Set (Vec d) := Metric.cthickening delta (tsupport u) with hKdef
  have hKcompact : IsCompact K := hcu.isCompact.cthickening
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hKfin : volume K ≠ ⊤ := hKcompact.measure_ne_top
  set C : ℝ≥0∞ := volume K ^ (1 / (2 : ℝ)) with hCdef
  have hCfin : C ≠ ⊤ := by
    rw [hCdef]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKfin
  -- every difference is supported in `K`
  have hsupp : ∀ n x, x ∉ K → mollify (d := d) (eps n) (hpos n) u x - u x = 0 := by
    intro n x hx
    have h1 : mollify (d := d) (eps n) (hpos n) u x = 0 := by
      by_contra hne
      exact hx (Metric.cthickening_mono (hle n) _
        (mollify_tsupport_subset (d := d) (eps n) (hpos n) (subset_tsupport _ hne)))
    have h2 : u x = 0 := by
      by_contra hne
      exact hx (Metric.self_subset_cthickening _ (subset_tsupport u hne))
    rw [h1, h2, sub_zero]
  rw [ENNReal.tendsto_atTop_zero]
  intro b hb
  rcases eq_or_ne b ⊤ with rfl | hbtop
  · exact ⟨0, fun n _ => le_top⟩
  set Cr : ℝ := C.toReal with hCrdef
  have hCr0 : 0 ≤ Cr := ENNReal.toReal_nonneg
  have hbpos : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hbtop
  set eta : ℝ := b.toReal / (Cr + 1) with hetadef
  have hetapos : 0 < eta := by positivity
  obtain ⟨delta', hdelta', hbound⟩ :=
    exists_mollify_uniform_bound (d := d) hu hcu hetapos
  have hev : ∀ᶠ n in Filter.atTop, eps n ≤ delta' := by
    have := hto.eventually (eventually_lt_nhds hdelta')
    exact this.mono fun n hn => hn.le
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  have hεsmall : eps n ≤ delta' := hN n hn
  have hle2 := eLpNorm_le_of_bound_of_support (d := d) hKmeas hetapos.le
    (hsupp n) (hbound (eps n) (hpos n) hεsmall) U
  have hmeas : AEStronglyMeasurable
      (fun x => mollify (d := d) (eps n) (hpos n) u x - u x) (volume.restrict U) := by
    simpa only [Pi.sub_apply] using!
      (((mollify_smooth (d := d) hu (eps n) (hpos n)).continuous.sub hu).aestronglyMeasurable)
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hmeas] at hle2
  refine hle2.trans ?_
  have hmul : ENNReal.ofReal eta * C = ENNReal.ofReal (eta * Cr) := by
    rw [ENNReal.ofReal_mul hetapos.le, hCrdef, ENNReal.ofReal_toReal hCfin]
  rw [hmul]
  have : eta * Cr ≤ b.toReal := by
    rw [hetadef, div_mul_eq_mul_div]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc ENNReal.ofReal (eta * Cr) ≤ ENNReal.ofReal b.toReal := ENNReal.ofReal_le_ofReal this
    _ = b := ENNReal.ofReal_toReal hbtop

/-- **The density lemma.** A `C¹` function with compact support inside an open set `U`
belongs to `H¹₀(U)`.

`H10Function` demands a sequence of *smooth* compactly supported approximants; the three
constructors in the dependency all require `ContDiff ⊤` outright. This supplies the
missing case by plain mollification below the margin. -/
theorem exists_h10_of_contDiffOne {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) (hf_supp : HasCompactSupport f) (hf_sub : tsupport f ⊆ U) :
    ∃ v : H10Function U, v.toH1Function.toFun = f ∧
      v.toH1Function.grad = fun x i => (fderiv ℝ f x) (basisVec i) := by
  obtain ⟨delta, hdelta, hdsub⟩ :=
    hf_supp.isCompact.exists_cthickening_subset_open hU hf_sub
  set eps : ℕ → ℝ := fun n => delta / (n + 1) with hepsdef
  have hpos : ∀ n, 0 < eps n := fun n => by
    rw [hepsdef]; positivity
  have hle : ∀ n, eps n ≤ delta := fun n => by
    rw [hepsdef]
    refine div_le_self hdelta.le ?_
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hto : Filter.Tendsto eps Filter.atTop (nhds 0) := by
    rw [hepsdef]
    have h := (tendsto_const_div_atTop_nhds_zero_nat delta).comp
      (Filter.tendsto_add_atTop_nat 1)
    have heq : ((fun n : ℕ => delta / (n : ℝ)) ∘ fun a : ℕ => a + 1)
        = fun n : ℕ => delta / ((n : ℝ) + 1) := by
      funext n; simp [Function.comp]
    rwa [heq] at h
  have hcont : Continuous f := hf.continuous
  -- the coordinate derivatives, continuous with compact support
  have hdcont : ∀ i : Fin d, Continuous (fun x => (fderiv ℝ f x) (basisVec i)) := by
    intro i
    simpa using! (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdsupp : ∀ i : Fin d, HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i)) := by
    intro i
    simpa using! hf_supp.fderiv_apply (𝕜 := ℝ) (basisVec i)
  refine ⟨{ toH1Function := H1Function.ofContDiff hU hf hf_supp
            approx := fun n => mollify (d := d) (eps n) (hpos n) f
            approx_smooth := fun n => mollify_smooth (d := d) hcont (eps n) (hpos n)
            approx_hasCompactSupport := fun n =>
              mollify_compactSupport (d := d) hf_supp (eps n) (hpos n)
            approx_support_subset := fun n => ?_
            tendsto_approx := ?_
            tendsto_approx_grad := ?_ }, rfl, rfl⟩
  · exact (mollify_tsupport_subset (d := d) (eps n) (hpos n)).trans
      ((Metric.cthickening_mono (hle n) _).trans hdsub)
  · simpa [H1Function.ofContDiff] using!
      tendsto_eLpNorm_mollify_sub (d := d) hcont hf_supp hdelta hpos hle hto U
  · intro i
    have hkey : ∀ n x, (fderiv ℝ (mollify (d := d) (eps n) (hpos n) f) x) (basisVec i)
        = mollify (d := d) (eps n) (hpos n) (fun y => (fderiv ℝ f y) (basisVec i)) x :=
      fun n x => fderiv_mollify_apply (d := d) hf hf_supp (eps n) (hpos n) x i
    have := tendsto_eLpNorm_mollify_sub (d := d) (hdcont i) (hdsupp i) hdelta hpos hle hto U
    simpa [H1Function.ofContDiff, hkey] using! this


/-- The density lemma, membership form. -/
theorem memH10_of_contDiffOne {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiff ℝ 1 f) (hf_supp : HasCompactSupport f) (hf_sub : tsupport f ⊆ U) :
    MemH10 U f :=
  let ⟨v, hv, _⟩ := exists_h10_of_contDiffOne hU hf hf_supp hf_sub
  ⟨v, hv⟩

/-! ### The Poisson-reduction test function

`WeakHarmonic a W h` tests against `H10Function W`. The reduction to
`WeakPoissonEquationOn` substitutes `psi = phi / a` for a smooth compactly supported
`phi`, and `psi` is only `C^1` because `a` is `C^{1,1}`. `memH10_div` below admits it.

**Scope note.** `memH10_div` asks for `a` positive and `C^1` *globally*. In Section 9 the
coefficient carries those properties only on the double cube of the relevant member of the
family. Since `phi / a` depends on `a` only on `tsupport phi`, the application needs a
globally positive `C^1` function agreeing with `a` there; producing that extension is a
further, small step and is not done here.
-/

/-- The test function of the Poisson reduction, `φ / a`, is admissible in `H¹₀(U)`. -/
theorem memH10_div {U : Set (Vec d)} (hU : IsOpen U) {a phi : Vec d → ℝ}
    (ha : ContDiff ℝ 1 a) (hapos : ∀ x, 0 < a x)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (hphisupp : HasCompactSupport phi)
    (hphisub : tsupport phi ⊆ U) :
    MemH10 U (fun x => phi x / a x) := by
  have hne : ∀ x, a x ≠ 0 := fun x => (hapos x).ne'
  have hC1 : ContDiff ℝ 1 (fun x => phi x / a x) :=
    (hphi.of_le (by simp)).div ha hne
  have hsupp : Function.support (fun x => phi x / a x) ⊆ Function.support phi := by
    intro x hx
    simp only [Function.mem_support, ne_eq, div_eq_zero_iff, not_or] at hx
    exact hx.1
  have htsub : tsupport (fun x => phi x / a x) ⊆ tsupport phi :=
    closure_minimal (hsupp.trans (subset_tsupport phi)) (isClosed_tsupport phi)
  have hcs : HasCompactSupport (fun x => phi x / a x) :=
    hphisupp.isCompact.of_isClosed_subset (isClosed_tsupport _) htsub
  have hsub : tsupport (fun x => phi x / a x) ⊆ U := htsub.trans hphisub
  exact memH10_of_contDiffOne hU hC1 hcs hsub

/-- `phi / a` is globally `C¹` as soon as `a` is `C¹` and positive on a neighbourhood of
`tsupport phi`: off that support the quotient is identically `0`. No extension of `a` is
needed. -/
theorem contDiffOne_div_of_contDiffOn {V : Set (Vec d)} (hV : IsOpen V)
    {a phi : Vec d → ℝ} (ha : ContDiffOn ℝ 1 a V) (hapos : ∀ x ∈ V, 0 < a x)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (hsubV : tsupport phi ⊆ V) :
    ContDiff ℝ 1 (fun x => phi x / a x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport phi
  · have hxV : x ∈ V := hsubV hx
    have hdiv : ContDiffOn ℝ 1 (fun y => phi y / a y) V :=
      ((hphi.of_le (by simp)).contDiffOn).div ha (fun y hy => (hapos y hy).ne')
    exact hdiv.contDiffAt (hV.mem_nhds hxV)
  · have hopen : IsOpen (tsupport phi)ᶜ := (isClosed_tsupport phi).isOpen_compl
    have hnhds : (tsupport phi)ᶜ ∈ nhds x := hopen.mem_nhds hx
    have heq : (fun y => phi y / a y) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [hnhds] with y hy
      have : phi y = 0 := by
        by_contra hne
        exact hy (subset_tsupport phi hne)
      simp [this]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq heq

/-- Localized form of `memH10_div`: the Poisson-reduction test function is admissible
when the coefficient is merely `C¹` and positive near `tsupport phi`. -/
theorem memH10_div_of_contDiffOn {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    {a phi : Vec d → ℝ} (ha : ContDiffOn ℝ 1 a V) (hapos : ∀ x ∈ V, 0 < a x)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (hphisupp : HasCompactSupport phi)
    (hphisub : tsupport phi ⊆ U) (hsubV : tsupport phi ⊆ V) :
    MemH10 U (fun x => phi x / a x) := by
  have hsupp : Function.support (fun x => phi x / a x) ⊆ Function.support phi := by
    intro x hx
    simp only [Function.mem_support, ne_eq, div_eq_zero_iff, not_or] at hx
    exact hx.1
  have htsub : tsupport (fun x => phi x / a x) ⊆ tsupport phi :=
    closure_minimal (hsupp.trans (subset_tsupport phi)) (isClosed_tsupport phi)
  exact memH10_of_contDiffOne hU
    (contDiffOne_div_of_contDiffOn hV ha hapos hphi hsubV)
    (hphisupp.isCompact.of_isClosed_subset (isClosed_tsupport _) htsub)
    (htsub.trans hphisub)

/-- Localized form recording the gradient. -/
theorem exists_h10_div_of_contDiffOn {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    {a phi : Vec d → ℝ} (ha : ContDiffOn ℝ 1 a V) (hapos : ∀ x ∈ V, 0 < a x)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (hphisupp : HasCompactSupport phi)
    (hphisub : tsupport phi ⊆ U) (hsubV : tsupport phi ⊆ V) :
    ∃ v : H10Function U, v.toH1Function.toFun = (fun x => phi x / a x) ∧
      v.toH1Function.grad
        = fun x i => (fderiv ℝ (fun y => phi y / a y) x) (basisVec i) := by
  have hsupp : Function.support (fun x => phi x / a x) ⊆ Function.support phi := by
    intro x hx
    simp only [Function.mem_support, ne_eq, div_eq_zero_iff, not_or] at hx
    exact hx.1
  have htsub : tsupport (fun x => phi x / a x) ⊆ tsupport phi :=
    closure_minimal (hsupp.trans (subset_tsupport phi)) (isClosed_tsupport phi)
  exact exists_h10_of_contDiffOne hU
    (contDiffOne_div_of_contDiffOn hV ha hapos hphi hsubV)
    (hphisupp.isCompact.of_isClosed_subset (isClosed_tsupport _) htsub)
    (htsub.trans hphisub)


/-- The pointwise identity driving the Poisson reduction:
`a ∂ᵢ(φ/a) = ∂ᵢφ - φ ∂ᵢ(log a)`. Obtained from the product rule applied to
`(φ/a) · a = φ`, since Mathlib has no `HasFDerivAt.div`. -/
theorem coeff_mul_fderiv_div {V : Set (Vec d)} (hV : IsOpen V) {a phi : Vec d → ℝ}
    (ha : ContDiffOn ℝ 1 a V) (hapos : ∀ x ∈ V, 0 < a x)
    (hphi : ContDiff ℝ (⊤ : ℕ∞) phi) (hsubV : tsupport phi ⊆ V)
    {x : Vec d} (hx : x ∈ V) (i : Fin d) :
    a x * (fderiv ℝ (fun y => phi y / a y) x) (basisVec i)
      = (fderiv ℝ phi x) (basisVec i)
        - phi x * (fderiv ℝ (fun y => Real.log (a y)) x) (basisVec i) := by
  have hax : a x ≠ 0 := (hapos x hx).ne'
  have hadiff : DifferentiableAt ℝ a x :=
    ((ha.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx))
  have hpsiC1 : ContDiff ℝ 1 (fun y => phi y / a y) :=
    contDiffOne_div_of_contDiffOn hV ha hapos hphi hsubV
  have hpsi : HasFDerivAt (fun y => phi y / a y)
      (fderiv ℝ (fun y => phi y / a y) x) x :=
    (hpsiC1.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hA : HasFDerivAt a (fderiv ℝ a x) x := hadiff.hasFDerivAt
  have hprod := hpsi.mul hA
  -- `(φ/a) * a` agrees with `φ` near `x`
  have heq : ((fun y => phi y / a y) * a) =ᶠ[nhds x] phi := by
    filter_upwards [hV.mem_nhds hx] with y hy
    have : a y ≠ 0 := (hapos y hy).ne'
    simp [Pi.mul_apply, div_mul_cancel₀ _ this]
  have hphix : HasFDerivAt phi
      ((fun y => phi y / a y) x • fderiv ℝ a x
        + a x • fderiv ℝ (fun y => phi y / a y) x) x :=
    hprod.congr_of_eventuallyEq heq.symm
  have hlog : HasFDerivAt (fun y => Real.log (a y)) ((a x)⁻¹ • fderiv ℝ a x) x :=
    hA.log hax
  rw [hphix.fderiv, hlog.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Density
