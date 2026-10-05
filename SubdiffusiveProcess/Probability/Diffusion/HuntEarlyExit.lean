module

public import SubdiffusiveProcess.Probability.Diffusion.HuntChapmanKolmogorov
public import MarkovProcess.Trajectory.PathTightness

@[expose] public section

/-!
# B3 and B5 of the continuity route: uniform early exit, and the smoothing error

* `exists_uniform_early_exit` (**B3**) — `sup_{x ∈ K} P_x(τ_U ≤ t) → 0` as `t ↓ 0`, for a compact
  `K ⊆ U`.  The tightness theorem
  `SubMarkovKernelSemigroup.IsConservative.exists_isCompact_measure_compl_le` supplies a compact
  set `C` of paths carrying all but `ε` of the mass from every start in `K`; intersecting it with
  the closed set `{w | w 0 ∈ K}` loses nothing, because
  `IsConservative.measure_eval_zero_notMem_eq_zero` says the process starts where it is told; and
  B2 (`exists_time_forall_mem_of_isCompact`) turns that compact set into a common survival time.
  `exitTime_le_iff_mem_hitsSetBy` is what converts "the exit time is at most `t`" into "some
  time `s ≤ t` has `w s ∉ U`", which is exactly what B2 contradicts.  No regularity of `∂U` and
  no continuity of the exit-time functional is used.

* `integral_sub_le_earlyExit`, `abs_smoothing_error_le` (**B5**) — the free-Gaussian smoothing at
  scale `delta` differs from the killed density by at most `C_{t-delta} · P_x(τ_U ≤ delta)`.
  B1 rewrites `q_t(x,y)` as `∫_U q_delta(x,z) q_{t-delta}(z,y) dz`, so the error is
  `∫_U (g_delta − q_delta)(x,z) q_{t-delta}(z,y) dz` with a **nonnegative** integrand; the second
  factor is bounded by the Gaussian constant, and the mass defect of the first is the post-exit
  mass `laplacianSemigroup_eq_killed_add_postExit` at `B = univ`, which is dominated by the
  early-exit probability.  Supporting readouts: `integrableOn_laplacianDensity_row`,
  `integral_laplacianDensity_row`, `integral_huntDensity_row`.

Together with B0 and B1 these are five of the route's eight steps.  What remains is B4 (joint
continuity of the smoothing in `(t, x, y)`, a fixed-measure dominated-convergence argument),
and B6-B7 (uniform convergence on compact products, then `TendstoUniformlyOn.continuousOn`).
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- **B3 of the continuity route.**  The probability of leaving the domain before a short
horizon is uniformly small over a compact set of interior starting points. -/
theorem exists_uniform_early_exit {U : Set (Vec d)} (hU : IsOpen U)
    (K : Set (Vec d)) (hK : IsCompact K) (hKU : K ⊆ U) {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ a : ℝ, 0 < a ∧ ∀ t : ℝ, 0 < t → t ≤ a → ∀ x ∈ K,
      laplacianContinuousLaw d x
        {w | ContinuousPath.exitTime U w ≤ ENNReal.ofReal t} ≤ eps := by
  obtain ⟨C, hCcompact, hCmass⟩ :=
    SubMarkovKernelSemigroup.IsConservative.exists_isCompact_measure_compl_le
      (laplacianSemigroup d) isConservative_laplacianSemigroup
      hasKolmogorovMoments_laplacianSemigroup hK heps
  set Cstart : Set (ContinuousPath (Vec d)) := {w | w 0 ∈ K} with hCstart
  have hCstartClosed : IsClosed Cstart := by
    have hcont : Continuous (fun w : ContinuousPath (Vec d) => w 0) :=
      continuous_eval_const (0 : NNReal)
    exact hK.isClosed.preimage hcont
  set C' : Set (ContinuousPath (Vec d)) := C ∩ Cstart with hC'
  have hC'compact : IsCompact C' := hCcompact.inter_right hCstartClosed
  have hC'U : ∀ w ∈ C', w 0 ∈ U := fun w hw => hKU hw.2
  obtain ⟨a, ha, haU⟩ := exists_time_forall_mem_of_isCompact hU C' hC'compact hC'U
  refine ⟨(a : ℝ), by exact_mod_cast ha, ?_⟩
  intro t ht hta x hx
  have hsubset : {w : ContinuousPath (Vec d) |
      ContinuousPath.exitTime U w ≤ ENNReal.ofReal t} ⊆ C'ᶜ := by
    intro w hw hwC'
    rw [mem_ofPred_eq, show ENNReal.ofReal t = ((Real.toNNReal t : NNReal) : ℝ≥0∞) from rfl,
      ContinuousPath.exitTime_le_iff_mem_hitsSetBy U hU] at hw
    obtain ⟨s, hs⟩ := hw
    have hsa : (s : NNReal) ≤ a := by
      refine le_trans s.2 ?_
      exact Real.toNNReal_le_iff_le_coe.mpr hta
    exact hs (haU w hwC' s hsa)
  refine le_trans (measure_mono hsubset) ?_
  have hcompl : C'ᶜ = Cᶜ ∪ Cstartᶜ := by
    rw [hC', Set.compl_inter]
  rw [hcompl]
  have hzero : laplacianContinuousLaw d x Cstartᶜ = 0 :=
    SubMarkovKernelSemigroup.IsConservative.measure_eval_zero_notMem_eq_zero
      (laplacianSemigroup d) isConservative_laplacianSemigroup
      kolmogorovRegular_laplacianSemigroup hK.isClosed.measurableSet hx
  calc laplacianContinuousLaw d x (Cᶜ ∪ Cstartᶜ)
      ≤ laplacianContinuousLaw d x Cᶜ + laplacianContinuousLaw d x Cstartᶜ :=
        measure_union_le _ _
    _ = laplacianContinuousLaw d x Cᶜ := by rw [hzero, add_zero]
    _ ≤ eps := hCmass x hx

/-- The free Gaussian row is integrable on a bounded domain. -/
theorem integrableOn_laplacianDensity_row {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) {t : ℝ} (ht : 0 < t) (x : Vec d) :
    IntegrableOn (fun z => laplacianDensity t x z) U := by
  have := isFiniteMeasure_restrict_of_isBounded hUb
  have hmeas : Measurable (fun z : Vec d => laplacianDensity t x z) :=
    (measurable_uncurry_laplacianDensity (d := d) t).of_uncurry_left (x := x)
  refine Integrable.mono' (μ := volume.restrict U)
    (g := fun _ : Vec d => (Real.sqrt (4 * Real.pi * t))⁻¹ ^ d)
    (integrable_const _) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (laplacianDensity_nonneg t x z)]
  exact laplacianDensity_le_const ht x z

/-- The mass of the free Gaussian row over the domain. -/
theorem integral_laplacianDensity_row {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {t : ℝ} (ht : 0 < t) (x : Vec d) :
    ENNReal.ofReal (∫ z in U, laplacianDensity t x z)
      = laplacianSemigroup d (Real.toNNReal t) x U := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_laplacianDensity_row hUb ht x)
    (Filter.Eventually.of_forall fun z => laplacianDensity_nonneg t x z),
    laplacianSemigroup_eq_withDensity ht x, withDensity_apply _ hU.measurableSet]

/-- The mass of the Hunt density row over the domain is the killed kernel's total mass. -/
theorem integral_huntDensity_row {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    ENNReal.ofReal (∫ z in U, huntDensity U t x z)
      = killedKernel (laplacianLaw d) U hU (Real.toNNReal t) x univ := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_huntDensity_row hU hUb ht x)
    (Filter.Eventually.of_forall fun z => huntDensity_nonneg U t x z),
    ← lintegral_huntDensity_eq_killed (brownian_hunt_identity d) hU hUb ht hx univ
      MeasurableSet.univ, univ_inter]

/-- **The mass defect of the killed row is the early-exit probability.** -/
theorem integral_sub_le_earlyExit {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    (∫ z in U, laplacianDensity t x z) - (∫ z in U, huntDensity U t x z)
      ≤ (laplacianContinuousLaw d x
          {w | ContinuousPath.exitTime U w ≤ ENNReal.ofReal t}).toReal := by
  have hsplit := laplacianSemigroup_eq_killed_add_postExit U hU t x univ MeasurableSet.univ
  rw [univ_inter] at hsplit
  have hgle : laplacianSemigroup d (Real.toNNReal t) x U ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((laplacianSemigroup d).isSubMarkovKernel _ |>.measure_le_one x U)
  have hkle : killedKernel (laplacianLaw d) U hU (Real.toNNReal t) x univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((killedKernel_subMarkov (laplacianLaw d) U hU (Real.toNNReal t)).measure_le_one x univ)
  have hpost : postExitMass U t x univ
      ≤ laplacianContinuousLaw d x {w | ContinuousPath.exitTime U w ≤ ENNReal.ofReal t} := by
    refine measure_mono fun w hw => ?_
    exact hw.1
  have hg := integral_laplacianDensity_row hU hUb ht x
  have hk := integral_huntDensity_row hU hUb ht hx
  have hgnn : 0 ≤ ∫ z in U, laplacianDensity t x z :=
    integral_nonneg fun z => laplacianDensity_nonneg t x z
  have hknn : 0 ≤ ∫ z in U, huntDensity U t x z :=
    integral_nonneg fun z => huntDensity_nonneg U t x z
  have hreal : (∫ z in U, laplacianDensity t x z) - (∫ z in U, huntDensity U t x z)
      = (postExitMass U t x univ).toReal := by
    have hpt : postExitMass U t x univ ≠ ⊤ :=
      ne_top_of_le_ne_top (measure_ne_top _ _) hpost
    have : ENNReal.ofReal (∫ z in U, laplacianDensity t x z)
        = ENNReal.ofReal (∫ z in U, huntDensity U t x z) + postExitMass U t x univ := by
      rw [hg, hk, hsplit]
    have h2 := congrArg ENNReal.toReal this
    rw [ENNReal.toReal_add (by rw [hk]; exact hkle) hpt,
      ENNReal.toReal_ofReal hgnn, ENNReal.toReal_ofReal hknn] at h2
    linarith
  rw [hreal]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hpost

/-- **B5 of the continuity route.**  The free-Gaussian smoothing error at scale `delta` is
controlled by the early-exit probability, uniformly in the terminal point. -/
theorem abs_smoothing_error_le {U : Set (Vec d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {delta t : ℝ} (hdelta : 0 < delta) (hdt : delta < t)
    {x : Vec d} (hx : x ∈ U) {y : Vec d} (hy : y ∈ U) :
    |(∫ z in U, laplacianDensity delta x z * huntDensity U (t - delta) z y) -
        huntDensity U t x y|
      ≤ (Real.sqrt (4 * Real.pi * (t - delta)))⁻¹ ^ d *
        (laplacianContinuousLaw d x
          {w | ContinuousPath.exitTime U w ≤ ENNReal.ofReal delta}).toReal := by
  have := isFiniteMeasure_restrict_of_isBounded hUb
  have hrest : 0 < t - delta := by linarith
  set C : ℝ := (Real.sqrt (4 * Real.pi * (t - delta)))⁻¹ ^ d with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hck := (huntDensity_chapmanKolmogorov hU hUb hdelta hrest hx hy).2
  rw [show delta + (t - delta) = t by ring] at hck
  have hint1 : IntegrableOn
      (fun z => laplacianDensity delta x z * huntDensity U (t - delta) z y) U := by
    have hmeas : Measurable (fun z : Vec d =>
        laplacianDensity delta x z * huntDensity U (t - delta) z y) :=
      Measurable.mul ((measurable_uncurry_laplacianDensity (d := d) delta).of_uncurry_left (x := x))
        ((measurable_uncurry_huntDensity U hU (t - delta)).of_uncurry_right (y := y))
    refine Integrable.mono' (μ := volume.restrict U)
      (g := fun _ : Vec d => (Real.sqrt (4 * Real.pi * delta))⁻¹ ^ d * C)
      (integrable_const _) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (laplacianDensity_nonneg delta x z)
      (huntDensity_nonneg U (t - delta) z y))]
    refine mul_le_mul (laplacianDensity_le_const hdelta x z) ?_
      (huntDensity_nonneg U (t - delta) z y) (by positivity)
    exact le_trans (_root_.SubdiffusiveProcess.Probability.Diffusion.HuntContinuityChecks.huntDensity_le_laplacianDensity U (t - delta) z y)
      (laplacianDensity_le_const hrest z y)
  have hint2 := integrableOn_huntDensity_mul hU hUb hdelta hrest x y
  have hdiff : (∫ z in U, laplacianDensity delta x z * huntDensity U (t - delta) z y) -
      huntDensity U t x y
      = ∫ z in U, (laplacianDensity delta x z - huntDensity U delta x z) *
          huntDensity U (t - delta) z y := by
    rw [hck, ← integral_sub hint1 hint2]
    congr 1
    funext z
    ring
  rw [hdiff]
  have hptwise : ∀ z : Vec d,
      |(laplacianDensity delta x z - huntDensity U delta x z) *
        huntDensity U (t - delta) z y|
        ≤ C * (laplacianDensity delta x z - huntDensity U delta x z) := by
    intro z
    have h0 : 0 ≤ laplacianDensity delta x z - huntDensity U delta x z := by
      have := _root_.SubdiffusiveProcess.Probability.Diffusion.HuntContinuityChecks.huntDensity_le_laplacianDensity U delta x z
      linarith
    have h1 : huntDensity U (t - delta) z y ≤ C :=
      le_trans (_root_.SubdiffusiveProcess.Probability.Diffusion.HuntContinuityChecks.huntDensity_le_laplacianDensity U (t - delta) z y)
        (laplacianDensity_le_const hrest z y)
    rw [abs_of_nonneg (mul_nonneg h0 (huntDensity_nonneg U (t - delta) z y))]
    calc (laplacianDensity delta x z - huntDensity U delta x z) *
          huntDensity U (t - delta) z y
        ≤ (laplacianDensity delta x z - huntDensity U delta x z) * C :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = C * (laplacianDensity delta x z - huntDensity U delta x z) := by ring
  have hintd : IntegrableOn (fun z => laplacianDensity delta x z - huntDensity U delta x z) U :=
    (integrableOn_laplacianDensity_row hUb hdelta x).sub
      (integrableOn_huntDensity_row hU hUb hdelta x)
  have hintdiff : IntegrableOn (fun z => (laplacianDensity delta x z - huntDensity U delta x z) *
      huntDensity U (t - delta) z y) U := by
    have hrw : (fun z => (laplacianDensity delta x z - huntDensity U delta x z) *
        huntDensity U (t - delta) z y)
        = fun z => laplacianDensity delta x z * huntDensity U (t - delta) z y -
          huntDensity U delta x z * huntDensity U (t - delta) z y := by
      funext z; ring
    rw [hrw]
    exact hint1.sub hint2
  calc |∫ z in U, (laplacianDensity delta x z - huntDensity U delta x z) *
          huntDensity U (t - delta) z y|
      ≤ ∫ z in U, |(laplacianDensity delta x z - huntDensity U delta x z) *
          huntDensity U (t - delta) z y| := abs_integral_le_integral_abs
    _ ≤ ∫ z in U, C * (laplacianDensity delta x z - huntDensity U delta x z) :=
        integral_mono hintdiff.abs (hintd.const_mul C)
          (fun z => hptwise z)
    _ = C * ((∫ z in U, laplacianDensity delta x z) - ∫ z in U, huntDensity U delta x z) := by
        rw [integral_const_mul, integral_sub (integrableOn_laplacianDensity_row hUb hdelta x)
          (integrableOn_huntDensity_row hU hUb hdelta x)]
    _ ≤ C * (laplacianContinuousLaw d x
          {w | ContinuousPath.exitTime U w ≤ ENNReal.ofReal delta}).toReal :=
        mul_le_mul_of_nonneg_left (integral_sub_le_earlyExit hU hUb hdelta hx) hC0

end SubdiffusiveProcess.Probability.Diffusion
