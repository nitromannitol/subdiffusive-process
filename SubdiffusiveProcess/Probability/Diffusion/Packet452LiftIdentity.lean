module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452GoodEvent

@[expose] public section

/-!
# P-452 seed (ii), Steps 5 and 7: the fixed-time identity and the exit-time vanishing

  §2.3, Steps 5
and 7 -- the second and third clauses of `sobolevPathLiftGoal`.

**Step 5** (`ae_pathLift_eq`).  For a fixed time `t`, `pathLift a.fn ω t = u.zeroExtension (ω t)`
for a.e. `x`, a.e. `ω`.  The two limits are identified without any further extraction: the *same*
geometric rate that produced the good event makes `∑ₖ ∫ |aₖ(ω t) − u⁰(ω t)|² dμ` converge, so
`ae_tendsto_zero_of_tsum_lintegral_ne_top` gives a.e. convergence along the **full** sequence, and
`tendsto_nhds_unique` finishes.  B8's Step 5 passes to "a further subsequence"; that is avoidable
for the same reason Step 2's extraction was.

The identity `(pathMeasure d).map (ω ↦ ω t) = volume` (`map_eval_pathMeasure`) is what lets the
`L²`-in-`x` rate be read as an `L²`-in-`ω` rate, and it also transports the a.e.-`x` choice of a
measurable representative of `u.zeroExtension` to an a.e.-`ω` statement -- which is needed because
`u.zeroExtension` is only `AEStronglyMeasurable`, so the event in the goal's second clause is not
measurable on the nose.  `ae_pathMeasure_of_ae_forall` removes that obstruction once and for all by
passing to a measurable null superset.

**Step 7** (`ae_pathLift_exit`) is the already-PROVED `zero_at_exit_of_tendstoUniformlyOn` applied
at the horizon `T = (exitTime U ω).toNNReal` itself, using `pathLift_spec`'s uniform convergence on
*every* `Icc 0 T` -- so no horizon has to be chosen in advance, and `hT` is `le_rfl`.
-/

set_option autoImplicit false

open Filter Homogenization MeasureTheory MarkovProcess Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-! ## The law of a fixed coordinate under the path measure -/

theorem map_eval_pathMeasure (t : ℝ≥0) :
    (pathMeasure d).map (fun ω : ContinuousPath (Vec d) => ω t) = volume := by
  have heval : Measurable fun ω : ContinuousPath (Vec d) => ω t :=
    ContinuousPath.measurable_coordinateProcess t
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply heval hs, ← lintegral_indicator_one (heval hs),
    ← lintegral_indicator_one (μ := volume) hs]
  have h2 : ∀ ω : ContinuousPath (Vec d),
      ((fun ω : ContinuousPath (Vec d) => ω t) ⁻¹' s).indicator
          (1 : ContinuousPath (Vec d) → ℝ≥0∞) ω
        = s.indicator (1 : Vec d → ℝ≥0∞) (ω t) := by
    intro ω
    by_cases hω : ω t ∈ s
    · rw [Set.indicator_of_mem (show ω ∈ (fun ω : ContinuousPath (Vec d) => ω t) ⁻¹' s from hω),
        Set.indicator_of_mem hω]
      rfl
    · rw [Set.indicator_of_notMem
        (show ω ∉ (fun ω : ContinuousPath (Vec d) => ω t) ⁻¹' s from hω),
        Set.indicator_of_notMem hω]
  simp only [h2]
  exact lintegral_pathMeasure_eval (measurable_one.indicator hs) t

theorem quasiMeasurePreserving_eval (t : ℝ≥0) :
    Measure.QuasiMeasurePreserving (fun ω : ContinuousPath (Vec d) => ω t)
      (pathMeasure d) volume :=
  ⟨ContinuousPath.measurable_coordinateProcess t, by rw [map_eval_pathMeasure t]⟩

/-! ## Two transfer lemmas -/

/-- Convergence of `ofReal` of the squared errors to `0` is convergence. -/
theorem tendsto_of_tendsto_ofReal_sq {y : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun k => ENNReal.ofReal ((y k - L) ^ 2)) atTop (𝓝 0)) :
    Tendsto y atTop (𝓝 L) := by
  have hsq : Tendsto (fun k => (y k - L) ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (by simp)).comp h
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_zero]
      using! this
  have habs : Tendsto (fun k => |y k - L|) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] using! this
  have hd : Tendsto (fun k => y k - L) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have h2 := hd.add (tendsto_const_nhds (x := L) (f := (atTop : Filter ℕ)))
  simpa using! h2

/-- `ae_laplacianLaw_of_ae_pathMeasure` with no measurability hypothesis: pass to a measurable null
superset of the exceptional set. -/
theorem ae_pathMeasure_of_ae_forall {p : ContinuousPath (Vec d) → Prop}
    (h : ∀ᵐ ω ∂(pathMeasure d), p ω) :
    ∀ᵐ x ∂volume, ∀ᵐ ω ∂(laplacianContinuousLaw d x), p ω := by
  rw [ae_iff] at h
  obtain ⟨s, hsub, hs, hzero⟩ := exists_measurable_superset_of_null h
  have h2 : ∀ᵐ ω ∂(pathMeasure d), ω ∈ sᶜ := by
    rw [ae_iff]
    simpa using! hzero
  filter_upwards [ae_laplacianLaw_of_ae_pathMeasure hs.compl h2] with x hx
  filter_upwards [hx] with ω hω
  by_contra hp
  exact hω (hsub hp)

/-! ## Step 5: the fixed-time identity -/

variable {U : Set (Vec d)} {u : H10Function U}

theorem ae_pathLift_eq (hmax : maximalEstimateGoal d) (hU : IsOpen U) (a : RateApprox d U u)
    (t : ℝ≥0) :
    ∀ᵐ x ∂volume, ∀ᵐ ω ∂(laplacianContinuousLaw d x),
      pathLift a.fn ω t = u.zeroExtension (ω t) := by
  have hz : AEStronglyMeasurable u.zeroExtension volume :=
    (memLp_zeroExtension_two hU u).aestronglyMeasurable
  obtain ⟨w, hwmeas, hweq⟩ : ∃ w : Vec d → ℝ, Measurable w ∧ u.zeroExtension =ᵐ[volume] w :=
    ⟨hz.mk u.zeroExtension, hz.stronglyMeasurable_mk.measurable, hz.ae_eq_mk⟩
  have hmeasG : ∀ k : ℕ, Measurable fun y : Vec d =>
      ENNReal.ofReal ((a.fn k y - w y) ^ 2) := fun k =>
    ENNReal.measurable_ofReal.comp (((a.fn k).continuous.measurable.sub hwmeas).pow_const 2)
  have hrate : ∀ k : ℕ,
      (∫⁻ ω, ENNReal.ofReal ((a.fn k (ω t) - w (ω t)) ^ 2) ∂(pathMeasure d))
        ≤ ((4 : ℝ≥0∞)⁻¹) ^ k := by
    intro k
    rw [lintegral_pathMeasure_eval (hmeasG k) t, lintegral_ofReal_sq_eq_eLpNorm_sq]
    have hm : AEStronglyMeasurable (fun y => a.fn k y - w y) volume := by
      exact ((a.fn k).continuous.measurable.sub hwmeas).aestronglyMeasurable
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hm]
    have hae : (fun y => a.fn k y - w y) =ᵐ[volume] fun y => a.fn k y - u.zeroExtension y := by
      filter_upwards [hweq] with y hy
      rw [hy]
    have hcongr : eLpNorm (fun y => a.fn k y - w y) 2 volume
        = eLpNorm (fun y => a.fn k y - u.zeroExtension y) 2 volume :=
      eLpNorm_congr_ae hae
    rw [hcongr]
    calc (eLpNorm (fun y => a.fn k y - u.zeroExtension y) 2 volume) ^ 2
        ≤ (((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2 := ENNReal.pow_le_pow_left (a.rate k)
      _ = ((16 : ℝ≥0∞)⁻¹) ^ k := inv_four_pow_sq k
      _ ≤ ((4 : ℝ≥0∞)⁻¹) ^ k :=
          ENNReal.pow_le_pow_left
            (ENNReal.inv_le_inv.mpr (by norm_num : (4 : ℝ≥0∞) ≤ 16))
  have hsum : (∑' k : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((a.fn k (ω t) - w (ω t)) ^ 2) ∂(pathMeasure d)) ≠ ⊤ :=
    ne_top_of_le_ne_top tsum_geometric_four_inv_ne_top (ENNReal.tsum_le_tsum hrate)
  have hconv : ∀ᵐ ω ∂(pathMeasure d),
      Tendsto (fun k => ENNReal.ofReal ((a.fn k (ω t) - w (ω t)) ^ 2)) atTop (𝓝 0) :=
    ae_tendsto_zero_of_tsum_lintegral_ne_top
      (fun k => ((hmeasG k).comp (ContinuousPath.measurable_coordinateProcess t)).aemeasurable)
      hsum
  have hwae : ∀ᵐ ω ∂(pathMeasure d), w (ω t) = u.zeroExtension (ω t) :=
    (quasiMeasurePreserving_eval t).ae (p := fun y => w y = u.zeroExtension y) hweq.symm
  have hfinal : ∀ᵐ ω ∂(pathMeasure d), pathLift a.fn ω t = u.zeroExtension (ω t) := by
    filter_upwards [ae_mem_goodSet hmax hU a, hconv, hwae] with ω hω hc hw
    rw [← hw]
    exact tendsto_nhds_unique (tendsto_pathLift_apply hω t) (tendsto_of_tendsto_ofReal_sq hc)
  exact ae_pathMeasure_of_ae_forall hfinal

/-! ## Step 7: vanishing at the exit time -/

theorem ae_pathLift_exit (hmax : maximalEstimateGoal d) (hU : IsOpen U) (a : RateApprox d U u) :
    ∀ᵐ x ∂(volume.restrict U), ∀ᵐ ω ∂(laplacianContinuousLaw d x),
      ContinuousPath.exitTime U ω ≠ ⊤ →
        pathLift a.fn ω ((ContinuousPath.exitTime U ω).toNNReal) = 0 := by
  have hgood : ∀ᵐ x ∂volume, ∀ᵐ ω ∂(laplacianContinuousLaw d x), ω ∈ goodSet a.fn :=
    ae_pathMeasure_of_ae_forall (ae_mem_goodSet hmax hU a)
  filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem hU.measurableSet] with x hgx hxU
  filter_upwards [hgx, ae_eval_zero_eq x] with ω hω h0
  intro hfin
  exact Packet452ScopeChecks.zero_at_exit_of_tendstoUniformlyOn hU ω (h0 ▸ hxU) hfin
    ((ContinuousPath.exitTime U ω).toNNReal) le_rfl (fun k => ⇑(a.fn k)) a.support
    (fun s => pathLift a.fn ω s) ((pathLift_spec hω).2 _)

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
