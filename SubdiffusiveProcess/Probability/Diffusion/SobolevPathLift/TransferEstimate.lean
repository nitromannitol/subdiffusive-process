module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift.LiftIdentity

@[expose] public section

/-!
# the transfer estimate


the fourth and last clause of `sobolevPathLiftGoal`.  The constant `32` is **inherited** from
`maximalEstimateGoal`, never re-derived.

Fatou (weakest tool: no dominating envelope is available) turns the maximal estimate applied to
`φ − aₖ` into the estimate for `φ − Z`:

```text
∫ sup_{t≤T}(φ(ω t) − Z(ω t))² dμ ≤ ∫ liminfₖ sup_{t≤T}(φ(ω t) − aₖ(ω t))²
                                 ≤ liminfₖ 32(‖φ−aₖ‖₂² + T·E(φ−aₖ))
                                 ≤ 32(‖φ−u⁰‖₂² + T·E(φ−u⁰)).
```

The last step is where care is needed: one may take the limit of the right-hand side using
`aₖ → u⁰` in `L²`, which would need `‖φ − aₖ‖₂ → ‖φ − u⁰‖₂`, i.e. a reverse triangle inequality
that is awkward in `ℝ≥0∞` for want of subtraction.  It is avoided: the one-sided
`‖φ − aₖ‖₂ ≤ ‖φ − u⁰‖₂ + 4^{-k}` is all Fatou needs, and the majorant
`32((‖φ−u⁰‖₂ + 4^{-k})² + T ∑ᵢ(‖∂ᵢφ − gᵢ‖₂ + 4^{-k})²)` converges to the target with no finiteness
hypothesis, because addition and `x ↦ x²` are continuous on all of `ℝ≥0∞`.
-/

set_option autoImplicit false

open Filter Homogenization MeasureTheory MarkovProcess Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift

variable {d : ℕ} {U : Set (Vec d)} {u : H10Function U}

/-! ## The majorant converges -/

theorem tendsto_transfer_majorant (N : ℝ≥0∞) (P : Fin d → ℝ≥0∞) (T : ℝ≥0) :
    Tendsto (fun k : ℕ => (32 : ℝ≥0∞) * ((N + ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2
        + (T : ℝ≥0∞) * ∑ i : Fin d, (P i + ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2))
      atTop (𝓝 ((32 : ℝ≥0∞) * (N ^ 2 + (T : ℝ≥0∞) * ∑ i : Fin d, (P i) ^ 2))) := by
  have hε : Tendsto (fun k : ℕ => ((4 : ℝ≥0∞)⁻¹) ^ k) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.mpr (by norm_num))
  have hsq : ∀ c : ℝ≥0∞, Tendsto (fun k : ℕ => (c + ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2) atTop (𝓝 (c ^ 2)) := by
    intro c
    have h0 : Tendsto (fun k : ℕ => c + ((4 : ℝ≥0∞)⁻¹) ^ k) atTop (𝓝 c) := by
      have h := (tendsto_const_nhds (x := c) (f := (atTop : Filter ℕ))).add hε
      rwa [add_zero] at h
    have h1 := ((ENNReal.continuous_pow 2).tendsto c).comp h0
    simpa only [Function.comp_def] using! h1
  have hsum : Tendsto (fun k : ℕ => ∑ i : Fin d, (P i + ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2) atTop
      (𝓝 (∑ i : Fin d, (P i) ^ 2)) :=
    tendsto_finsetSum _ fun i _ => hsq (P i)
  have hmulT := ENNReal.Tendsto.const_mul (a := (T : ℝ≥0∞)) hsum (Or.inr ENNReal.coe_ne_top)
  exact ENNReal.Tendsto.const_mul ((hsq N).add hmulT) (Or.inr (by norm_num))

/-! ## The reversed rate -/

theorem RateApprox.rate_symm (a : RateApprox d U u) (k : ℕ) :
    eLpNorm (fun x => u.zeroExtension x - a.fn k x) 2 volume ≤ ((4 : ℝ≥0∞)⁻¹) ^ k := by
  have h1 : (fun x => a.fn k x - u.zeroExtension x)
      = -(fun x => u.zeroExtension x - a.fn k x) := by funext x; simp
  have h2 : eLpNorm (fun x => u.zeroExtension x - a.fn k x) 2 volume
      = eLpNorm (fun x => a.fn k x - u.zeroExtension x) 2 volume := by
    rw [h1, eLpNorm_neg]
  rw [h2]
  exact a.rate k

theorem RateApprox.rateGrad_symm (a : RateApprox d U u) (i : Fin d) (k : ℕ) :
    eLpNorm (fun x => u.zeroExtensionGrad x i
      - fderiv ℝ (a.fn k) x (Pi.single i 1)) 2 volume ≤ ((4 : ℝ≥0∞)⁻¹) ^ k := by
  have h1 : (fun x => fderiv ℝ (a.fn k) x (Pi.single i 1) - u.zeroExtensionGrad x i)
      = -(fun x => u.zeroExtensionGrad x i - fderiv ℝ (a.fn k) x (Pi.single i 1)) := by
    funext x; simp
  have h2 : eLpNorm (fun x => u.zeroExtensionGrad x i
        - fderiv ℝ (a.fn k) x (Pi.single i 1)) 2 volume
      = eLpNorm (fun x => fderiv ℝ (a.fn k) x (Pi.single i 1)
        - u.zeroExtensionGrad x i) 2 volume := by
    rw [h1, eLpNorm_neg]
  rw [h2]
  exact a.rateGrad k i

/-! ## Step 8: the transfer estimate -/

/-- The maximal estimate applied to `φ − aₖ`, in `ℝ≥0∞` form and already majorised by the rate. -/
theorem lintegral_iSup_sq_sub_approx_le (hmax : maximalEstimateGoal d) (hU : IsOpen U)
    (a : RateApprox d U u) {φ : Vec d → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (T : ℝ≥0) (k : ℕ) :
    (∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
        ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2)) ∂(pathMeasure d))
      ≤ (32 : ℝ≥0∞) * ((eLpNorm (fun x => φ x - u.zeroExtension x) 2 volume
            + ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2
          + (T : ℝ≥0∞) * ∑ i : Fin d, (eLpNorm (fun x =>
              fderiv ℝ φ x (Pi.single i 1) - u.zeroExtensionGrad x i) 2 volume
            + ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2) := by
  have hz : AEStronglyMeasurable u.zeroExtension volume :=
    (memLp_zeroExtension_two hU u).aestronglyMeasurable
  have hzg : ∀ i : Fin d, AEStronglyMeasurable (fun x => u.zeroExtensionGrad x i) volume :=
    fun i => (memLp_zeroExtensionGrad_two hU u i).aestronglyMeasurable
  have hmeasF : Measurable fun ω : ContinuousPath (Vec d) =>
      ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2) := by
    refine measurable_iSup_le_of_continuous
      (F := fun (ω : ContinuousPath (Vec d)) (t : ℝ≥0) =>
        ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2)) ?_ ?_ T
    · intro ω
      exact ENNReal.continuous_ofReal.comp
        (((hφ.continuous.comp ω.continuous).sub
          ((a.fn k).continuous.comp ω.continuous)).pow 2)
    · intro t
      have hev : Measurable fun ω : ContinuousPath (Vec d) => ω t :=
        ContinuousPath.measurable_coordinateProcess t
      exact ENNReal.measurable_ofReal.comp
        (((hφ.continuous.measurable.comp hev).sub
          ((a.fn k).continuous.measurable.comp hev)).pow_const 2)
  have hintA : Integrable (fun x => (φ x - a.fn k x) ^ 2) volume :=
    integrable_sq_of_continuous_of_hasCompactSupport
      (hφ.continuous.sub (a.fn k).continuous) (hφc.sub (a.compact k))
  have hintB : ∀ i : Fin d, Integrable (fun x =>
      (fderiv ℝ φ x (Pi.single i 1) - fderiv ℝ (a.fn k) x (Pi.single i 1)) ^ 2) volume :=
    fun i => integrable_sq_of_continuous_of_hasCompactSupport
      ((continuous_fderiv_apply hφ i).sub (continuous_fderiv_apply (a.smooth k) i))
      ((hasCompactSupport_fderiv_apply hφc i).sub
        (hasCompactSupport_fderiv_apply (a.compact k) i))
  calc (∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
        ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2)) ∂(pathMeasure d))
      = ∫⁻ x, ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
          ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2))
          ∂(laplacianContinuousLaw d x) ∂volume := lintegral_pathMeasure hmeasF
    _ ≤ ENNReal.ofReal (32 * ((∫ x, (φ x - a.fn k x) ^ 2) + (T : ℝ) * ∫ x, ∑ i : Fin d,
          (fderiv ℝ φ x (Pi.single i 1) - fderiv ℝ (a.fn k) x (Pi.single i 1)) ^ 2)) :=
        maximalEstimate_sub hmax hφ hφc (a.smooth k) (a.compact k) T
    _ = 32 * (ENNReal.ofReal (∫ x, (φ x - a.fn k x) ^ 2)
          + (T : ℝ≥0∞) * ENNReal.ofReal (∫ x, ∑ i : Fin d,
            (fderiv ℝ φ x (Pi.single i 1) - fderiv ℝ (a.fn k) x (Pi.single i 1)) ^ 2)) :=
        ofReal_maximal_rhs (integral_nonneg fun x => sq_nonneg _)
          (integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
    _ = 32 * ((eLpNorm (fun x => φ x - a.fn k x) 2 volume) ^ 2
          + (T : ℝ≥0∞) * ∑ i : Fin d, (eLpNorm (fun x =>
            fderiv ℝ φ x (Pi.single i 1)
              - fderiv ℝ (a.fn k) x (Pi.single i 1)) 2 volume) ^ 2) := by
        rw [ofReal_integral_sq_eq_eLpNorm_sq hintA,
          ofReal_integral_sum_sq_eq_sum_eLpNorm_sq hintB]
        have hf : AEStronglyMeasurable (fun x => φ x - a.fn k x) volume := by
          simpa only [Pi.sub_apply] using!
            (hφ.continuous.aestronglyMeasurable.sub (a.aestronglyMeasurable k))
        have hg : ∀ i : Fin d, AEStronglyMeasurable (fun x =>
            fderiv ℝ φ x (Pi.single i 1) - fderiv ℝ (a.fn k) x (Pi.single i 1)) volume := by
          intro i
          simpa only [Pi.sub_apply] using!
            ((continuous_fderiv_apply hφ i).aestronglyMeasurable.sub
              (a.aestronglyMeasurable_grad k i))
        rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf]
        simp_rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hg _)]

    _ ≤ 32 * ((eLpNorm (fun x => φ x - u.zeroExtension x) 2 volume
            + ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2
          + (T : ℝ≥0∞) * ∑ i : Fin d, (eLpNorm (fun x =>
              fderiv ℝ φ x (Pi.single i 1) - u.zeroExtensionGrad x i) 2 volume
            + ((4 : ℝ≥0∞)⁻¹) ^ k) ^ 2) := by
        gcongr with i
        · exact le_trans (eLpNorm_sub_le_add hφ.continuous.aestronglyMeasurable
            (a.aestronglyMeasurable k) hz) (add_le_add le_rfl (a.rate_symm k))
        · exact le_trans (eLpNorm_sub_le_add (continuous_fderiv_apply hφ i).aestronglyMeasurable
            (a.aestronglyMeasurable_grad k i) (hzg i))
            (add_le_add le_rfl (a.rateGrad_symm i k))

/-- **Step 8.**  The transfer estimate, constant `32` inherited from `maximalEstimateGoal`. -/
theorem lintegral_iSup_sq_sub_pathLift_le (hmax : maximalEstimateGoal d) (hU : IsOpen U)
    (a : RateApprox d U u) {φ : Vec d → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (T : ℝ≥0) :
    (∫⁻ x, ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
        ENNReal.ofReal ((φ (ω t) - pathLift a.fn ω t) ^ 2))
        ∂(laplacianContinuousLaw d x) ∂volume)
      ≤ ENNReal.ofReal (32 * ((∫ x, (φ x - u.zeroExtension x) ^ 2) + (T : ℝ) *
          ∫ x, ∑ i : Fin d,
            (fderiv ℝ φ x (Pi.single i 1) - u.zeroExtensionGrad x i) ^ 2)) := by
  have hmeasFk : ∀ k : ℕ, Measurable fun ω : ContinuousPath (Vec d) =>
      ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2) := by
    intro k
    refine measurable_iSup_le_of_continuous
      (F := fun (ω : ContinuousPath (Vec d)) (t : ℝ≥0) =>
        ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2)) ?_ ?_ T
    · intro ω
      exact ENNReal.continuous_ofReal.comp
        (((hφ.continuous.comp ω.continuous).sub
          ((a.fn k).continuous.comp ω.continuous)).pow 2)
    · intro t
      have hev : Measurable fun ω : ContinuousPath (Vec d) => ω t :=
        ContinuousPath.measurable_coordinateProcess t
      exact ENNReal.measurable_ofReal.comp
        (((hφ.continuous.measurable.comp hev).sub
          ((a.fn k).continuous.measurable.comp hev)).pow_const 2)
  have hmeasF : Measurable fun ω : ContinuousPath (Vec d) =>
      ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
        ENNReal.ofReal ((φ (ω t) - pathLift a.fn ω t) ^ 2) := by
    refine measurable_iSup_le_of_continuous
      (F := fun (ω : ContinuousPath (Vec d)) (t : ℝ≥0) =>
        ENNReal.ofReal ((φ (ω t) - pathLift a.fn ω t) ^ 2)) ?_ ?_ T
    · intro ω
      exact ENNReal.continuous_ofReal.comp
        (((hφ.continuous.comp ω.continuous).sub (pathLift a.fn ω).continuous).pow 2)
    · intro t
      have hev : Measurable fun ω : ContinuousPath (Vec d) => ω t :=
        ContinuousPath.measurable_coordinateProcess t
      have hZ : Measurable fun ω : ContinuousPath (Vec d) => pathLift a.fn ω t :=
        (ContinuousPath.measurable_coordinateProcess (alpha := ℝ) t).comp
          (measurable_pathLift a.fn)
      exact ENNReal.measurable_ofReal.comp
        (((hφ.continuous.measurable.comp hev).sub hZ).pow_const 2)
  -- the pointwise Fatou bound on the good event
  have hpt : ∀ᵐ ω ∂(pathMeasure d),
      (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T), ENNReal.ofReal ((φ (ω t) - pathLift a.fn ω t) ^ 2))
        ≤ liminf (fun k => ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
          ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2)) atTop := by
    filter_upwards [ae_mem_goodSet hmax hU a] with ω hω
    refine iSup₂_le fun t ht => ?_
    have hconv : Tendsto (fun k => ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((φ (ω t) - pathLift a.fn ω t) ^ 2))) := by
      have h0 : Tendsto (fun k => (φ (ω t) - a.fn k (ω t)) ^ 2) atTop
          (𝓝 ((φ (ω t) - pathLift a.fn ω t) ^ 2)) :=
        ((tendsto_const_nhds (x := φ (ω t)) (f := (atTop : Filter ℕ))).sub
          (tendsto_pathLift_apply hω t)).pow 2
      exact (ENNReal.continuous_ofReal.tendsto _).comp h0
    rw [← hconv.liminf_eq]
    refine liminf_le_liminf (.of_forall fun k => ?_)
    exact le_iSup₂ (f := fun s (_ : s ≤ T) =>
      ENNReal.ofReal ((φ (ω s) - a.fn k (ω s)) ^ 2)) t ht
  have hintA : Integrable (fun x => (φ x - u.zeroExtension x) ^ 2) volume :=
    MemLp.integrable_sq ((hφ.continuous.memLp_of_hasCompactSupport (p := 2) hφc).sub
      (memLp_zeroExtension_two hU u))
  have hintB : ∀ i : Fin d, Integrable (fun x =>
      (fderiv ℝ φ x (Pi.single i 1) - u.zeroExtensionGrad x i) ^ 2) volume := fun i =>
    MemLp.integrable_sq
      (((continuous_fderiv_apply hφ i).memLp_of_hasCompactSupport (p := 2)
        (hasCompactSupport_fderiv_apply hφc i)).sub (memLp_zeroExtensionGrad_two hU u i))
  calc (∫⁻ x, ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
        ENNReal.ofReal ((φ (ω t) - pathLift a.fn ω t) ^ 2))
        ∂(laplacianContinuousLaw d x) ∂volume)
      = ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
          ENNReal.ofReal ((φ (ω t) - pathLift a.fn ω t) ^ 2)) ∂(pathMeasure d) :=
        (lintegral_pathMeasure hmeasF).symm
    _ ≤ ∫⁻ ω, liminf (fun k => ⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
          ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2)) atTop ∂(pathMeasure d) :=
        lintegral_mono_ae hpt
    _ ≤ liminf (fun k => ∫⁻ ω, (⨆ t : ℝ≥0, ⨆ (_ : t ≤ T),
          ENNReal.ofReal ((φ (ω t) - a.fn k (ω t)) ^ 2)) ∂(pathMeasure d)) atTop :=
        lintegral_liminf_le hmeasFk
    _ ≤ (32 : ℝ≥0∞) * ((eLpNorm (fun x => φ x - u.zeroExtension x) 2 volume) ^ 2
          + (T : ℝ≥0∞) * ∑ i : Fin d, (eLpNorm (fun x =>
            fderiv ℝ φ x (Pi.single i 1) - u.zeroExtensionGrad x i) 2 volume) ^ 2) :=
        liminf_le_of_le_of_tendsto
          (fun k => lintegral_iSup_sq_sub_approx_le hmax hU a hφ hφc T k)
          (tendsto_transfer_majorant _ _ T)
    _ = ENNReal.ofReal (32 * ((∫ x, (φ x - u.zeroExtension x) ^ 2) + (T : ℝ) *
          ∫ x, ∑ i : Fin d,
            (fderiv ℝ φ x (Pi.single i 1) - u.zeroExtensionGrad x i) ^ 2)) := by
        rw [ofReal_maximal_rhs (integral_nonneg fun x => sq_nonneg _)
            (integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _),
          ofReal_integral_sq_eq_eLpNorm_sq hintA,
          ofReal_integral_sum_sq_eq_sum_eLpNorm_sq hintB]
        have hf : AEStronglyMeasurable (fun x => φ x - u.zeroExtension x) volume := by
          simpa only [Pi.sub_apply] using!
            (hφ.continuous.aestronglyMeasurable.sub
              (memLp_zeroExtension_two hU u).aestronglyMeasurable)
        have hg : ∀ i : Fin d, AEStronglyMeasurable (fun x =>
            fderiv ℝ φ x (Pi.single i 1) - u.zeroExtensionGrad x i) volume := by
          intro i
          simpa only [Pi.sub_apply] using!
            ((continuous_fderiv_apply hφ i).aestronglyMeasurable.sub
              (memLp_zeroExtensionGrad_two hU u i).aestronglyMeasurable)
        rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hf]
        simp_rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded (hg _)]

end SubdiffusiveProcess.Probability.Diffusion.SobolevPathLift
