module

public import SubdiffusiveProcess.Probability.Diffusion.Packet452IntegrationByParts

@[expose] public section

/-!
# P-452 seed (i): `∫ φ·Δφ = −E(φ)` on `Vec d`

`ledger/reports/P-452-agent1.md` §2.2, completing `Packet452IntegrationByParts.lean`.

**The Fubini step is avoided entirely.**  The plan (and the dispatch) expected the `d`-dimensional
identity to come from `MeasurableEquiv.piFinSuccAbove` / `Measure.pi` with the `i`-th coordinate
innermost.  It does not need to: `integral_partial_eq_zero` proves `∫_{Vec d} ∂ᵢg = 0` for
compactly supported `C¹` `g` from **translation invariance** of `volume` on `Vec d` plus dominated
convergence along the difference quotients in the `i`-th direction.  Each quotient integrates to
exactly zero because `∫ g(x + h eᵢ) dx = ∫ g(x) dx`; the mean value theorem bounds them uniformly
by `‖fderiv g‖_∞`, and all of them are supported in the compact `1`-thickening of `tsupport g`, so
the dominating function is a constant on a set of finite measure.  No measure decomposition, no
`piFinSuccAbove`, no iterated-integral bookkeeping.

* `norm_pi_single`, `smul_pi_single` — the sup norm of a one-coordinate vector, and `c • eᵢ = Pi.single i c`.
* `integral_partial_eq_zero` — the statement above.
* `hasFDerivAt_partial` — the second derivative along one coordinate, as a Fréchet derivative of
  the partial, through `ContinuousLinearMap.apply`.
* **`integral_mul_fullLaplacian`** — `∫ φ · fullLaplacian φ = −∫ energyDensity φ` for `φ ∈ C_c²`,
  by summing `∫ ∂ᵢ(φ ∂ᵢφ) = 0` over the coordinates.

With this, the first of the two analytic inputs the stationary expansion needs is closed; the
remaining one is the `L²` continuity of `r ↦ ⟨φ, P_r φ⟩`.
-/

set_option autoImplicit false
open MeasureTheory Set Function Homogenization Filter
open scoped Topology
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

theorem norm_pi_single (i : Fin d) (c : ℝ) : ‖(Pi.single i c : Vec d)‖ = |c| := by
  classical
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg c)).mpr fun j => ?_) ?_
  · rw [Real.norm_eq_abs, Pi.single_apply]
    split_ifs with hj
    · exact le_rfl
    · simp
  · have := norm_le_pi_norm (Pi.single i c : Vec d) i
    rwa [Real.norm_eq_abs, Pi.single_eq_same] at this

theorem smul_pi_single (i : Fin d) (c : ℝ) :
    c • (Pi.single i (1 : ℝ) : Vec d) = Pi.single i c := by
  classical
  funext j
  simp [Pi.single_apply]

/-- **The integral of a partial derivative of a compactly supported `C¹` function vanishes.**
No decomposition of the measure is used: translation invariance of `volume` on `Vec d` kills each
difference quotient exactly, and dominated convergence passes to the limit.  This replaces the
`Measure.pi` / `piFinSuccAbove` bookkeeping entirely. -/
theorem integral_partial_eq_zero {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g)
    (hsupp : HasCompactSupport g) (i : Fin d) :
    ∫ x : Vec d, fderiv ℝ g x (Pi.single i (1 : ℝ)) = 0 := by
  classical
  set v : Vec d := Pi.single i (1 : ℝ) with hv
  have hvnorm : ‖v‖ = 1 := by rw [hv, norm_pi_single]; simp
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  obtain ⟨M, hM⟩ := (hg.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hsupp.fderiv ℝ)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  set c : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ with hc
  have hcpos : ∀ n, 0 < c n := fun n => by rw [hc]; positivity
  have hcle : ∀ n, c n ≤ 1 := by
    intro n
    rw [hc]
    have h1 : (1:ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    simpa using inv_le_one_of_one_le₀ h1
  set F : ℕ → Vec d → ℝ := fun n x => (g (x + c n • v) - g x) / c n with hF
  have hgint : Integrable g (volume : Measure (Vec d)) :=
    hg.continuous.integrable_of_hasCompactSupport hsupp
  -- each difference quotient integrates to zero
  have hFint : ∀ n, ∫ x : Vec d, F n x = 0 := by
    intro n
    have hshift : ∫ x : Vec d, g (x + c n • v) = ∫ x : Vec d, g x :=
      integral_add_right_eq_self (μ := (volume : Measure (Vec d))) g _
    have hgint' : Integrable (fun x : Vec d => g (x + c n • v)) (volume : Measure (Vec d)) :=
      hgint.comp_add_right (c n • v)
    rw [hF]
    simp only [div_eq_mul_inv]
    rw [integral_mul_const, integral_sub hgint' hgint, hshift, sub_self, zero_mul]
  -- the uniform bound
  have hbound : ∀ n, ∀ x : Vec d, ‖F n x‖ ≤ M := by
    intro n x
    have hseg := (convex_univ (𝕜 := ℝ) (E := Vec d)).norm_image_sub_le_of_norm_fderiv_le
      (f := g) (C := M) (fun y _ => hdiff y) (fun y _ => hM y) (mem_univ x)
      (mem_univ (x + c n • v))
    have hnorm : ‖(x + c n • v) - x‖ = c n := by
      rw [add_sub_cancel_left, norm_smul, hvnorm, mul_one, Real.norm_eq_abs,
        abs_of_pos (hcpos n)]
    rw [hnorm] at hseg
    rw [hF]
    simp only [Real.norm_eq_abs, abs_div, abs_of_pos (hcpos n)]
    rw [div_le_iff₀ (hcpos n)]
    rw [← Real.norm_eq_abs]
    exact hseg
  -- the common compact support
  set K : Set (Vec d) := Metric.cthickening 1 (tsupport g) with hK
  have hKcompact : IsCompact K := IsCompact.cthickening (r := (1:ℝ)) hsupp
  have hFsupp : ∀ n, ∀ x : Vec d, x ∉ K → F n x = 0 := by
    intro n x hxK
    have h1 : x ∉ tsupport g := fun h => hxK (Metric.self_subset_cthickening _ h)
    have h2 : x + c n • v ∉ tsupport g := by
      intro h
      refine hxK ?_
      refine Metric.mem_cthickening_of_dist_le x (x + c n • v) 1 (tsupport g) h ?_
      rw [dist_eq_norm, ← neg_sub, norm_neg, add_sub_cancel_left, norm_smul, hvnorm, mul_one,
        Real.norm_eq_abs, abs_of_pos (hcpos n)]
      exact hcle n
    rw [hF]
    simp only
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2, sub_self,
      zero_div]
  have hKvol : volume K ≠ ⊤ := hKcompact.measure_lt_top.ne
  have hdomint : Integrable (K.indicator fun _ : Vec d => M) (volume : Measure (Vec d)) := by
    rw [integrable_indicator_iff hKcompact.isClosed.measurableSet]
    exact integrableOn_const hKvol
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) (volume : Measure (Vec d)) := by
    intro n
    refine Continuous.aestronglyMeasurable ?_
    rw [hF]
    exact ((hg.continuous.comp (by fun_prop)).sub hg.continuous).div_const _
  have hFdom : ∀ n, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ‖F n x‖ ≤ K.indicator (fun _ : Vec d => M) x := by
    intro n
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      exact hbound n x
    · rw [Set.indicator_of_notMem hx, hFsupp n x hx, norm_zero]
  have hlim : ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun n => F n x) atTop (𝓝 (fderiv ℝ g x v)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
    have hD : HasDerivAt (fun t : ℝ => g (x + t • v)) (fderiv ℝ g x v) 0 := by
      have h := ((hdiff (x + (0:ℝ) • v)).hasFDerivAt).comp_hasDerivAt 0 hline
      simpa [Function.comp_def] using h
    have hslope := hasDerivAt_iff_tendsto_slope.mp hD
    have hctend : Tendsto c atTop (𝓝[≠] (0:ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · rw [hc]
        exact tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by rw [one_div]
      · exact (hcpos n).ne'
    have := hslope.comp hctend
    refine this.congr fun n => ?_
    rw [hF]
    simp only [Function.comp_apply, slope_def_field, sub_zero, zero_smul, add_zero]
  have hconv := tendsto_integral_of_dominated_convergence
    (bound := K.indicator fun _ : Vec d => M) hFmeas hdomint hFdom hlim
  have hzero : Tendsto (fun n : ℕ => (0:ℝ)) atTop (𝓝 (∫ x : Vec d, fderiv ℝ g x v)) := by
    simpa only [hFint] using hconv
  exact tendsto_nhds_unique hzero tendsto_const_nhds

/-! ## The `d`-dimensional integration-by-parts identity -/

/-- The second derivative along one coordinate, as a Fréchet derivative of the partial. -/
theorem hasFDerivAt_partial {φ : Vec d → ℝ} (hφ : ContDiff ℝ 2 φ) (i : Fin d) (x : Vec d) :
    HasFDerivAt (fun y : Vec d => fderiv ℝ φ y (Pi.single i (1 : ℝ)))
      ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))).comp
        (fderiv ℝ (fderiv ℝ φ) x)) x := by
  have hfd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  exact (ContinuousLinearMap.apply ℝ ℝ
    (Pi.single i (1 : ℝ))).hasFDerivAt.comp x (hfd x).hasFDerivAt

/-- **Integration by parts on `Vec d`: `∫ φ Δφ = -E(φ)`.**  Summing the one-coordinate identity
`∫ ∂ᵢ(φ ∂ᵢφ) = 0`, which is `integral_partial_eq_zero` applied to `φ ∂ᵢφ`. -/
theorem integral_mul_fullLaplacian {φ : Vec d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : HasCompactSupport φ) :
    ∫ x : Vec d, φ x * fullLaplacian φ x = - ∫ x : Vec d, energyDensity φ x := by
  classical
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hfd1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  set e : Fin d → Vec d := fun i => Pi.single i (1 : ℝ) with he
  set P : Fin d → Vec d → ℝ := fun i x => fderiv ℝ φ x (e i) with hP
  set Q : Fin d → Vec d → ℝ := fun i x => fderiv ℝ (fderiv ℝ φ) x (e i) (e i) with hQ
  have hPC1 : ∀ i, ContDiff ℝ 1 (P i) := fun i =>
    (ContinuousLinearMap.apply ℝ ℝ (e i)).contDiff.comp hfd1
  have hPcont : ∀ i, Continuous (P i) := fun i => (hPC1 i).continuous
  have hQcont : ∀ i, Continuous (Q i) := fun i =>
    ((hfd1.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const
  have hPsupp : ∀ i, HasCompactSupport (P i) := by
    intro i
    refine HasCompactSupport.intro (hsupp.fderiv ℝ) fun y hy => ?_
    rw [hP]
    simp only
    rw [image_eq_zero_of_notMem_tsupport hy]
    simp
  -- the one-coordinate identity
  have hone : ∀ i : Fin d, ∫ x : Vec d, (φ x * Q i x + (P i x) ^ 2) = 0 := by
    intro i
    have hgC1 : ContDiff ℝ 1 (fun x : Vec d => φ x * P i x) := hφ1.mul (hPC1 i)
    have hgsupp : HasCompactSupport (fun x : Vec d => φ x * P i x) := hsupp.mul_right
    have hzero := integral_partial_eq_zero hgC1 hgsupp i
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)) hzero
    have hprod := ((hφ1.differentiable one_ne_zero x).hasFDerivAt).fun_mul
      (hasFDerivAt_partial hφ i x)
    show φ x * Q i x + (P i x) ^ 2 = fderiv ℝ (fun y : Vec d => φ y * P i y) x (e i)
    rw [hprod.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul, hQ, hP]
    ring
  have hint1 : ∀ i : Fin d, Integrable (fun x : Vec d => φ x * Q i x)
      (volume : Measure (Vec d)) :=
    fun i => (hφ.continuous.mul (hQcont i)).integrable_of_hasCompactSupport hsupp.mul_right
  have hint2 : ∀ i : Fin d, Integrable (fun x : Vec d => (P i x) ^ 2)
      (volume : Measure (Vec d)) :=
    fun i => ((hPcont i).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (hPsupp i) fun y hy => by
        simp only [Pi.pow_apply]
        rw [image_eq_zero_of_notMem_tsupport hy]; simp)
  have hsum : ∀ i : Fin d,
      (∫ x : Vec d, φ x * Q i x) + ∫ x : Vec d, (P i x) ^ 2 = 0 := by
    intro i
    rw [← integral_add (hint1 i) (hint2 i)]
    exact hone i
  have hL : ∫ x : Vec d, φ x * fullLaplacian φ x = ∑ i : Fin d, ∫ x : Vec d, φ x * Q i x := by
    rw [← integral_finset_sum _ fun i _ => hint1 i]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show φ x * (∑ i : Fin d, iteratedFDeriv ℝ 2 φ x ![e i, e i]) = ∑ i : Fin d, φ x * Q i x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [iteratedFDeriv_two_eq_bilin]
  have hE : ∫ x : Vec d, energyDensity φ x = ∑ i : Fin d, ∫ x : Vec d, (P i x) ^ 2 := by
    rw [← integral_finset_sum _ fun i _ => hint2 i]
    rfl
  rw [hL, hE, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by linarith [hsum i]

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
