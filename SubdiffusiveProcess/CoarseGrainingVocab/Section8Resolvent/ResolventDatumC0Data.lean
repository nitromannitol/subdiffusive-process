import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumGMC
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumCaccioppoli




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ZeroAtInfty CompactlySupported

noncomputable section

variable {d : ℕ}

/-! ### Sup-norm bounds for raw decaying local solutions -/

/-- **The sup-norm contraction, for a raw pair.**  If `g ∈ C₀` solves
`μ ρ g − ∇·(c∇g) = ρ h` weakly on every centred cube, then `μ ‖g‖ ≤ ‖h‖`.
This is `MassiveC0Resolvent.norm_sol_le` with no operator in sight. -/
theorem norm_le_of_localMassiveWeakSolution {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) {mu : ℝ} (hmu : 0 < mu)
    (g h : C₀(Vec d, ℝ))
    (hloc : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      (∀ x, v.toFun x = g x) ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun x ↦ h x)) :
    ‖g‖ ≤ mu⁻¹ * ‖h‖ := by
  have hk0 : 0 ≤ mu⁻¹ * ‖h‖ := mul_nonneg (inv_nonneg.2 hmu.le) (norm_nonneg _)
  have hbound : ∀ x, |h x| ≤ mu * (mu⁻¹ * ‖h‖) := by
    intro x
    have hpoint : |h x| ≤ ‖h‖ := by
      simpa only [Real.norm_eq_abs] using
        BoundedContinuousFunction.norm_coe_le_norm
          (ZeroAtInftyContinuousMap.toBCF h) x
    have hmul : mu * (mu⁻¹ * ‖h‖) = ‖h‖ := by field_simp
    rw [hmul]
    exact hpoint
  have habs := forall_abs_le_of_localMassiveWeakSolution_of_tendsto_cocompact B
    hmu g.continuous (zero_at_infty g)
    (fun k ↦ memL2On_of_zeroAtInfty
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)) h)
    (fun k ↦ by
      obtain ⟨v, hv, hvsol⟩ := hloc k
      exact ⟨v, Filter.Eventually.of_forall fun x ↦ hv x, hvsol⟩)
    hk0 hbound
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le hk0).2 fun x ↦ ?_
  simpa only [ZeroAtInftyContinuousMap.toBCF_apply, Real.norm_eq_abs] using habs x

/-- **The contraction between two raw decaying local solutions.** -/
theorem norm_sub_le_of_localMassiveWeakSolution {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) {mu : ℝ} (hmu : 0 < mu)
    (g₁ g₂ h₁ h₂ : C₀(Vec d, ℝ))
    (hloc₁ : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      (∀ x, v.toFun x = g₁ x) ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun x ↦ h₁ x))
    (hloc₂ : ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      (∀ x, v.toFun x = g₂ x) ∧
        IsMassiveWeakSolutionOn c rho mu (cube d (k : ℤ)) v (fun x ↦ h₂ x)) :
    ‖g₁ - g₂‖ ≤ mu⁻¹ * ‖h₁ - h₂‖ := by
  refine norm_le_of_localMassiveWeakSolution B hmu (g₁ - g₂) (h₁ - h₂) fun k ↦ ?_
  obtain ⟨v₁, hv₁, hv₁sol⟩ := hloc₁ k
  obtain ⟨v₂, hv₂, hv₂sol⟩ := hloc₂ k
  have hW := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  have hs := IsMassiveWeakSolutionOn.sub (B.ell k) (B.rho_measurable k)
    (B.rho_bounded k) (memL2On_of_zeroAtInfty hW h₁) (memL2On_of_zeroAtInfty hW h₂)
    hv₁sol hv₂sol
  refine ⟨v₁ - v₂, fun x ↦ ?_, IsMassiveWeakSolutionOn.congr_forcing ?_ hs⟩
  · simp only [H1Function.sub_toFun, hv₁, hv₂]
    rfl
  · funext x
    simp

/-! ### The spatial truncation -/

/-- The smooth cutoff of `exists_smooth_cube_cutoff`, chosen once: it equals `1`
on `cube d j` and vanishes off `cube d (j+1)`. -/
def cubeCutoff (d j : ℕ) : Vec d → ℝ :=
  Classical.choose (exists_smooth_cube_cutoff d j)

theorem cubeCutoff_contDiff (d j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeCutoff d j) :=
  (Classical.choose_spec (exists_smooth_cube_cutoff d j)).1

theorem cubeCutoff_abs_le (d j : ℕ) (x : Vec d) : |cubeCutoff d j x| ≤ 1 :=
  (Classical.choose_spec (exists_smooth_cube_cutoff d j)).2.1 x

theorem cubeCutoff_eq_one {d j : ℕ} {x : Vec d} (hx : x ∈ cube d (j : ℤ)) :
    cubeCutoff d j x = 1 :=
  (Classical.choose_spec (exists_smooth_cube_cutoff d j)).2.2.1 x hx

theorem cubeCutoff_hasCompactSupport (d j : ℕ) :
    HasCompactSupport (cubeCutoff d j) :=
  (Classical.choose_spec (exists_smooth_cube_cutoff d j)).2.2.2.1

/-- **The spatial truncation of a datum vanishing at infinity.**  It is
compactly supported and agrees with `f` on `cube d j`. -/
def cubeTruncation (f : C₀(Vec d, ℝ)) (j : ℕ) : C_c(Vec d, ℝ) where
  toFun := fun x ↦ f x * cubeCutoff d j x
  continuous_toFun := f.continuous.mul (cubeCutoff_contDiff d j).continuous
  hasCompactSupport' := by
    refine HasCompactSupport.intro (cubeCutoff_hasCompactSupport d j).isCompact
      fun x hx ↦ ?_
    have hzero : cubeCutoff d j x = 0 := by
      by_contra hne
      exact hx (subset_closure hne)
    simp [hzero]

@[simp]
theorem cubeTruncation_apply (f : C₀(Vec d, ℝ)) (j : ℕ) (x : Vec d) :
    cubeTruncation f j x = f x * cubeCutoff d j x := rfl

/-- On every cube of the exhaustion up to level `j`, the truncated datum *is*
the datum.  This is what makes the local weak equations of the approximating
solutions carry the unchanged forcing. -/
theorem cubeTruncation_eq_of_mem (f : C₀(Vec d, ℝ)) {m j : ℕ} (hmj : m ≤ j)
    {x : Vec d} (hx : x ∈ cube d (m : ℤ)) : cubeTruncation f j x = f x := by
  have hsub : cube d (m : ℤ) ⊆ cube d (j : ℤ) :=
    Section6ExcessDecay.cube_subset_cube_of_le (by exact_mod_cast hmj)
  rw [cubeTruncation_apply, cubeCutoff_eq_one (hsub hx), mul_one]

/-- The truncations converge to the datum uniformly. -/
theorem tendsto_cubeTruncation (f : C₀(Vec d, ℝ)) :
    Tendsto (fun j ↦ compactSupportToC0 (cubeTruncation f j)) atTop (nhds f) := by
  refine Metric.tendsto_atTop.2 fun eps heps ↦ ?_
  set eps' : ℝ := eps / 3 with heps'_def
  have heps' : 0 < eps' := by positivity
  have hnear : {t : ℝ | |t| < eps'} ∈ nhds (0 : ℝ) := by
    simpa only [abs_lt] using Ioo_mem_nhds (neg_lt_zero.mpr heps') heps'
  obtain ⟨K, hKcompact, hK⟩ :=
    mem_cocompact.mp (tendsto_def.mp (zero_at_infty f) _ hnear)
  obtain ⟨J, hJ⟩ := exists_nat_cube_superset hKcompact.isBounded
  refine ⟨J, fun j hj ↦ ?_⟩
  have hsub : cube d (J : ℤ) ⊆ cube d (j : ℤ) :=
    Section6ExcessDecay.cube_subset_cube_of_le (by exact_mod_cast hj)
  have hnorm : ‖compactSupportToC0 (cubeTruncation f j) - f‖ ≤ 2 * eps' := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ ?_
    simp only [ZeroAtInftyContinuousMap.toBCF_apply,
      ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, compactSupportToC0_apply,
      cubeTruncation_apply, Real.norm_eq_abs]
    by_cases hx : x ∈ cube d (j : ℤ)
    · rw [cubeCutoff_eq_one hx, mul_one, sub_self, abs_zero]
      positivity
    · have hxK : x ∉ K := fun hxK ↦ hx (hsub (hJ hxK))
      have hfx : |f x| < eps' := hK hxK
      have hchi : |cubeCutoff d j x - 1| ≤ 2 := by
        have := cubeCutoff_abs_le d j x
        rw [abs_le] at this ⊢
        constructor <;> linarith [this.1, this.2]
      calc |f x * cubeCutoff d j x - f x| = |f x| * |cubeCutoff d j x - 1| := by
            rw [← abs_mul]
            congr 1
            ring
        _ ≤ eps' * 2 := by
            refine mul_le_mul hfx.le hchi (abs_nonneg _) heps'.le
        _ = 2 * eps' := by ring
  have : dist (compactSupportToC0 (cubeTruncation f j)) f ≤ 2 * eps' := by
    rw [dist_eq_norm]
    exact hnorm
  calc dist (compactSupportToC0 (cubeTruncation f j)) f ≤ 2 * eps' := this
    _ < eps := by rw [heps'_def]; linarith

/-! ### Changing the forcing inside the domain only -/

/-- The weak equation only sees the forcing on `W`. -/
theorem IsMassiveWeakSolutionOn.congr_forcing_on {c rho : Vec d → ℝ}
    {W : Set (Vec d)} (hWmeas : MeasurableSet W) {mu : ℝ} {u : H1Function W}
    {f g : Vec d → ℝ} (h : ∀ x ∈ W, f x = g x)
    (hu : IsMassiveWeakSolutionOn c rho mu W u f) :
    IsMassiveWeakSolutionOn c rho mu W u g := by
  intro φ
  have hEq := hu φ
  have hr : (∫ x in W, rho x * f x * φ.toH1Function.toFun x ∂volume) =
      ∫ x in W, rho x * g x * φ.toH1Function.toFun x ∂volume := by
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    rw [h x hx]
  rw [← hr]
  exact hEq

/-! ### The `C₀` datum instance -/

/-- **The obligation `HasC0MassiveSolutions`, for data vanishing at infinity.**
Given `C₀` solutions for compactly supported data, every `f ∈ C₀` has a `C₀`
whole-space massive solution with the exact local representatives the
resolvent datum asks for.

The compact-support restriction is removed by the spatial truncation `f · χⱼ`,
whose local weak equations carry the unchanged forcing on the cubes below level
`j`, together with the Caccioppoli gradient bound
`exists_uniform_cube_gradient_bound`, which is uniform along the truncation
sequence precisely because it does not see the forcing outside the cube. -/
theorem exists_c0MassiveSolution_of_zeroAtInfty [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {rho : Vec d → ℝ} (B : MassiveCubeBounds (coefficientAt M L omega) rho)
    (hsolve : HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega) rho)
    {mu : ℝ} (hmu : 0 < mu) (f : C₀(Vec d, ℝ)) :
    ∃ g : C₀(Vec d, ℝ), ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      (∀ x, v.toFun x = g x) ∧
        IsMassiveWeakSolutionOn (coefficientAt M L omega) rho mu
          (cube d (k : ℤ)) v (fun x ↦ f x) := by
  classical
  -- the solutions of the truncated data
  choose G hG using fun j : ℕ ↦ hsolve mu hmu (cubeTruncation f j)
  have hGloc : ∀ j : ℕ, ∀ k : ℕ, ∃ v : H1Function (cube d (k : ℤ)),
      (∀ x, v.toFun x = G j x) ∧
        IsMassiveWeakSolutionOn (coefficientAt M L omega) rho mu
          (cube d (k : ℤ)) v
          (fun x ↦ (compactSupportToC0 (cubeTruncation f j)) x) := fun j k ↦ hG j k
  -- the truncated data are dominated by the datum
  have htrunc_norm : ∀ j : ℕ, ‖compactSupportToC0 (cubeTruncation f j)‖ ≤ ‖f‖ := by
    intro j
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x ↦ ?_
    simp only [ZeroAtInftyContinuousMap.toBCF_apply, compactSupportToC0_apply,
      cubeTruncation_apply, Real.norm_eq_abs, abs_mul]
    have h1 : |f x| ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs] using
        BoundedContinuousFunction.norm_coe_le_norm
          (ZeroAtInftyContinuousMap.toBCF f) x
    have h2 := cubeCutoff_abs_le d j x
    nlinarith [abs_nonneg (f x), abs_nonneg (cubeCutoff d j x)]
  have hGnorm : ∀ j : ℕ, ‖G j‖ ≤ mu⁻¹ * ‖f‖ := by
    intro j
    have h := norm_le_of_localMassiveWeakSolution B hmu (G j)
      (compactSupportToC0 (cubeTruncation f j)) (hGloc j)
    have hmono : mu⁻¹ * ‖compactSupportToC0 (cubeTruncation f j)‖ ≤ mu⁻¹ * ‖f‖ :=
      mul_le_mul_of_nonneg_left (htrunc_norm j) (inv_nonneg.2 hmu.le)
    exact h.trans hmono
  have hGpoint : ∀ (j : ℕ) (x : Vec d), |G j x| ≤ mu⁻¹ * ‖f‖ := by
    intro j x
    have h1 : |G j x| ≤ ‖G j‖ := by
      simpa only [Real.norm_eq_abs] using
        BoundedContinuousFunction.norm_coe_le_norm
          (ZeroAtInftyContinuousMap.toBCF (G j)) x
    exact h1.trans (hGnorm j)
  -- the sequence of solutions is Cauchy
  have hdata : CauchySeq (fun j ↦ compactSupportToC0 (cubeTruncation f j)) :=
    (tendsto_cubeTruncation f).cauchySeq
  have hCauchy : CauchySeq G := by
    refine Metric.cauchySeq_iff.2 fun eps heps ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hdata (mu * eps) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h1 := hN m hm n hn
    have h2 := norm_sub_le_of_localMassiveWeakSolution B hmu (G m) (G n)
      (compactSupportToC0 (cubeTruncation f m))
      (compactSupportToC0 (cubeTruncation f n)) (hGloc m) (hGloc n)
    rw [dist_eq_norm] at h1 ⊢
    calc ‖G m - G n‖ ≤ mu⁻¹ * ‖compactSupportToC0 (cubeTruncation f m) -
            compactSupportToC0 (cubeTruncation f n)‖ := h2
      _ < mu⁻¹ * (mu * eps) := by
          exact mul_lt_mul_of_pos_left h1 (inv_pos.2 hmu)
      _ = eps := by field_simp
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hgpoint : ∀ x : Vec d, Tendsto (fun j ↦ G j x) atTop (nhds (g x)) := by
    intro x
    refine Metric.tendsto_atTop.2 fun eps heps ↦ ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hg eps heps
    refine ⟨N, fun j hj ↦ ?_⟩
    have h := hN j hj
    rw [dist_eq_norm] at h ⊢
    have hpt : ‖G j x - g x‖ ≤ ‖G j - g‖ := by
      simpa only [ZeroAtInftyContinuousMap.toBCF_apply,
        ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply,
        ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using
        BoundedContinuousFunction.norm_coe_le_norm
          (ZeroAtInftyContinuousMap.toBCF (G j - g)) x
    exact lt_of_le_of_lt hpt h
  refine ⟨g, fun k ↦ ?_⟩
  -- the local weak equation on `cube d k`, from the outer cube `cube d (k+1)`
  set Q : Set (Vec d) := cube d (k : ℤ) with hQdef
  have hQ := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)
  have hWbig := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d ((k + 1 : ℕ) : ℤ)
  have hQW : cube d (k : ℤ) ⊆ cube d ((k + 1 : ℕ) : ℤ) :=
    Section6ExcessDecay.cube_subset_cube_of_le (by omega)
  letI : IsFiniteMeasure (volumeMeasureOn (cube d (k : ℤ))) :=
    hQ.isBoundedDomain.isFiniteMeasure_restrict_volume
  choose V hV1 hV2 using fun n : ℕ ↦ hG (k + 1 + n) (k + 1)
  have hVsol : ∀ n : ℕ, IsMassiveWeakSolutionOn (coefficientAt M L omega) rho mu
      (cube d ((k + 1 : ℕ) : ℤ)) (V n) (fun x ↦ f x) := by
    intro n
    refine IsMassiveWeakSolutionOn.congr_forcing_on hWbig.isOpen.measurableSet
      (fun x hx ↦ ?_) (hV2 n)
    exact cubeTruncation_eq_of_mem f (by omega) hx
  have hVbound : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (cube d ((k + 1 : ℕ) : ℤ))),
      |(V n).toFun x| ≤ mu⁻¹ * ‖f‖ := by
    intro n
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [hV1 n x]
    exact hGpoint (k + 1 + n) x
  obtain ⟨Cgrad, hCgrad0, hCgrad⟩ :=
    exists_uniform_cube_gradient_bound B hmu.le k (fun x ↦ f x) (mu⁻¹ * ‖f‖)
  set w : ℕ → H1Function (cube d (k : ℤ)) :=
    fun n ↦ (V n).restrict hQ.isOpen hQW with hw_def
  have hwsol : ∀ n, IsMassiveWeakSolutionOn (coefficientAt M L omega) rho mu
      (cube d (k : ℤ)) (w n) (fun x ↦ f x) := fun n ↦
    IsMassiveWeakSolutionOn.restrict hQ.isOpen hWbig.isOpen hQW (hVsol n)
  have hwbound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      |(w n).toFun x| ≤ mu⁻¹ * ‖f‖ :=
    fun n ↦ (hVbound n).filter_mono (ae_mono (Measure.restrict_mono hQW le_rfl))
  have hwgrad : ∀ n, ‖(w n).gradToHilbertVectorL2‖ ≤ Cgrad := fun n ↦
    hCgrad (V n) hQ.isOpen hQW (memL2On_of_zeroAtInfty hWbig f) (hVsol n) (hVbound n)
  have hwpoint : ∀ᵐ x ∂(volumeMeasureOn (cube d (k : ℤ))),
      Tendsto (fun n ↦ (w n).toFun x) atTop (nhds (g x)) := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have hshift : Tendsto (fun n ↦ G (k + 1 + n) x) atTop (nhds (g x)) := by
      simpa only [Function.comp_apply] using
        (hgpoint x).comp (strictMono_id.const_add (k + 1)).tendsto_atTop
    refine hshift.congr fun n ↦ ?_
    simp only [hw_def, H1Function.restrict]
    exact (hV1 n x).symm
  obtain ⟨v, hvae, hvsol⟩ :=
    exists_isMassiveWeakSolutionOn_of_bounded_pointwise_limit (B.ell k)
      (B.rho_measurable k) (B.rho_bounded k)
      (memL2On_of_zeroAtInfty hQ f) w hwbound hwpoint hwgrad hwsol
  refine ⟨H1Function.ofAEEq v (fun x ↦ g x) hvae.symm, fun x ↦ rfl, ?_⟩
  exact IsMassiveWeakSolutionOn.congr (u := v) hvae
    (Filter.Eventually.of_forall fun _ ↦ rfl) hvsol

/-! ### The first obligation from compactly supported data -/

/-- **`HasC0MassiveSolutions` follows from solvability on compactly supported
data.**  With the Caccioppoli estimate in hand, the exhaustion for `C₀` data is
not a separate analytic input. -/
theorem hasC0MassiveSolutions_of_hasC0MassiveSolutionsOnCompactData [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : WithTop ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d)
    {rho : Vec d → ℝ} (B : MassiveCubeBounds (coefficientAt M L omega) rho)
    (hsolve : HasC0MassiveSolutionsOnCompactData (coefficientAt M L omega) rho) :
    HasC0MassiveSolutions (coefficientAt M L omega) rho :=
  fun mu f ↦ exists_c0MassiveSolution_of_zeroAtInfty M L omega B hsolve mu.2 f

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
