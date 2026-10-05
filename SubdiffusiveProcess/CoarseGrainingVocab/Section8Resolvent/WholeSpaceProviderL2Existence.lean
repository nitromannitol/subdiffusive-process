module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceProviderL2Data

@[expose] public section

/-!
# The whole-space carrier as an `L²` limit

The compact-data construction of `WholeSpaceDecayFiniteCutoff` produces the
frozen carrier only for continuous compactly supported data.  The frozen
whole-space resolvent statement quantifies an arbitrary `L²`
datum supported in the source ball.

This file closes that gap.  Its main theorem assembles the frozen carrier from
`L²` limits of value, coefficient-weighted gradient, and datum: the local
Sobolev certificate on a bounded open convex domain passes to the limit by
Cauchy--Schwarz in the two Hilbert norms, using the two-sided coefficient
bounds available on every bounded set.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Set Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Section8
open scoped BigOperators

noncomputable section

variable {d : ℕ} {a : Vec d → ℝ}

/-! ### Division by the square root of the coefficient -/

/-- Dividing an `L²` function by `sqrt a` keeps it in `L²` of any bounded set
on which the coefficient is bounded below. -/
theorem memLp_div_sqrt_of_le_on (hcont : Continuous a) (hpos : ∀ x, 0 < a x)
    {W : Set (Vec d)} (hWmeas : MeasurableSet W) {lam : ℝ} (hlam : 0 < lam)
    (hlow : ∀ x ∈ W, lam ≤ a x) {H : Vec d → ℝ}
    (hH : MemLp H 2 (volume.restrict W)) :
    MemLp (fun x ↦ H x / Real.sqrt (a x)) 2 (volume.restrict W) := by
  have hsqrtpos : ∀ x, 0 < Real.sqrt (a x) := fun x ↦ Real.sqrt_pos.2 (hpos x)
  have hden : Continuous (fun x ↦ (Real.sqrt (a x))⁻¹) :=
    (Real.continuous_sqrt.comp hcont).inv₀ fun x ↦ (hsqrtpos x).ne'
  have hmeas : AEStronglyMeasurable (fun x ↦ H x / Real.sqrt (a x))
      (volume.restrict W) := by
    simp only [div_eq_mul_inv]
    exact hH.aestronglyMeasurable.mul hden.aestronglyMeasurable
  have hlampos : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  refine hH.of_le_mul (c := (Real.sqrt lam)⁻¹) hmeas ?_
  filter_upwards [ae_restrict_mem hWmeas] with x hx
  have hlamx : Real.sqrt lam ≤ Real.sqrt (a x) := Real.sqrt_le_sqrt (hlow x hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
    abs_of_pos (hsqrtpos x), div_le_iff₀ (hsqrtpos x)]
  have hstep : (Real.sqrt lam)⁻¹ * |H x| * Real.sqrt lam ≤
      (Real.sqrt lam)⁻¹ * |H x| * Real.sqrt (a x) :=
    mul_le_mul_of_nonneg_left hlamx (by positivity)
  have hid : (Real.sqrt lam)⁻¹ * |H x| * Real.sqrt lam = |H x| := by
    field_simp
  linarith [hstep, hid.symm.le, hid.le]

/-- The `L²` norm of `H / sqrt a` on a set where `a ≥ lam > 0` is controlled by
the global `L²` norm of `H`. -/
theorem integral_sq_div_sqrt_le (hpos : ∀ x, 0 < a x)
    {W : Set (Vec d)} (hWmeas : MeasurableSet W) {lam : ℝ} (hlam : 0 < lam)
    (hlow : ∀ x ∈ W, lam ≤ a x) {H : Vec d → ℝ} (hH : MemLp H 2 volume)
    (hdiv : MemLp (fun x ↦ H x / Real.sqrt (a x)) 2 (volume.restrict W)) :
    ∫ x in W, (H x / Real.sqrt (a x)) ^ 2 ∂volume ≤
      lam⁻¹ * ∫ x, H x ^ 2 ∂volume := by
  have hHsq : Integrable (fun x ↦ H x ^ 2) volume := hH.integrable_sq
  have hstep : ∫ x in W, (H x / Real.sqrt (a x)) ^ 2 ∂volume ≤
      ∫ x in W, lam⁻¹ * H x ^ 2 ∂volume := by
    refine setIntegral_mono_on hdiv.integrable_sq
      ((hHsq.restrict (s := W)).const_mul lam⁻¹) hWmeas fun x hx ↦ ?_
    have hax : 0 < a x := hpos x
    have hsq : (H x / Real.sqrt (a x)) ^ 2 = H x ^ 2 / a x := by
      rw [div_pow, Real.sq_sqrt hax.le]
    rw [hsq, div_le_iff₀ hax]
    have hlamx : lam ≤ a x := hlow x hx
    have : lam⁻¹ * H x ^ 2 * lam ≤ lam⁻¹ * H x ^ 2 * a x :=
      mul_le_mul_of_nonneg_left hlamx (by positivity)
    calc H x ^ 2 = lam⁻¹ * H x ^ 2 * lam := by field_simp
      _ ≤ lam⁻¹ * H x ^ 2 * a x := this
  refine hstep.trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact setIntegral_le_integral hHsq
    (Filter.Eventually.of_forall fun x ↦ sq_nonneg _)

/-- Restricting an `L²` convergence to a subset. -/
theorem tendsto_setIntegral_sq_sub_of_tendsto {W : Set (Vec d)}
    {p : ℕ → Vec d → ℝ} {P : Vec d → ℝ}
    (hp : ∀ n, MemLp (p n) 2 volume) (hP : MemLp P 2 volume)
    (hconv : Tendsto (fun n ↦ ∫ x, (p n x - P x) ^ 2 ∂volume) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x in W, (p n x - P x) ^ 2 ∂volume) atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ integral_nonneg fun x ↦ sq_nonneg _)
    (fun n ↦ ?_) hconv
  exact setIntegral_le_integral (((hp n).sub hP).integrable_sq)
    (Filter.Eventually.of_forall fun x ↦ sq_nonneg _)


/-! ### The carrier as an `L²` limit -/

/-- **The frozen whole-space carrier assembled from `L²` limits.**

If a sequence of value/gradient/datum triples satisfies the local weak
certificates of the frozen carrier and converges in the unweighted `L²` norm
of the value, the coefficient-weighted `L²` norm of the gradient, and the
unweighted `L²` norm of the datum, then the limits again form a frozen
carrier.

-/
theorem exists_wholeSpaceSolution_of_l2_limits
    (hcont : Continuous a) (hpos : ∀ x, 0 < a x) {t : ℝ}
    {fn un : ℕ → Vec d → ℝ} {Gn : ℕ → Vec d → Vec d}
    {f V : Vec d → ℝ} {Gl : Fin d → Vec d → ℝ}
    (hfn : ∀ n, MemLp (fn n) 2 volume)
    (hun : ∀ n, MemLp (un n) 2 volume)
    (hGn : ∀ n i, MemLp (fun x ↦ Real.sqrt (a x) * Gn n x i) 2 volume)
    (hfmem : MemLp f 2 volume) (hVmem : MemLp V 2 volume)
    (hGlmem : ∀ i, MemLp (Gl i) 2 volume)
    (hweak : ∀ (n : ℕ) (W : Set (Vec d)), IsOpenBoundedConvexDomain W →
      ∀ i : Fin d, HasWeakPartialDerivOn W i (un n) (fun x ↦ Gn n x i))
    (hmassive : ∀ (n : ℕ) (W : Set (Vec d)), IsOpenBoundedConvexDomain W →
      ∀ φ : H10Function W,
        t⁻¹ * ∫ x in W, un n x * φ.toH1Function.toFun x ∂volume +
            ∫ x in W, vecDot (a x • Gn n x) (φ.toH1Function.grad x) ∂volume =
          ∫ x in W, t⁻¹ * fn n x * φ.toH1Function.toFun x ∂volume)
    (hconvF : Tendsto (fun n ↦ ∫ x, (fn n x - f x) ^ 2 ∂volume) atTop (𝓝 0))
    (hconvU : Tendsto (fun n ↦ ∫ x, (un n x - V x) ^ 2 ∂volume) atTop (𝓝 0))
    (hconvG : ∀ i, Tendsto
      (fun n ↦ ∫ x, (Real.sqrt (a x) * Gn n x i - Gl i x) ^ 2 ∂volume)
        atTop (𝓝 0)) :
    ∃ u : WholeSpaceDivergenceResolventSolution a t f,
      u.toFun = V ∧ ∀ x i, Real.sqrt (a x) * u.grad x i = Gl i x := by
  classical
  have hnonneg : ∀ x, 0 ≤ a x := fun x ↦ (hpos x).le
  have hsqrtpos : ∀ x, 0 < Real.sqrt (a x) := fun x ↦ Real.sqrt_pos.2 (hpos x)
  refine ⟨{ toFun := V
            grad := fun x i ↦ Gl i x / Real.sqrt (a x)
            memL2_toFun := hVmem
            integrable_energy := ?_
            locally_weak_solution := ?_ }, rfl, ?_⟩
  · have hsum : Integrable (fun x ↦ ∑ i, Gl i x ^ 2) volume :=
      integrable_finsetSum Finset.univ fun i _ ↦ (hGlmem i).integrable_sq
    refine hsum.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    show (∑ i, Gl i x ^ 2) =
      a x * vecNormSq (fun i ↦ Gl i x / Real.sqrt (a x))
    have h1 : vecNormSq (fun i ↦ Gl i x / Real.sqrt (a x)) =
        ∑ i, (Gl i x / Real.sqrt (a x)) * (Gl i x / Real.sqrt (a x)) := rfl
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hs : Real.sqrt (a x) ≠ 0 := (hsqrtpos x).ne'
    field_simp
    rw [Real.sq_sqrt (hnonneg x)]
  · intro W hW
    have hWmeas : MeasurableSet W := hW.isOpen.measurableSet
    obtain ⟨lam, Lam, hlam, _hEll, hbounds⟩ :=
      exists_isEllipticFieldOn_of_isBounded hcont hpos hWmeas
        hW.isBoundedDomain.isBounded
    have hlow : ∀ x ∈ W, lam ≤ a x := fun x hx ↦ (hbounds x hx).1
    have hupp : ∀ x ∈ W, a x ≤ Lam := fun x hx ↦ (hbounds x hx).2
    have hgl : ∀ x i, Real.sqrt (a x) * (Gl i x / Real.sqrt (a x)) = Gl i x := by
      intro x i
      rw [mul_comm, div_mul_cancel₀ _ (hsqrtpos x).ne']
    have hgradW : ∀ i,
        MemLp (fun x ↦ Gl i x / Real.sqrt (a x)) 2 (volume.restrict W) :=
      fun i ↦ memLp_div_sqrt_of_le_on hcont hpos hWmeas hlam hlow
        ((hGlmem i).restrict W)
    have hGnW : ∀ n i, MemLp (fun x ↦ Gn n x i) 2 (volume.restrict W) := by
      intro n i
      have h := memLp_div_sqrt_of_le_on hcont hpos hWmeas hlam hlow
        ((hGn n i).restrict W)
      refine (memLp_congr_ae ?_).1 h
      refine Filter.Eventually.of_forall fun x ↦ ?_
      have hs : Real.sqrt (a x) ≠ 0 := (hsqrtpos x).ne'
      field_simp
    have hVW : MemLp V 2 (volume.restrict W) := hVmem.restrict W
    have hunW : ∀ n, MemLp (un n) 2 (volume.restrict W) :=
      fun n ↦ (hun n).restrict W
    have hfW : MemLp f 2 (volume.restrict W) := hfmem.restrict W
    have hfnW : ∀ n, MemLp (fn n) 2 (volume.restrict W) :=
      fun n ↦ (hfn n).restrict W
    have hconvUW := tendsto_setIntegral_sq_sub_of_tendsto (W := W) hun hVmem hconvU
    have hconvFW := tendsto_setIntegral_sq_sub_of_tendsto (W := W) hfn hfmem hconvF
    have hconvGWsqrt : ∀ i, Tendsto
        (fun n ↦ ∫ x in W,
          (Real.sqrt (a x) * Gn n x i - Gl i x) ^ 2 ∂volume) atTop (𝓝 0) :=
      fun i ↦ tendsto_setIntegral_sq_sub_of_tendsto (W := W)
        (fun n ↦ hGn n i) (hGlmem i) (hconvG i)
    have hconvGW : ∀ i, Tendsto
        (fun n ↦ ∫ x in W,
          (Gn n x i - Gl i x / Real.sqrt (a x)) ^ 2 ∂volume) atTop (𝓝 0) := by
      intro i
      refine squeeze_zero (g := fun n ↦ lam⁻¹ *
          ∫ x, (Real.sqrt (a x) * Gn n x i - Gl i x) ^ 2 ∂volume)
        (fun n ↦ integral_nonneg fun x ↦ sq_nonneg _) (fun n ↦ ?_) ?_
      · have hEq : ∫ x in W, (Gn n x i - Gl i x / Real.sqrt (a x)) ^ 2 ∂volume =
            ∫ x in W,
              ((Real.sqrt (a x) * Gn n x i - Gl i x) / Real.sqrt (a x)) ^ 2
                ∂volume := by
          refine setIntegral_congr_fun hWmeas fun x _ ↦ ?_
          have hs : Real.sqrt (a x) ≠ 0 := (hsqrtpos x).ne'
          field_simp
        rw [hEq]
        have hmemH : MemLp
            (fun x ↦ Real.sqrt (a x) * Gn n x i - Gl i x) 2 volume :=
          (hGn n i).sub (hGlmem i)
        exact integral_sq_div_sqrt_le hpos hWmeas hlam hlow hmemH
          (memLp_div_sqrt_of_le_on hcont hpos hWmeas hlam hlow
            (hmemH.restrict W))
      · simpa using (hconvG i).const_mul lam⁻¹
    refine ⟨{ toFun := V
              grad := fun x i ↦ Gl i x / Real.sqrt (a x)
              memL2 := hVW
              gradMemL2 := hgradW
              hasWeakGradient := ?_ }, fun _ _ ↦ rfl,
      Filter.Eventually.of_forall fun _ ↦ rfl, ?_⟩
    · intro i φ hsmooth hcompact hsupport
      have hq1cont : Continuous (fun x ↦ (fderiv ℝ φ x) (basisVec i)) :=
        (hsmooth.continuous_fderiv (by simp)).clm_apply continuous_const
      have hq1supp : HasCompactSupport (fun x ↦ (fderiv ℝ φ x) (basisVec i)) :=
        (hcompact.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ ↦ L (basisVec i))
          (by simp)
      have hq1 : MemLp (fun x ↦ (fderiv ℝ φ x) (basisVec i)) 2
          (volume.restrict W) :=
        (hq1cont.memLp_of_hasCompactSupport hq1supp).restrict W
      have hq2 : MemLp φ 2 (volume.restrict W) :=
        (hsmooth.continuous.memLp_of_hasCompactSupport hcompact).restrict W
      have hlim1 := tendsto_integral_mul_of_l2_tendsto (mu := volume.restrict W)
        hunW hVW hq1 hconvUW
      have hlim2 := tendsto_integral_mul_of_l2_tendsto (mu := volume.restrict W)
        (fun n ↦ hGnW n i) (hgradW i) hq2 (hconvGW i)
      have heq : ∀ n, ∫ x in W, un n x * (fderiv ℝ φ x) (basisVec i) ∂volume =
          -∫ x in W, Gn n x i * φ x ∂volume :=
        fun n ↦ hweak n W hW i φ hsmooth hcompact hsupport
      have hlim2' : Tendsto
          (fun n ↦ ∫ x in W, un n x * (fderiv ℝ φ x) (basisVec i) ∂volume)
          atTop (𝓝 (-∫ x in W, Gl i x / Real.sqrt (a x) * φ x ∂volume)) := by
        simp only [heq]
        exact hlim2.neg
      exact tendsto_nhds_unique hlim1 hlim2'
    · intro ψ
      have hψmem : MemLp ψ.toH1Function.toFun 2 (volume.restrict W) :=
        ψ.toH1Function.memL2
      have hψgrad : ∀ i, MemLp (fun x ↦ ψ.toH1Function.grad x i) 2
          (volume.restrict W) := ψ.toH1Function.gradMemL2
      have hsq : ∀ i, MemLp
          (fun x ↦ Real.sqrt (a x) * ψ.toH1Function.grad x i) 2
          (volume.restrict W) :=
        fun i ↦ memLp_sqrt_mul_of_le_on hcont hWmeas hupp (hψgrad i)
      have hA : Tendsto
          (fun n ↦ ∫ x in W, un n x * ψ.toH1Function.toFun x ∂volume) atTop
          (𝓝 (∫ x in W, V x * ψ.toH1Function.toFun x ∂volume)) :=
        tendsto_integral_mul_of_l2_tendsto hunW hVW hψmem hconvUW
      have hC : Tendsto
          (fun n ↦ ∫ x in W, fn n x * ψ.toH1Function.toFun x ∂volume) atTop
          (𝓝 (∫ x in W, f x * ψ.toH1Function.toFun x ∂volume)) :=
        tendsto_integral_mul_of_l2_tendsto hfnW hfW hψmem hconvFW
      have hBi : ∀ i, Tendsto
          (fun n ↦ ∫ x in W, Real.sqrt (a x) * Gn n x i *
            (Real.sqrt (a x) * ψ.toH1Function.grad x i) ∂volume) atTop
          (𝓝 (∫ x in W, Gl i x *
            (Real.sqrt (a x) * ψ.toH1Function.grad x i) ∂volume)) :=
        fun i ↦ tendsto_integral_mul_of_l2_tendsto
          (fun n ↦ (hGn n i).restrict W) ((hGlmem i).restrict W) (hsq i)
          (hconvGWsqrt i)
      have hrewrite : ∀ n, ∫ x in W,
          vecDot (a x • Gn n x) (ψ.toH1Function.grad x) ∂volume =
            ∑ i, ∫ x in W, Real.sqrt (a x) * Gn n x i *
              (Real.sqrt (a x) * ψ.toH1Function.grad x i) ∂volume :=
        fun n ↦ integral_vecDot_smul_eq_sum hnonneg
          fun i ↦ ((hGn n i).restrict W).integrable_mul (hsq i)
      have hlimsqrt : ∀ i, MemLp
          (fun x ↦ Real.sqrt (a x) * (Gl i x / Real.sqrt (a x))) 2
          (volume.restrict W) := by
        intro i
        refine (memLp_congr_ae ?_).1 ((hGlmem i).restrict W)
        exact Filter.Eventually.of_forall fun x ↦ (hgl x i).symm
      have hrewriteLim : ∫ x in W,
          vecDot (a x • (fun i ↦ Gl i x / Real.sqrt (a x)))
            (ψ.toH1Function.grad x) ∂volume =
          ∑ i, ∫ x in W, Real.sqrt (a x) * (Gl i x / Real.sqrt (a x)) *
            (Real.sqrt (a x) * ψ.toH1Function.grad x i) ∂volume :=
        integral_vecDot_smul_eq_sum hnonneg
          fun i ↦ (hlimsqrt i).integrable_mul (hsq i)
      have hBsum : Tendsto
          (fun n ↦ ∫ x in W,
            vecDot (a x • Gn n x) (ψ.toH1Function.grad x) ∂volume) atTop
          (𝓝 (∫ x in W, vecDot (a x • (fun i ↦ Gl i x / Real.sqrt (a x)))
            (ψ.toH1Function.grad x) ∂volume)) := by
        rw [hrewriteLim]
        simp only [hrewrite]
        refine tendsto_finsetSum Finset.univ fun i _ ↦ ?_
        have hcongr : ∫ x in W, Real.sqrt (a x) * (Gl i x / Real.sqrt (a x)) *
            (Real.sqrt (a x) * ψ.toH1Function.grad x i) ∂volume =
              ∫ x in W, Gl i x *
                (Real.sqrt (a x) * ψ.toH1Function.grad x i) ∂volume := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
          simp only [hgl x i]
        rw [hcongr]
        exact hBi i
      have hforcing : ∀ n, ∫ x in W, t⁻¹ * fn n x * ψ.toH1Function.toFun x
          ∂volume = t⁻¹ * ∫ x in W, fn n x * ψ.toH1Function.toFun x ∂volume := by
        intro n
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        ring
      have hforcingLim : ∫ x in W, t⁻¹ * f x * ψ.toH1Function.toFun x ∂volume =
          t⁻¹ * ∫ x in W, f x * ψ.toH1Function.toFun x ∂volume := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        ring
      have hgoal : t⁻¹ * ∫ x in W, V x * ψ.toH1Function.toFun x ∂volume +
          ∫ x in W, vecDot (a x • (fun i ↦ Gl i x / Real.sqrt (a x)))
            (ψ.toH1Function.grad x) ∂volume =
          ∫ x in W, t⁻¹ * f x * ψ.toH1Function.toFun x ∂volume := by
        refine tendsto_nhds_unique (f := fun n ↦
          t⁻¹ * ∫ x in W, un n x * ψ.toH1Function.toFun x ∂volume +
            ∫ x in W, vecDot (a x • Gn n x) (ψ.toH1Function.grad x) ∂volume)
          ((hA.const_mul t⁻¹).add hBsum) ?_
        have hid : ∀ n, t⁻¹ * ∫ x in W, un n x * ψ.toH1Function.toFun x ∂volume +
            ∫ x in W, vecDot (a x • Gn n x) (ψ.toH1Function.grad x) ∂volume =
            t⁻¹ * ∫ x in W, fn n x * ψ.toH1Function.toFun x ∂volume := by
          intro n
          rw [← hforcing n]
          exact hmassive n W hW ψ
        simp only [hid, hforcingLim]
        exact hC.const_mul t⁻¹
      simpa only [one_mul] using hgoal
  · intro x i
    rw [mul_comm, div_mul_cancel₀ _ (hsqrtpos x).ne']

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
