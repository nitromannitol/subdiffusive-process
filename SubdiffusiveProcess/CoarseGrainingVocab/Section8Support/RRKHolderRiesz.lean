module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Data.Finsupp.Encodable

@[expose] public section




set_option autoImplicit false

open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderRiesz

/-! ## Countability of an orthonormal family in a separable space -/

/-- **An orthonormal subset of a separable inner product space is countable.**
Two distinct members are at distance `√2`, so rounding each of them to a point of
a countable dense set at distance `< 1/2` is injective. -/
theorem countable_of_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [TopologicalSpace.SeparableSpace E] {w : Set E}
    (hw : Orthonormal ℝ ((↑) : w → E)) : w.Countable := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  haveI : Countable D := hDc.to_subtype
  have hpick : ∀ u : E, ∃ y : D, dist u (y : E) < 1 / 2 := by
    intro u
    obtain ⟨y, hyD, hy⟩ :=
      Metric.mem_closure_iff.mp (by rw [hDd.closure_eq]; exact Set.mem_univ u) (1 / 2)
        (by norm_num)
    exact ⟨⟨y, hyD⟩, hy⟩
  choose F hF using hpick
  rw [← Set.countable_coe_iff]
  refine Function.Injective.countable (f := fun u : w => F (u : E)) ?_
  intro u v huv
  by_contra hne
  have huv' : F (u : E) = F (v : E) := huv
  have hsq : ‖(u : E) - (v : E)‖ ^ 2 = 2 := by
    rw [norm_sub_sq_real, hw.norm_eq_one u, hw.norm_eq_one v, hw.inner_eq_zero hne]
    norm_num
  have hlt : dist (u : E) (v : E) < 1 := by
    calc dist (u : E) (v : E) ≤ dist (u : E) (F (u : E) : E) + dist (F (u : E) : E) (v : E) :=
          dist_triangle _ _ _
      _ < 1 / 2 + 1 / 2 := by
          refine add_lt_add (hF _) ?_
          rw [dist_comm, huv']
          exact hF _
      _ = 1 := by norm_num
  rw [dist_eq_norm] at hlt
  nlinarith [norm_nonneg ((u : E) - (v : E))]

/-! ## The rational-coefficient bound upgrades to an `ℓ²` bound -/

/-- **From finitely supported rational test vectors to the `ℓ²` bound.**  If the
Cauchy–Schwarz-shaped inequality `|∑ c i · a i| ≤ C (∑ c i ²)^{1/2}` holds for all
finitely supported *rational* `c`, then `∑_{i ∈ F} a i ² ≤ C²` for every finite
`F`: approximate `a` on `F` by rationals and pass to the limit. -/
theorem sq_sum_le_of_finsupp_bound {ι : Type*} (a : ι → ℝ) {C : ℝ}
    (hb : ∀ c : ι →₀ ℚ, |∑ i ∈ c.support, (c i : ℝ) * a i|
      ≤ C * Real.sqrt (∑ i ∈ c.support, ((c i : ℝ)) ^ 2))
    (F : Finset ι) : ∑ i ∈ F, (a i) ^ 2 ≤ C ^ 2 := by
  classical
  set M := ∑ i ∈ F, (a i) ^ 2 with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- rational approximations of `a` on `F`
  have hq : ∀ n : ℕ, ∀ i : ι, ∃ q : ℚ, |a i - (q : ℝ)| < 1 / (n + 1) := by
    intro n i
    exact exists_rat_near (a i) (by positivity)
  choose q hq using hq
  -- the finitely supported rational vector attached to `(n, F)`
  set c : ℕ → (ι →₀ ℚ) := fun n =>
    Finsupp.onFinset F (fun i => if i ∈ F then q n i else 0)
      (fun i hi => by by_contra hiF; simp [hiF] at hi) with hc
  have hcval : ∀ n, ∀ i ∈ F, ((c n i : ℚ) : ℝ) = ((q n i : ℚ) : ℝ) := by
    intro n i hi
    simp [hc, Finsupp.onFinset_apply, hi]
  have hshrink : ∀ (n : ℕ) (u : ι → ℝ),
      ∑ i ∈ (c n).support, ((c n i : ℚ) : ℝ) * u i = ∑ i ∈ F, ((c n i : ℚ) : ℝ) * u i := by
    intro n u
    refine Finset.sum_subset Finsupp.support_onFinset_subset ?_
    intro i _ hnot
    have hzero : c n i = 0 := by
      simpa [Finsupp.notMem_support_iff] using hnot
    simp [hzero]
  -- the hypothesis, rewritten over `F` with the coefficients `q n`
  have hkey : ∀ n : ℕ, |∑ i ∈ F, ((q n i : ℚ) : ℝ) * a i|
      ≤ C * Real.sqrt (∑ i ∈ F, (((q n i : ℚ) : ℝ)) ^ 2) := by
    intro n
    have h1 : ∑ i ∈ (c n).support, ((c n i : ℚ) : ℝ) * a i
        = ∑ i ∈ F, ((q n i : ℚ) : ℝ) * a i := by
      rw [hshrink n a]
      exact Finset.sum_congr rfl fun i hi => by rw [hcval n i hi]
    have h2 : ∑ i ∈ (c n).support, (((c n i : ℚ) : ℝ)) ^ 2
        = ∑ i ∈ F, (((q n i : ℚ) : ℝ)) ^ 2 := by
      have := hshrink n (fun i => ((c n i : ℚ) : ℝ))
      simp only [← pow_two] at this
      rw [this]
      exact Finset.sum_congr rfl fun i hi => by rw [hcval n i hi]
    have := hb (c n)
    rwa [h1, h2] at this
  -- pass to the limit
  have hconv : ∀ i : ι, Tendsto (fun n : ℕ => ((q n i : ℚ) : ℝ)) atTop (nhds (a i)) := by
    intro i
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Real.dist_eq, abs_sub_comm]
    exact (hq n i).le
  have h1 : Tendsto (fun n : ℕ => ∑ i ∈ F, ((q n i : ℚ) : ℝ) * a i) atTop
      (nhds (∑ i ∈ F, a i * a i)) :=
    tendsto_finset_sum _ fun i _ => (hconv i).mul tendsto_const_nhds
  have h2 : Tendsto (fun n : ℕ => ∑ i ∈ F, (((q n i : ℚ) : ℝ)) ^ 2) atTop (nhds M) := by
    rw [hM]
    exact tendsto_finset_sum _ fun i _ => ((hconv i).pow 2)
  have h3 : Tendsto (fun n : ℕ => C * Real.sqrt (∑ i ∈ F, (((q n i : ℚ) : ℝ)) ^ 2)) atTop
      (nhds (C * Real.sqrt M)) :=
    ((Real.continuous_sqrt.tendsto M).comp h2).const_mul C
  have hMle : M ≤ C * Real.sqrt M := by
    have hsum : ∑ i ∈ F, a i * a i = M := by
      rw [hM]
      exact Finset.sum_congr rfl fun i _ => (pow_two (a i)).symm
    have hlim := le_of_tendsto_of_tendsto h1.abs h3 (Eventually.of_forall hkey)
    rwa [hsum, abs_of_nonneg hM0] at hlim
  nlinarith [Real.sq_sqrt hM0, Real.sqrt_nonneg M, sq_nonneg (Real.sqrt M - C)]

/-! ## Almost-everywhere representatives of finite sums in `L²` -/

section Lp

variable {X : Type*} [MeasurableSpace X] {mu : Measure X}

/-- The representative of a finite sum in `Lp` is the pointwise sum. -/
theorem coeFn_finset_sum {ι : Type*} (s : Finset ι) (F : ι → Lp ℝ 2 mu) :
    ⇑(∑ i ∈ s, F i) =ᵐ[mu] fun x => ∑ i ∈ s, (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := mu)] with x hx
      simpa using hx
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j), ih] with x hx hx2
      rw [hx, Pi.add_apply, hx2, Finset.sum_insert hi]

/-- The representative of a finite linear combination in `Lp` is the pointwise
linear combination. -/
theorem coeFn_finset_sum_smul {ι : Type*} (s : Finset ι) (a : ι → ℝ) (F : ι → Lp ℝ 2 mu) :
    ⇑(∑ i ∈ s, a i • F i) =ᵐ[mu] fun x => ∑ i ∈ s, a i * (F i) x := by
  refine (coeFn_finset_sum s fun i => a i • F i).trans ?_
  have hall : ∀ᵐ x ∂mu, ∀ i ∈ s, (a i • F i) x = a i * (F i) x :=
    (eventually_all_finset s).2 fun i _ => by
      filter_upwards [Lp.coeFn_smul (a i) (F i)] with x hx
      rw [hx]
      rfl
  filter_upwards [hall] with x hx
  exact Finset.sum_congr rfl fun i hi => hx i hi

/-! ## The Riesz representative -/



theorem exists_repr_of_ae_bound [SecondCountableTopology (Lp ℝ 2 mu)]
    (T : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ f : Lp ℝ 2 mu, ∀ᵐ x ∂mu, |(T f) x| ≤ C * ‖f‖) :
    ∃ g : X → Lp ℝ 2 mu, (∀ x, ‖g x‖ ≤ C) ∧
      ∀ f : Lp ℝ 2 mu, (fun x => (T f) x) =ᵐ[mu] fun x => ⟪g x, f⟫ := by
  classical
  obtain ⟨w, b, hbw⟩ := exists_hilbertBasis ℝ (Lp ℝ 2 mu)
  have hwo : Orthonormal ℝ ((↑) : w → Lp ℝ 2 mu) := hbw ▸ b.orthonormal
  haveI : Countable w := (countable_of_orthonormal hwo).to_subtype
  set h : w → X → ℝ := fun i => ⇑(T (b i)) with hh
  -- the countable family of rational test vectors
  set v : (w →₀ ℚ) → Lp ℝ 2 mu := fun c => ∑ i ∈ c.support, ((c i : ℚ) : ℝ) • b i with hv
  have hnormv : ∀ c : w →₀ ℚ, ‖v c‖ = Real.sqrt (∑ i ∈ c.support, (((c i : ℚ) : ℝ)) ^ 2) := by
    intro c
    have hinner : ⟪v c, v c⟫ = ∑ i ∈ c.support, (((c i : ℚ) : ℝ)) ^ 2 := by
      rw [hv]
      simpa [pow_two] using
        b.orthonormal.inner_sum (fun i => ((c i : ℚ) : ℝ)) (fun i => ((c i : ℚ) : ℝ)) c.support
    have hnn : (0 : ℝ) ≤ ∑ i ∈ c.support, (((c i : ℚ) : ℝ)) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have : ‖v c‖ ^ 2 = ∑ i ∈ c.support, (((c i : ℚ) : ℝ)) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hinner
    rw [← this, Real.sqrt_sq (norm_nonneg _)]
  -- the countably many almost-everywhere bounds
  have hbd : ∀ c : w →₀ ℚ, ∀ᵐ x ∂mu, |∑ i ∈ c.support, ((c i : ℚ) : ℝ) * h i x|
      ≤ C * Real.sqrt (∑ i ∈ c.support, (((c i : ℚ) : ℝ)) ^ 2) := by
    intro c
    have hTv : T (v c) = ∑ i ∈ c.support, ((c i : ℚ) : ℝ) • T (b i) := by
      rw [hv]
      simp [map_sum, map_smul]
    filter_upwards [hsup (v c),
      hTv ▸ coeFn_finset_sum_smul (mu := mu) c.support (fun i => ((c i : ℚ) : ℝ))
        (fun i => T (b i))] with x hx1 hx2
    rw [← hnormv c, ← hx2]
    exact hx1
  -- off a single null set, the coefficients are square-summable with sum at most `C²`
  set P : X → Prop := fun x => ∀ F : Finset w, ∑ i ∈ F, (h i x) ^ 2 ≤ C ^ 2 with hP
  have hPae : ∀ᵐ x ∂mu, P x := by
    filter_upwards [ae_all_iff.2 hbd] with x hx
    exact fun F => sq_sum_le_of_finsupp_bound (fun i => h i x) hx F
  have hcast : ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) := by norm_num
  have hterm : ∀ (r : ℝ), ‖r‖ ^ ((2 : ℝ≥0∞)).toReal = r ^ 2 := by
    intro r
    rw [hcast, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have hmem : ∀ x, P x → Memℓp (fun i => h i x) 2 := by
    intro x hx
    refine memℓp_gen ?_
    refine summable_of_sum_le (c := C ^ 2) (fun i => by rw [hterm]; positivity) fun s => ?_
    calc ∑ i ∈ s, ‖h i x‖ ^ ((2 : ℝ≥0∞)).toReal = ∑ i ∈ s, (h i x) ^ 2 :=
          Finset.sum_congr rfl fun i _ => hterm _
      _ ≤ C ^ 2 := hx s
  -- the representative
  set g : X → Lp ℝ 2 mu := fun x =>
    if hx : P x then b.repr.symm ⟨fun i => h i x, hmem x hx⟩ else 0 with hg
  have hgnorm : ∀ x, ‖g x‖ ≤ C := by
    intro x
    by_cases hx : P x
    · rw [hg]
      simp only [dif_pos hx]
      rw [LinearIsometryEquiv.norm_map]
      refine lp.norm_le_of_forall_sum_le (by norm_num) hC fun s => ?_
      have hC2 : C ^ ((2 : ℝ≥0∞)).toReal = C ^ 2 := by
        rw [hcast, Real.rpow_natCast]
      calc ∑ i ∈ s, ‖(⟨fun i => h i x, hmem x hx⟩ : lp (fun _ : w => ℝ) 2) i‖
            ^ ((2 : ℝ≥0∞)).toReal
          = ∑ i ∈ s, (h i x) ^ 2 := Finset.sum_congr rfl fun i _ => hterm _
        _ ≤ C ^ 2 := hx s
        _ = C ^ ((2 : ℝ≥0∞)).toReal := hC2.symm
    · rw [hg]
      simp only [dif_neg hx, norm_zero]
      exact hC
  have hginner : ∀ x, P x → ∀ i : w, ⟪g x, b i⟫ = h i x := by
    intro x hx i
    have hgx : g x = b.repr.symm ⟨fun i => h i x, hmem x hx⟩ := by
      rw [hg]; simp only [dif_pos hx]
    rw [real_inner_comm, ← HilbertBasis.repr_apply_apply, hgx,
      LinearIsometryEquiv.apply_symm_apply]
  refine ⟨g, hgnorm, fun f => ?_⟩
  -- approximate `f` by finite combinations of basis vectors
  have happrox : ∀ k : ℕ, ∃ s : Finset w,
      ‖(∑ i ∈ s, ((b.repr f) i) • b i) - f‖ < 1 / (k + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / (k + 1) := by positivity
    have := (Metric.tendsto_nhds.mp (b.hasSum_repr f) _ hpos).exists
    obtain ⟨s, hs⟩ := this
    exact ⟨s, by rwa [dist_eq_norm] at hs⟩
  choose s hs using happrox
  set u : ℕ → Lp ℝ 2 mu := fun k => ∑ i ∈ s k, ((b.repr f) i) • b i with hu
  have hufin : ∀ k, ∀ᵐ x ∂mu, (T (u k)) x = ⟪g x, u k⟫ := by
    intro k
    have hTu : T (u k) = ∑ i ∈ s k, ((b.repr f) i) • T (b i) := by
      rw [hu]
      simp [map_sum, map_smul]
    filter_upwards [hPae,
      hTu ▸ coeFn_finset_sum_smul (mu := mu) (s k) (fun i => ((b.repr f) i))
        (fun i => T (b i))] with x hxP hx2
    rw [hx2, hu, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, hginner x hxP i]
  have hudiff : ∀ k, ∀ᵐ x ∂mu, |(T f) x - (T (u k)) x| ≤ C * ‖f - u k‖ := by
    intro k
    filter_upwards [hsup (f - u k), Lp.coeFn_sub (T f) (T (u k))] with x hx1 hx2
    rw [map_sub] at hx1
    rw [hx2] at hx1
    simpa using hx1
  filter_upwards [hPae, ae_all_iff.2 hufin, ae_all_iff.2 hudiff] with x hxP hx1 hx2
  have hbnd : ∀ k : ℕ, |(T f) x - ⟪g x, f⟫| ≤ 2 * C * (1 / (k + 1)) := by
    intro k
    have e1 : |(T f) x - (T (u k)) x| ≤ C * ‖f - u k‖ := hx2 k
    have e2 : (T (u k)) x = ⟪g x, u k⟫ := hx1 k
    have e3 : |⟪g x, u k⟫ - ⟪g x, f⟫| ≤ C * ‖f - u k‖ := by
      rw [← inner_sub_right]
      calc |⟪g x, u k - f⟫| ≤ ‖g x‖ * ‖u k - f‖ := abs_real_inner_le_norm _ _
        _ ≤ C * ‖f - u k‖ := by
            rw [norm_sub_rev]
            exact mul_le_mul_of_nonneg_right (hgnorm x) (norm_nonneg _)
    have e4 : ‖f - u k‖ ≤ 1 / (k + 1) := by
      rw [norm_sub_rev]
      exact (hs k).le
    have e5 : |(T f) x - ⟪g x, f⟫| ≤ |(T f) x - (T (u k)) x| + |⟪g x, u k⟫ - ⟪g x, f⟫| := by
      rw [e2] at *
      calc |(T f) x - ⟪g x, f⟫|
          = |((T f) x - ⟪g x, u k⟫) + (⟪g x, u k⟫ - ⟪g x, f⟫)| := by ring_nf
        _ ≤ |(T f) x - ⟪g x, u k⟫| + |⟪g x, u k⟫ - ⟪g x, f⟫| := abs_add_le _ _
    have hCnn : 0 ≤ C := hC
    nlinarith [e1, e3, e4, e5, norm_nonneg (f - u k)]
  have hlim : Tendsto (fun k : ℕ => 2 * C * (1 / ((k : ℝ) + 1))) atTop (nhds 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C)
    simpa using this
  have hzero : |(T f) x - ⟪g x, f⟫| ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbnd)
  have := abs_nonneg ((T f) x - ⟪g x, f⟫)
  have hEq : (T f) x - ⟪g x, f⟫ = 0 := by
    have : |(T f) x - ⟪g x, f⟫| = 0 := le_antisymm hzero (abs_nonneg _)
    exact abs_eq_zero.mp this
  linarith [hEq]

end Lp

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderRiesz
