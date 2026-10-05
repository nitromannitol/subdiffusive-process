module

public import Homogenization.Sobolev.Foundations.DifferenceQuotientH1
public import Homogenization.Sobolev.Truncation.H10Limit
public import Homogenization.Sobolev.Truncation.Basic
public import Homogenization.Sobolev.Truncation.Approx
public import Homogenization.Sobolev.Truncation.WeakGradientLimit
public import Homogenization.Sobolev.H1.Algebra.H1Function
public import Homogenization.Sobolev.H1.Algebra.H10Function
public import Homogenization.Sobolev.Foundations.PoincareMeanZero
public import Homogenization.Sobolev.CubeEmbedding.Extension
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

open Filter Topology

/-- A continuous function is essentially bounded on a bounded domain. -/
theorem aux_bp_memLp_top_of_continuous {d : ℕ} {U : Set (Homogenization.Vec d)}
    (hU : Homogenization.IsOpenBoundedConvexDomain U) {g : Homogenization.Vec d → ℝ}
    (hg : Continuous g) : MemLp g ⊤ (volume.restrict U) := by
  obtain ⟨C, hC⟩ := hU.isBoundedDomain.isBounded.isCompact_closure.exists_bound_of_continuousOn
    hg.continuousOn
  refine memLp_top_of_bound hg.aestronglyMeasurable C ?_
  exact (ae_restrict_iff' hU.isOpen.measurableSet).mpr
    (Eventually.of_forall fun x hx => hC x (subset_closure hx))

/-- The bump used by the smooth truncation: equal to `1` on `[-(M+1), M+1]`. -/
def aux_bp_bump (M : ℝ) (hM : 0 ≤ M) : ContDiffBump (0 : ℝ) :=
  ⟨M + 1, M + 2, by linarith, by linarith⟩

/-- The smooth truncation `T(t) = t β(t)`. -/
def aux_bp_T (M : ℝ) (hM : 0 ≤ M) : ℝ → ℝ := fun t => t * aux_bp_bump M hM t

theorem aux_bp_T_contDiff (M : ℝ) (hM : 0 ≤ M) : ContDiff ℝ (⊤ : ℕ∞) (aux_bp_T M hM) :=
  contDiff_id.mul (aux_bp_bump M hM).contDiff

theorem aux_bp_T_hasCompactSupport (M : ℝ) (hM : 0 ≤ M) : HasCompactSupport (aux_bp_T M hM) := by
  have h := (aux_bp_bump M hM).hasCompactSupport.mul_left (f := fun t : ℝ => t)
  exact h

theorem aux_bp_T_bound (M : ℝ) (hM : 0 ≤ M) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |aux_bp_T M hM t| ≤ B := by
  obtain ⟨C, hC⟩ := (aux_bp_T_contDiff M hM).continuous.bounded_above_of_compact_support
    (aux_bp_T_hasCompactSupport M hM)
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

theorem aux_bp_deriv_bound (M : ℝ) (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t, |deriv (aux_bp_T M hM) t| ≤ L := by
  obtain ⟨C, hC⟩ := ((aux_bp_T_contDiff M hM).continuous_deriv (by simp)).bounded_above_of_compact_support
    (aux_bp_T_hasCompactSupport M hM).deriv
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

theorem aux_bp_T_eventuallyEq (M : ℝ) (hM : 0 ≤ M) {t : ℝ} (ht : |t| < M + 1) :
    aux_bp_T M hM =ᶠ[𝓝 t] id := by
  have hopen : IsOpen (Metric.ball (0 : ℝ) (M + 1)) := Metric.isOpen_ball
  have hmem : t ∈ Metric.ball (0 : ℝ) (M + 1) := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht
  filter_upwards [hopen.mem_nhds hmem] with s hs
  have h1 : aux_bp_bump M hM s = 1 :=
    (aux_bp_bump M hM).one_of_mem_closedBall (Metric.ball_subset_closedBall hs)
  simp [aux_bp_T, h1]

theorem aux_bp_T_eq (M : ℝ) (hM : 0 ≤ M) {t : ℝ} (ht : |t| < M + 1) : aux_bp_T M hM t = t :=
  (aux_bp_T_eventuallyEq M hM ht).eq_of_nhds

theorem aux_bp_deriv_eq (M : ℝ) (hM : 0 ≤ M) {t : ℝ} (ht : |t| < M + 1) :
    deriv (aux_bp_T M hM) t = 1 := by
  rw [(aux_bp_T_eventuallyEq M hM ht).deriv_eq]; simp

/-- Chain rule for a smooth scalar composition, applied to a direction. -/
theorem aux_bp_fderiv_comp {d : ℕ} {f : Homogenization.Vec d → ℝ} (hf : Differentiable ℝ f)
    {T : ℝ → ℝ} (hT : Differentiable ℝ T) (x e : Homogenization.Vec d) :
    fderiv ℝ (fun y => T (f y)) x e = deriv T (f x) * fderiv ℝ f x e := by
  have h := (hT (f x)).hasDerivAt.comp_hasFDerivAt x (hf x).hasFDerivAt
  rw [show (fun y => T (f y)) = T ∘ f from rfl, h.fderiv]
  simp [smul_eq_mul]

open Homogenization in
/-- The core: given smooth approximants `f n` of `v` in `H¹(U)`, the truncated approximants
`T ∘ f n` times `u` are `H¹₀` and converge to `u v` in `H¹`. -/
theorem aux_bp_core {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    (u : H10Function U) (v : H1Function U)
    {Mu Mv : ℝ} (hMu : 0 ≤ Mu) (hMv : 0 ≤ Mv)
    (hu : ∀ᵐ x ∂volume.restrict U, |u.toH1Function.toFun x| ≤ Mu)
    (hv : ∀ᵐ x ∂volume.restrict U, |v.toFun x| ≤ Mv)
    (f : ℕ → Vec d → ℝ) (hfs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n))
    (hfv : Tendsto (fun n => eLpNorm (fun x => f n x - v.toFun x) 2 (volume.restrict U))
      atTop (𝓝 0))
    (hfg : ∀ i : Fin d, Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (f n) x (basisVec i) - v.grad x i) 2 (volume.restrict U)) atTop (𝓝 0)) :
    ∃ w : H10Function U,
      (w.toH1Function.toFun =ᵐ[volume.restrict U]
        (fun x => u.toH1Function.toFun x * v.toFun x)) ∧
      ∀ i : Fin d,
        (fun x => w.toH1Function.grad x i) =ᵐ[volume.restrict U]
          (fun x => u.toH1Function.toFun x * v.grad x i +
            v.toFun x * u.toH1Function.grad x i) := by
  classical
  set μ : Measure (Vec d) := volume.restrict U with hμ
  have : IsFiniteMeasure μ := hU.isFiniteMeasure_restrict_volume
  -- an a.e.-convergent subsequence of the approximants
  have hTIM : TendstoInMeasure μ f atTop v.toFun :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      hfv
  obtain ⟨ns, hns, hae⟩ := hTIM.exists_seq_tendsto_ae
  set g : ℕ → Vec d → ℝ := fun k => f (ns k) with hg
  have hgs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k) := fun k => hfs (ns k)
  have hgg : ∀ i : Fin d, Tendsto (fun k => eLpNorm
      (fun x => fderiv ℝ (g k) x (basisVec i) - v.grad x i) 2 μ) atTop (𝓝 0) :=
    fun i => (hfg i).comp hns.tendsto_atTop
  -- the truncation
  set T : ℝ → ℝ := aux_bp_T Mv hMv with hT
  have hTs : ContDiff ℝ (⊤ : ℕ∞) T := aux_bp_T_contDiff Mv hMv
  obtain ⟨B, hB0, hB⟩ := aux_bp_T_bound Mv hMv
  obtain ⟨L, hL0, hL⟩ := aux_bp_deriv_bound Mv hMv
  have hTv : ∀ᵐ x ∂μ, T (v.toFun x) = v.toFun x := by
    filter_upwards [hv] with x hx
    exact aux_bp_T_eq Mv hMv (by linarith)
  have hT'v : ∀ᵐ x ∂μ, deriv T (v.toFun x) = 1 := by
    filter_upwards [hv] with x hx
    exact aux_bp_deriv_eq Mv hMv (by linarith)
  -- the smooth bounded multipliers
  set φ : ℕ → Vec d → ℝ := fun k x => T (g k x) with hφ
  have hφs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k) := fun k => hTs.comp (hgs k)
  have hφtop : ∀ k, MemLp (φ k) ⊤ μ := fun k =>
    aux_bp_memLp_top_of_continuous hU (hφs k).continuous
  have hdφcont : ∀ k (i : Fin d), Continuous fun x => fderiv ℝ (φ k) x (basisVec i) :=
    fun k i => ((hφs k).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφtop : ∀ k (i : Fin d), MemLp (fun x => fderiv ℝ (φ k) x (basisVec i)) ⊤ μ :=
    fun k i => aux_bp_memLp_top_of_continuous hU (hdφcont k i)
  have hdφ : ∀ k x (i : Fin d), fderiv ℝ (φ k) x (basisVec i) =
      deriv T (g k x) * fderiv ℝ (g k) x (basisVec i) := fun k x i =>
    aux_bp_fderiv_comp ((hgs k).differentiable (by simp)) (hTs.differentiable (by simp)) x _
  -- the H¹₀ products
  set w : ℕ → H10Function U := fun k => u.mulContDiffMemLpTop (hφs k) (hφtop k) (hdφtop k)
    with hw
  have hwf : ∀ k, (w k).toH1Function.toFun = fun x => φ k x * u.toH1Function.toFun x :=
    fun k => by simp [hw]
  have hwg : ∀ k, (w k).toH1Function.grad = fun x i => φ k x * u.toH1Function.grad x i +
      u.toH1Function.toFun x * fderiv ℝ (φ k) x (basisVec i) :=
    fun k => by simp [hw]
  -- bounds and membership of the target product
  have hPmem : MemLp (fun x => u.toH1Function.toFun x * v.toFun x) 2 μ := by
    refine (v.memL2.const_mul Mu).of_le (u.toH1Function.memL2.aestronglyMeasurable.mul v.memL2.aestronglyMeasurable) ?_
    filter_upwards [hu] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hMu]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hPgrad : GradMemL2On U (fun x i => u.toH1Function.toFun x * v.grad x i +
      v.toFun x * u.toH1Function.grad x i) := by
    intro i
    have h1 : MemLp (fun x => u.toH1Function.toFun x * v.grad x i) 2 μ := by
      refine ((v.gradMemL2 i).const_mul Mu).of_le
        (u.toH1Function.memL2.aestronglyMeasurable.mul (v.gradMemL2 i).aestronglyMeasurable) ?_
      filter_upwards [hu] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hMu]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have h2 : MemLp (fun x => v.toFun x * u.toH1Function.grad x i) 2 μ := by
      refine ((u.toH1Function.gradMemL2 i).const_mul Mv).of_le
        (v.memL2.aestronglyMeasurable.mul (u.toH1Function.gradMemL2 i).aestronglyMeasurable) ?_
      filter_upwards [hv] with x hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hMv]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    exact h1.add h2
  -- pointwise limits along the subsequence
  have hTd : Continuous (deriv T) := hTs.continuous_deriv (by simp)
  have hφlim : ∀ᵐ x ∂μ, Tendsto (fun k => φ k x) atTop (𝓝 (v.toFun x)) := by
    filter_upwards [hae, hTv] with x hx hTx
    have h := (hTs.continuous.tendsto (v.toFun x)).comp hx
    rw [hTx] at h
    exact h
  have hT'lim : ∀ᵐ x ∂μ, Tendsto (fun k => deriv T (g k x)) atTop (𝓝 1) := by
    filter_upwards [hae, hT'v] with x hx hTx
    have h := (hTd.tendsto (v.toFun x)).comp hx
    rw [hTx] at h
    exact h
  -- convergence of the values
  have hA : Tendsto (fun k => eLpNorm (fun x => (w k).toH1Function.toFun x -
      u.toH1Function.toFun x * v.toFun x) 2 μ) atTop (𝓝 0) := by
    simp only [hwf]
    refine tendsto_eLpNorm_two_of_tendsto_ae_of_dominated (μ := μ)
      (f := fun k x => φ k x * u.toH1Function.toFun x)
      (g := fun x => u.toH1Function.toFun x * v.toFun x) (h := fun _ => B * Mu)
      (fun k => (hφs k).continuous.aestronglyMeasurable.mul u.toH1Function.memL2.aestronglyMeasurable)
      hPmem (memLp_const _) ?_ ?_
    · intro k
      filter_upwards [hu] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hB _) hx (abs_nonneg _) hB0
    · filter_upwards [hφlim] with x hx
      simpa [mul_comm] using hx.mul_const (u.toH1Function.toFun x)
  -- convergence of the gradients
  have hB' : ∀ i : Fin d, Tendsto (fun k => eLpNorm (fun x => (w k).toH1Function.grad x i -
      (u.toH1Function.toFun x * v.grad x i + v.toFun x * u.toH1Function.grad x i)) 2 μ)
      atTop (𝓝 0) := by
    intro i
    set a : ℕ → Vec d → ℝ := fun k x => (φ k x - v.toFun x) * u.toH1Function.grad x i with ha_def
    set b : ℕ → Vec d → ℝ := fun k x => u.toH1Function.toFun x * deriv T (g k x) *
      (fderiv ℝ (g k) x (basisVec i) - v.grad x i) with hb_def
    set c : ℕ → Vec d → ℝ := fun k x => u.toH1Function.toFun x * (deriv T (g k x) - 1) *
      v.grad x i with hc_def
    have hsplit : ∀ k, (fun x => (w k).toH1Function.grad x i -
        (u.toH1Function.toFun x * v.grad x i + v.toFun x * u.toH1Function.grad x i)) =
        a k + b k + c k := by
      intro k; funext x
      rw [hwg k]
      simp only [Pi.add_apply, hdφ, ha_def, hb_def, hc_def]
      ring
    have hgc : ∀ k, Continuous (g k) := fun k => (hgs k).continuous
    have hdgc : ∀ k, Continuous fun x => fderiv ℝ (g k) x (basisVec i) := fun k =>
      ((hgs k).continuous_fderiv (by simp)).clm_apply continuous_const
    have ham : ∀ k, AEStronglyMeasurable (a k) μ := fun k =>
      ((hφs k).continuous.aestronglyMeasurable.sub v.memL2.aestronglyMeasurable).mul
        (u.toH1Function.gradMemL2 i).aestronglyMeasurable
    have hbm : ∀ k, AEStronglyMeasurable (b k) μ := fun k =>
      (u.toH1Function.memL2.aestronglyMeasurable.mul (hTd.comp (hgc k)).aestronglyMeasurable).mul
        ((hdgc k).aestronglyMeasurable.sub (v.gradMemL2 i).aestronglyMeasurable)
    have hcm : ∀ k, AEStronglyMeasurable (c k) μ := fun k =>
      (u.toH1Function.memL2.aestronglyMeasurable.mul
        ((hTd.comp (hgc k)).aestronglyMeasurable.sub aestronglyMeasurable_const)).mul
        (v.gradMemL2 i).aestronglyMeasurable
    have ha : Tendsto (fun k => eLpNorm (a k) 2 μ) atTop (𝓝 0) := by
      have h := tendsto_eLpNorm_two_of_tendsto_ae_of_dominated (μ := μ) (f := a)
        (g := fun _ => (0 : ℝ)) (h := fun x => (B + Mv) * ‖u.toH1Function.grad x i‖) ham
        (memLp_const 0) ((u.toH1Function.gradMemL2 i).norm.const_mul (B + Mv)) ?_ ?_
      · simpa using h
      · intro k
        filter_upwards [hv] with x hx
        simp only [ha_def, Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact (abs_sub _ _).trans (add_le_add (hB _) hx)
      · filter_upwards [hφlim] with x hx
        have h := (hx.sub_const (v.toFun x)).mul_const (u.toH1Function.grad x i)
        simpa [ha_def] using h
    have hc : Tendsto (fun k => eLpNorm (c k) 2 μ) atTop (𝓝 0) := by
      have h := tendsto_eLpNorm_two_of_tendsto_ae_of_dominated (μ := μ) (f := c)
        (g := fun _ => (0 : ℝ)) (h := fun x => (Mu * (L + 1)) * ‖v.grad x i‖) hcm
        (memLp_const 0) ((v.gradMemL2 i).norm.const_mul (Mu * (L + 1))) ?_ ?_
      · simpa using h
      · intro k
        filter_upwards [hu] with x hx
        simp only [hc_def, Real.norm_eq_abs, abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        refine mul_le_mul hx ?_ (abs_nonneg _) hMu
        exact (abs_sub _ _).trans (by rw [abs_one]; linarith [hL (g k x)])
      · filter_upwards [hT'lim] with x hx
        have h := ((hx.sub_const 1).const_mul (u.toH1Function.toFun x)).mul_const (v.grad x i)
        simpa [hc_def] using h
    have hb : Tendsto (fun k => eLpNorm (b k) 2 μ) atTop (𝓝 0) := by
      have hle : ∀ k, eLpNorm (b k) 2 μ ≤ ENNReal.ofReal (Mu * L) *
          eLpNorm (fun x => fderiv ℝ (g k) x (basisVec i) - v.grad x i) 2 μ := by
        intro k
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hbm k) ?_ 2
        filter_upwards [hu] with x hx
        simp only [hb_def, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul hx (hL _) (abs_nonneg _) hMu) (abs_nonneg _)
      have hlim : Tendsto (fun k => ENNReal.ofReal (Mu * L) *
          eLpNorm (fun x => fderiv ℝ (g k) x (basisVec i) - v.grad x i) 2 μ) atTop (𝓝 0) := by
        have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Mu * L)) (hgg i)
          (Or.inr ENNReal.ofReal_ne_top)
        simpa using h
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun k => zero_le) hle
    have hsum : Tendsto (fun k => eLpNorm (a k) 2 μ + eLpNorm (b k) 2 μ + eLpNorm (c k) 2 μ)
        atTop (𝓝 0) := by
      simpa using (ha.add hb).add hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun k => zero_le) fun k => ?_
    rw [hsplit k]
    calc eLpNorm (a k + b k + c k) 2 μ ≤ eLpNorm (a k + b k) 2 μ + eLpNorm (c k) 2 μ :=
          eLpNorm_add_le (by norm_num)
      _ ≤ eLpNorm (a k) 2 μ + eLpNorm (b k) 2 μ + eLpNorm (c k) 2 μ := by
          gcongr
          exact eLpNorm_add_le (by norm_num)
  -- the product as an H¹ function, and its H¹₀ membership
  let P : H1Function U :=
    { toFun := fun x => u.toH1Function.toFun x * v.toFun x
      grad := fun x i => u.toH1Function.toFun x * v.grad x i +
        v.toFun x * u.toH1Function.grad x i
      memL2 := hPmem
      gradMemL2 := hPgrad
      hasWeakGradient := HasWeakGradientOn.of_tendsto_eLpNorm_two hPmem hPgrad
        (fun k => (w k).toH1Function.memL2) (fun k => (w k).toH1Function.gradMemL2)
        (fun k => (w k).toH1Function.hasWeakGradient) hA hB' }
  have hmemP : MemH10 U P.toFun :=
    memH10_of_tendsto_H1 hU P (fun k => (w k).toH1Function) (fun k => ⟨w k, rfl⟩)
      (hA.congr fun k => eLpNorm_sub_swap _ _) (fun i => (hB' i).congr fun k => eLpNorm_sub_swap _ _)
  obtain ⟨W, hW⟩ := hmemP
  refine ⟨W, ?_, fun i => ?_⟩
  · rw [hW]
  · have hloc : ∀ (z : H1Function U) (j : Fin d),
        LocallyIntegrableOn (fun x => z.grad x j) U volume := fun z j =>
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((z.gradMemL2 j).locallyIntegrable (by norm_num))
    have hwW := W.toH1Function.hasWeakGradient i
    rw [hW] at hwW
    exact HasWeakPartialDerivOn.ae_eq hU.isOpen (hloc _ i) (hloc P i) hwW (P.hasWeakGradient i)



theorem inputs_classical_bounded_h10_h1_product
    {d : ℕ} {U : Set (Homogenization.Vec d)}
    (hU : Homogenization.IsOpenBoundedConvexDomain U)
    (u : Homogenization.H10Function U)
    (v : Homogenization.H1Function U)
    {Mu Mv : ℝ} (hMu : 0 ≤ Mu) (hMv : 0 ≤ Mv)
    (hu : ∀ᵐ x ∂volume.restrict U, |u.toH1Function.toFun x| ≤ Mu)
    (hv : ∀ᵐ x ∂volume.restrict U, |v.toFun x| ≤ Mv) :
    ∃ w : Homogenization.H10Function U,
      (w.toH1Function.toFun =ᵐ[volume.restrict U]
        (fun x => u.toH1Function.toFun x * v.toFun x)) ∧
      ∀ i : Fin d,
        (fun x => w.toH1Function.grad x i) =ᵐ[volume.restrict U]
          (fun x => u.toH1Function.toFun x * v.grad x i +
            v.toFun x * u.toH1Function.grad x i) := by
  classical
  by_cases hUe : U = ∅
  · subst hUe
    refine ⟨u, ?_, fun i => ?_⟩ <;> simp [Filter.EventuallyEq]
  obtain ⟨x0, hx0⟩ := Set.nonempty_iff_ne_empty.mpr hUe
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.isOpen.mem_nhds hx0)
  refine aux_bp_core hU u v hMu hMv hu hv
    (fun n => (Homogenization.H1Function.convexApproxSmoothH1 hU v x0 hr n).toFun) ?_ ?_ ?_
  · intro n
    rw [Homogenization.H1Function.convexApproxSmoothH1_toFun]
    exact Homogenization.contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet
      Homogenization.isConvexApproxKernel_unitConvexApproxKernel (by norm_num) v.memL2 hr
      (by dsimp [Homogenization.unitConvexApproxScale]; positivity)
  · exact Homogenization.tendsto_eLpNorm_convexApproxSmoothH1 hU v hr hball
  · intro i
    have h := Homogenization.tendsto_eLpNorm_grad_convexApproxSmoothH1 hU v hr hball i
    simp only [Homogenization.H1Function.convexApproxSmoothH1_grad] at h
    simpa only [Homogenization.H1Function.convexApproxSmoothH1_toFun] using h

end SubdiffusiveProcess.Paper
