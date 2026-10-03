module

public import Mathlib
public import SubdiffusiveProcess.Gluing.CutoffStep

@[expose] public section

/-!
# Gluing: cutoffs of an open cube

For a cube `ball c h` (sup norm) the product `gcTheta c h δ` of one-dimensional cutoffs is a
smooth function with compact support in the cube, `0 ≤ · ≤ 1`, equal to `1` at every fixed point
of the cube once `δ` is small, and whose partial derivatives have `L¹` norm bounded independently
of `δ` (the derivative is of size `1/(δ h)` on a layer of volume `∝ δ h`).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
noncomputable section
namespace SubdiffusiveProcess.Gluing

variable {d : ℕ}

theorem hasFDerivAt_prod_coord' {f : Fin d → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (s : Finset (Fin d)) (x : Fin d → ℝ) :
    HasFDerivAt (fun y : Fin d → ℝ => ∏ i ∈ s, f i (y i))
      (∑ i ∈ s, (∏ k ∈ s.erase i, f k (x k)) •
        (deriv (f i) (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)) x := by
  classical
  have h : ∀ i ∈ s, HasFDerivAt (fun y : Fin d → ℝ => f i (y i))
      (deriv (f i) (x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) x := by
    intro i _
    have hd : HasDerivAt (f i) (deriv (f i) (x i)) (x i) :=
      (((hf i).differentiable (by simp)) (x i)).hasDerivAt
    exact hd.comp_hasFDerivAt x (hasFDerivAt_apply i x)
  exact HasFDerivAt.finset_prod (u := s) (g := fun i (y : Fin d → ℝ) => f i (y i)) h

/-- Directional derivative of a coordinate product. -/
theorem fderiv_prod_coord' {f : Fin d → ℝ → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (x : Fin d → ℝ) (j : Fin d) :
    fderiv ℝ (fun y : Fin d → ℝ => ∏ i, f i (y i)) x (Pi.single j 1) =
      deriv (f j) (x j) * ∏ i ∈ Finset.univ.erase j, f i (x i) := by
  classical
  rw [(hasFDerivAt_prod_coord' hf Finset.univ x).fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp; ring
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The product cutoff of the cube `ball c h`, with relative transition width `δ`. -/
def gcTheta (c : Fin d → ℝ) (h δ : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ k, gcEta (c k - h) (c k + h) (δ * h) (x k)

theorem gcTheta_contDiff (c : Fin d → ℝ) (h δ : ℝ) : ContDiff ℝ ∞ (gcTheta c h δ) := by
  unfold gcTheta
  exact contDiff_prod (fun k _ => (gcEta_contDiff _ _ _).comp (contDiff_apply ℝ ℝ k))

theorem gcTheta_nonneg (c : Fin d → ℝ) (h δ : ℝ) (x : Fin d → ℝ) : 0 ≤ gcTheta c h δ x :=
  Finset.prod_nonneg fun k _ => gcEta_nonneg _ _ _ _

theorem gcTheta_le_one (c : Fin d → ℝ) (h δ : ℝ) (x : Fin d → ℝ) : gcTheta c h δ x ≤ 1 :=
  Finset.prod_le_one₀ (fun k _ => gcEta_nonneg _ _ _ _) fun k _ => gcEta_le_one _ _ _ _

theorem gcTheta_ne_zero_imp {c : Fin d → ℝ} {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) {x : Fin d → ℝ}
    (hx : gcTheta c h δ x ≠ 0) : ∀ k, c k - h + δ * h < x k ∧ x k < c k + h - δ * h := by
  intro k
  have hk : gcEta (c k - h) (c k + h) (δ * h) (x k) ≠ 0 := by
    intro h0
    exact hx (Finset.prod_eq_zero (Finset.mem_univ k) h0)
  have := gcEta_ne_zero_imp (mul_pos hδ hh) hk
  constructor <;> linarith [this.1, this.2]

/-- The box outside which `gcTheta` vanishes. -/
def gcBox (c : Fin d → ℝ) (h δ : ℝ) : Set (Fin d → ℝ) :=
  Set.pi univ fun k => Icc (c k - h + δ * h) (c k + h - δ * h)

theorem gcTheta_eq_zero_of_notMem {c : Fin d → ℝ} {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    {x : Fin d → ℝ} (hx : x ∉ gcBox c h δ) : gcTheta c h δ x = 0 := by
  by_contra hne
  apply hx
  intro k _
  have := gcTheta_ne_zero_imp hh hδ hne k
  exact ⟨this.1.le, this.2.le⟩

theorem gcBox_subset_ball {c : Fin d → ℝ} {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    gcBox c h δ ⊆ Metric.ball c h := by
  intro x hx
  rw [mem_ball_iff_norm, pi_norm_lt_iff hh]
  intro k
  have := hx k (mem_univ k)
  rw [Real.norm_eq_abs, Pi.sub_apply, abs_lt]
  have hδh : 0 < δ * h := mul_pos hδ hh
  constructor <;> linarith [this.1, this.2]

theorem hasCompactSupport_gcTheta {c : Fin d → ℝ} {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    HasCompactSupport (gcTheta c h δ) := by
  refine HasCompactSupport.intro (K := gcBox c h δ)
    (isCompact_univ_pi fun k => isCompact_Icc) ?_
  intro x hx
  exact gcTheta_eq_zero_of_notMem hh hδ hx

theorem tsupport_gcTheta_subset {c : Fin d → ℝ} {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    tsupport (gcTheta c h δ) ⊆ Metric.ball c h := by
  have hcl : IsClosed (gcBox c h δ) := isClosed_set_pi fun k _ => isClosed_Icc
  refine (closure_minimal ?_ hcl).trans (gcBox_subset_ball hh hδ)
  intro x hx
  by_contra hxb
  exact hx (gcTheta_eq_zero_of_notMem hh hδ hxb)

/-- At a fixed point of the cube the cutoff is `1` once `δ` is small. -/
theorem eventually_gcTheta_eq_one {c : Fin d → ℝ} {h : ℝ} (hh : 0 < h) {x : Fin d → ℝ}
    (hx : x ∈ Metric.ball c h) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), gcTheta c h δ x = 1 := by
  rw [mem_ball_iff_norm, pi_norm_lt_iff hh] at hx
  have hk : ∀ k, ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ c k - h + 2 * (δ * h) ≤ x k ∧
      x k ≤ c k + h - 2 * (δ * h) := by
    intro k
    have hxk := hx k
    rw [Real.norm_eq_abs, Pi.sub_apply, abs_lt] at hxk
    have hcont : Tendsto (fun δ : ℝ => 2 * (δ * h)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun δ : ℝ => 2 * (δ * h)) (𝓝 0) (𝓝 (2 * (0 * h))) :=
        (by fun_prop : Continuous fun δ : ℝ => 2 * (δ * h)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have e1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 2 * (δ * h) < x k - (c k - h) :=
      hcont.eventually (gt_mem_nhds (by linarith [hxk.1]))
    have e2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 2 * (δ * h) < (c k + h) - x k :=
      hcont.eventually (gt_mem_nhds (by linarith [hxk.2]))
    filter_upwards [e1, e2, self_mem_nhdsWithin] with δ h1 h2 h3
    exact ⟨h3, by linarith, by linarith⟩
  have := Filter.eventually_all.2 hk
  filter_upwards [this] with δ hδ
  unfold gcTheta
  refine Finset.prod_eq_one fun k _ => ?_
  obtain ⟨h0, h1, h2⟩ := hδ k
  exact gcEta_eq_one (mul_pos h0 hh) (by linarith) (by linarith)

end SubdiffusiveProcess.Gluing
