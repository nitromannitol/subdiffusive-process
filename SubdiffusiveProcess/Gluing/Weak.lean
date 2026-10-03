module

public import Mathlib
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.Sobolev.H1.Definitions
public import SubdiffusiveProcess.Gluing.SumIdentity

@[expose] public section

/-!
# Gluing: the glued function has the glued gradient as weak derivative

Let `Q_i = ball c_i h_i` be pairwise disjoint cubes in an open set `Ω`, covering `Ω` up to a null
set, `u_i ∈ H¹(Q_i)`, and `W` a *continuous* compactly supported function with `W = u_i` on
`Q_i`.  Then the glued gradient `G` (the cell gradients extended by zero) is the weak `j`-th partial
derivative of `W` in `Ω`.

The cell identities `∫ W θ_i ∂_jφ + ∫ W φ ∂_jθ_i = -∫ g_i θ_i φ` (test function `θ_i φ` supported in
`Q_i`) are summed over the cells, `S = ∑ θ_i → 1` a.e. in `Ω`, and the only remaining term
`∫ W φ ∂_j S` tends to zero because `‖∂_j S‖_{L¹}` is bounded and `Wφ` is continuous.  No trace
and no face geometry is used.
-/

open MeasureTheory Set Filter Topology Homogenization
open scoped ContDiff
noncomputable section
namespace SubdiffusiveProcess.Gluing

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

section
variable {c : ι → Fin d → ℝ} {h : ι → ℝ}

theorem norm_mul_cut_le (a s b : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : ‖a * (s * b)‖ ≤ ‖a * b‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hs0]
  have h1 := abs_nonneg a
  have h2 := abs_nonneg b
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) (sub_nonneg.2 hs1)]

theorem integrable_gluedGrad (u : ∀ i, H1Function (gcCell c h i)) (j : Fin d) :
    Integrable (gluedGrad c h u j) := by
  unfold gluedGrad
  refine integrable_finset_sum _ fun i _ => ?_
  rw [integrable_indicator_iff Metric.isOpen_ball.measurableSet]
  haveI : IsFiniteMeasure (volume.restrict (gcCell c h i)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  exact ((u i).gradMemL2 j).integrable one_le_two

theorem hasWeakPartialDerivOn_glue {Ω : Set (Fin d → ℝ)} (hΩ : IsOpen Ω)
    (hh : ∀ i, 0 < h i) (hsub : ∀ i, gcCell c h i ⊆ Ω)
    (hdisj : Pairwise fun i k => Disjoint (gcCell c h i) (gcCell c h k))
    (hnull : volume (Ω \ ⋃ i, gcCell c h i) = 0)
    (u : ∀ i, H1Function (gcCell c h i)) {W : (Fin d → ℝ) → ℝ} (hWc : Continuous W)
    (hW : ∀ i, ∀ x ∈ gcCell c h i, W x = (u i).toFun x) (j : Fin d) :
    HasWeakPartialDerivOn Ω j W (gluedGrad c h u j) := by
  intro φ hφ hφc hφΩ
  change (∫ x in Ω, W x * fderiv ℝ φ x (Pi.single j 1)) =
    -∫ x in Ω, gluedGrad c h u j x * φ x
  have hφ0 : ∀ x, x ∉ Ω → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hxt => hx (hφΩ hxt)
  have hdφ0 : ∀ x, x ∉ Ω → fderiv ℝ φ x (Pi.single j 1) = 0 := by
    intro x hx
    have hnot : x ∉ tsupport fun x => fderiv ℝ φ x (Pi.single j 1) :=
      fun hxt => hx (hφΩ (gl_tsupport_fderiv_apply_subset _ hxt))
    simpa using image_eq_zero_of_notMem_tsupport hnot
  rw [setIntegral_eq_integral_of_notMem_zero (fun x hx => by simp [hdφ0 x hx]),
    setIntegral_eq_integral_of_notMem_zero (fun x hx => by simp [hφ0 x hx])]
  -- basic facts
  have hcφ' : Continuous fun x => fderiv ℝ φ x (Pi.single j 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcs' : HasCompactSupport fun x => fderiv ℝ φ x (Pi.single j 1) :=
    hφc.fderiv_apply (𝕜 := ℝ) (Pi.single j 1)
  obtain ⟨B, hB⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hBφ : ∀ x, |φ x| ≤ max B 0 := fun x => by
    have := hB x; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hae : ∀ᵐ x, x ∈ Ω → ∃ i, x ∈ gcCell c h i := by
    have := measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [this] with x hx hxΩ
    by_contra hcon
    exact hx ⟨hxΩ, by simpa using hcon⟩
  set S : ℕ → (Fin d → ℝ) → ℝ := fun n => gcS c h (gcDelta n) with hS
  have hS01 : ∀ n x, 0 ≤ S n x ∧ S n x ≤ 1 := fun n x =>
    ⟨gcS_nonneg x _, gcS_le_one hh hdisj (gcDelta_pos n) x⟩
  have hSlim : ∀ᵐ x, x ∈ Ω → Tendsto (fun n => S n x) atTop (𝓝 1) := by
    filter_upwards [hae] with x hx hxΩ
    exact tendsto_gcS hh hdisj (hx hxΩ)
  -- (I1)
  have I1 : Tendsto (fun n => ∫ x, W x * (S n x * fderiv ℝ φ x (Pi.single j 1))) atTop
      (𝓝 (∫ x, W x * fderiv ℝ φ x (Pi.single j 1))) := by
    have hint : Integrable fun x => W x * fderiv ℝ φ x (Pi.single j 1) :=
      (hWc.mul hcφ').integrable_of_hasCompactSupport hcs'.mul_left
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖W x * fderiv ℝ φ x (Pi.single j 1)‖) (fun n => ?_) hint.norm (fun n => ?_) ?_
    · exact (hWc.mul ((gcS_contDiff _).continuous.mul hcφ')).aestronglyMeasurable
    · exact Eventually.of_forall fun x => norm_mul_cut_le _ _ _ (hS01 n x).1 (hS01 n x).2
    · filter_upwards [hSlim] with x hx
      by_cases hxΩ : x ∈ Ω
      · have := (hx hxΩ).mul_const (fderiv ℝ φ x (Pi.single j 1))
        simpa using this.const_mul (W x)
      · simp [hdφ0 x hxΩ]
  -- (I3)
  have I3 : Tendsto (fun n => ∫ x, gluedGrad c h u j x * (S n x * φ x)) atTop
      (𝓝 (∫ x, gluedGrad c h u j x * φ x)) := by
    have hGφ : Integrable fun x => gluedGrad c h u j x * φ x :=
      (integrable_gluedGrad u j).mul_bdd hφ.continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBφ x)
    have hGm : AEStronglyMeasurable (gluedGrad c h u j) volume :=
      (integrable_gluedGrad u j).aestronglyMeasurable
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖gluedGrad c h u j x * φ x‖) (fun n => ?_) hGφ.norm (fun n => ?_) ?_
    · exact hGm.mul (((gcS_contDiff _).continuous.mul hφ.continuous).aestronglyMeasurable)
    · exact Eventually.of_forall fun x => norm_mul_cut_le _ _ _ (hS01 n x).1 (hS01 n x).2
    · filter_upwards [hSlim] with x hx
      by_cases hxΩ : x ∈ Ω
      · have := (hx hxΩ).mul_const (φ x)
        simpa using this.const_mul (gluedGrad c h u j x)
      · simp [hφ0 x hxΩ]
  -- (I2)
  have I2 : Tendsto (fun n => ∫ x, W x * (φ x * fderiv ℝ (S n) x (Pi.single j 1))) atTop
      (𝓝 0) := by
    obtain ⟨C, hC⟩ := exists_integral_abs_fderiv_gcS_le (c := c) (h := h) hh
    have key := tendsto_integral_mul_fderiv_zero (Ω := Ω) (S := S)
      (fun n => gcS_contDiff _) (fun n => hasCompactSupport_gcS hh (gcDelta_pos n)) hSlim hS01 j
      (C := C) (fun n => hC _ (gcDelta_pos n) j)
      (f := fun x => W x * φ x) (hWc.mul hφ.continuous) hφc.mul_left ?_
    · refine key.congr fun n => ?_
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [mul_assoc]
    · intro ε hε
      have hpos : 0 < ε / (max B 0 + 1) := by positivity
      obtain ⟨g, hg, hgd, -⟩ := Continuous.exists_contDiff_approx (n := (⊤ : ℕ∞)) hWc
        (continuous_const (y := ε / (max B 0 + 1))) (fun _ => hpos)
      refine ⟨fun x => φ x * g x, hφ.mul hg, hφc.mul_right, ?_, fun x => ?_⟩
      · exact tsupport_mul_subset_left.trans hφΩ
      · have hdx := hgd x
        rw [Real.dist_eq] at hdx
        calc |W x * φ x - φ x * g x| = |φ x| * |W x - g x| := by
              rw [← abs_mul]; congr 1; ring
          _ ≤ max B 0 * (ε / (max B 0 + 1)) := by
              refine mul_le_mul (hBφ x) ?_ (abs_nonneg _) (le_max_right _ _)
              rw [abs_sub_comm]; exact hdx.le
          _ ≤ ε := by
              have hB0 : 0 ≤ max B 0 := le_max_right _ _
              calc max B 0 * (ε / (max B 0 + 1)) ≤ (max B 0 + 1) * (ε / (max B 0 + 1)) :=
                    mul_le_mul_of_nonneg_right (by linarith) hpos.le
                _ = ε := by field_simp
  -- assemble
  have hid : ∀ n, (∫ x, W x * (S n x * fderiv ℝ φ x (Pi.single j 1))) +
      (∫ x, W x * (φ x * fderiv ℝ (S n) x (Pi.single j 1))) =
      -∫ x, gluedGrad c h u j x * (S n x * φ x) := fun n =>
    sum_identity hh hdisj u hWc hW hφ hφc j (gcDelta_pos n)
  have h12 := I1.add I2
  have h3 := I3.neg
  have hfun : (fun n => (∫ x, W x * (S n x * fderiv ℝ φ x (Pi.single j 1))) +
      (∫ x, W x * (φ x * fderiv ℝ (S n) x (Pi.single j 1)))) =
      fun n => -∫ x, gluedGrad c h u j x * (S n x * φ x) := funext hid
  rw [hfun] at h12
  have := tendsto_nhds_unique h12 h3
  linarith

end

end SubdiffusiveProcess.Gluing
