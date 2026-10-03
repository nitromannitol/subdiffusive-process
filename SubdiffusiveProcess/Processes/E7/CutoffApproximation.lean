module

public import SubdiffusiveProcess.Processes.E7.WeightComparison
public import SubdiffusiveProcess.Processes.E7.GradMarkov
public import SubdiffusiveProcess.DirichletForm.Regular
public import Homogenization.Sobolev.Foundations.Cutoff.OpenSet

@[expose] public section

/-!
# Core functions supported in an open set are graph limits of `C_c^∞` functions supported in it

If `z` is a domain element with a continuous representative whose compact support lies in the open
set `U`, choose a smooth cutoff `χ` equal to one on the support and supported in `U`; multiplying an
approximating sequence of test functions by `χ` gives test functions supported in `U` which converge
to `z` in the graph norm.
-/
open MeasureTheory Filter Set Topology Homogenization
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

theorem dpartial_mul {f g : St d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (i : Fin d) : dpartial i (fun x => f x * g x) =
      fun x => f x * dpartial i g x + g x * dpartial i f x := by
  funext x
  have hfd : DifferentiableAt ℝ f x := (hf.differentiable (by decide)).differentiableAt
  have hgd : DifferentiableAt ℝ g x := (hg.differentiable (by decide)).differentiableAt
  unfold dpartial
  have h := (hfd.hasFDerivAt.mul hgd.hasFDerivAt).fderiv
  rw [show (fun x => f x * g x) = f * g from rfl, h]
  simp

theorem exists_test_approx_supported {c ρ : St d → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x) {U : Set (St d)} (hU : IsOpen U)
    {z : Lp ℝ 2 (wm ρ)} (hz : z ∈ gradDomain hc hρ)
    (hcore : DirichletForm.HasCoreRep (wm ρ) U z) :
    ∃ (ψ : ℕ → St d → ℝ) (hψ : ∀ n, ψ n ∈ testFns d), (∀ n, tsupport (ψ n) ⊆ U) ∧
      Tendsto (fun n => tcls hρ (ψ n) (hψ n)) atTop (𝓝 z) ∧
      ∀ i, Tendsto (fun n => gcls hc (ψ n) (hψ n) i) atTop (𝓝 (gradOf hc hρ z i)) := by
  obtain ⟨g0, hg0c, hg0cs, hg0U, hae⟩ := hcore
  set K := tsupport g0 with hK
  have hKc : IsCompact K := hg0cs
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_ball (0 : St d)
  obtain ⟨χ, hχ, hχb, hχ1, hχU⟩ := exists_contDiff_one_on_compact_tsupport_subset hKc
    (show K ⊆ U ∩ Metric.ball 0 R from fun x hx => ⟨hg0U hx, hR hx⟩)
    (hU.inter Metric.isOpen_ball)
  have hχW : tsupport χ ⊆ Metric.ball (0 : St d) R := fun x hx => (hχU hx).2
  have hχcs : HasCompactSupport χ :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport χ)
      ((Metric.isBounded_ball).subset hχW)
  obtain ⟨φ, hφ, h1, h2⟩ := exists_test_sequence hc hρ hcpos hρpos hz
  have hψ : ∀ n, (fun x => χ x * φ n x) ∈ testFns d := fun n =>
    ⟨hχ.mul (hφ n).1, (hφ n).2.mul_left⟩
  -- a.e. facts
  have hz0 : ∀ᵐ x ∂(volume : Measure (St d)), x ∈ Kᶜ → z x = 0 := by
    filter_upwards [ae_volume_of_ae_wm hρ hρpos hae] with x hx hxK
    rw [hx]
    exact image_eq_zero_of_notMem_tsupport hxK
  have hzχ : ∀ᵐ x ∂(wm ρ), χ x * z x = z x := by
    refine ae_wm_of_ae_volume hρ hρpos ?_
    filter_upwards [hz0] with x hx
    by_cases hxK : x ∈ K
    · rw [hχ1 hxK]; simp
    · rw [hx hxK]; simp
  have hgχ : ∀ i, ∀ᵐ x ∂(wm c), χ x * gradOf hc hρ z i x = gradOf hc hρ z i x := by
    intro i
    refine ae_wm_of_ae_volume hc hcpos ?_
    filter_upwards [gradOf_ae_zero_of_ae_zero hc hρ hcpos hρpos hz hKc.isClosed.isOpen_compl hz0 i]
      with x hx
    by_cases hxK : x ∈ K
    · rw [hχ1 hxK]; simp
    · rw [hx hxK]; simp
  have hdχ0 : ∀ i, ∀ x ∈ K, dpartial i χ x = 0 := by
    intro i x hx
    have hmax : IsLocalMax χ x := by
      refine Filter.Eventually.of_forall fun y => ?_
      rw [show χ x = 1 from hχ1 hx]
      exact (hχb y).2
    have : fderiv ℝ χ x = 0 := hmax.fderiv_eq_zero
    simp [dpartial, this]
  refine ⟨fun n x => χ x * φ n x, hψ, fun n => ?_, ?_, ?_⟩
  · exact ((tsupport_mul_subset_left (f := χ) (g := φ n)).trans hχU).trans inter_subset_left
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_eLpNorm_tcls hρ h1) (fun _ => zero_le) (fun n => ?_)
    refine eLpNorm_mono_ae
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_wm_of_test hρ (hψ n)), hzχ] with x hx hx2
    simp only [tcls, Pi.sub_apply, hx]
    have : χ x * φ n x - z x = χ x * (φ n x - z x) := by
      have := hx2; nlinarith [this]
    rw [this, norm_mul]
    calc ‖χ x‖ * ‖φ n x - z x‖ ≤ 1 * ‖φ n x - z x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg (hχb x).1]
          exact (hχb x).2
      _ = ‖φ n x - z x‖ := one_mul _
  · intro i
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    have hdχcont : Continuous (dpartial i χ) := dpartial_mem_test_cont ⟨hχ, hχcs⟩ i
    have hdχcs : HasCompactSupport (dpartial i χ) := by
      unfold dpartial
      exact HasCompactSupport.comp_left (g := fun (f : St d →L[ℝ] ℝ) => f (Pi.single i 1))
        (HasCompactSupport.fderiv ℝ hχcs)
        (by change (0 : St d →L[ℝ] ℝ) (Pi.single i 1) = 0; simp)
    obtain ⟨M, hM⟩ := hdχcont.bounded_above_of_compact_support hdχcs
    obtain ⟨C, hC, hCle⟩ := eLpNorm_wm_le_wm hc hρ hρpos (W := Metric.ball (0 : St d) R)
      Metric.isOpen_ball.measurableSet Metric.isBounded_ball
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
    set g := gradOf hc hρ z i with hg
    have ha := tendsto_eLpNorm_gcls hc (h2 i)
    have hb := tendsto_eLpNorm_tcls hρ h1
    have hlim : Tendsto (fun n => eLpNorm (fun x => dpartial i (φ n) x - g x) 2 (wm c) +
        (‖M‖ₑ * C) * eLpNorm (fun x => φ n x - z x) 2 (wm ρ)) atTop (𝓝 0) := by
      have := ha.add (ENNReal.Tendsto.const_mul hb (Or.inr (ENNReal.mul_ne_top
        (enorm_ne_top (x := M)) hC)))
      simpa [Function.comp_def, g] using! this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun n => ?_)
    -- pointwise decomposition
    have hφm : StronglyMeasurable (φ n) := (hφ n).1.continuous.stronglyMeasurable
    have hdφm : StronglyMeasurable (dpartial i (φ n)) :=
      (dpartial_mem_test_cont (hφ n) i).stronglyMeasurable
    have hum : StronglyMeasurable ⇑z := Lp.stronglyMeasurable z
    have hgm : StronglyMeasurable ⇑g := Lp.stronglyMeasurable g
    have hm1 : AEStronglyMeasurable (fun x => χ x * (dpartial i (φ n) x - g x)) (wm c) :=
      (hχ.continuous.stronglyMeasurable.mul (hdφm.sub hgm)).aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun x => (φ n x - z x) * dpartial i χ x) (wm c) :=
      ((hφm.sub hum).mul hdχcont.stronglyMeasurable).aestronglyMeasurable
    have hae2 : ∀ᵐ x ∂(wm c), z x * dpartial i χ x = 0 := by
      refine ae_wm_of_ae_volume hc hcpos ?_
      filter_upwards [hz0] with x hx
      by_cases hxK : x ∈ K
      · rw [hdχ0 i x hxK, mul_zero]
      · rw [hx hxK, zero_mul]
    have hcoe : (⇑(gcls hc (fun x => χ x * φ n x) (hψ n) i) - ⇑g) =ᵐ[wm c]
        fun x => χ x * (dpartial i (φ n) x - g x) + (φ n x - z x) * dpartial i χ x := by
      filter_upwards [MemLp.coeFn_toLp (memLp_wm_dpartial hc (hψ n) i), hgχ i, hae2]
        with x hx hx2 hx3
      have hx' : (⇑(gcls hc (fun x => χ x * φ n x) (hψ n) i)) x =
          dpartial i (fun x => χ x * φ n x) x := hx
      simp only [Pi.sub_apply]
      rw [hx', dpartial_mul hχ (hφ n).1 i]
      linear_combination hx2 + hx3
    rw [eLpNorm_congr_ae hcoe]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
    · refine eLpNorm_mono hm1 fun x => ?_
      rw [norm_mul]
      calc ‖χ x‖ * ‖dpartial i (φ n) x - g x‖ ≤ 1 * ‖dpartial i (φ n) x - g x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [Real.norm_eq_abs, abs_of_nonneg (hχb x).1]
            exact (hχb x).2
        _ = ‖dpartial i (φ n) x - g x‖ := one_mul _
    · have hvan : ∀ x, x ∉ Metric.ball (0 : St d) R →
          (φ n x - z x) * dpartial i χ x = 0 := by
        intro x hx
        have : x ∉ tsupport χ := fun h => hx (hχW h)
        have h0 : fderiv ℝ χ x = 0 :=
          Function.notMem_support.mp fun hs => this (support_fderiv_subset ℝ hs)
        simp [dpartial, h0]
      calc eLpNorm (fun x => (φ n x - z x) * dpartial i χ x) 2 (wm c)
          ≤ C * eLpNorm (fun x => (φ n x - z x) * dpartial i χ x) 2 (wm ρ) := hCle _ hvan
        _ ≤ C * (‖M‖ₑ * eLpNorm (fun x => φ n x - z x) 2 (wm ρ)) := by
            gcongr
            calc eLpNorm (fun x => (φ n x - z x) * dpartial i χ x) 2 (wm ρ)
                ≤ eLpNorm (M • fun x => φ n x - z x) 2 (wm ρ) := by
                  refine eLpNorm_mono
                    ((hφm.aestronglyMeasurable.sub (Lp.aestronglyMeasurable z)).mul
                      ((dpartial_mem_test_cont ⟨hχ, hχcs⟩ i).stronglyMeasurable.aestronglyMeasurable)) fun x => ?_
                  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
                  rw [mul_comm]
                  exact mul_le_mul_of_nonneg_right
                    ((hM x).trans (by rw [Real.norm_eq_abs]; exact le_abs_self M)) (norm_nonneg _)
              _ = ‖M‖ₑ * eLpNorm (fun x => φ n x - z x) 2 (wm ρ) := by rw [eLpNorm_const_smul]
        _ = ‖M‖ₑ * C * eLpNorm (fun x => φ n x - z x) 2 (wm ρ) := by ring

end SubdiffusiveProcess.E7
