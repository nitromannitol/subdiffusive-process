module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.VariationalZeroTraceComposition
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserPowerTests
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.MassiveMaximumPrinciple

@[expose] public section

/-!
# Nonlinear zero-boundary tests for the Green inverse

The qualitative bound is used only to construct the zero-trace powers.
The functions and gradient identities retain their exact power formulas.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Any chosen H¹ witness of a zero-trace function can be upgraded to H¹₀. -/
theorem variational_h10_upgrade {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (v : H1Function U) (hv : MemH10 U v.toFun) :
    ∃ w : H10Function U, w.toH1Function = v := by
  obtain ⟨w, hw⟩ := hv
  have hgrad := Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hU
    (show w.toH1Function.toFun =ᵐ[volume.restrict U] v.toFun by rw [hw])
  refine ⟨{ toH1Function := v
            approx := w.approx
            approx_smooth := w.approx_smooth
            approx_hasCompactSupport := w.approx_hasCompactSupport
            approx_support_subset := w.approx_support_subset
            tendsto_approx := by simpa only [hw] using w.tendsto_approx
            tendsto_approx_grad := ?_ }, rfl⟩
  intro i
  refine (w.tendsto_approx_grad i).congr (fun n => ?_)
  apply eLpNorm_congr_ae
  filter_upwards [hgrad] with x hx
  rw [hx]

/-- Zero-preserving C¹ nonlinearities preserve zero trace on a bounded input. -/
theorem variational_memH10_comp_of_bounded {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H10Function U) (v : H1Function U)
    {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ᵐ x ∂volume.restrict U, |u.toH1Function.toFun x| ≤ M)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) (hG0 : G 0 = 0)
    (hv : v.toFun = fun x => G (u.toH1Function.toFun x)) : MemH10 U v.toFun := by
  let chi : ContDiffBump (0 : ℝ) := ⟨M + 1, M + 2, by linarith, by linarith⟩
  let H : ℝ → ℝ := fun t => chi t * G t
  have hH : ContDiff ℝ 1 H := (chi.contDiff : ContDiff ℝ 1 chi).mul hG
  have hHc : HasCompactSupport H := chi.hasCompactSupport.mul_right
  obtain ⟨D, hD⟩ := hHc.deriv.exists_bound_of_continuous (hH.continuous_deriv le_rfl)
  have hlocal (t : ℝ) (ht : |t| ≤ M) : H =ᶠ[nhds t] G := by
    have htball : t ∈ Metric.ball (0 : ℝ) chi.rIn := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      change |t| < M + 1
      linarith
    filter_upwards [chi.eventuallyEq_one_of_mem_ball htball] with s hs
    change chi s * G s = G s
    rw [show chi s = 1 from hs, one_mul]
  obtain ⟨w, hw, hwg⟩ := exists_moser_h1_comp hU u.toH1Function hM hu hG
  have hgrad := Homogenization.Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq hU.isOpen
    (show v.toFun =ᵐ[volume.restrict U] w.toFun by rw [hv, hw])
  apply variational_memH10_comp hU u v hH (by simp only [H, hG0, mul_zero])
    (le_max_right D 0) (fun t => (hD t).trans (le_max_left D 0))
  · filter_upwards [hu] with x hx
    rw [hv]
    exact ((hlocal _ hx).eq_of_nhds).symm
  · intro i
    filter_upwards [hu, hgrad] with x hx hg
    rw [hg, hwg]
    dsimp only
    rw [(hlocal _ hx).deriv_eq]

/-- Both positive powers in the Green test are genuine zero-trace functions. -/
theorem exists_variational_power_pair {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H10Function U)
    {M : ℝ} (hM : 0 ≤ M)
    (hu : ∀ᵐ x ∂volume.restrict U, |u.toH1Function.toFun x| ≤ M)
    {s : ℝ} (hs : 1 ≤ s) :
    ∃ w f : H10Function U,
      w.toH1Function.toFun = (fun x => (max (u.toH1Function.toFun x) 0) ^ s) ∧
      f.toH1Function.toFun = (fun x => (max (u.toH1Function.toFun x) 0) ^ (2 * s - 1)) ∧
      MoserPowerPair u.toH1Function w.toH1Function f.toH1Function s := by
  obtain ⟨w, f, hw, hf, hpair⟩ := exists_moser_power_pair hU u.toH1Function hM hu hs
  obtain ⟨v, hv, _⟩ := exists_h10_positivePart hU u (k := 0) le_rfl
  simp only [sub_zero] at hv
  have hvM : ∀ᵐ x ∂volume.restrict U, |v.toH1Function.toFun x| ≤ M := by
    filter_upwards [hu] with x hx
    rw [hv, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans hx) hM
  have hwm : MemH10 U w.toFun := variational_memH10_comp_of_bounded hU v w hM hvM
    (Real.contDiff_rpow_const_of_le (n := 1) (by simpa using hs))
    (Real.zero_rpow (by linarith : s ≠ 0)) (by simp only [hw, hv])
  have hfm : MemH10 U f.toFun := variational_memH10_comp_of_bounded hU v f hM hvM
    (Real.contDiff_rpow_const_of_le (p := 2 * s - 1) (n := 1) (by norm_num; linarith))
    (Real.zero_rpow (by linarith : 2 * s - 1 ≠ 0)) (by simp only [hf, hv])
  obtain ⟨w0, hw0⟩ := variational_h10_upgrade hU.isOpen w hwm
  obtain ⟨f0, hf0⟩ := variational_h10_upgrade hU.isOpen f hfm
  exact ⟨w0, f0, by simpa only [hw0] using hw, by simpa only [hf0] using hf,
    by simpa only [hw0, hf0] using hpair⟩

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
