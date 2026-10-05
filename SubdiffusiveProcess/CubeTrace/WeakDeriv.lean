module

public import Mathlib
public import Homogenization.Sobolev.WeakDerivatives

@[expose] public section

/-!
# Cube trace extension: a function of class `C¹` on an open set has its classical partial
derivatives as weak partial derivatives there

The test function is its own cutoff: for `φ` with `tsupport φ ⊆ U` the product `f φ` is
differentiable on all of `ℝ^d` (off `U` it vanishes on a neighbourhood), so Mathlib's
integration by parts against the constant `1` gives `∫ ∂ᵢ(f φ) = 0`.
-/

open MeasureTheory Set Filter
open scoped ContDiff Topology
noncomputable section
namespace SubdiffusiveProcess.CubeTrace

variable {d : ℕ}

theorem ct_mul_continuous {U : Set (Fin d → ℝ)} (hU : IsOpen U) {u ψ : (Fin d → ℝ) → ℝ}
    (hu : ContinuousOn u U) (hψ : Continuous ψ) (hsub : tsupport ψ ⊆ U) :
    Continuous fun x => u x * ψ x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact ((hu x hx).continuousAt (hU.mem_nhds hx)).mul hψ.continuousAt
  · have hxs : x ∉ tsupport ψ := fun hx' => hx (hsub hx')
    have hzero : (fun y => u y * ψ y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hxs] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact continuousAt_const.congr hzero.symm

theorem ct_tsupport_fderiv_apply_subset {φ : (Fin d → ℝ) → ℝ} (v : Fin d → ℝ) :
    tsupport (fun x => (fderiv ℝ φ x) v) ⊆ tsupport φ := by
  refine closure_minimal ?_ (isClosed_tsupport φ)
  intro x hx
  by_contra hxs
  have hzero : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxs] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  have : fderiv ℝ φ x = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hzero]
    simp
  exact hx (by simp [this])

theorem ct_hasWeakPartialDerivOn {U : Set (Fin d → ℝ)} (hU : IsOpen U) {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (i : Fin d) :
    Homogenization.HasWeakPartialDerivOn U i f (fun x => fderiv ℝ f x (Pi.single i 1)) := by
  intro φ hφ_smooth hφ_supp hφ_sub
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by simp)
  have hφ_cont : Continuous φ := hφ_diff.continuous
  have hdφ_cont : Continuous fun x => (fderiv ℝ φ x) (Homogenization.basisVec i) := by
    simpa using (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfd : ∀ y ∈ U, HasFDerivAt f (fderiv ℝ f y) y := fun y hy =>
    ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hf_cont : ContinuousOn f U := hf.continuousOn
  have hG_cont : ContinuousOn (fun x => fderiv ℝ f x (Pi.single i 1)) U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  set A : (Fin d → ℝ) → ℝ := fun x => f x * φ x with hA
  set D : (Fin d → ℝ) → ((Fin d → ℝ) →L[ℝ] ℝ) :=
    fun x => f x • fderiv ℝ φ x + φ x • fderiv ℝ f x with hD
  have hhas : ∀ x, HasFDerivAt A (D x) x := by
    intro x
    by_cases hx : x ∈ U
    · exact (hfd x hx).mul (hφ_diff x).hasFDerivAt
    · have hxs : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
      have hφ_eq : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxs] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
      have hfderiv_zero : fderiv ℝ φ x = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
        simp
      have hDx : D x = 0 := by
        simp [hD, hfderiv_zero, image_eq_zero_of_notMem_tsupport hxs]
      rw [hDx]
      refine (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq ?_
      filter_upwards [hφ_eq] with y hy
      simp [hA, hy]
  have hA_diff : Differentiable ℝ A := fun x => (hhas x).differentiableAt
  have hfderiv_A : ∀ x, fderiv ℝ A x = D x := fun x => (hhas x).fderiv
  have hDval : ∀ x, (D x) (Pi.single i 1) =
      f x * (fderiv ℝ φ x) (Pi.single i 1) + fderiv ℝ f x (Pi.single i 1) * φ x := by
    intro x
    simp [hD, mul_comm]
  have hA_supp : HasCompactSupport A := hφ_supp.mul_left
  have hA_int : Integrable A volume :=
    hA_diff.continuous.integrable_of_hasCompactSupport hA_supp
  have hB_cont : Continuous fun x => f x * (fderiv ℝ φ x) (Pi.single i 1) :=
    ct_mul_continuous hU hf_cont hdφ_cont ((ct_tsupport_fderiv_apply_subset _).trans hφ_sub)
  have hB_int : Integrable (fun x => f x * (fderiv ℝ φ x) (Pi.single i 1)) volume :=
    hB_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.mul_left (hφ_supp.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)))
  have hC_cont : Continuous fun x => fderiv ℝ f x (Pi.single i 1) * φ x :=
    ct_mul_continuous hU hG_cont hφ_cont hφ_sub
  have hC_int : Integrable (fun x => fderiv ℝ f x (Pi.single i 1) * φ x) volume :=
    hC_cont.integrable_of_hasCompactSupport hφ_supp.mul_left
  have hD_int : Integrable (fun x => (fderiv ℝ A x) (Pi.single i 1)) volume := by
    refine (hB_int.add hC_int).congr ?_
    filter_upwards with x
    simp only [Pi.add_apply]
    rw [hfderiv_A x, hDval x]
  have key : ∫ x, A x * (fderiv ℝ (fun _ : Fin d → ℝ => (1 : ℝ)) x) (Pi.single i 1)
      = -∫ x, (fderiv ℝ A x) (Pi.single i 1) * (1 : ℝ) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (by simpa using hD_int) (by simp) (by simpa using hA_int) (fun x _ => hA_diff x) (fun x _ => differentiableAt_const (1 : ℝ))
  have hkey : ∫ x, (fderiv ℝ A x) (Pi.single i 1) = 0 := by
    have h0 : (0 : ℝ) = -∫ x, (fderiv ℝ A x) (Pi.single i 1) := by simpa using key
    linarith [h0]
  have hsplit : ∫ x, f x * (fderiv ℝ φ x) (Pi.single i 1)
      = -∫ x, fderiv ℝ f x (Pi.single i 1) * φ x := by
    have hsum : ∫ x, (fderiv ℝ A x) (Pi.single i 1)
        = (∫ x, f x * (fderiv ℝ φ x) (Pi.single i 1)) +
          ∫ x, fderiv ℝ f x (Pi.single i 1) * φ x := by
      rw [← integral_add hB_int hC_int]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [hfderiv_A x, hDval x]
    rw [hsum] at hkey
    linarith [hkey]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hsplit
  · intro x hx
    have hxs : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
    simp [image_eq_zero_of_notMem_tsupport hxs]
  · intro x hx
    have hxs : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
    have hφ_eq : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxs] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    have : fderiv ℝ φ x = 0 := by
      rw [Filter.EventuallyEq.fderiv_eq hφ_eq]
      simp
    simp [this]

end SubdiffusiveProcess.CubeTrace
