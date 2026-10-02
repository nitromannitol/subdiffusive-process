import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.InteriorLogEnergy
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

/-! The logarithmic energy estimate for the source's continuous local weak
solutions. Compactness supplies the temporary upper bound. Adding `epsilon`
supplies the lower bound, and the final constant is uniform in `epsilon`. -/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A nonnegative local weak solution has a regularized logarithm with a
cutoff energy estimate uniform in the positive regularization parameter. -/
theorem interior_weakHarmonic_log_energy {d : ℕ} {U W : Set (Vec d)}
    (hW : IsOpenBoundedConvexDomain W) (hsub : closure W ⊆ U)
    {a h : Vec d → ℝ} {lam Lam : ℝ} (hlam : 0 < lam)
    (ha : AEStronglyMeasurable a (volume.restrict W))
    (hab : ∀ᵐ x ∂volume.restrict W, lam ≤ a x ∧ a x ≤ Lam)
    (hh : WeakHarmonic a U h) (hh0 : ∀ x ∈ U, 0 ≤ h x)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {eta : Vec d → ℝ} (heta : ContDiff ℝ (⊤ : ℕ∞) eta)
    (hetac : HasCompactSupport eta) (hetasub : tsupport eta ⊆ W)
    (hetaRange : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) :
    ∃ w : H1Function W,
      (∀ᵐ x ∂volume.restrict W, w.toFun x = Real.log (h x + epsilon)) ∧
      (∫ x in W, eta x ^ 2 * vecNormSq (w.grad x)) ≤
        (4 * Lam / lam) * ∫ x in W, vecNormSq (euclideanGradient eta x) := by
  letI : IsFiniteMeasure (volumeMeasureOn W) := hW.isFiniteMeasure_restrict_volume
  have hcompact := hW.isBoundedDomain.isBounded.isCompact_closure
  obtain ⟨u, hueq, hu⟩ := hh.2 W hW.isOpen hcompact hsub
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn (hh.1.mono hsub)
  let v := u.addConst epsilon
  have hval (x : Vec d) : v.toFun x = u.toFun x + epsilon := rfl
  have hv : IsWeaklyHarmonicOn a W v := by
    intro phi
    simpa only [v, H1Function.grad_addConst, vecDot_smul_left] using hu phi
  have hvb : ∀ᵐ x ∂volume.restrict W,
      epsilon ≤ v.toFun x ∧ |v.toFun x| ≤ max M 0 + epsilon := by
    filter_upwards [hueq, ae_restrict_mem hW.isOpen.measurableSet] with x hx hxW
    rw [hval, hx]
    have hxU := hsub (subset_closure hxW)
    have hx0 := hh0 x hxU
    constructor
    · linarith
    · calc
        |h x + epsilon| ≤ |h x| + |epsilon| := abs_add_le _ _
        _ ≤ max M 0 + epsilon := by
          rw [abs_of_pos hepsilon]
          have hMx : |h x| ≤ max M 0 := by
            simpa only [Real.norm_eq_abs] using
              (hM x (subset_closure hxW)).trans (le_max_left M 0)
          exact add_le_add hMx le_rfl
  obtain ⟨w, hw, _, henergy⟩ := interior_log_caccioppoli_cutoff hW hlam ha hab v hv
    hepsilon (show 0 ≤ max M 0 + epsilon by positivity) hvb heta hetac hetasub hetaRange
  refine ⟨w, ?_, henergy⟩
  filter_upwards [hueq] with x hx
  rw [hw]
  change Real.log (v.toFun x) = _
  rw [hval, hx]

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
