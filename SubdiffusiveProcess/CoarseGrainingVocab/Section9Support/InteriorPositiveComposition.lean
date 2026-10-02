import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.MoserBoundedComposition

/-!
# Positive nonlinear tests for the interior Harnack argument

A positive lower bound and a qualitative upper bound justify compositions
with any function that is `C¹` on the positive half-line. In particular this
applies to the logarithm and to negative powers. The bounds enter only the
construction of the Sobolev witness, whose exported gradient is exact.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open scoped Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Extend a positive-half-line profile smoothly across zero, without changing
it in a neighborhood of any input at least `epsilon`. -/
theorem exists_contDiff_positive_extension {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Ioi 0)) :
    ∃ H : ℝ → ℝ, ContDiff ℝ 1 H ∧
      ∀ t, epsilon ≤ t → H =ᶠ[𝓝 t] G := by
  let chi : ℝ → ℝ := fun t => Real.smoothTransition (4 * t / epsilon - 2)
  let H : ℝ → ℝ := fun t => chi t * G t
  have hchi : ContDiff ℝ 1 chi :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).div_const epsilon |>.sub contDiff_const)
  have hzero (t : ℝ) (ht : t < epsilon / 2) : chi t = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    apply sub_nonpos.mpr
    apply (div_le_iff₀ hepsilon).mpr
    linarith
  refine ⟨H, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : 0 < t
    · exact hchi.contDiffAt.mul (hG.contDiffAt (isOpen_Ioi.mem_nhds ht))
    · have ht' : t < epsilon / 2 := by linarith
      have heq : H =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds ht'] with s hs
        change chi s * G s = 0
        rw [hzero s hs, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · intro t ht
    have ht' : 3 * epsilon / 4 < t := by linarith
    filter_upwards [Ioi_mem_nhds ht'] with s hs
    change chi s * G s = G s
    have hchi1 : chi s = 1 := by
      apply Real.smoothTransition.one_of_one_le
      change 3 * epsilon / 4 < s at hs
      have : 3 ≤ 4 * s / epsilon := (le_div_iff₀ hepsilon).mpr (by linarith)
      linarith
    rw [hchi1, one_mul]

/-- Exact Sobolev composition for a bounded function bounded away from zero.
The profile need only be `C¹` at positive arguments. -/
theorem exists_interior_positive_h1_comp {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {epsilon M : ℝ} (hepsilon : 0 < epsilon) (hM : 0 ≤ M)
    (hu : ∀ᵐ x ∂volume.restrict U, epsilon ≤ u.toFun x ∧ |u.toFun x| ≤ M)
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Ioi 0)) :
    ∃ v : H1Function U,
      v.toFun = (fun x => G (u.toFun x)) ∧
      v.grad = (fun x i => deriv G (u.toFun x) * u.grad x i) := by
  obtain ⟨H, hH, hlocal⟩ := exists_contDiff_positive_extension hepsilon hG
  obtain ⟨v, hv, hvg⟩ := exists_moser_h1_comp hU u hM (hu.mono fun _ hx => hx.2) hH
  have hval : v.toFun =ᵐ[volume.restrict U] fun x => G (u.toFun x) := by
    rw [hv]
    exact hu.mono fun x hx => (hlocal _ hx.1).eq_of_nhds
  have hgrad : v.grad =ᵐ[volume.restrict U]
      fun x i => deriv G (u.toFun x) * u.grad x i := by
    rw [hvg]
    filter_upwards [hu] with x hx
    funext i
    rw [(hlocal _ hx.1).deriv_eq]
  refine ⟨{ toFun := fun x => G (u.toFun x)
            grad := fun x i => deriv G (u.toFun x) * u.grad x i
            memL2 := v.memL2.ae_eq hval
            gradMemL2 := fun i => (v.gradMemL2 i).ae_eq
              (hgrad.mono fun x hx => congrFun hx i)
            hasWeakGradient := ?_ }, rfl, rfl⟩
  intro i phi hphi hphic hphisub
  have heq := v.hasWeakGradient i phi hphi hphic hphisub
  have hl : (∫ x in U, v.toFun x * (fderiv ℝ phi x) (basisVec i)) =
      ∫ x in U, G (u.toFun x) * (fderiv ℝ phi x) (basisVec i) :=
    integral_congr_ae (hval.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
  have hr : (∫ x in U, v.grad x i * phi x) =
      ∫ x in U, (deriv G (u.toFun x) * u.grad x i) * phi x :=
    integral_congr_ae (hgrad.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
  rwa [hl, hr] at heq

/-- Every real power, including negative powers, is an admissible local `H¹`
composition of a bounded positive function. -/
theorem exists_interior_positive_power {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {epsilon M : ℝ} (hepsilon : 0 < epsilon) (hM : 0 ≤ M)
    (hu : ∀ᵐ x ∂volume.restrict U, epsilon ≤ u.toFun x ∧ |u.toFun x| ≤ M)
    (p : ℝ) :
    ∃ v : H1Function U, v.toFun = (fun x => u.toFun x ^ p) ∧
      v.grad = (fun x i => p * u.toFun x ^ (p - 1) * u.grad x i) := by
  have hp : ContDiffOn ℝ 1 (fun t : ℝ => t ^ p) (Ioi 0) := fun t ht =>
    (Real.contDiffAt_rpow_const_of_ne (ne_of_gt ht)).contDiffWithinAt
  obtain ⟨v, hv, hvg⟩ := exists_interior_positive_h1_comp hU u hepsilon hM hu hp
  refine ⟨v, hv, ?_⟩
  simpa only [Real.deriv_rpow_const] using hvg

/-- The logarithm and reciprocal have their exact weak gradients. -/
theorem exists_interior_log_reciprocal {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {epsilon M : ℝ} (hepsilon : 0 < epsilon) (hM : 0 ≤ M)
    (hu : ∀ᵐ x ∂volume.restrict U, epsilon ≤ u.toFun x ∧ |u.toFun x| ≤ M) :
    ∃ w f : H1Function U,
      w.toFun = (fun x => Real.log (u.toFun x)) ∧
      f.toFun = (fun x => (u.toFun x)⁻¹) ∧
      w.grad = (fun x i => (u.toFun x)⁻¹ * u.grad x i) ∧
      f.grad = (fun x i => -((u.toFun x)⁻¹ ^ 2) * u.grad x i) := by
  have hsub : Ioi (0 : ℝ) ⊆ {0}ᶜ := fun _ hx => ne_of_gt hx
  obtain ⟨w, hw, hwg⟩ := exists_interior_positive_h1_comp hU u hepsilon hM hu
    (Real.contDiffOn_log.mono hsub)
  obtain ⟨f, hf, hfg⟩ := exists_interior_positive_h1_comp hU u hepsilon hM hu
    ((contDiffOn_inv ℝ).mono hsub)
  refine ⟨w, f, hw, hf, ?_, ?_⟩
  · simpa only [Real.deriv_log] using hwg
  · simpa only [deriv_inv, inv_pow] using hfg

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
