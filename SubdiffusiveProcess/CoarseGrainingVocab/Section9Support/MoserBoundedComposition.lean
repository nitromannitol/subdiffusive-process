module

public import Homogenization.Sobolev.Truncation.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# Nonlinear `H¹` compositions of bounded functions

The bound on the input is used only to justify the chain rule. A smooth
cutoff in the value variable reduces a `C¹` nonlinearity to one with bounded
derivative, and the existing Sobolev chain rule then applies. The resulting
function and gradient are the original, uncut formulas.
-/

set_option autoImplicit false
noncomputable section
open Homogenization MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A bounded `H¹` function admits every `C¹` real composition, with its exact weak gradient. -/
theorem exists_moser_h1_comp {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U)
    {M : ℝ} (hM : 0 ≤ M) (hu : ∀ᵐ x ∂volume.restrict U, |u.toFun x| ≤ M)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    ∃ v : H1Function U,
      v.toFun = (fun x => G (u.toFun x)) ∧
      v.grad = (fun x i => deriv G (u.toFun x) * u.grad x i) := by
  letI : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
  let chi : ContDiffBump (0 : ℝ) := ⟨M + 1, M + 2, by linarith, by linarith⟩
  let H : ℝ → ℝ := fun t => chi t * G t
  have hH : ContDiff ℝ 1 H := (chi.contDiff : ContDiff ℝ 1 chi).mul hG
  have hHc : HasCompactSupport H := chi.hasCompactSupport.mul_right
  have hDcont : Continuous (deriv H) := hH.continuous_deriv le_rfl
  obtain ⟨D, hD⟩ := hHc.deriv.exists_bound_of_continuous hDcont
  let D' := max D 0
  have hD' : ∀ t, |deriv H t| ≤ D' := fun t =>
    (hD t).trans (le_max_left _ _)
  have hlocal (t : ℝ) (ht : |t| ≤ M) : H =ᶠ[𝓝 t] G := by
    have htball : t ∈ Metric.ball (0 : ℝ) chi.rIn := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      change |t| < M + 1
      linarith
    filter_upwards [chi.eventuallyEq_one_of_mem_ball htball] with s hs
    change chi s * G s = G s
    rw [show chi s = 1 from hs, one_mul]
  have hval : (fun x => H (u.toFun x)) =ᵐ[volume.restrict U] fun x => G (u.toFun x) :=
    hu.mono fun x hx => (hlocal _ hx).eq_of_nhds
  have hder : (fun x => deriv H (u.toFun x)) =ᵐ[volume.restrict U]
      fun x => deriv G (u.toFun x) :=
    hu.mono fun x hx => (hlocal _ hx).deriv_eq
  obtain ⟨B, hB⟩ := hHc.exists_bound_of_continuous hH.continuous
  have hmem : MemLp (fun x => H (u.toFun x)) 2 (volume.restrict U) :=
    MemLp.of_bound (hH.continuous.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable)
      B (Eventually.of_forall fun x => hB _)
  have hgrad (i : Fin d) : MemLp
      (fun x => deriv H (u.toFun x) * u.grad x i) 2 (volume.restrict U) := by
    refine ((u.gradMemL2 i).const_mul D').mono
      ((hDcont.comp_aestronglyMeasurable u.memL2.aestronglyMeasurable).mul
        (u.gradMemL2 i).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (le_max_right D 0)]
    exact mul_le_mul_of_nonneg_right (hD' _) (norm_nonneg _)
  have hweak := hasWeakGradientOn_comp_of_deriv_bounded hU u hH
    (le_max_right D 0) hD'
  refine ⟨{ toFun := fun x => G (u.toFun x)
            grad := fun x i => deriv G (u.toFun x) * u.grad x i
            memL2 := hmem.ae_eq hval
            gradMemL2 := fun i => (hgrad i).ae_eq (hder.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
            hasWeakGradient := ?_ }, rfl, rfl⟩
  intro i phi hphi hphic hphisub
  have heq := hweak i phi hphi hphic hphisub
  have hl : (∫ x in U, H (u.toFun x) * (fderiv ℝ phi x) (basisVec i)) =
      ∫ x in U, G (u.toFun x) * (fderiv ℝ phi x) (basisVec i) :=
    integral_congr_ae (hval.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
  have hr : (∫ x in U, (deriv H (u.toFun x) * u.grad x i) * phi x) =
      ∫ x in U, (deriv G (u.toFun x) * u.grad x i) * phi x :=
    integral_congr_ae (hder.mono fun x hx => by dsimp only at hx ⊢; rw [hx])
  rwa [hl, hr] at heq

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
