module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.StrongValueWeakGradientEquation

@[expose] public section

/-!
# Bounded pointwise limits of local massive solutions

This file packages the local analytic limit used by the expanding-cube
construction.  A common pointwise bound upgrades almost-everywhere convergence
to strong local `L²` convergence; a uniform gradient bound then supplies an
`H¹` limit, and the massive equation passes to that limit.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization

noncomputable section

variable {d : ℕ} {W : Set (Vec d)}

/-- On a finite-measure window, a uniformly bounded pointwise limit of local
massive solutions with uniformly bounded gradients has an `H¹` representative
which solves the limiting massive equation. -/
theorem exists_isMassiveWeakSolutionOn_of_bounded_pointwise_limit
    [IsFiniteMeasure (volumeMeasureOn W)]
    {c rho : Vec d → ℝ} {mu lam Lam rhoMax C Cgrad : ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    {f u : Vec d → ℝ} (hf : MemL2On W f)
    (w : ℕ → H1Function W)
    (hbound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn W), |(w n).toFun x| ≤ C)
    (hpoint : ∀ᵐ x ∂(volumeMeasureOn W),
      Tendsto (fun n ↦ (w n).toFun x) atTop (nhds (u x)))
    (hgradient : ∀ n, ‖(w n).gradToHilbertVectorL2‖ ≤ Cgrad)
    (hw : ∀ n, IsMassiveWeakSolutionOn c rho mu W (w n) f) :
    ∃ v : H1Function W,
      v.toFun =ᵐ[volumeMeasureOn W] u ∧
        IsMassiveWeakSolutionOn c rho mu W v f := by
  have hwMeas : ∀ n, AEStronglyMeasurable (w n).toFun (volumeMeasureOn W) :=
    fun n ↦ (w n).memL2.aestronglyMeasurable
  have huMeas : AEStronglyMeasurable u (volumeMeasureOn W) :=
    aestronglyMeasurable_of_tendsto_ae atTop hwMeas hpoint
  have huBound : ∀ᵐ x ∂(volumeMeasureOn W), ‖u x‖ ≤ C := by
    filter_upwards [hpoint, ae_all_iff.2 hbound] with x hx hxb
    have hmem : u x ∈ Set.Icc (-C) C := by
      apply isClosed_Icc.mem_of_tendsto hx
      exact Filter.Eventually.of_forall fun n ↦ (abs_le.mp (hxb n))
    simpa only [Real.norm_eq_abs] using (abs_le.mpr hmem)
  have hu : MemL2On W u := MemLp.of_bound huMeas C huBound
  have hvalue : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ (w n).toFun x - u x) 2
        (volumeMeasureOn W)) atTop (nhds 0) :=
    tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hwMeas hu
      (memLp_const C) hbound hpoint
  obtain ⟨v, phi, _hphi, hvu, hvalueSub, hgradientSub⟩ :=
    exists_h1Function_of_tendsto_value_of_gradient_norm_le w hu hvalue
      Cgrad hgradient
  refine ⟨v, hvu, ?_⟩
  exact isMassiveWeakSolutionOn_of_tendsto_value_of_tendsto_inner_gradient
    hEll hrhoMeas hrhoBdd hf w v phi hvalueSub hgradientSub hw

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
