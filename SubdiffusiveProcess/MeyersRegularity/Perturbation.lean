import SubdiffusiveProcess.MeyersRegularity.Basic

/-! Interior Meyers regularity: Perturbation. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

theorem smoothEquation_of_vectorEquation {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (u : H1Function U) (a : Vec d → ℝ) (F : Vec d → Vec d) {δ : ℝ}
    (ha : AEMeasurable a (volume.restrict U)) (hδ : 0 ≤ δ)
    (hclose : ∀ᵐ x ∂volume.restrict U, |a x-1| ≤ δ)
    (hF : MemVectorL2 U F) (heq : VectorEquation a F u) :
    MemVectorL2 U (fun x => (a x-1) • u.grad x + F x) ∧
      SmoothEquation (fun x => (a x-1) • u.grad x + F x) u := by
  let bound : ℝ≥0 := ⟨δ, hδ⟩
  have hb : MemLp (fun x => a x - 1) ⊤ (volume.restrict U) :=
    memLp_top_of_bound (ha.aestronglyMeasurable.sub aestronglyMeasurable_const)
      (bound : ℝ) (by simpa only [Real.norm_eq_abs] using hclose)
  have hg : MemVectorL2 U (fun x => (a x - 1) • u.grad x) :=
    u.grad_memVectorL2.smul hb
  refine ⟨hg.add hF, ?_⟩
  intro phi hs hc hsub
  let psi : H10Function U := H10Function.ofContDiff hU hs hc hsub
  have hpsi : psi.toH1Function.grad = euclideanGradient phi := rfl
  have hd : IntegrableOn (fun x => vecDot (u.grad x) (euclideanGradient phi x)) U :=
    integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2
      (by rw [← hpsi]; exact psi.toH1Function.grad_memVectorL2)
  have hbint : IntegrableOn
      (fun x => (a x - 1) * vecDot (u.grad x) (euclideanGradient phi x)) U :=
    integrableOn_vecDot_of_memVectorL2 hg
      (by rw [← hpsi]; exact psi.toH1Function.grad_memVectorL2) |>.congr
      (Filter.Eventually.of_forall fun x => vecDot_smul_left _ _ _)
  have hFint : IntegrableOn (fun x => vecDot (F x) (euclideanGradient phi x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF
      (by rw [← hpsi]; exact psi.toH1Function.grad_memVectorL2)
  have heq' := heq psi
  rw [hpsi] at heq'
  have haeq : (∫ x in U, a x * vecDot (u.grad x) (euclideanGradient phi x)) =
      (∫ x in U, vecDot (u.grad x) (euclideanGradient phi x)) +
        ∫ x in U, (a x - 1) * vecDot (u.grad x) (euclideanGradient phi x) := by
    rw [← integral_add hd hbint]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [haeq] at heq'
  simp_rw [vecDot_add_left, vecDot_smul_left]
  rw [integral_add hbint hFint]
  linarith

end SubdiffusiveProcess.MeyersRegularity
