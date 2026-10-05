module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationAlgebra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierProfile

@[expose] public section

/-!
# Radial functions for the conservativity argument

The free exponent permits an approximation to one with a uniformly small generator.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec
open Filter Topology SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty

theorem radialProfileD_mul_one_add {A beta q : ℝ} (hq : 0 ≤ q) :
    radialProfileD A beta q * (1 + q) = -(beta / 2) * radialProfile A beta q := by
  have h1 : 0 < 1 + q := by linarith
  rw [radialProfileD, radialProfile, Real.rpow_sub h1]
  simp only [Real.rpow_one]
  field_simp

theorem radialProfileDD_nonneg {A beta q : ℝ}
    (hA : 0 ≤ A) (hbeta : 0 ≤ beta) (hq : 0 ≤ q) :
    0 ≤ radialProfileDD A beta q := by
  unfold radialProfileDD
  have h : A * (-(beta/2)) * (-(beta/2)-1) = A*(beta/2)*(beta/2+1) := by ring
  rw [h]
  positivity

theorem radialBarrier_one_le_one {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (x : Vec d) : radialBarrier 1 beta x ≤ 1 := by
  simp only [radialBarrier, radialProfile, one_mul]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · linarith [vecNormSq_nonneg x]
  · linarith

noncomputable def radialBarrierC0 {d : ℕ} (beta : ℝ) (hbeta : 0 < beta) :
    C₀(Vec d, ℝ) :=
  ⟨⟨radialBarrier 1 beta, (contDiff_radialBarrier 1 beta).continuous⟩,
    tendsto_radialBarrier_cocompact 1 hbeta⟩

theorem tendsto_radialBarrier_beta_zero {d : ℕ} (x : Vec d) :
    Tendsto (fun beta : ℝ ↦ radialBarrier 1 beta x) (nhds 0) (nhds 1) := by
  have ha : (1 + vecNormSq x : ℝ) ≠ 0 := by linarith [vecNormSq_nonneg x]
  have hc : ContinuousAt (fun t : ℝ ↦ (1 + vecNormSq x) ^ (t : ℝ)) (0 : ℝ) :=
    Real.continuousAt_const_rpow ha
  have hlim : Tendsto (fun beta : ℝ ↦ -(beta / 2)) (nhds 0) (nhds 0) := by
    simpa using ((tendsto_id : Tendsto (fun y : ℝ ↦ y) (nhds 0) (nhds 0)).div_const (2 : ℝ)).neg
  simpa [radialBarrier, radialProfile, Function.comp_def] using hc.tendsto.comp hlim

noncomputable def dominatedC0 {alpha : Type*} [TopologicalSpace alpha]
    (f : alpha → ℝ) (hf : Continuous f) (g : C₀(alpha, ℝ)) (C : ℝ)
    (hbound : ∀ x, ‖f x‖ ≤ C * g x) : C₀(alpha, ℝ) := by
  refine ⟨⟨f, hf⟩, ?_⟩
  exact squeeze_zero_norm hbound (by simpa using (zero_at_infty g).const_mul C)

theorem one_add_norm_sq_le_vecNormSq {d : ℕ} (x : Vec d) :
    1 + ‖x‖ ^ 2 ≤ 1 + vecNormSq x := by
  nlinarith [SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.norm_le_euclideanNorm x, euclideanNorm_nonneg x, norm_nonneg x, euclideanNorm_sq x]

theorem norm_c0_le_const_of_dominated {alpha : Type*} [TopologicalSpace alpha]
    (f g : C₀(alpha, ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x, g x ≤ 1) (hf : ∀ x, ‖f x‖ ≤ C * g x) : ‖f‖ ≤ C := by
  have h : ‖f.toBCF‖ ≤ C := by
    refine (BoundedContinuousFunction.norm_le hC).2 ?_
    intro x
    calc ‖f.toBCF x‖ ≤ C * g x := hf x
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left (hg x) hC
      _ = C := by simp only [mul_one]
  exact h

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
