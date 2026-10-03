module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationAlgebra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierProfile

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

open Homogenization hiding Vec
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

theorem coeffFluxDiv_one_add_norm_sq {d : ℕ} {c : Vec d → ℝ}
    (hc : Differentiable ℝ c) (x : Vec d) :
    coeffFluxDiv c (fun y ↦ 1 + euclideanNorm y ^ 2) x =
      2 * (d : ℝ) * c x + 2 * vecDot x (euclideanGradient c x) := by
  simp only [euclideanNorm_sq]
  have hF : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun s : ℝ ↦ 1 + s) 1 t := by
    intro t _
    exact HasDerivAt.const_add 1 (hasDerivAt_id t)
  have hFprime : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun _ : ℝ ↦ (1 : ℝ)) 0 t := by
    intro t _
    exact hasDerivAt_const t (1 : ℝ)
  rw [coeffFluxDiv_compVecNormSq hc hF hFprime x]
  ring

theorem weighted_quadratic_drift_identity {d : ℕ} {c : Vec d → ℝ}
    (hc : Differentiable ℝ c) (x g : Vec d) (hcx : c x ≠ 0)
    (hg : euclideanGradient c x = c x • g) :
    (c x)⁻¹ * coeffFluxDiv c (fun y ↦ 1 + euclideanNorm y ^ 2) x =
      2 * (d : ℝ) + 2 * vecDot x g := by
  rw [coeffFluxDiv_one_add_norm_sq hc x, hg, vecDot_smul_right]
  field_simp [hcx]

theorem vecDot_drift_le_quadratic {d : ℕ} (x g : Vec d) {C : ℝ}
    (hC : 0 ≤ C) (hg : euclideanNorm g ≤ C * (1 + euclideanNorm x)) :
    2 * (d : ℝ) + 2 * vecDot x g ≤
      (2 * (d : ℝ) + 4 * C) * (1 + euclideanNorm x ^ 2) := by
  have habs := abs_vecDot_le_euclideanNorm_mul x g
  have hv : vecDot x g ≤ euclideanNorm x * euclideanNorm g := (abs_le.mp habs).2
  have hrev := reversible_drift_le_quadratic (Nat.cast_nonneg d) (euclideanNorm_nonneg x) hC hg
  linarith

theorem vecDot_divergence_drift_le_quadratic {d : ℕ} (x g : Vec d) {C b : ℝ}
    (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hg : b + euclideanNorm g ≤ C * (1 + euclideanNorm x)) :
    2 * (d : ℝ) * b + 2 * vecDot x g ≤
      4 * ((d : ℝ) + 1) * C * (1 + euclideanNorm x ^ 2) := by
  have h1 : vecDot x g ≤ euclideanNorm x * euclideanNorm g := by
    have habs := abs_vecDot_le_euclideanNorm_mul x g
    have hself : vecDot x g ≤ |vecDot x g| := le_abs_self _
    linarith
  have h2 := divergence_drift_le_quadratic (Nat.cast_nonneg d) (euclideanNorm_nonneg x)
    hC hb (euclideanNorm_nonneg g) hg
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
