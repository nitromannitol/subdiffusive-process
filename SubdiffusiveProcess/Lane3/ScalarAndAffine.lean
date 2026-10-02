import SubdiffusiveProcess.Lane3.Forms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic




open Filter Topology Matrix
open scoped BigOperators

noncomputable section

namespace SubdiffusiveProcess
namespace Lane3

/-- Corollary `mfd:cor-32`, `eq:mfd-32`, paper lines 3477-3501.  `c0` is the
deterministic lower bound on `λ_min(A_E) / tr A_E` from condition (a) of the
good event, paper lines 3492-3495; `eps'` is the threshold of the additional
test `|B_k/Δ| ≤ ε'`, paper line 3488. -/
theorem affine_saving_on_good_cubes
    (d : ℕ) (AE AF : Matrix (Fin d) (Fin d) ℝ) (ck Del eps' c0 : ℝ)
    (hc0 : 0 < c0) (heps : 0 ≤ eps') (hDel : 0 ≤ Del)
    (htr : 0 < Matrix.trace AE)
    (hBk : ∀ x : Fin d → ℝ,
      |x ⬝ᵥ (AF - ck • AE).mulVec x| ≤
        eps' * Del * Matrix.trace AE * (x ⬝ᵥ x))
    (hlam : ∀ x : Fin d → ℝ,
      c0 * Matrix.trace AE * (x ⬝ᵥ x) ≤ x ⬝ᵥ AE.mulVec x) :
    ∀ x : Fin d → ℝ,
      |x ⬝ᵥ (AF - ck • AE).mulVec x| ≤
        eps' / c0 * Del * (x ⬝ᵥ AE.mulVec x) := by
  intro x
  have hcoef : 0 ≤ eps' / c0 * Del := by positivity
  calc |x ⬝ᵥ (AF - ck • AE).mulVec x|
      ≤ eps' * Del * Matrix.trace AE * (x ⬝ᵥ x) := hBk x
    _ = eps' / c0 * Del * (c0 * Matrix.trace AE * (x ⬝ᵥ x)) := by
        field_simp
    _ ≤ eps' / c0 * Del * (x ⬝ᵥ AE.mulVec x) :=
        mul_le_mul_of_nonneg_left (hlam x) hcoef

/-- The limit `eq:mfd-33` of the exponent of Lemma `mfd:lem-affine`,
paper lines 3536-3541: admissible exponents exist in every dimension. -/
theorem affine_exponent_limit (d beta : ℝ) (hd : 0 < d)
    (hb0 : 1 / 2 < beta) (hb1 : beta < 1) :
    affineExponent d 1 beta 1 0 = -((1 - beta) / (1 + d / 2)) ∧
      affineExponent d 1 beta 1 0 < 0 := by
  have hden : (0 : ℝ) < 1 + d / 2 := by linarith
  have heq : affineExponent d 1 beta 1 0 = -((1 - beta) / (1 + d / 2)) := by
    unfold affineExponent
    field_simp
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have hpos : 0 < (1 - beta) / (1 + d / 2) := div_pos (by linarith) hden
  linarith

/-- Theorem `mfd:thm-c1`, paper lines 3972-4008: the proportionality constant
is one.  `LamE`, `LamF` are the affine Dirichlet responses of the two
candidates with the infrared field removed on the cube of side `3^k`, `vol k`
its volume, and the two hypotheses are Corollary `mfd:cor-37` passed to the
candidates. -/
theorem scalar_equals_one (c : ℝ) (hc : 0 < c) (pn : ℝ) (hpn : 0 < pn)
    (LamE LamF vol : ℕ → ℝ) (hvol : ∀ k, 0 < vol k)
    (hprop : ∀ k, LamF k = c * LamE k)
    (hE : Tendsto (fun k => |LamE k / vol k - pn ^ 2|) atTop (𝓝 0))
    (hF : Tendsto (fun k => |LamF k / vol k - pn ^ 2|) atTop (𝓝 0)) :
    c = 1 := by
  have hE' : Tendsto (fun k => LamE k / vol k) atTop (𝓝 (pn ^ 2)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [Real.dist_eq] using hE
  have hF' : Tendsto (fun k => LamF k / vol k) atTop (𝓝 (pn ^ 2)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa only [Real.dist_eq] using hF
  have hrw : ∀ k, LamF k / vol k = c * (LamE k / vol k) := by
    intro k
    rw [hprop k]
    ring
  have hFc : Tendsto (fun k => LamF k / vol k) atTop (𝓝 (c * pn ^ 2)) := by
    simpa only [hrw] using hE'.const_mul c
  have heq : c * pn ^ 2 = pn ^ 2 := tendsto_nhds_unique hFc hF'
  have hpn2 : pn ^ 2 ≠ 0 := by positivity
  have heq' : c * pn ^ 2 = 1 * pn ^ 2 := by rw [one_mul]; exact heq
  exact mul_right_cancel₀ hpn2 heq'

end Lane3
end SubdiffusiveProcess
