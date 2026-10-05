module

public import SubdiffusiveProcess.Section9.ShapeCubeGeometry
public import Homogenization.Sobolev.Foundations.Cutoff.Box

@[expose] public section

/-!
# Quantitative cutoffs on arbitrary centered axis cubes

The cutoff is one on the inner cube and supported compactly in the outer
cube. Its squared Euclidean gradient is bounded by `d * (64 / (R-r))²`.
The extra collar is essential for the `H¹₀` test, since both cubes are open.
-/

set_option autoImplicit false
noncomputable section

open Homogenization Set
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped Topology BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A smooth cutoff on centered cubes, with a dimensional gradient bound. -/
theorem exists_moser_cube_cutoff {d : ℕ} (z : Vec d) {r R : ℝ}
    (hrR : r < R) :
    ∃ eta : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) eta ∧ HasCompactSupport eta ∧
      tsupport eta ⊆ centeredAxisCube z R ∧
      (∀ x, 0 ≤ eta x ∧ eta x ≤ 1) ∧
      (∀ x ∈ centeredAxisCube z r, eta x = 1) ∧
      ∀ x, vecNormSq (euclideanGradient eta x) ≤
        (d : ℝ) * (64 / (R - r)) ^ 2 := by
  let lo : Vec d := fun i => z i - r / 2
  let hi : Vec d := fun i => z i + r / 2
  let ell : ℝ := (R - r) / 4
  have hell : 0 < ell := div_pos (sub_pos.mpr hrR) (by norm_num)
  let K := Icc (fun i => lo i - ell) (fun i => hi i + ell)
  have hK : IsCompact K := isCompact_Icc
  have hsub : tsupport (boxCutoff lo hi ell) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (boxCutoff_eq_zero hell hn)
  have hKU : K ⊆ centeredAxisCube z R := by
    intro x hx i _
    have hlo := hx.1 i
    have hhi := hx.2 i
    dsimp only [lo, hi, ell] at hlo hhi
    change z i - R / 2 < x i ∧ x i < z i - R / 2 + R
    constructor <;> linarith
  refine ⟨boxCutoff lo hi ell, boxCutoff_contDiff,
    hK.of_isClosed_subset isClosed_closure hsub, hsub.trans hKU,
    fun x => ⟨boxCutoff_nonneg x, boxCutoff_le_one x⟩, ?_, ?_⟩
  · intro x hx
    apply boxCutoff_eq_one hell
    constructor <;> intro i
    · exact (hx i (mem_univ i)).1.le
    · have h := (hx i (mem_univ i)).2
      change x i ≤ z i + r / 2
      change x i < z i - r / 2 + r at h
      linarith
  · intro x
    have hgrad := boxCutoff_sq_grad_bound (lo := lo) (hi := hi) hell x
    have heq : (16 : ℝ) / ell = 64 / (R - r) := by
      dsimp only [ell]
      field_simp
      ring
    rw [heq] at hgrad
    simpa only [vecNormSq, vecDot, euclideanGradient, euclideanCoordDeriv,
      basisVec, pow_two] using hgrad

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
