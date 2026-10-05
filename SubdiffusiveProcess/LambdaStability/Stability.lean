module

public import SubdiffusiveProcess.LambdaStability.LiteralCarriers
public import SubdiffusiveProcess.LambdaStability.OriginGeometry
public import SubdiffusiveProcess.LambdaStability.Arithmetic

@[expose] public section

/-! The three stability estimates on the paper's local coefficient field. -/
open Homogenization Homogenization.Book MeasureTheory
open scoped BigOperators

noncomputable section
namespace SubdiffusiveProcess.LambdaStability
variable {d : ℕ} [NeZero d]

theorem stability_on_origin {q : Ch02.MultiscaleExponent} (hq : q.IsAdmissible)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t ≤ 1 / 2)
    {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d 0)) g)
    (hsym : ∀ y ∈ openCubeSet (originCube d 0), (g y).IsSymm)
    {x : Vec d}
    (hx : translateSet x (openCubeSet (originCube d (-1))) ⊆ openCubeSet (originCube d 0)) :
    lowerInv x (originCube d (-1)) t q g ≤
      stabilityConstant d / (1 - 2 * s) * indexFactor q s t * lowerInv 0 (originCube d 0) s q g ∧
    primalUpper x (originCube d (-1)) t q g ≤
      stabilityConstant d / (1 - 2 * s) * indexFactor q s t * primalUpper 0 (originCube d 0) s q g ∧
    ∀ B A : Mat d, responseError x (originCube d (-1)) t g B A ≤
      stabilityConstant d / Real.sqrt (1 - 2 * s) * Real.sqrt (t / (t - s)) *
        responseError 0 (originCube d 0) s g B A := by
  let U := Ch02.cubeDomain (originCube d 0)
  let g' := extendField (U : Set (Vec d)) g lam
  have hg' : IsEllipticFieldOn lam Lam Set.univ g' := extendField_elliptic U g hEll
  have hs' : IsSymmetricCoeffField g' := extendField_symm _ g lam hsym
  have heq : Set.EqOn g g' (U : Set (Vec d)) := (extendField_eqOn _ g lam).symm
  have hlocal := literalQuantities_eq_of_eqOn U t q hEll hg' heq hx
  have hroot := literalQuantities_eq_of_eqOn U s q hEll hg' heq
    (by rw [translateSet_zero]; exact Set.Subset.rfl : translateSet 0 (openCubeSet (originCube d 0)) ⊆ _)
  rw [hlocal.1, hroot.1, hlocal.2.1, hroot.2.1]
  simp only [hlocal.2.2, hroot.2.2]
  have hcontain := origin_halfOpen_containment hx
  let F := fieldFamily g' hg'
  have hF : ∀ R : TriadicCube d, (F.coeffOn R).toCoeffField = g' := fun _ => rfl
  have hslt : s < 1 / 2 := hst.trans_le ht
  have hden : 0 < 1 - 2 * s := by linarith
  have ht0 : 0 < t := hs.trans hst
  have hdiff : 0 < t - s := sub_pos.mpr hst
  have hI : 0 ≤ indexFactor q s t := by
    cases q with
    | finite q => exact Real.rpow_nonneg (div_nonneg ht0.le hdiff.le) _
    | infinity => exact zero_le_one
  have hclosed : MeasurableSet (translateSet x (cubeSet (originCube d (-1)))) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet _).preimage (measurable_id.sub measurable_const)
  have hEllP := hg'.mono hclosed (Set.subset_univ _)
  have hLroot := lowerInv_zero_eq (originCube d 0) s q hs hq F g' hF
  have hLnonneg : 0 ≤ lowerInv 0 (originCube d 0) s q g' := by
    rw [hLroot]
    exact inv_nonneg.mpr (Ch02.lambdaSq_nonneg _ F hs hq)
  have hUroot := upper_zero_eq (originCube d 0) s q F g' hF hg'
  have hUnonneg : 0 ≤ upper 0 (originCube d 0) s q g' := by
    rw [hUroot]
    exact Ch02.LambdaSq_nonneg _ F hs hq
  have hscale : (((((originCube d 0).scale - (originCube d (-1)).scale).toNat : ℕ) : ℝ)) = 1 := by
    norm_num [originCube]
  refine ⟨?_, ?_, ?_⟩
  · have hraw := lowerInv_le F hq hs hst ht hF hEllP hcontain
    rw [hscale, mul_one, ← hLroot] at hraw
    exact hraw.trans (matrix_stability_arithmetic d hslt hI hLnonneg)
  · rw [primalUpper_eq_upper _ _ _ _ hg' hs', primalUpper_eq_upper _ _ _ _ hg' hs']
    have hraw := upper_le F hq hs hst ht hF hEllP hcontain
    rw [hscale, mul_one, ← hUroot] at hraw
    exact hraw.trans (matrix_stability_arithmetic d hslt hI hUnonneg)
  · intro B A
    rw [responseError_eq_probeError, responseError_eq_probeError]
    have hraw := probeError_le hs hst ht hg' B A hcontain
      (by norm_num [originCube] : (originCube d (-1)).scale ≤ (originCube d 0).scale)
    rw [hscale, mul_one] at hraw
    exact hraw.trans (error_stability_arithmetic d hslt (Real.sqrt_nonneg _))

end SubdiffusiveProcess.LambdaStability
