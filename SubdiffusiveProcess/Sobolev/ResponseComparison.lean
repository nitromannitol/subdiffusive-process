module

public import SubdiffusiveProcess.Sobolev.ResponseSpace
public import SubdiffusiveProcess.Variational.WeightedCoefficient
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

/-!
# Canonical inverse responses: coefficient order and potential comparison

Coefficient order is reversed for inverse responses. Scalar homogeneity and
the attained variational formula prove the exact exponential comparison used
by the finite-band compactness argument. These are actual responses on the
concrete Sobolev spaces; no comparison property is assumed of the response.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Positive scalar multiplication of the actual coefficient. -/
def scalePositiveCoefficient (r : ℝ) (hr : 0 < r) (a : PositiveCoefficient Ω) :
    PositiveCoefficient Ω := by
  refine ⟨r • a.val, ?_⟩
  obtain ⟨c, hc, ha⟩ := a.property
  refine ⟨r * c, mul_pos hr hc, ?_⟩
  filter_upwards [ha, Lp.coeFn_smul r a.val] with x hx he
  rw [he]
  exact mul_le_mul_of_nonneg_left hx hr.le

/-- The scaled coefficient is scalar multiplication almost everywhere. -/
theorem scalePositiveCoefficient_coeFn (r : ℝ) (hr : 0 < r) (a : PositiveCoefficient Ω) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (scalePositiveCoefficient r hr a).val x = r * a.val x := by
  change ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
    (r • a.val) x = r * a.val x
  filter_upwards [Lp.coeFn_smul r a.val] with x hx
  simpa only [Pi.smul_apply, smul_eq_mul] using hx

/-- Scalar coefficient homogeneity for the concrete Sobolev energy. -/
theorem responseForm_scale_coefficient (S : ResponseSpace Ω)
    (r : ℝ) (hr : 0 < r) (a : PositiveCoefficient Ω) (u v : S.space) :
    responseForm S (scalePositiveCoefficient r hr a) u v = r * responseForm S a u v := by
  change weightedGradientForm (r • a.val) (subspaceGradient S.space u) (subspaceGradient S.space v) = _
  simp only [responseForm, ContinuousLinearMap.bilinearComp_apply,
    weightedGradientForm, sum_apply, PiLp.proj_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => weightedL2Form_smul (E := ℝ) r a.val _ _

/-- Pointwise coefficient order gives quadratic energy order on the actual space. -/
theorem responseForm_mono (S : ResponseSpace Ω) (a b : PositiveCoefficient Ω)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ b.val x)
    (u : S.space) : responseForm S a u u ≤ responseForm S b u u := by
  simp only [responseForm, ContinuousLinearMap.bilinearComp_apply,
    weightedGradientForm, sum_apply, PiLp.proj_apply]
  exact Finset.sum_le_sum fun i _ => weightedL2Form_mono (E := ℝ) hab _

/-- Increasing the coefficient decreases the inverse response. -/
theorem inverseResponse_antitone (S : ResponseSpace Ω) (a b : PositiveCoefficient Ω)
    (hab : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val x ≤ b.val x)
    (L : S.space →L[ℝ] ℝ) : inverseResponse S b L ≤ inverseResponse S a L := by
  let u := responseSolution S b L
  have hb : inverseResponse S b L = 2 * L u - responseForm S b u u := by
    change inverseResponse S b L = 2 * L u - inverseResponse S b L
    rw [inverseResponse_eq_load]
    change L u = 2 * L u - L u
    ring
  calc
    inverseResponse S b L = 2 * L u - responseForm S b u u := hb
    _ ≤ 2 * L u - responseForm S a u u := sub_le_sub_left (responseForm_mono S a b hab u) _
    _ ≤ inverseResponse S a L := (inverseResponse_isGreatest S a L).2 ⟨u, rfl⟩

/-- The unique solution scales reciprocally with the scalar coefficient. -/
theorem responseSolution_scale_coefficient (S : ResponseSpace Ω)
    (r : ℝ) (hr : 0 < r) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) :
    responseSolution S (scalePositiveCoefficient r hr a) L = r⁻¹ • responseSolution S a L := by
  symm
  apply responseSolution_eq
  intro v
  rw [responseForm_scale_coefficient]
  simp only [map_smul, smul_apply, smul_eq_mul, responseSolution_spec]
  rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-- Canonical inverse responses have reciprocal scalar coefficient homogeneity. -/
theorem inverseResponse_scale_coefficient (S : ResponseSpace Ω)
    (r : ℝ) (hr : 0 < r) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) :
    inverseResponse S (scalePositiveCoefficient r hr a) L = r⁻¹ * inverseResponse S a L := by
  rw [inverseResponse_eq_load, responseSolution_scale_coefficient, map_smul,
    inverseResponse_eq_load]
  rfl

/-- Actual coefficients satisfying a potential comparison give the same two-sided
multiplicative estimate for their inverse responses. -/
theorem inverseResponse_exp_comparison (S : ResponseSpace Ω)
    (a b : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) (D : ℝ)
    (hl : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      Real.exp (-D) * a.val x ≤ b.val x)
    (hu : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      b.val x ≤ Real.exp D * a.val x) :
    Real.exp (-D) * inverseResponse S a L ≤ inverseResponse S b L ∧
      inverseResponse S b L ≤ Real.exp D * inverseResponse S a L := by
  have hlow := inverseResponse_antitone S b (scalePositiveCoefficient (Real.exp D) (Real.exp_pos D) a)
    (by
      filter_upwards [hu, scalePositiveCoefficient_coeFn (Real.exp D) (Real.exp_pos D) a] with x hx he
      rwa [he]) L
  have hupp := inverseResponse_antitone S
    (scalePositiveCoefficient (Real.exp (-D)) (Real.exp_pos (-D)) a) b
    (by
      filter_upwards [hl, scalePositiveCoefficient_coeFn (Real.exp (-D)) (Real.exp_pos (-D)) a]
        with x hx he
      rwa [he]) L
  rw [inverseResponse_scale_coefficient, ← Real.exp_neg] at hlow hupp
  simpa only [neg_neg] using And.intro hlow hupp

end SubdiffusiveProcess
