module

public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.dilation_coefficient_transport
public import SubdiffusiveProcess.Paper.weak_gradient_chain_rule

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Unnormalized coefficient-energy dilation.
* Positive scale and concrete cubes.
* Uniformly positive coefficients a,b are tied a.e. by the affine map; supplier dilation_coefficient_transport.
* u,w belong to their weak Sobolev graphs (standing H¹ domains).
* Their values are tied a.e.; weak_gradient_chain_rule supplies the derivative identity with factor r.
* The energy is the unnormalized integral; the Jacobian contributes r^d and undoing the gradient factor contributes r^(-2).
* Conclusion: the exact factor is r^(d-2), with no cutoff or expectation limit. -/
theorem energy_dilation_scaling :
  ∀ (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube z' 1 h1))
    (u : SobolevData (centeredCube z r hr)) (w : SobolevData (centeredCube z' 1 h1)),
    u ∈ weakSobolevGraph (centeredCube z r hr) →
    w ∈ weakSobolevGraph (centeredCube z' 1 h1) →
    (∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      b.val x = a.val (cubeDilation z z' r x)) →
    -- the value tie; the gradient tie follows from it by
    
    (∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      (w.1 : SpatialCoordinates d → ℝ) x =
        (u.1 : SpatialCoordinates d → ℝ) (cubeDilation z z' r x)) →
    sobolevCoefficientForm a u u =
      r ^ ((d : ℝ) - 2) * sobolevCoefficientForm b w w := by
  rintro d z z' r hr h1 a b u w hu hw hb hv
  have hgrad := weak_gradient_chain_rule d z z' r hr h1 u w hu hw hv
  have hpow : (r ^ d : ℝ) * (r⁻¹ * r⁻¹) = r ^ ((d : ℝ) - 2) := by
    rw [show r⁻¹ = r ^ (-1 : ℝ) from (Real.rpow_neg_one r).symm,
      ← Real.rpow_add hr (-1 : ℝ) (-1 : ℝ), ← Real.rpow_natCast r d,
      ← Real.rpow_add hr (d : ℝ) ((-1 : ℝ) + (-1 : ℝ))]
    congr 1
    ring
  have hcov : ∀ f : SpatialCoordinates d → ℝ,
      (∫ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
          f (cubeDilation z z' r x)) =
        (r ^ d)⁻¹ * ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x := by
    intro f
    have hcoe : ⇑(cubeDilationEquiv z z' hr.ne') = cubeDilation z z' r := rfl
    have h := integral_map_equiv
      (μ := volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))
      (e := cubeDilationEquiv z z' hr.ne') (f := f)
    rw [hcoe, map_cubeDilation_restrict z z' hr h1] at h
    have hcoef : (ENNReal.ofReal |(r ^ d)⁻¹|).toReal = (r ^ d)⁻¹ := by
      rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr (pow_pos hr d))]
    rw [integral_smul_measure, hcoef, smul_eq_mul] at h
    exact h.symm
  simp only [sobolevCoefficientForm, ContinuousLinearMap.bilinearComp_apply,
    weightedGradientForm_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hkey : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        a.val x * (sobolevGradient u i x * sobolevGradient u i x)) =
      r ^ d * ∫ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        a.val (cubeDilation z z' r x) *
          (sobolevGradient u i (cubeDilation z z' r x) *
            sobolevGradient u i (cubeDilation z z' r x)) := by
    have k := hcov (fun x => a.val x * (sobolevGradient u i x * sobolevGradient u i x))
    rw [k, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hr.ne'), one_mul]
  rw [hkey]
  have hfun : (fun y => a.val (cubeDilation z z' r y) *
        (sobolevGradient u i (cubeDilation z z' r y) *
          sobolevGradient u i (cubeDilation z z' r y)))
      =ᵐ[volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))]
      (fun y => (r⁻¹ * r⁻¹) *
        (b.val y * (sobolevGradient w i y * sobolevGradient w i y))) := by
    filter_upwards [hb, hgrad i] with y hby hgy
    have hg : sobolevGradient u i (cubeDilation z z' r y) =
        r⁻¹ * sobolevGradient w i y := by
      rw [hgy, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    rw [← hby, hg]
    ring
  rw [integral_congr_ae hfun, integral_const_mul, ← mul_assoc, hpow]


end SubdiffusiveProcess.Paper
