import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Sobolev.GradientRange
import SubdiffusiveProcess.Sobolev.NativeH1
import SubdiffusiveProcess.Paper.lane4_dilation_quasi_measure_preserving
import Homogenization.Sobolev.H1.Translation
import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
import Homogenization.Sobolev.W1p.Dilation

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_lane4_weak_gradient_chain_rule_cube_sets
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) :
    Homogenization.translateSet (-z)
        (centeredCube z r hr : Set (SpatialCoordinates d)) =
      r • Homogenization.translateSet (-z')
        (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) := by
  ext x
  constructor
  · intro hx
    have hxB : x + z ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      simpa [Homogenization.mem_translateSet_iff_sub_mem, sub_eq_add_neg] using hx
    have hxcoord : ∀ i : Fin d, -r / 2 < x i ∧ x i < r / 2 := by
      rw [centeredCube_eq_pi z hr] at hxB
      intro i
      have hi := hxB i (Set.mem_univ i)
      rw [Set.mem_Ioo] at hi
      simp only [Pi.add_apply] at hi
      constructor <;> linarith [hi.1, hi.2]
    apply (Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _).2
    rw [Homogenization.mem_translateSet_iff_sub_mem]
    rw [centeredCube_eq_pi z' h1]
    intro i
    intro _
    have hi := hxcoord i
    have hlow : (-1 / 2 : ℝ) < x i / r := by
      apply (lt_div_iff₀ hr).2
      linarith [hi.1]
    have hupp : x i / r < (1 / 2 : ℝ) := by
      apply (div_lt_iff₀ hr).2
      linarith [hi.2]
    have hxi : (r⁻¹ • x) i = x i / r := by
      simp [Pi.smul_apply, div_eq_mul_inv, mul_comm]
    simp only [Set.mem_Ioo, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply]
    have hxi' : r⁻¹ * x i = x i / r := by
      simp [div_eq_mul_inv, mul_comm]
    change z' i - 1 / 2 < r⁻¹ * x i - -z' i ∧
      r⁻¹ * x i - -z' i < z' i + 1 / 2
    rw [hxi']
    constructor <;> linarith
  · intro hx
    have hxU : r⁻¹ • x ∈ Homogenization.translateSet (-z')
        (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) :=
      (Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _).1 hx
    have hxA : r⁻¹ • x + z' ∈ (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) := by
      simpa [Homogenization.mem_translateSet_iff_sub_mem, sub_eq_add_neg] using hxU
    have hxcoord : ∀ i : Fin d, (-1 / 2 : ℝ) < x i / r ∧
        x i / r < (1 / 2 : ℝ) := by
      rw [centeredCube_eq_pi z' h1] at hxA
      intro i
      have hi := hxA i (Set.mem_univ i)
      rw [Set.mem_Ioo] at hi
      have hxi : (r⁻¹ • x) i = x i / r := by
        simp [Pi.smul_apply, div_eq_mul_inv, mul_comm]
      simp only [Pi.add_apply, hxi] at hi
      have hi' : (-1 / 2 : ℝ) < x i / r ∧
          x i / r < (1 / 2 : ℝ) := by
        constructor <;> linarith [hi.1, hi.2]
      constructor <;> linarith [hi'.1, hi'.2]
    have hxB : x + z ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      rw [centeredCube_eq_pi z hr]
      intro i
      intro _
      rw [Set.mem_Ioo]
      simp only [Pi.add_apply]
      have hi := hxcoord i
      have hlow : (-r / 2 : ℝ) < x i := by
        have := (lt_div_iff₀ hr).1 hi.1
        linarith
      have hupp : x i < r / 2 := by
        have := (div_lt_iff₀ hr).1 hi.2
        linarith
      constructor <;> linarith
    exact (Homogenization.mem_translateSet_iff_sub_mem).2 (by
      simpa [sub_eq_add_neg] using hxB)

theorem aux_lane4_weak_gradient_chain_rule_target_set
    (d : ℕ) (z' : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) :
    Homogenization.translateSet z'
        (Homogenization.translateSet (-z')
          (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) =
      (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) := by
  simpa using
    (Homogenization.translateSet_translateSet (-z') z'
      (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))

theorem aux_lane4_weak_gradient_chain_rule_congr_ae
    {d : ℕ} {U : Set (SpatialCoordinates d)}
    {i : Fin d} {f f' g g' : SpatialCoordinates d → ℝ}
    (hf : f =ᵐ[volume.restrict U] f')
    (hg : g =ᵐ[volume.restrict U] g')
    (h : Homogenization.HasWeakPartialDerivOn U i f g) :
    Homogenization.HasWeakPartialDerivOn U i f' g' := by
  intro φ hφ hφc hφs
  have h1 : ∫ x in U, f' x * (fderiv ℝ φ x) (Homogenization.basisVec i) =
      ∫ x in U, f x * (fderiv ℝ φ x) (Homogenization.basisVec i) := by
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hx]
  have h2 : ∫ x in U, g' x * φ x = ∫ x in U, g x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]
  rw [h1, h2]
  exact h φ hφ hφc hφs



theorem lane4_weak_gradient_chain_rule :
  ∀ (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (u : SobolevData (centeredCube z r hr)) (w : SobolevData (centeredCube z' 1 h1)),
    u ∈ weakSobolevGraph (centeredCube z r hr) →
    w ∈ weakSobolevGraph (centeredCube z' 1 h1) →
    -- the value tie: the transported datum agrees with `u ∘ T` a.e. on the unit cube
    (∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      (w.1 : SpatialCoordinates d → ℝ) x =
        (u.1 : SpatialCoordinates d → ℝ) (cubeDilation z z' r x)) →
    -- then the gradients are tied, with the factor `r` from the linear part of `T`
    ∀ i : Fin d,
      ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        (sobolevGradient w i) x = r * (sobolevGradient u i) (cubeDilation z z' r x) := by
  intro d z z' r hr h1 u w hu hw hvalue i
  let uSub : weakSobolevGraph (centeredCube z r hr) := ⟨u, hu⟩
  obtain ⟨uH, huHval, huHgrad⟩ :=
    exists_nativeH1Function_of_weakSobolevGraph uSub
  let target : Set (SpatialCoordinates d) :=
    (centeredCube z' 1 h1 : Set (SpatialCoordinates d))
  let target0 : Set (SpatialCoordinates d) :=
    Homogenization.translateSet (-z') target
  have hscale := aux_lane4_weak_gradient_chain_rule_cube_sets d z z' r hr h1
  have htarget := aux_lane4_weak_gradient_chain_rule_target_set d z' h1
  have htarget' : Homogenization.translateSet z' target0 = target := by
    simpa [target0, target] using htarget
  let uShift : Homogenization.H1Function
      (Homogenization.translateSet (-z)
        (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    uH.translate (-z)
  let uScale : Homogenization.H1Function (r • target0) := hscale ▸ uShift
  let uUnit : Homogenization.H1Function target0 := uScale.unscale hr
  let vH0 : Homogenization.H1Function
      (Homogenization.translateSet z' target0) := uUnit.translate z'
  let vH : Homogenization.H1Function target := htarget' ▸ vH0
  have hvHval : (vH : SpatialCoordinates d → ℝ) =
      fun x => (uH : SpatialCoordinates d → ℝ) (cubeDilation z z' r x) := by
    have harg (x : SpatialCoordinates d) :
        r • (x - z') + z = cubeDilation z z' r x := by
      funext j
      simp [cubeDilation, Pi.smul_apply]
      ring
    funext x
    simp [vH, vH0, uUnit, uScale, uShift, target, target0,
      Homogenization.H1Function.translate,
      Homogenization.H1Function.unscale, Homogenization.H1Function.translate, harg]
  have hvHgrad : vH.grad =
      fun x => r • uH.grad (cubeDilation z z' r x) := by
    have harg (x : SpatialCoordinates d) :
        r • (x - z') + z = cubeDilation z z' r x := by
      funext j
      simp [cubeDilation, Pi.smul_apply]
      ring
    funext x
    simp [vH, vH0, uUnit, uScale, uShift, target, target0,
      Homogenization.H1Function.translate,
      Homogenization.H1Function.unscale, Homogenization.H1Function.translate, harg]
  let v : SobolevData (centeredCube z' 1 h1) :=
    (vH.memL2.toLp _, fun j => (vH.gradMemL2 j).toLp _)
  have hv : v ∈ weakSobolevGraph (centeredCube z' 1 h1) := by
    rw [mem_weakSobolevGraph_iff_hasWeakGradientOn]
    intro j
    exact aux_lane4_weak_gradient_chain_rule_congr_ae
      (MemLp.coeFn_toLp vH.memL2).symm
      (MemLp.coeFn_toLp (vH.gradMemL2 j)).symm
      (vH.hasWeakGradient j)
  have hfirst : w.1 = v.1 := by
    apply Lp.ext
    filter_upwards [hvalue, MemLp.coeFn_toLp vH.memL2] with x hxw hxv
    calc
      (w.1 : SpatialCoordinates d → ℝ) x =
          (u.1 : SpatialCoordinates d → ℝ) (cubeDilation z z' r x) := hxw
      _ = (uH : SpatialCoordinates d → ℝ) (cubeDilation z z' r x) := by
        simpa [uSub] using (congrFun huHval (cubeDilation z z' r x)).symm
      _ = (vH : SpatialCoordinates d → ℝ) x := (congrFun hvHval x).symm
      _ = (v.1 : SpatialCoordinates d → ℝ) x := hxv.symm
  have hv' : (w.1, v.2) ∈ weakSobolevGraph (centeredCube z' 1 h1) := by
    simpa only [hfirst] using hv
  have hgrad_eq : w.2 = v.2 :=
    weakSobolevGraph_gradient_unique hw hv'
  change ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
    (w.2 i : SpatialCoordinates d → ℝ) x =
      r * (u.2 i : SpatialCoordinates d → ℝ) (cubeDilation z z' r x)
  have hwi : (w.2 i : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))]
      (v.2 i : SpatialCoordinates d → ℝ) := by
    rw [hgrad_eq]
  have hvi : (v.2 i : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))]
      fun x => vH.grad x i := by
    exact MemLp.coeFn_toLp (vH.gradMemL2 i)
  have hui : (u.2 i : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      fun x => uH.grad x i := by
    filter_upwards [] with x
    exact (congrFun (congrFun huHgrad x) i).symm
  have hpull := lane4_dilation_quasi_measure_preserving d z z' r hr h1
  have huip := hpull.ae hui
  filter_upwards [hwi, hvi, huip] with x hxw hxv hxu
  calc
    (w.2 i : SpatialCoordinates d → ℝ) x = (v.2 i : SpatialCoordinates d → ℝ) x := hxw
    _ = vH.grad x i := hxv
    _ = (r • uH.grad (cubeDilation z z' r x)) i :=
      congrFun (congrFun hvHgrad x) i
    _ = r * (uH.grad (cubeDilation z z' r x)) i := by
      simp [Pi.smul_apply]
    _ = r * (u.2 i : SpatialCoordinates d → ℝ) (cubeDilation z z' r x) := by
      rw [hxu]

end Paper
