module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Sobolev.H1.Translation
public import SubdiffusiveProcess.Paper.aux_coercivity_dilation_cube_geometry

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Proof-step fine child: affine transport of weak Sobolev data. -/
theorem aux_coercivity_dilation_weak_pullback
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : weakSobolevGraph (centeredCube z r hr)) :
    ∃ w : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1),
      (∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x =
          (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x)) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)),
        ((w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
          SpatialCoordinates d → ℝ) x =
          r * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (cubeDilation z 0 r x)) := by
  classical
  have htranslate :
      (centeredCube z r hr : Set (SpatialCoordinates d)) =
        Homogenization.translateSet z
          (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) := by
    rw [centeredCube_eq_pi z hr, centeredCube_eq_pi (0 : SpatialCoordinates d) hr]
    ext x
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo,
      Homogenization.mem_translateSet_iff_sub_mem]
    constructor
    · intro hx i
      have hi := hx i
      simp only [Pi.sub_apply, Pi.zero_apply] at hi ⊢
      constructor <;> linarith [hi.1, hi.2]
    · intro hx i
      have hi := hx i
      simp only [Pi.sub_apply, Pi.zero_apply] at hi ⊢
      constructor <;> linarith [hi.1, hi.2]
  have hscale :
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
        r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) := by
    rw [centeredCube_eq_pi (0 : SpatialCoordinates d) hr,
      centeredCube_eq_pi (0 : SpatialCoordinates d) h1]
    ext x
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo,
      Set.mem_smul_set]
    constructor
    · rintro hx
      refine ⟨r⁻¹ • x, ?_, ?_⟩
      · intro i
        have hi := hx i
        simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
        constructor
        · refine lt_of_mul_lt_mul_right ?_ hr.le
          field_simp [hr.ne']
          linarith [hi.1]
        · refine lt_of_mul_lt_mul_right ?_ hr.le
          field_simp [hr.ne']
          linarith [hi.2]
      · simp [hr.ne']
    · rintro ⟨y, hy, rfl⟩
      intro i
      have hi := hy i
      simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
      constructor
      · have h := mul_lt_mul_of_pos_left hi.1 hr
        linarith
      · have h := mul_lt_mul_of_pos_left hi.2 hr
        linarith
  obtain ⟨u, hu, hgrad⟩ :=
    exists_nativeH1Function_of_weakSobolevGraph v
  let uT : Homogenization.H1Function
      (Homogenization.translateSet z
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))) :=
    htranslate ▸ u
  let u0 : Homogenization.H1Function
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) :=
    Homogenization.H1Function.untranslate z uT
  let uR : Homogenization.H1Function
      (r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) :=
    hscale ▸ u0
  let u1 : Homogenization.H1Function
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) :=
    Homogenization.H1Function.unscale hr uR
  obtain ⟨w, hw, hwgrad⟩ :=
    exists_weakSobolevGraph_of_nativeH1 (Om := centeredCube (0 : SpatialCoordinates d) 1 h1) u1
  have hcastFun {U V : Set (SpatialCoordinates d)} (h : U = V)
      (a : Homogenization.H1Function U) : (h ▸ a).toFun = a.toFun := by
    cases h
    rfl
  have hcastGrad {U V : Set (SpatialCoordinates d)} (h : U = V)
      (a : Homogenization.H1Function U) : (h ▸ a).grad = a.grad := by
    cases h
    rfl
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw] with x hx
    rw [hx]
    simp [u1, uR, u0, uT, hcastFun, Homogenization.H1Function.unscale_toFun]
    have hcube : r • x + z = cubeDilation z 0 r x := by
      ext j
      simp [cubeDilation]
      ring
    rw [hcube]
    exact congrFun hu _
  · intro i
    filter_upwards [hwgrad i] with x hx
    rw [hx]
    have hu1grad : u1.grad x i = r * u.grad (r • x + z) i := by
      simp [u1, uR, u0, uT, hcastGrad, Homogenization.H1Function.unscale_grad,
        Pi.smul_apply, smul_eq_mul]
    rw [hu1grad]
    have hcube : r • x + z = cubeDilation z 0 r x := by
      ext j
      simp [cubeDilation]
      ring
    rw [hcube]
    exact congrArg (fun t => r * t) (congrFun (congrFun hgrad _ ) i)

end SubdiffusiveProcess.Paper
