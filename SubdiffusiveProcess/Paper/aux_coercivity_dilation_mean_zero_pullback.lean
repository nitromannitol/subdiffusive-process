module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Sobolev.H1.Translation
public import SubdiffusiveProcess.Paper.aux_coercivity_dilation_cube_geometry
public import SubdiffusiveProcess.Paper.aux_coercivity_dilation_weak_pullback

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Proof-step fine child: affine transport of mean-zero Sobolev data. -/
theorem aux_coercivity_dilation_mean_zero_pullback
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : meanZeroSobolevGraph (centeredCube z r hr)) :
    ∃ w : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1),
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
  have hvweak :
      (v : SobolevData (centeredCube z r hr)) ∈
        weakSobolevGraph (centeredCube z r hr) :=
    (mem_meanZeroSobolevGraph_iff
      (v : SobolevData (centeredCube z r hr))).1 v.2 |>.1
  have hvmean :
      (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (v : SobolevData (centeredCube z r hr)).1 x) = 0 := by
    exact (mem_meanZeroSobolevGraph_iff
      (v : SobolevData (centeredCube z r hr))).1 v.2
      |>.2
  let U : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))
  have hgeom :
      Homogenization.translateSet z (r • U) =
        (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    have hscaleSet :
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
          r • U := by
      ext x
      rw [centeredCube_eq_pi (0 : SpatialCoordinates d) hr]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
      constructor
      · intro hx
        rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
        dsimp [U]
        rw [centeredCube_eq_pi (0 : SpatialCoordinates d) h1]
        simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
        intro i
        simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, zero_sub, zero_add]
        have hlow := mul_lt_mul_of_pos_right (hx i).1 (inv_pos.mpr hr)
        have hupp := mul_lt_mul_of_pos_right (hx i).2 (inv_pos.mpr hr)
        constructor
        · calc
            -(1 / 2 : ℝ) = (0 - r / 2) * r⁻¹ := by field_simp [hr.ne']; ring
            _ < x i * r⁻¹ := hlow
            _ = r⁻¹ * x i := by ring
        · calc
            r⁻¹ * x i = x i * r⁻¹ := by ring
            _ < (0 + r / 2) * r⁻¹ := hupp
            _ = 1 / 2 := by field_simp [hr.ne']; ring
      · intro hx
        rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx
        dsimp [U] at hx
        rw [centeredCube_eq_pi (0 : SpatialCoordinates d) h1] at hx
        simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hx
        intro i
        simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, zero_sub, zero_add] at hx ⊢
        constructor
        · calc
            -(r / 2) = (-(1 / 2 : ℝ)) * r := by ring
            _ < (r⁻¹ * x i) * r := mul_lt_mul_of_pos_right (hx i).1 hr
            _ = x i := by field_simp [hr.ne']
        · calc
            x i = (r⁻¹ * x i) * r := by field_simp [hr.ne']
            _ < (1 / 2) * r := mul_lt_mul_of_pos_right (hx i).2 hr
            _ = r / 2 := by ring
    ext x
    rw [Homogenization.mem_translateSet_iff_sub_mem]
    rw [← hscaleSet]
    rw [centeredCube_eq_pi (0 : SpatialCoordinates d) hr]
    rw [centeredCube_eq_pi z hr]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    constructor
    · intro hx i
      have hi := hx i
      simp only [Pi.sub_apply, Pi.zero_apply] at hi ⊢
      constructor <;> linarith
    · intro hx i
      have hi := hx i
      simp only [Pi.sub_apply, Pi.zero_apply, zero_sub, zero_add] at hi ⊢
      constructor <;> linarith
  obtain ⟨u, huv, hug⟩ :=
    exists_nativeH1Function_of_weakSobolevGraph
      ⟨(v : SobolevData (centeredCube z r hr)), hvweak⟩
  have hcastFun : ∀ {A B : Set (SpatialCoordinates d)} (h : A = B)
      (u : Homogenization.H1Function A), (h ▸ u).toFun = u.toFun := by
    intro A B h u
    subst B
    rfl
  have hcastGrad : ∀ {A B : Set (SpatialCoordinates d)} (h : A = B)
      (u : Homogenization.H1Function A), (h ▸ u).grad = u.grad := by
    intro A B h u
    subst B
    rfl
  let uT : Homogenization.H1Function (Homogenization.translateSet z (r • U)) :=
    hgeom ▸ u
  let u₀ : Homogenization.H1Function U :=
    (uT.untranslate z).unscale hr
  obtain ⟨w₀, hw₀, hw₁⟩ :=
    exists_weakSobolevGraph_of_nativeH1
      (Om := centeredCube (0 : SpatialCoordinates d) 1 h1) u₀
  have hcube : ∀ x : SpatialCoordinates d,
      cubeDilation z 0 r x = z + r • x := by
    intro x
    ext i
    simp [cubeDilation]
  have hwval :
      ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)),
        (w₀ : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x =
          (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x) := by
    filter_upwards [hw₀] with x hx
    calc
      (w₀ : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x =
          u₀.toFun x := hx
      _ = uT.toFun (r • x + z) := by
        simp [u₀, add_comm]
      _ = (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x) := by
        rw [hcube x]
        simpa [uT, hcastFun, add_comm] using! congrFun huv (r • x + z)
  have hwgrad :
      ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)),
        ((w₀ : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
          SpatialCoordinates d → ℝ) x =
          r * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (cubeDilation z 0 r x) := by
    intro i
    filter_upwards [hw₁ i] with x hx
    calc
      ((w₀ : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
          SpatialCoordinates d → ℝ) x = u₀.grad x i := hx
      _ = r * uT.grad (r • x + z) i := by
        simp [u₀, Pi.smul_apply, smul_eq_mul, add_comm]
      _ = r * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (cubeDilation z 0 r x) := by
        rw [hcube x]
        have hugu := congrFun (congrFun hug (r • x + z)) i
        simpa [uT, hcastGrad, add_comm] using! congrArg (fun q : ℝ => r * q) hugu
  have hmean :
      (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
        (w₀ : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x) = 0 := by
    let f : SpatialCoordinates d → ℝ :=
      (v : SobolevData (centeredCube z r hr)).1
    have hscale :
        (∫ x in U, f (z + r • x) ∂volume) =
          (r ^ d)⁻¹ • ∫ y in r • U, f (z + y) ∂volume := by
      simpa [U, f, add_comm, add_left_comm, add_assoc, smul_eq_mul] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := (volume : Measure (SpatialCoordinates d)))
          (f := fun y : SpatialCoordinates d => f (z + y))
          (s := U) hr)
    have htranslate :
        (∫ y in r • U, f (z + y) ∂volume) =
          ∫ q in Homogenization.translateSet z (r • U), f q ∂volume := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (Homogenization.setIntegral_comp_addRight_translateSet
          (d := d) z (r • U) f)
    calc
      (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
          (w₀ : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x) =
          ∫ x in U, f (cubeDilation z 0 r x) := by
            simpa [U, f] using (integral_congr_ae hwval)
      _ = ∫ x in U, f (z + r • x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hx : cubeDilation z 0 r x = z + r • x := by
          ext i
          simp [cubeDilation]
        rw [hx]
      _ = (r ^ d)⁻¹ • ∫ y in r • U, f (z + y) ∂volume := hscale
      _ = (r ^ d)⁻¹ • ∫ q in Homogenization.translateSet z (r • U), f q ∂volume := by
        rw [htranslate]
      _ = (r ^ d)⁻¹ • ∫ q in (centeredCube z r hr : Set (SpatialCoordinates d)), f q ∂volume := by
        rw [hgeom]
      _ = 0 := by simp [hvmean, f]
  refine ⟨⟨w₀, ?_⟩, ?_, ?_⟩
  · exact (mem_meanZeroSobolevGraph_iff
      (w₀ : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))).2
      ⟨w₀.2, hmean⟩
  · exact hwval
  · exact hwgrad

end SubdiffusiveProcess.Paper
