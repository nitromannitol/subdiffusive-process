import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane4.Bridge
import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
import Homogenization.Sobolev.H1.Translation
import SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_cube_geometry

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem aux_lane4_coercivity_dilation_killed_pullback_cast_toFun
    {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (hUV : U = V) (u : Homogenization.H10Function U) :
    (hUV ▸ u).toH1Function.toFun = u.toH1Function.toFun := by
  subst V
  rfl

theorem aux_lane4_coercivity_dilation_killed_pullback_cast_grad
    {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (hUV : U = V) (u : Homogenization.H10Function U) :
    (hUV ▸ u).toH1Function.grad = u.toH1Function.grad := by
  subst V
  rfl

theorem aux_lane4_coercivity_dilation_killed_pullback
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : killedSobolevGraph (centeredCube z r hr)) :
    ∃ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1),
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
  obtain ⟨u, hu_val, hu_grad⟩ :=
    SubdiffusiveProcess.exists_nativeH10Function_of_killedSobolevGraph v
  have hgeom := aux_lane4_coercivity_dilation_cube_geometry d z r hr h1
  have htranslate : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) :=
    hgeom.1
  have hscale : (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
      r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) :=
    hgeom.2
  let uT : Homogenization.H10Function
      (Homogenization.translateSet z
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))) :=
    htranslate ▸ u
  have huT_val : uT.toH1Function.toFun = u.toH1Function.toFun := by
    exact aux_lane4_coercivity_dilation_killed_pullback_cast_toFun htranslate u
  have huT_grad : uT.toH1Function.grad = u.toH1Function.grad := by
    exact aux_lane4_coercivity_dilation_killed_pullback_cast_grad htranslate u
  let u0 : Homogenization.H10Function
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) :=
    Homogenization.H10Function.untranslate z uT
  have hu0_val (x : SpatialCoordinates d) :
      u0.toH1Function.toFun x = uT.toH1Function.toFun (x + z) := by
    simp [u0, Homogenization.H10Function.untranslate_toH1Function,
      Homogenization.H1Function.untranslate_toFun]
  have hu0_grad (x : SpatialCoordinates d) :
      u0.toH1Function.grad x = uT.toH1Function.grad (x + z) := by
    simp [u0, Homogenization.H10Function.untranslate_toH1Function,
      Homogenization.H1Function.untranslate_grad]
  let uS : Homogenization.H10Function
      (r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) :=
    hscale ▸ u0
  have huS_val : uS.toH1Function.toFun = u0.toH1Function.toFun := by
    exact aux_lane4_coercivity_dilation_killed_pullback_cast_toFun hscale u0
  have huS_grad : uS.toH1Function.grad = u0.toH1Function.grad := by
    exact aux_lane4_coercivity_dilation_killed_pullback_cast_grad hscale u0
  let u1 : Homogenization.H10Function
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) :=
    Homogenization.H10Function.unscale hr uS
  obtain ⟨w, hw_val, hw_grad⟩ :=
    SubdiffusiveProcess.Lane4.exists_killedSobolevGraph_of_nativeH10 u1
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw_val] with x hx
    rw [hx]
    have hux : (u1 : SpatialCoordinates d → ℝ) x =
        (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x) := by
      change u1.toH1Function.toFun x = _
      rw [Homogenization.H10Function.unscale_toH1Function,
        Homogenization.H1Function.unscale_toFun]
      rw [huS_val, hu0_val, huT_val]
      rw [hu_val]
      congr 1
      funext i
      simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
      ring
    exact hux
  · intro i
    filter_upwards [hw_grad i] with x hx
    rw [hx]
    have hgradx : (u1.toH1Function.grad x) i =
        r * ((v : SobolevData (centeredCube z r hr)).2 i :
          SpatialCoordinates d → ℝ) (cubeDilation z 0 r x) := by
      rw [Homogenization.H10Function.unscale_toH1Function,
        Homogenization.H1Function.unscale_grad, Pi.smul_apply, smul_eq_mul]
      rw [huS_grad, hu0_grad, huT_grad]
      rw [hu_grad]
      congr 2
      funext j
      simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
      ring
    exact hgradx

end Paper
