import SubdiffusiveProcess.Paper.inputs_poincare_gradient
import SubdiffusiveProcess.Analysis.AffineSobolevNorms
import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
import Homogenization.Sobolev.H1.Translation
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Sobolev.NativeH10
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Frozen.Section2.CoarseGrainedPoincare

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_inputs_poincare_killed_transport_cube_geometry (d : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) =
        Homogenization.translateSet z
          (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) ∧
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
        r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) := by
  constructor
  · change Metric.ball z (r / 2) =
      Homogenization.translateSet z (Metric.ball (0 : SpatialCoordinates d) (r / 2))
    ext x
    rw [Homogenization.mem_translateSet_iff_sub_mem]
    simp only [Metric.mem_ball]
    rw [dist_eq_norm, dist_eq_norm]
    simp
  · change Metric.ball (0 : SpatialCoordinates d) (r / 2) =
      r • Metric.ball (0 : SpatialCoordinates d) (1 / 2)
    rw [_root_.smul_ball hr.ne']
    simp [abs_of_pos hr]
    ring_nf

theorem aux_inputs_poincare_killed_transport_cast_toFun
    {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (hUV : U = V) (u : Homogenization.H10Function U) :
    (hUV ▸ u).toH1Function.toFun = u.toH1Function.toFun := by
  subst V
  rfl

theorem aux_inputs_poincare_killed_transport_cast_grad
    {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (hUV : U = V) (u : Homogenization.H10Function U) :
    (hUV ▸ u).toH1Function.grad = u.toH1Function.grad := by
  subst V
  rfl

theorem aux_inputs_poincare_killed_transport_native
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : killedSobolevGraph (centeredCube z r hr)) :
    ∃ u1 : Homogenization.H10Function
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      (∀ x, u1.toH1Function.toFun x =
        (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x)) ∧
      (∀ x i, u1.toH1Function.grad x i =
        r * (v : SobolevData (centeredCube z r hr)).2 i (cubeDilation z 0 r x)) := by
  obtain ⟨u, hu_val, hu_grad⟩ :=
    SubdiffusiveProcess.exists_nativeH10Function_of_killedSobolevGraph v
  have hgeom := aux_inputs_poincare_killed_transport_cube_geometry d z r hr h1
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
    exact aux_inputs_poincare_killed_transport_cast_toFun htranslate u
  have huT_grad : uT.toH1Function.grad = u.toH1Function.grad := by
    exact aux_inputs_poincare_killed_transport_cast_grad htranslate u
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
    exact aux_inputs_poincare_killed_transport_cast_toFun hscale u0
  have huS_grad : uS.toH1Function.grad = u0.toH1Function.grad := by
    exact aux_inputs_poincare_killed_transport_cast_grad hscale u0
  let u1 : Homogenization.H10Function
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) :=
    Homogenization.H10Function.unscale hr uS
  refine ⟨u1, ?_, ?_⟩
  · intro x
    rw [Homogenization.H10Function.unscale_toH1Function,
      Homogenization.H1Function.unscale_toFun]
    rw [huS_val, hu0_val, huT_val, hu_val]
    congr 1
    funext i
    simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
    ring
  · intro x i
    rw [Homogenization.H10Function.unscale_toH1Function,
      Homogenization.H1Function.unscale_grad, Pi.smul_apply, smul_eq_mul]
    rw [huS_grad, hu0_grad, huT_grad, hu_grad]
    congr 2
    funext j
    simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
    ring

theorem inputs_poincare_killed_transport (d : ℕ) (hd : 2 ≤ d) (Jc : Paper.in_J d) :
    (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (u : killedSobolevGraph (centeredCube z r hr)),
      ∃ v : Homogenization.H10Function
        (Homogenization.openCubeSet (Homogenization.originCube d 0)),
        Homogenization.cubeLpNorm (Homogenization.originCube d 0) (2 : ℝ≥0∞)
          v.toH1Function.toFun =
          ‖(u : SobolevData (centeredCube z r hr)).1‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr a z r) v.toH1Function.grad =
          r * normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData (centeredCube z r hr)))) := by
  intro z r hr a u
  obtain ⟨v1, hv1, hgv1⟩ := aux_inputs_poincare_killed_transport_native d z r hr one_pos u
  let Q := Homogenization.originCube d 0
  have hroot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
      Homogenization.openCubeSet Q := by
    simpa [Q] using SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube
      (d := d) (m := 0) (by norm_num : (0 : ℝ) < (3 : ℝ) ^ (0 : ℤ))
  let v : Homogenization.H10Function (Homogenization.openCubeSet Q) := hroot ▸ v1
  have hv : ∀ x, v.toH1Function.toFun x =
      (u : SobolevData (centeredCube z r hr)).1 (fun i => z i + r * x i) := by
    intro x
    rw [show v.toH1Function.toFun = v1.toH1Function.toFun from
      aux_inputs_poincare_killed_transport_cast_toFun hroot v1, hv1]
    congr 1
    funext i
    simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
  have hgv : ∀ x i, v.toH1Function.grad x i =
      r * (u : SobolevData (centeredCube z r hr)).2 i (fun j => z j + r * x j) := by
    intro x i
    rw [show v.toH1Function.grad = v1.toH1Function.grad from
      aux_inputs_poincare_killed_transport_cast_grad hroot v1, hgv1]
    congr 2
    funext j
    simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
  let vs : Homogenization.H1Function (Homogenization.openCubeSet Q) := r⁻¹ • v.toH1Function
  let uw : weakSobolevGraph (centeredCube z r hr) :=
    ⟨u, killedSobolevGraph_le_weakSobolevGraph u.property⟩
  have hvs : ∀ x, vs.toFun x = r⁻¹ *
      (u : SobolevData (centeredCube z r hr)).1 (fun i => z i + r * x i) := by
    intro x
    change r⁻¹ * v.toH1Function.toFun x = _
    rw [hv]
  have hgvs : ∀ x i, vs.grad x i =
      (uw : SobolevData (centeredCube z r hr)).2 i (fun j => z j + r * x j) := by
    intro x i
    change r⁻¹ * v.toH1Function.grad x i = _
    rw [hgv, inv_mul_cancel_left₀ hr.ne']
  refine ⟨v, ?_, ?_⟩
  · obtain ⟨uA, huA, _⟩ := SubdiffusiveProcess.AffineSobolevNorms.nativeH1_axis z r hr uw
    have hnorm := SubdiffusiveProcess.AffineSobolevNorms.normalized_l2_rescaled_pullback
      z r hr (u : SobolevData (centeredCube z r hr)) uA huA vs hvs
    have hscale : Homogenization.cubeLpNorm Q 2 vs.toFun =
        r⁻¹ * Homogenization.cubeLpNorm Q 2 v.toH1Function.toFun := by
      change Homogenization.cubeLpNorm Q 2 (fun x => r⁻¹ * v.toH1Function.toFun x) = _
      rw [Homogenization.cubeLpNorm_const_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    rw [hscale, mul_inv_cancel_left₀ hr.ne'] at hnorm
    exact hnorm.symm
  · have he := aux_inputs_poincare_gradient_energy Jc z r hr a uw vs hgvs
    let A := Jc.chart z r hr a z r
    change Real.sqrt (∫ x, Homogenization.vecDot (vs.grad x)
      (Homogenization.matVecMul (Homogenization.symmPart ((A.coeffOn Q).toCoeffField x))
        (vs.grad x)) ∂Homogenization.normalizedCubeMeasure Q) = _ at he
    simp only [Homogenization.vecDot_matVecMul_symmPart] at he
    change SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm Q A vs.grad =
      normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) at he
    have hg : v.toH1Function.grad = fun x => r • vs.grad x := by
      funext x i
      change v.toH1Function.grad x i = r * (r⁻¹ * v.toH1Function.grad x i)
      rw [mul_inv_cancel_left₀ hr.ne']
    rw [hg, SubdiffusiveProcess.AffineSobolevNorms.coefficientEnergyNorm_smul,
      abs_of_pos hr]
    rw [he]

end Paper

