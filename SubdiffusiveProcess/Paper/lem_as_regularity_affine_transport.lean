module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane4.CubeDilation
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Lane4.Bridge
public import SubdiffusiveProcess.Paper.lane4_dilation_coefficient_transport
public import SubdiffusiveProcess.Paper.lane4_dilation_quasi_measure_preserving
public import SubdiffusiveProcess.Paper.lane4_energy_dilation_scaling
public import SubdiffusiveProcess.Paper.lane4_gagliardo_dilation_scaling
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

noncomputable section
namespace Paper

theorem aux_lem_as_regularity_affine_transport_geometry
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) =
        Homogenization.translateSet z
          (r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) := by
  have ht : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) := by
    change Metric.ball z (r / 2) =
      Homogenization.translateSet z (Metric.ball (0 : SpatialCoordinates d) (r / 2))
    ext x
    rw [Homogenization.mem_translateSet_iff_sub_mem]
    simp only [Metric.mem_ball, dist_eq_norm]
    simp
  have hs : (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
      r • (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) := by
    change Metric.ball (0 : SpatialCoordinates d) (r / 2) =
      r • Metric.ball (0 : SpatialCoordinates d) (1 / 2)
    rw [_root_.smul_ball hr.ne']
    simp [abs_of_pos hr]
    ring_nf
  rw [ht, hs]

theorem aux_lem_as_regularity_affine_transport_weak_pullback
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : weakSobolevGraph (centeredCube z r hr)) :
    ∃ w : weakSobolevGraph (centeredCube z' 1 h1),
      (∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube z' 1 h1)).1 x =
          (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x)) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        ((w : SobolevData (centeredCube z' 1 h1)).2 i : SpatialCoordinates d → ℝ) x =
          r * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (cubeDilation z z' r x)) := by
  let U : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))
  have hgeom' : (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z' U := by
    change Metric.ball z' (1 / 2) =
      Homogenization.translateSet z' (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
    ext x
    rw [Homogenization.mem_translateSet_iff_sub_mem]
    simp only [Metric.mem_ball, dist_eq_norm]
    simp
  have hgeom : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z (r • U) := by
    simpa [U] using! aux_lem_as_regularity_affine_transport_geometry d z r hr h1
  obtain ⟨u, huval, hugrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph v
  let uT : Homogenization.H1Function (Homogenization.translateSet z (r • U)) :=
    hgeom ▸ u
  let u0 : Homogenization.H1Function U :=
    Homogenization.H1Function.unscale hr (Homogenization.H1Function.untranslate z uT)
  let wH : Homogenization.H1Function
      (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) :=
    hgeom'.symm ▸ u0.translate z'
  obtain ⟨w, hwval, hwgrad⟩ :=
    SubdiffusiveProcess.Lane4.exists_weakSobolevGraph_of_nativeH1
      (Om := centeredCube z' 1 h1) wH
  have hcast_toFun {U V : Set (SpatialCoordinates d)} (h : U = V)
      (u : Homogenization.H1Function U) : (h ▸ u).toFun = u.toFun := by
    subst V
    rfl
  have hvalue :
      ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube z' 1 h1)).1 x =
          (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x) := by
    filter_upwards [hwval] with x hx
    calc
      (w : SobolevData (centeredCube z' 1 h1)).1 x = wH.toFun x := hx
      _ = u0.toFun (x - z') := by
        simp [wH, hcast_toFun, Homogenization.H1Function.translate_toFun]
      _ = uT.toFun (r • (x - z') + z) := by
        simp [u0, Homogenization.H1Function.untranslate_toFun,
          Homogenization.H1Function.unscale_toFun]
      _ = (v : SobolevData (centeredCube z r hr)).1
          (cubeDilation z z' r x) := by
        have harg : r • (x - z') + z = cubeDilation z z' r x := by
          funext i
          simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
          ring
        rw [harg]
        simpa [uT, hcast_toFun] using! congrFun huval (cubeDilation z z' r x)
  refine ⟨w, hvalue, ?_⟩
  · have hv := Paper.lane4_weak_gradient_chain_rule d z z' r hr h1
      (v : SobolevData (centeredCube z r hr)) (w : SobolevData (centeredCube z' 1 h1))
      v.property w.property
    exact hv hvalue

theorem aux_lem_as_regularity_affine_transport_integral_scaling
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) (f : SpatialCoordinates d → ℝ)
    (hf : AEMeasurable f
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    (∫ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        f (cubeDilation z z' r x)) =
      (r ^ d)⁻¹ * (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), f y) := by
  have hmap := map_cubeDilation_restrict z z' hr h1
  have hfm : AEStronglyMeasurable f
      (Measure.map (cubeDilation z z' r)
        (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))) := by
    rw [hmap]
    exact hf.aestronglyMeasurable.mono_ac Measure.smul_absolutelyContinuous
  have hchange :
      (∫ y, f y ∂Measure.map (cubeDilation z z' r)
        (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))) =
        ∫ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
          f (cubeDilation z z' r x) := by
    exact integral_map (continuous_cubeDilation z z' r).measurable.aemeasurable hfm
  have htransport :
      (ENNReal.ofReal |(r ^ d)⁻¹|).toReal •
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), f y) =
        ∫ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
          f (cubeDilation z z' r x) := by
    calc
      (ENNReal.ofReal |(r ^ d)⁻¹|).toReal •
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), f y) =
          ∫ y, f y ∂(ENNReal.ofReal |(r ^ d)⁻¹| •
            volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
              symm
              exact integral_smul_measure f _
      _ = ∫ y, f y ∂Measure.map (cubeDilation z z' r)
          (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by
            rw [hmap]
      _ = ∫ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
          f (cubeDilation z z' r x) := hchange
  have hreal : (ENNReal.ofReal |(r ^ d)⁻¹|).toReal = (r ^ d)⁻¹ := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos]
    positivity
  rw [hreal] at htransport
  simpa only [smul_eq_mul] using! htransport.symm

theorem aux_lem_as_regularity_affine_transport_h1_cast_toFun
    {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (hUV : U = V) (u : Homogenization.H1Function U) :
    (hUV ▸ u).toFun = u.toFun := by
  subst V
  rfl

theorem aux_lem_as_regularity_affine_transport_h10_cast_toFun
    {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (hUV : U = V) (u : Homogenization.H10Function U) :
    (hUV ▸ u).toH1Function.toFun = u.toH1Function.toFun := by
  subst V
  rfl

theorem aux_lem_as_regularity_affine_transport_killed_pullback
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : killedSobolevGraph (centeredCube z r hr)) :
    ∃ w : killedSobolevGraph (centeredCube z' 1 h1),
      (∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube z' 1 h1)).1 x =
          (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x)) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        ((w : SobolevData (centeredCube z' 1 h1)).2 i : SpatialCoordinates d → ℝ) x =
          r * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (cubeDilation z z' r x)) := by
  let U : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))
  have hgeom : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z (r • U) := by
    simpa [U] using! aux_lem_as_regularity_affine_transport_geometry d z r hr h1
  have hgeom' : (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z' U := by
    change Metric.ball z' (1 / 2) =
      Homogenization.translateSet z' (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
    ext x
    rw [Homogenization.mem_translateSet_iff_sub_mem]
    simp only [Metric.mem_ball, dist_eq_norm]
    simp
  obtain ⟨u, huval, hugrad⟩ :=
    SubdiffusiveProcess.exists_nativeH10Function_of_killedSobolevGraph v
  let uT : Homogenization.H10Function (Homogenization.translateSet z (r • U)) :=
    hgeom ▸ u
  let u0 : Homogenization.H10Function (r • U) :=
    Homogenization.H10Function.untranslate z uT
  let u1 : Homogenization.H10Function U :=
    Homogenization.H10Function.unscale hr u0
  let wH : Homogenization.H10Function
      (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) :=
    hgeom'.symm ▸ u1.translate z'
  have hwHval : wH.toH1Function.toFun = (u1.translate z').toFun := by
    exact aux_lem_as_regularity_affine_transport_h10_cast_toFun hgeom'.symm
      (u1.translate z')
  have huTval : uT.toH1Function.toFun = u.toH1Function.toFun := by
    exact aux_lem_as_regularity_affine_transport_h10_cast_toFun hgeom u
  obtain ⟨w, hwval, hwgrad⟩ :=
    SubdiffusiveProcess.Lane4.exists_killedSobolevGraph_of_nativeH10
      (Ω := centeredCube z' 1 h1) wH
  have hvalue :
      ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube z' 1 h1)).1 x =
          (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x) := by
    filter_upwards [hwval] with x hx
    calc
      (w : SobolevData (centeredCube z' 1 h1)).1 x = wH.toH1Function.toFun x := hx
      _ = u1.toH1Function.toFun (x - z') := by
        rw [hwHval]
        simp [Homogenization.H10Function.toH1Function,
          Homogenization.H1Function.translate_toFun]
      _ = uT.toH1Function.toFun (r • (x - z') + z) := by
        simp [u1, Homogenization.H10Function.unscale_toH1Function,
          Homogenization.H1Function.unscale_toFun,
          u0, Homogenization.H10Function.untranslate_toH1Function,
          Homogenization.H1Function.untranslate_toFun]
      _ = (v : SobolevData (centeredCube z r hr)).1
          (cubeDilation z z' r x) := by
        have harg : r • (x - z') + z = cubeDilation z z' r x := by
          funext i
          simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
          ring
        rw [harg]
        rw [huTval]
        exact congrFun huval (cubeDilation z z' r x)
  refine ⟨w, hvalue, ?_⟩
  have hvweak : (v : SobolevData (centeredCube z r hr)) ∈
      weakSobolevGraph (centeredCube z r hr) :=
    (killedSobolevGraph_le_weakSobolevGraph v.property)
  have hwweak : (w : SobolevData (centeredCube z' 1 h1)) ∈
      weakSobolevGraph (centeredCube z' 1 h1) :=
    (killedSobolevGraph_le_weakSobolevGraph w.property)
  have hv := Paper.lane4_weak_gradient_chain_rule d z z' r hr h1
      (v : SobolevData (centeredCube z r hr)) (w : SobolevData (centeredCube z' 1 h1))
      hvweak hwweak
  exact hv hvalue

theorem aux_lem_as_regularity_affine_transport_meanzero_pullback
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : meanZeroSobolevGraph (centeredCube z r hr)) :
    ∃ w : meanZeroSobolevGraph (centeredCube z' 1 h1),
      (∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube z' 1 h1)).1 x =
          (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x)) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        ((w : SobolevData (centeredCube z' 1 h1)).2 i : SpatialCoordinates d → ℝ) x =
          r * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
            (cubeDilation z z' r x)) := by
  have hvweak : (v : SobolevData (centeredCube z r hr)) ∈
      weakSobolevGraph (centeredCube z r hr) :=
    ((mem_meanZeroSobolevGraph_iff
      (v : SobolevData (centeredCube z r hr))).mp v.property).1
  have hvmean :
      (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        (v : SobolevData (centeredCube z r hr)).1 y) = 0 :=
    ((mem_meanZeroSobolevGraph_iff
      (v : SobolevData (centeredCube z r hr))).mp v.property).2
  obtain ⟨w, hwval, hwgrad⟩ :=
    aux_lem_as_regularity_affine_transport_weak_pullback d z z' r hr h1
      ⟨(v : SobolevData (centeredCube z r hr)), hvweak⟩
  have hf : AEMeasurable
      ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (Lp.aestronglyMeasurable
      ((v : SobolevData (centeredCube z r hr)).1)).aemeasurable
  have hwmean :
      (∫ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube z' 1 h1)).1 x) = 0 := by
    calc
      (∫ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
          (w : SobolevData (centeredCube z' 1 h1)).1 x) =
          ∫ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
            (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x) :=
        integral_congr_ae hwval
      _ = (r ^ d)⁻¹ *
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            (v : SobolevData (centeredCube z r hr)).1 y) :=
        aux_lem_as_regularity_affine_transport_integral_scaling d z z' r hr h1 _ hf
      _ = 0 := by rw [hvmean, mul_zero]
  refine ⟨⟨w, ?_⟩, hwval, hwgrad⟩
  exact (mem_meanZeroSobolevGraph_iff
    (w : SobolevData (centeredCube z' 1 h1))).2 ⟨w.property, hwmean⟩

theorem aux_lem_as_regularity_affine_transport_weak_pushforward
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : weakSobolevGraph (centeredCube z' 1 h1)) :
    ∃ w : weakSobolevGraph (centeredCube z r hr),
      (∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        (v : SobolevData (centeredCube z' 1 h1)).1 x =
          (w : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x)) := by
  let U : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))
  have hgeom : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z (r • U) := by
    simpa [U] using! aux_lem_as_regularity_affine_transport_geometry d z r hr h1
  have hgeom' : (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z' U := by
    change Metric.ball z' (1 / 2) =
      Homogenization.translateSet z' (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
    ext x
    rw [Homogenization.mem_translateSet_iff_sub_mem]
    simp only [Metric.mem_ball, dist_eq_norm]
    simp
  have hinv : r⁻¹ • (r • U) = U := by
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨u, huval, hugrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph v
  let u0 : Homogenization.H1Function U :=
    Homogenization.H1Function.untranslate z' (hgeom' ▸ u)
  let u0' : Homogenization.H1Function (r⁻¹ • (r • U)) :=
    hinv.symm ▸ u0
  let uR : Homogenization.H1Function (r • U) :=
    Homogenization.H1Function.unscale (inv_pos.mpr hr) u0'
  let wH : Homogenization.H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    hgeom.symm ▸ uR.translate z
  have hu0eq : (hgeom' ▸ u).toFun = u.toFun :=
    aux_lem_as_regularity_affine_transport_h1_cast_toFun hgeom' u
  have hu0'val : u0'.toFun = u0.toFun := by
    exact aux_lem_as_regularity_affine_transport_h1_cast_toFun hinv.symm u0
  have hwHval : wH.toFun = (uR.translate z).toFun := by
    exact aux_lem_as_regularity_affine_transport_h1_cast_toFun hgeom.symm (uR.translate z)
  obtain ⟨w, hwval, hwgrad⟩ :=
    SubdiffusiveProcess.Lane4.exists_weakSobolevGraph_of_nativeH1
      (Om := centeredCube z r hr) wH
  refine ⟨w, ?_⟩
  have hq := lane4_dilation_quasi_measure_preserving d z z' r hr h1
  have hwval_pull := hq.ae hwval
  filter_upwards [hwval_pull] with x hx
  calc
    (v : SobolevData (centeredCube z' 1 h1)).1 x = u.toFun x :=
      (congrFun huval x).symm
    _ = u0.toFun (x - z') := by
      simp [u0, Homogenization.H1Function.untranslate_toFun, hu0eq]
    _ = uR.toFun (r • (x - z')) := by
      simp [uR, Homogenization.H1Function.unscale_toFun, hu0'val,
        smul_smul, hr.ne']
    _ = wH.toFun (cubeDilation z z' r x) := by
      rw [hwHval]
      simp [Homogenization.H1Function.translate_toFun]
      congr 1
      funext i
      simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
    _ = (w : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x) := hx.symm

theorem aux_lem_as_regularity_affine_transport_killed_pushforward
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (v : killedSobolevGraph (centeredCube z' 1 h1)) :
    ∃ w : killedSobolevGraph (centeredCube z r hr),
      (∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        (v : SobolevData (centeredCube z' 1 h1)).1 x =
          (w : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x)) := by
  let U : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))
  have hgeom : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z (r • U) := by
    simpa [U] using! aux_lem_as_regularity_affine_transport_geometry d z r hr h1
  have hgeom' : (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z' U := by
    change Metric.ball z' (1 / 2) =
      Homogenization.translateSet z' (Metric.ball (0 : SpatialCoordinates d) (1 / 2))
    ext x
    rw [Homogenization.mem_translateSet_iff_sub_mem]
    simp only [Metric.mem_ball, dist_eq_norm]
    simp
  have hinv : r⁻¹ • (r • U) = U := by
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨u, huval, hugrad⟩ :=
    SubdiffusiveProcess.exists_nativeH10Function_of_killedSobolevGraph v
  let u0 : Homogenization.H10Function U :=
    Homogenization.H10Function.untranslate z' (hgeom' ▸ u)
  let u0' : Homogenization.H10Function (r⁻¹ • (r • U)) :=
    hinv.symm ▸ u0
  let uR : Homogenization.H10Function (r • U) :=
    Homogenization.H10Function.unscale (inv_pos.mpr hr) u0'
  let wH : Homogenization.H10Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    hgeom.symm ▸ uR.translate z
  have hu0eq : (hgeom' ▸ u).toH1Function.toFun = u.toH1Function.toFun :=
    aux_lem_as_regularity_affine_transport_h10_cast_toFun hgeom' u
  have hu0'val : u0'.toH1Function.toFun = u0.toH1Function.toFun := by
    exact aux_lem_as_regularity_affine_transport_h10_cast_toFun hinv.symm u0
  have hwHval : wH.toH1Function.toFun = (uR.translate z).toH1Function.toFun := by
    exact aux_lem_as_regularity_affine_transport_h10_cast_toFun hgeom.symm
      (uR.translate z)
  obtain ⟨w, hwval, hwgrad⟩ :=
    SubdiffusiveProcess.Lane4.exists_killedSobolevGraph_of_nativeH10
      (Ω := centeredCube z r hr) wH
  refine ⟨w, ?_⟩
  have hq := lane4_dilation_quasi_measure_preserving d z z' r hr h1
  have hwval_pull := hq.ae hwval
  filter_upwards [hwval_pull] with x hx
  calc
    (v : SobolevData (centeredCube z' 1 h1)).1 x = u.toH1Function.toFun x :=
      (congrFun huval x).symm
    _ = u0.toH1Function.toFun (x - z') := by
      simp [u0, Homogenization.H10Function.untranslate_toH1Function,
        Homogenization.H1Function.untranslate_toFun, hu0eq]
    _ = uR.toH1Function.toFun (r • (x - z')) := by
      simp [uR, Homogenization.H10Function.unscale_toH1Function,
        Homogenization.H1Function.unscale_toFun, hu0'val,
        smul_smul, hr.ne']
    _ = wH.toH1Function.toFun (cubeDilation z z' r x) := by
      rw [hwHval]
      simp [Homogenization.H1Function.translate_toFun]
      congr 1
      funext i
      simp [cubeDilation, Pi.smul_apply, smul_eq_mul]
    _ = (w : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x) := hx.symm

theorem aux_lem_as_regularity_affine_transport_form_scaling
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube z' 1 h1))
    (u u' : weakSobolevGraph (centeredCube z r hr))
    (w w' : weakSobolevGraph (centeredCube z' 1 h1))
    (hab : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      b.val x = a.val (cubeDilation z z' r x))
    (hu : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      (w : SobolevData (centeredCube z' 1 h1)).1 x =
        (u : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x))
    (hu' : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      (w' : SobolevData (centeredCube z' 1 h1)).1 x =
        (u' : SobolevData (centeredCube z r hr)).1 (cubeDilation z z' r x)) :
    sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
        (u' : SobolevData (centeredCube z r hr)) =
      r ^ ((d : ℝ) - 2) *
        sobolevCoefficientForm b (w : SobolevData (centeredCube z' 1 h1))
          (w' : SobolevData (centeredCube z' 1 h1)) := by
  let us : SobolevData (centeredCube z r hr) :=
    (u : SobolevData (centeredCube z r hr)) +
      (u' : SobolevData (centeredCube z r hr))
  let ws : SobolevData (centeredCube z' 1 h1) :=
    (w : SobolevData (centeredCube z' 1 h1)) +
      (w' : SobolevData (centeredCube z' 1 h1))
  have hus : us ∈ weakSobolevGraph (centeredCube z r hr) := by
    exact (weakSobolevGraph (centeredCube z r hr)).add_mem u.property u'.property
  have hws : ws ∈ weakSobolevGraph (centeredCube z' 1 h1) := by
    exact (weakSobolevGraph (centeredCube z' 1 h1)).add_mem w.property w'.property
  have hq := lane4_dilation_quasi_measure_preserving d z z' r hr h1
  have husae := hq.ae
    (Lp.coeFn_add (u : SobolevData (centeredCube z r hr)).1
      (u' : SobolevData (centeredCube z r hr)).1)
  have hvals : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      ws.1 x = us.1 (cubeDilation z z' r x) := by
    filter_upwards [hu, hu',
      Lp.coeFn_add (w : SobolevData (centeredCube z' 1 h1)).1
        (w' : SobolevData (centeredCube z' 1 h1)).1,
      husae] with x hx hx' hwsx husx
    change ((w : SobolevData (centeredCube z' 1 h1)).1 +
      (w' : SobolevData (centeredCube z' 1 h1)).1) x =
      (((u : SobolevData (centeredCube z r hr)).1 +
        (u' : SobolevData (centeredCube z r hr)).1) (cubeDilation z z' r x))
    rw [hwsx, husx]
    simp only [Pi.add_apply]
    rw [hx, hx']
  have he : sobolevCoefficientForm a us us =
      r ^ ((d : ℝ) - 2) * sobolevCoefficientForm b ws ws :=
    lane4_energy_dilation_scaling d z z' r hr h1 a b us ws hus hws hab hvals
  have heu : sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
      (u : SobolevData (centeredCube z r hr)) =
      r ^ ((d : ℝ) - 2) * sobolevCoefficientForm b (w : SobolevData (centeredCube z' 1 h1))
        (w : SobolevData (centeredCube z' 1 h1)) :=
    lane4_energy_dilation_scaling d z z' r hr h1 a b u.val w.val u.property w.property hab hu
  have heu' : sobolevCoefficientForm a (u' : SobolevData (centeredCube z r hr))
      (u' : SobolevData (centeredCube z r hr)) =
      r ^ ((d : ℝ) - 2) * sobolevCoefficientForm b (w' : SobolevData (centeredCube z' 1 h1))
        (w' : SobolevData (centeredCube z' 1 h1)) :=
    lane4_energy_dilation_scaling d z z' r hr h1 a b u'.val w'.val u'.property w'.property hab hu'
  have hsource : sobolevCoefficientForm a us us =
      sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
          (u : SobolevData (centeredCube z r hr)) +
        sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
          (u' : SobolevData (centeredCube z r hr)) +
        sobolevCoefficientForm a (u' : SobolevData (centeredCube z r hr))
          (u : SobolevData (centeredCube z r hr)) +
        sobolevCoefficientForm a (u' : SobolevData (centeredCube z r hr))
          (u' : SobolevData (centeredCube z r hr)) := by
    simp only [us, map_add, ContinuousLinearMap.add_apply]
    ring
  have htarget : sobolevCoefficientForm b ws ws =
      sobolevCoefficientForm b (w : SobolevData (centeredCube z' 1 h1))
          (w : SobolevData (centeredCube z' 1 h1)) +
        sobolevCoefficientForm b (w : SobolevData (centeredCube z' 1 h1))
          (w' : SobolevData (centeredCube z' 1 h1)) +
        sobolevCoefficientForm b (w' : SobolevData (centeredCube z' 1 h1))
          (w : SobolevData (centeredCube z' 1 h1)) +
        sobolevCoefficientForm b (w' : SobolevData (centeredCube z' 1 h1))
          (w' : SobolevData (centeredCube z' 1 h1)) := by
    simp only [ws, map_add, ContinuousLinearMap.add_apply]
    ring
  have hsymm_source : sobolevCoefficientForm a (u' : SobolevData (centeredCube z r hr))
      (u : SobolevData (centeredCube z r hr)) =
      sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
        (u' : SobolevData (centeredCube z r hr)) :=
    sobolevCoefficientForm_symm a _ _
  have hsymm_target : sobolevCoefficientForm b (w' : SobolevData (centeredCube z' 1 h1))
      (w : SobolevData (centeredCube z' 1 h1)) =
      sobolevCoefficientForm b (w : SobolevData (centeredCube z' 1 h1))
        (w' : SobolevData (centeredCube z' 1 h1)) :=
    sobolevCoefficientForm_symm b _ _
  calc
    sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
        (u' : SobolevData (centeredCube z r hr)) =
        (sobolevCoefficientForm a us us -
          sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
            (u : SobolevData (centeredCube z r hr)) -
          sobolevCoefficientForm a (u' : SobolevData (centeredCube z r hr))
            (u' : SobolevData (centeredCube z r hr))) / 2 := by
              rw [hsource]
              rw [← hsymm_source]
              ring
    _ = (r ^ ((d : ℝ) - 2) * sobolevCoefficientForm b ws ws -
          r ^ ((d : ℝ) - 2) * sobolevCoefficientForm b (w : SobolevData _) w -
          r ^ ((d : ℝ) - 2) * sobolevCoefficientForm b (w' : SobolevData _) w') / 2 := by
            simp only [he, heu, heu']
    _ = r ^ ((d : ℝ) - 2) *
          ((sobolevCoefficientForm b ws ws -
            sobolevCoefficientForm b (w : SobolevData _) w -
            sobolevCoefficientForm b (w' : SobolevData _) w') / 2) := by ring
    _ = r ^ ((d : ℝ) - 2) *
          sobolevCoefficientForm b (w : SobolevData (centeredCube z' 1 h1))
            (w' : SobolevData (centeredCube z' 1 h1)) := by
            rw [htarget]
            rw [← hsymm_target]
            ring

theorem aux_lem_as_regularity_affine_transport_fderiv
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) :
    ∀ x : SpatialCoordinates d,
      fderiv ℝ (cubeDilation z z' r) x =
        r • ContinuousLinearMap.id ℝ (SpatialCoordinates d) := by
  intro x
  have hpi : HasFDerivAt (cubeDilation z z' r)
      (ContinuousLinearMap.pi (fun i : Fin d =>
        r • (ContinuousLinearMap.proj i : SpatialCoordinates d →L[ℝ] ℝ))) x := by
    rw [hasFDerivAt_pi]
    intro i
    simpa [cubeDilation, smul_eq_mul] using!
      (((hasFDerivAt_apply (𝕜 := ℝ) i x).sub_const (z' i)).const_smul r).const_add (z i)
  rw [hpi.fderiv]
  ext y i
  simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply]

theorem aux_lem_as_regularity_affine_transport_c2_chain_rule
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi) :
    let T := cubeDilation z z' r
    let phi1 := fun x => phi (T x)
    ContDiff ℝ 2 phi1 ∧
      (∀ x, fderiv ℝ phi1 x =
        (fderiv ℝ phi (T x)).comp (r • ContinuousLinearMap.id ℝ (SpatialCoordinates d))) ∧
      (∀ x, ‖fderiv ℝ phi1 x‖ ≤ r * ‖fderiv ℝ phi (T x)‖) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ phi1) x‖ ≤
        r ^ 2 * ‖fderiv ℝ (fderiv ℝ phi) (T x)‖) := by
  dsimp
  let T : SpatialCoordinates d → SpatialCoordinates d := cubeDilation z z' r
  let A : SpatialCoordinates d →L[ℝ] SpatialCoordinates d :=
    r • ContinuousLinearMap.id ℝ (SpatialCoordinates d)
  have hT : ContDiff ℝ 2 T := by
    rw [contDiff_pi]
    intro i
    simpa [T, cubeDilation] using!
      contDiff_const.add
        (contDiff_const.mul ((contDiff_apply ℝ ℝ i).sub contDiff_const))
  have hTd : ∀ x, fderiv ℝ T x = A := by
    intro x
    simpa [T, A] using! aux_lem_as_regularity_affine_transport_fderiv d z z' r x
  have hfirst : ∀ x, fderiv ℝ (phi ∘ T) x =
      (fderiv ℝ phi (T x)).comp A := by
    intro x
    rw [fderiv_comp x (hphi.contDiffAt.differentiableAt (by norm_num))
      (hT.contDiffAt.differentiableAt (by norm_num)), hTd]
  let C : (SpatialCoordinates d →L[ℝ] ℝ) →L[ℝ]
      (SpatialCoordinates d →L[ℝ] ℝ) :=
    (ContinuousLinearMap.apply ℝ (SpatialCoordinates d →L[ℝ] ℝ) A).comp
      (ContinuousLinearMap.compL ℝ (SpatialCoordinates d)
        (SpatialCoordinates d) ℝ)
  have hC_apply (B : SpatialCoordinates d →L[ℝ] ℝ) : C B = B.comp A := by
    simp [C, ContinuousLinearMap.compL_apply]
  have hnormId : ‖ContinuousLinearMap.id ℝ (SpatialCoordinates d)‖ ≤ 1 := by
    apply (ContinuousLinearMap.id ℝ (SpatialCoordinates d)).opNorm_le_bound (by norm_num)
    intro y
    simp
  have hnormA : ‖A‖ ≤ r := by
    change ‖r • ContinuousLinearMap.id ℝ (SpatialCoordinates d)‖ ≤ r
    calc
      ‖r • ContinuousLinearMap.id ℝ (SpatialCoordinates d)‖ =
          r * ‖ContinuousLinearMap.id ℝ (SpatialCoordinates d)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ r * 1 := mul_le_mul_of_nonneg_left hnormId hr.le
      _ = r := by ring
  have hnormC : ‖C‖ ≤ r := by
    apply C.opNorm_le_bound hr.le
    intro B
    rw [hC_apply]
    calc
      ‖B.comp A‖ ≤ ‖B‖ * ‖A‖ := B.opNorm_comp_le A
      _ ≤ ‖B‖ * r :=
        mul_le_mul_of_nonneg_left hnormA (norm_nonneg B)
      _ = r * ‖B‖ := by rw [mul_comm]
  have hsecond : ∀ x, fderiv ℝ (fderiv ℝ (phi ∘ T)) x =
      C.comp ((fderiv ℝ (fderiv ℝ phi) (T x)).comp A) := by
    intro x
    have hG : ContDiffAt ℝ 1 (fderiv ℝ phi) (T x) :=
      hphi.contDiffAt.fderiv_right (by norm_num)
    have hGT : DifferentiableAt ℝ (fun y => fderiv ℝ phi (T y)) x :=
      (hG.comp x ((hT.contDiffAt (x := x)).of_le (by norm_num :
        (1 : WithTop ℕ∞) ≤ 2))).differentiableAt
        (by norm_num)
    have hfun : fderiv ℝ (phi ∘ T) =
        (fun y => (fderiv ℝ phi (T y)).comp A) := funext hfirst
    rw [hfun]
    have houter : DifferentiableAt ℝ C (fderiv ℝ phi (T x)) := C.differentiableAt
    rw [show (fun y => (fderiv ℝ phi (T y)).comp A) =
        C ∘ (fun y => fderiv ℝ phi (T y)) by
          funext y; exact (hC_apply _).symm]
    rw [fderiv_comp x houter hGT]
    rw [C.hasFDerivAt.fderiv]
    have hGTderiv :
        fderiv ℝ (fun y => fderiv ℝ phi (T y)) x =
          (fderiv ℝ (fderiv ℝ phi) (T x)).comp A := by
      change fderiv ℝ ((fderiv ℝ phi) ∘ T) x = _
      rw [fderiv_comp x (hG.differentiableAt (by norm_num))
        ((hT.contDiffAt (x := x)).differentiableAt (by norm_num)), hTd]
    rw [hGTderiv]
  refine ⟨by simpa [T] using! hphi.comp hT, ?_, ?_, ?_⟩
  · intro x
    exact hfirst x
  · intro x
    change ‖fderiv ℝ (phi ∘ T) x‖ ≤ r * ‖fderiv ℝ phi (T x)‖
    rw [hfirst x]
    calc
      ‖(fderiv ℝ phi (T x)).comp A‖ ≤ ‖fderiv ℝ phi (T x)‖ * ‖A‖ :=
        (fderiv ℝ phi (T x)).opNorm_comp_le A
      _ ≤ ‖fderiv ℝ phi (T x)‖ * r :=
        mul_le_mul_of_nonneg_left hnormA (norm_nonneg _)
      _ = r * ‖fderiv ℝ phi (T x)‖ := by rw [mul_comm]
  · intro x
    change ‖fderiv ℝ (fderiv ℝ (phi ∘ T)) x‖ ≤
      r ^ 2 * ‖fderiv ℝ (fderiv ℝ phi) (T x)‖
    rw [hsecond x]
    calc
      ‖C.comp ((fderiv ℝ (fderiv ℝ phi) (T x)).comp A)‖ ≤
          ‖C‖ * ‖(fderiv ℝ (fderiv ℝ phi) (T x)).comp A‖ :=
        C.opNorm_comp_le _
      _ ≤ r * (‖fderiv ℝ (fderiv ℝ phi) (T x)‖ * ‖A‖) := by
        calc
          ‖C‖ * ‖(fderiv ℝ (fderiv ℝ phi) (T x)).comp A‖ ≤
              r * ‖(fderiv ℝ (fderiv ℝ phi) (T x)).comp A‖ :=
            mul_le_mul_of_nonneg_right hnormC
              (norm_nonneg ((fderiv ℝ (fderiv ℝ phi) (T x)).comp A))
          _ ≤ r * (‖fderiv ℝ (fderiv ℝ phi) (T x)‖ * ‖A‖) :=
            mul_le_mul_of_nonneg_left
              ((fderiv ℝ (fderiv ℝ phi) (T x)).opNorm_comp_le A) hr.le
      _ ≤ r * (‖fderiv ℝ (fderiv ℝ phi) (T x)‖ * r) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnormA
            (norm_nonneg (fderiv ℝ (fderiv ℝ phi) (T x)))) hr.le
      _ = r ^ 2 * ‖fderiv ℝ (fderiv ℝ phi) (T x)‖ := by ring


theorem aux_lem_as_regularity_affine_transport_sup_comp_le
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S S' : Set X) (T : X → X) (g f : X → ℝ) (c : ℝ)
    (hS : S.Nonempty) (hc : 0 ≤ c)
    (hmap : ∀ x ∈ S, T x ∈ S')
    (hbdd : BddAbove {v : ℝ | ∃ y ∈ S', v = f y})
    (hpoint : ∀ x ∈ S, g x ≤ c * f (T x)) :
    sSup {v : ℝ | ∃ x ∈ S, v = g x} ≤
      c * sSup {v : ℝ | ∃ y ∈ S', v = f y} := by
  rcases hS with ⟨x, hx⟩
  refine csSup_le ⟨g x, ⟨x, hx, rfl⟩⟩ ?_
  rintro v ⟨x, hx, rfl⟩
  calc
    g x ≤ c * f (T x) := hpoint x hx
    _ ≤ c * sSup {v : ℝ | ∃ y ∈ S', v = f y} :=
      mul_le_mul_of_nonneg_left
        (le_csSup hbdd ⟨T x, hmap x hx, rfl⟩) hc

theorem aux_lem_as_regularity_affine_transport_sup_bdd
    {X : Type} [TopologicalSpace X] (S : Set X) (hS : IsCompact S)
    (f : X → ℝ) (hf : Continuous f) :
    BddAbove {v : ℝ | ∃ x ∈ S, v = f x} := by
  have himage : {v : ℝ | ∃ x ∈ S, v = f x} = f '' S := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [himage]
  exact hS.bddAbove_image hf.continuousOn

theorem aux_lem_as_regularity_affine_transport_c2_norm_bound
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ 2 phi) (Cphi : ℝ)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi) :
    c2Norm (closedCube z' 1 h1 : Set (SpatialCoordinates d))
      (fun x => phi (cubeDilation z z' r x)) ≤ (1 + r + r ^ 2) * Cphi := by
  have hmap : ∀ x ∈ (closedCube z' 1 h1 : Set (SpatialCoordinates d)),
      cubeDilation z z' r x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    intro x hx
    change dist (cubeDilation z z' r x) z ≤ r / 2
    change dist x z' ≤ 1 / 2 at hx
    rw [dist_eq_norm] at hx
    have heq : cubeDilation z z' r x - z = r • (x - z') := by
      ext i
      simp [cubeDilation, Pi.smul_apply]
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hz : z ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
    change dist z z ≤ r / 2
    simp only [dist_self]
    linarith
  have hz' : z' ∈ (closedCube z' 1 h1 : Set (SpatialCoordinates d)) := by
    change dist z' z' ≤ 1 / 2
    simp only [dist_self]
    norm_num
  have hcompact : IsCompact (closedCube z r hr : Set (SpatialCoordinates d)) :=
    (closedCube z r hr).isCompact
  have hbdd0 := aux_lem_as_regularity_affine_transport_sup_bdd
    (closedCube z r hr : Set (SpatialCoordinates d)) hcompact (fun x => |phi x|)
    (continuous_abs.comp hphi.continuous)
  have hfd : ContDiff ℝ 1 (fderiv ℝ phi) :=
    (contDiff_succ_iff_fderiv.mp hphi).2.2
  have hbdd1 := aux_lem_as_regularity_affine_transport_sup_bdd
    (closedCube z r hr : Set (SpatialCoordinates d)) hcompact
    (fun x => ‖fderiv ℝ phi x‖)
    (continuous_norm.comp (hphi.continuous_fderiv (by norm_num)))
  have hbdd2 := aux_lem_as_regularity_affine_transport_sup_bdd
    (closedCube z r hr : Set (SpatialCoordinates d)) hcompact
    (fun x => ‖fderiv ℝ (fderiv ℝ phi) x‖)
    (continuous_norm.comp (hfd.continuous_fderiv (by norm_num)))
  obtain ⟨_, _, hderiv_bound, hsecond_bound⟩ :=
    aux_lem_as_regularity_affine_transport_c2_chain_rule d z z' r hr phi hphi
  have ht0 := aux_lem_as_regularity_affine_transport_sup_comp_le
    (closedCube z' 1 h1 : Set (SpatialCoordinates d))
    (closedCube z r hr : Set (SpatialCoordinates d)) (cubeDilation z z' r)
    (fun x => |phi (cubeDilation z z' r x)|) (fun x => |phi x|) 1
    ⟨z', hz'⟩ (by norm_num) hmap hbdd0 (by intro x hx; simp)
  have ht1 := aux_lem_as_regularity_affine_transport_sup_comp_le
    (closedCube z' 1 h1 : Set (SpatialCoordinates d))
    (closedCube z r hr : Set (SpatialCoordinates d)) (cubeDilation z z' r)
    (fun x => ‖fderiv ℝ (fun y => phi (cubeDilation z z' r y)) x‖)
    (fun x => ‖fderiv ℝ phi x‖) r
    ⟨z', hz'⟩ hr.le hmap hbdd1 (by intro x hx; exact hderiv_bound x)
  have ht2 := aux_lem_as_regularity_affine_transport_sup_comp_le
    (closedCube z' 1 h1 : Set (SpatialCoordinates d))
    (closedCube z r hr : Set (SpatialCoordinates d)) (cubeDilation z z' r)
    (fun x => ‖fderiv ℝ (fderiv ℝ (fun y => phi (cubeDilation z z' r y))) x‖)
    (fun x => ‖fderiv ℝ (fderiv ℝ phi) x‖) (r ^ 2)
    ⟨z', hz'⟩ (sq_nonneg r) hmap hbdd2 (by intro x hx; exact hsecond_bound x)
  change
    sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), v = |phi x|} +
        sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          v = ‖fderiv ℝ phi x‖} +
        sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
          v = ‖fderiv ℝ (fderiv ℝ phi) x‖} ≤ Cphi at hCphi
  change
    sSup {v : ℝ | ∃ x ∈ (closedCube z' 1 h1 : Set (SpatialCoordinates d)),
        v = |phi (cubeDilation z z' r x)|} +
      sSup {v : ℝ | ∃ x ∈ (closedCube z' 1 h1 : Set (SpatialCoordinates d)),
        v = ‖fderiv ℝ (fun y => phi (cubeDilation z z' r y)) x‖} +
      sSup {v : ℝ | ∃ x ∈ (closedCube z' 1 h1 : Set (SpatialCoordinates d)),
        v = ‖fderiv ℝ (fderiv ℝ (fun y => phi (cubeDilation z z' r y))) x‖} ≤
      (1 + r + r ^ 2) * Cphi
  have hs0 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = |phi x|} :=
    (abs_nonneg (phi z)).trans (le_csSup hbdd0 ⟨z, hz, rfl⟩)
  have hs1 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = ‖fderiv ℝ phi x‖} :=
    (norm_nonneg (fderiv ℝ phi z)).trans (le_csSup hbdd1 ⟨z, hz, rfl⟩)
  have hs2 : 0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      v = ‖fderiv ℝ (fderiv ℝ phi) x‖} :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ phi) z)).trans (le_csSup hbdd2 ⟨z, hz, rfl⟩)
  have hfac : 0 ≤ 1 + r + r ^ 2 := by positivity
  have hweighted :
      sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), v = |phi x|} +
          r * sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
            v = ‖fderiv ℝ phi x‖} +
          r ^ 2 * sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
            v = ‖fderiv ℝ (fderiv ℝ phi) x‖} ≤
        (1 + r + r ^ 2) *
          (sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), v = |phi x|} +
            sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              v = ‖fderiv ℝ phi x‖} +
            sSup {v : ℝ | ∃ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
              v = ‖fderiv ℝ (fderiv ℝ phi) x‖}) := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ r + r ^ 2) hs0,
      mul_nonneg (by positivity : 0 ≤ 1 + r ^ 2) hs1,
      mul_nonneg (by positivity : 0 ≤ 1 + r) hs2]
  nlinarith [ht0, ht1, ht2, hweighted, mul_le_mul_of_nonneg_left hCphi hfac]

theorem aux_lem_as_regularity_affine_transport_local_set_preimage
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) (x : SpatialCoordinates d) (rho : ℝ) (hrho : 0 < rho) :
    cubeDilation z z' r ⁻¹'
        (Metric.ball (cubeDilation z z' r x) (r * rho) ∩
          (centeredCube z r hr : Set (SpatialCoordinates d))) =
      Metric.ball x rho ∩ (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) := by
  ext y
  constructor
  · intro hy
    have hball : dist (cubeDilation z z' r y) (cubeDilation z z' r x) < r * rho := hy.1
    have heq : cubeDilation z z' r y - cubeDilation z z' r x = r • (y - x) := by
      ext i
      simp [cubeDilation, Pi.smul_apply]
      ring
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at hball
    refine ⟨?_, (Set.ext_iff.mp (cubeDilation_preimage_centeredCube z z' hr h1) y).mp hy.2⟩
    change dist y x < rho
    rw [dist_eq_norm]
    nlinarith
  · intro hy
    refine ⟨?_, (Set.ext_iff.mp (cubeDilation_preimage_centeredCube z z' hr h1) y).mpr hy.2⟩
    have hball : dist y x < rho := hy.1
    rw [dist_eq_norm] at hball
    have heq : cubeDilation z z' r y - cubeDilation z z' r x = r • (y - x) := by
      ext i
      simp [cubeDilation, Pi.smul_apply]
      ring
    change dist (cubeDilation z z' r y) (cubeDilation z z' r x) < r * rho
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith

theorem aux_lem_as_regularity_affine_transport_local_energy_scaling
    (d : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube z' 1 h1))
    (g : HilbertGradient (centeredCube z r hr))
    (g1 : HilbertGradient (centeredCube z' 1 h1))
    (hcoef : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      b.val x = a.val (cubeDilation z z' r x))
    (hgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
      (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      g1 i x = r * g i (cubeDilation z z' r x))
    (x : SpatialCoordinates d) (rho : ℝ) (hrho : 0 < rho) :
    localGradientEnergy b (s := Metric.ball x rho ∩
        (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z' 1 h1).isOpen.measurableSet)
        g1 = r ^ ((2 : ℝ) - (d : ℝ)) *
      localGradientEnergy a (s := Metric.ball (cubeDilation z z' r x) (r * rho) ∩
        (centeredCube z r hr : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
        g := by
  let S1 := Metric.ball x rho ∩ (centeredCube z' 1 h1 : Set (SpatialCoordinates d))
  let S := Metric.ball (cubeDilation z z' r x) (r * rho) ∩
    (centeredCube z r hr : Set (SpatialCoordinates d))
  have hS1 : MeasurableSet S1 := isOpen_ball.measurableSet.inter
    (centeredCube z' 1 h1).isOpen.measurableSet
  have hS : MeasurableSet S := isOpen_ball.measurableSet.inter
    (centeredCube z r hr).isOpen.measurableSet
  have hpre : cubeDilation z z' r ⁻¹' S = S1 := by
    dsimp [S, S1]
    exact aux_lem_as_regularity_affine_transport_local_set_preimage
      d z z' r hr h1 x rho hrho
  have hfac : r ^ ((2 : ℝ) - (d : ℝ)) = r ^ 2 * (r ^ d)⁻¹ := by
    rw [Real.rpow_sub hr, div_eq_mul_inv]
    norm_num [Real.rpow_natCast]
  rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral]
  rw [hfac, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let f : SpatialCoordinates d → ℝ := fun y => a.val y * (g i y) ^ 2
  have hgi : AEMeasurable (g i) (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    (Lp.aestronglyMeasurable (g i)).aemeasurable
  have hfi : AEMeasurable f
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    simpa [f, pow_two] using!
      (Lp.aestronglyMeasurable a.val).aemeasurable.mul (hgi.mul hgi)
  have hfS : AEMeasurable (S.indicator f)
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    hfi.indicator hS
  have hscale := aux_lem_as_regularity_affine_transport_integral_scaling
    d z z' r hr h1 (S.indicator f) hfS
  have hi :
      (∫ y in S1, b.val y * (g1 i y) ^ 2 ∂volume.restrict
        (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) =
        r ^ 2 * (r ^ d)⁻¹ *
          (∫ y in S, a.val y * (g i y) ^ 2 ∂volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    calc
      (∫ y in S1, b.val y * (g1 i y) ^ 2 ∂volume.restrict
          (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) =
          ∫ y, S1.indicator (fun q => b.val q * (g1 i q) ^ 2) y ∂volume.restrict
            (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) :=
        (integral_indicator hS1).symm
      _ = r ^ 2 * (∫ y, (S.indicator f) (cubeDilation z z' r y) ∂volume.restrict
          (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hcoef, hgrad i] with y hyc hyg
        by_cases hy : y ∈ S1
        · have hyS : cubeDilation z z' r y ∈ S :=
            (Set.ext_iff.mp hpre y).mpr hy
          simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hyS]
          rw [hyc, hyg]
          dsimp [f]
          ring
        · have hyS : cubeDilation z z' r y ∉ S := by
            intro h
            exact hy ((Set.ext_iff.mp hpre y).mp h)
          simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hyS]
      _ = r ^ 2 * (r ^ d)⁻¹ *
          (∫ y in S, a.val y * (g i y) ^ 2 ∂volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))) := by
        rw [hscale]
        rw [integral_indicator hS]
        ring
  simpa [S1, S] using! hi

theorem aux_lem_as_regularity_affine_transport_sobolevData_eq_of_ae
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    {u v : SobolevData Ω}
    (hval : (u.1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] (v.1 : SpatialCoordinates d → ℝ))
    (hgrad : ∀ i : Fin d, (u.2 i : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] (v.2 i : SpatialCoordinates d → ℝ)) :
    u = v := by
  apply Prod.ext
  · apply Lp.ext
    exact hval
  · funext i
    apply Lp.ext
    exact hgrad i

theorem aux_lem_as_regularity_affine_transport_pow_inv_mul
    (d : ℕ) (r x : ℝ) (hr : 0 < r) :
    x = r ^ d * ((r ^ d)⁻¹ * x) := by
  field_simp [pow_ne_zero d hr.ne']

theorem aux_lem_as_regularity_affine_transport_pow_split
    (d : ℕ) (r : ℝ) (hr : 0 < r) :
    (r ^ d : ℝ) = r ^ ((d : ℝ) - 2) * r ^ 2 := by
  calc
    (r ^ d : ℝ) = r ^ (d : ℝ) := (Real.rpow_natCast r d).symm
    _ = r ^ ((d : ℝ) - 2 + 2) := by congr 1 <;> ring
    _ = r ^ ((d : ℝ) - 2) * r ^ 2 := by
      rw [Real.rpow_add hr]
      norm_num [Real.rpow_natCast]

theorem aux_lem_as_regularity_affine_transport_pow_split_mul
    (d : ℕ) (r x : ℝ) (hr : 0 < r) :
    r ^ d * x = r ^ ((d : ℝ) - 2) * (r ^ 2 * x) := by
  rw [aux_lem_as_regularity_affine_transport_pow_split d r hr]
  ring

theorem aux_lem_as_regularity_affine_transport_integral_const_congr
    (d : ℕ) (S : Set (SpatialCoordinates d)) (c : ℝ)
    (f g : SpatialCoordinates d → ℝ)
    (h : ∀ᵐ x ∂volume.restrict S, c * f x = g x) :
    c * (∫ x in S, f x) = ∫ x in S, g x := by
  rw [← integral_const_mul]
  exact integral_congr_ae h

theorem aux_lem_as_regularity_affine_transport_integral_const_congr_of_eq
    {d : ℕ} {S : Set (SpatialCoordinates d)} {c : ℝ}
    {f g : SpatialCoordinates d → ℝ} {I : ℝ}
    (hI : I = ∫ x in S, f x)
    (h : ∀ᵐ x ∂volume.restrict S, c * f x = g x) :
    c * I = ∫ x in S, g x := by
  calc
    c * I = c * (∫ x in S, f x) := congrArg (fun q : ℝ => c * q) hI
    _ = ∫ x in S, g x :=
      aux_lem_as_regularity_affine_transport_integral_const_congr d S c f g h

theorem aux_lem_as_regularity_affine_transport_scalar_mul_congr
    (c f x y : ℝ) (h : x = y) : c * (f * x) = (c * f) * y := by
  rw [h]
  ring

theorem aux_lem_as_regularity_affine_transport_neumann_solve
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (z0 : SpatialCoordinates d)
    (a1 : PositiveCoefficient (centeredCube z0 1 one_pos))
    (ha1 : ∀ᵐ x ∂volume.restrict
      (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      (a1.val : SpatialCoordinates d → ℝ) x =
        (cutoffPositiveCoefficient M H omega N z hr).val
          (cubeDilation z z0 r x))
    (F : SpatialCoordinates d → ℝ)
    (hF : AEMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (v : meanZeroSobolevGraph (centeredCube z r hr))
    (hsolve : SolvesNeumann
      (cutoffPositiveCoefficient M H omega N z hr) F v)
    (v1 : meanZeroSobolevGraph (centeredCube z0 1 one_pos))
    (hvval : ∀ᵐ x ∂volume.restrict
      (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      (v1 : SobolevData (centeredCube z0 1 one_pos)).1 x =
        (v : SobolevData (centeredCube z r hr)).1
          (cubeDilation z z0 r x))
    (hvgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
      (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      ((v1 : SobolevData (centeredCube z0 1 one_pos)).2 i :
        SpatialCoordinates d → ℝ) x =
        r * ((v : SobolevData (centeredCube z r hr)).2 i :
          SpatialCoordinates d → ℝ) (cubeDilation z z0 r x)) :
    SolvesNeumann a1 (fun x => r ^ 2 * F (cubeDilation z z0 r x)) v1 := by
  let F1 : SpatialCoordinates d → ℝ :=
    fun x => r ^ 2 * F (cubeDilation z z0 r x)
  let vw : weakSobolevGraph (centeredCube z r hr) :=
    ⟨(v : SobolevData (centeredCube z r hr)),
      ((mem_meanZeroSobolevGraph_iff
        (v : SobolevData (centeredCube z r hr))).1 v.property).1⟩
  let v1w : weakSobolevGraph (centeredCube z0 1 one_pos) :=
    ⟨(v1 : SobolevData (centeredCube z0 1 one_pos)),
      ((mem_meanZeroSobolevGraph_iff
        (v1 : SobolevData (centeredCube z0 1 one_pos))).1 v1.property).1⟩
  have hsolve1 : SolvesNeumann a1 F1 v1 := by
    change ∀ psi1 : weakSobolevGraph (centeredCube z0 1 one_pos), _
    intro psi1
    let psi1f : SpatialCoordinates d → ℝ := psi1.val.1
    obtain ⟨psi, hpsival⟩ :=
      aux_lem_as_regularity_affine_transport_weak_pushforward
        d z z0 r hr one_pos psi1
    have hform := aux_lem_as_regularity_affine_transport_form_scaling
      d z z0 r hr one_pos
      (cutoffPositiveCoefficient M H omega N z hr) a1 vw psi v1w psi1
      ha1 hvval hpsival
    let fp : SpatialCoordinates d → ℝ := fun y =>
      F y * (psi : SobolevData (centeredCube z r hr)).1 y
    have hsolvePsi :
        sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr)
            (v : SobolevData (centeredCube z r hr))
            (psi : SobolevData (centeredCube z r hr)) =
          ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y := by
      simpa [fp, vw] using! hsolve psi
    have hfp : AEMeasurable fp
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
      exact hF.mul (Lp.aestronglyMeasurable
        (psi : SobolevData (centeredCube z r hr)).1).aemeasurable
    have hscale := aux_lem_as_regularity_affine_transport_integral_scaling
      d z z0 r hr one_pos fp hfp
    let I : ℝ :=
      ∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        F (cubeDilation z z0 r y) * psi1f y
    have hbase :
        I = ∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
          fp (cubeDilation z z0 r y) := by
      dsimp [I, psi1f]
      apply integral_congr_ae
      refine hpsival.mono ?_
      intro y hy
      dsimp [fp]
      rw [hy]
    have hsource :
        (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y) =
          r ^ d * I := by
      calc
        (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y) =
            r ^ d * ((r ^ d)⁻¹ *
              (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y)) :=
          aux_lem_as_regularity_affine_transport_pow_inv_mul d r _ hr
        _ = r ^ d *
            (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
              fp (cubeDilation z z0 r y)) := by rw [hscale]
        _ = r ^ d * I := congrArg (fun q : ℝ => r ^ d * q) hbase.symm
    have hR : r ^ ((d : ℝ) - 2) ≠ 0 :=
      (Real.rpow_pos_of_pos hr _).ne'
    have hform' :
        sobolevCoefficientForm a1 v1.val psi1.val = r ^ 2 * I := by
      apply mul_left_cancel₀ hR
      calc
        r ^ ((d : ℝ) - 2) * sobolevCoefficientForm a1 v1.val psi1.val =
            sobolevCoefficientForm
              (cutoffPositiveCoefficient M H omega N z hr)
              (v : SobolevData (centeredCube z r hr))
              (psi : SobolevData (centeredCube z r hr)) := hform.symm
        _ = r ^ ((d : ℝ) - 2) * (r ^ 2 * I) := by
          calc
            sobolevCoefficientForm
                (cutoffPositiveCoefficient M H omega N z hr)
                (v : SobolevData (centeredCube z r hr))
                (psi : SobolevData (centeredCube z r hr)) =
                ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y :=
              hsolvePsi
            _ = r ^ d * I := hsource
            _ = r ^ ((d : ℝ) - 2) * (r ^ 2 * I) :=
              aux_lem_as_regularity_affine_transport_pow_split_mul d r _ hr
    have hfinal : r ^ 2 * I =
        ∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
          F1 y * (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y := by
      calc
        r ^ 2 * I = r ^ 2 *
            (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
              fp (cubeDilation z z0 r y)) := congrArg (fun q : ℝ => r ^ 2 * q) hbase
        _ = ∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
            r ^ 2 * fp (cubeDilation z z0 r y) := by rw [← integral_const_mul]
        _ = ∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
            F1 y * (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y := by
          apply integral_congr_ae
          refine hpsival.mono ?_
          intro y hy
          change r ^ 2 * fp (cubeDilation z z0 r y) = F1 y *
            (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y
          calc
            r ^ 2 * fp (cubeDilation z z0 r y) =
                (r ^ 2 * F (cubeDilation z z0 r y)) *
                  (psi : SobolevData (centeredCube z r hr)).1
                    (cubeDilation z z0 r y) := by
              dsimp [fp]
              ring
            _ = (r ^ 2 * F (cubeDilation z z0 r y)) *
                (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y := by
              rw [← hy]
            _ = F1 y *
                (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y := by rfl
    simpa only [F1] using! hform'.trans hfinal
  simpa only [F1] using! hsolve1



theorem lem_as_regularity_affine_transport
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d)
    (N : ℕ)
    (z : SpatialCoordinates d)
    (r : ℝ)
    (hr : 0 < r) :
  let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  let T : SpatialCoordinates d → SpatialCoordinates d := cubeDilation z z0 r
  let Q := centeredCube z r hr
  let Q1 := unitNeumannCube d
  let a := cutoffPositiveCoefficient M H omega N z hr
  ∃ a1 : PositiveCoefficient Q1,
    (∀ᵐ x ∂(volume.restrict (Q1 : Set (SpatialCoordinates d))),
      (a1.val : SpatialCoordinates d → ℝ) x =
        (a.val : SpatialCoordinates d → ℝ) (T x)) ∧
    (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf →
      AEMeasurable F (volume.restrict (Q : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        |F x| ≤ Kf) →
      ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
        ContDiff ℝ 2 phi →
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph Q),
          ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (Q : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet a F b u →
          ∃ (F1 phi1 : SpatialCoordinates d → ℝ)
            (b1 u1 : weakSobolevGraph Q1),
            F1 = (fun x => r ^ 2 * F (T x)) ∧
            AEMeasurable F1 (volume.restrict (Q1 : Set (SpatialCoordinates d))) ∧
            (∀ᵐ x ∂(volume.restrict (Q1 : Set (SpatialCoordinates d))),
              |F1 x| ≤ r ^ 2 * Kf) ∧
            phi1 = (fun x => phi (T x)) ∧
            ContDiff ℝ 2 phi1 ∧
            (∃ Cphi1 : ℝ, c2Norm
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) phi1 ≤ Cphi1 ∧
              Cphi1 ≤ (1 + r + r ^ 2) * Cphi) ∧
            ((b1 : SobolevData Q1).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (Q1 : Set (SpatialCoordinates d))] phi1 ∧
            SolvesDirichlet a1 F1 b1 u1 ∧
            ((b1 : SobolevData Q1).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (Q1 : Set (SpatialCoordinates d))]
              (fun x => (b : SobolevData Q).1 (T x)) ∧
            ((u1 : SobolevData Q1).1 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (Q1 : Set (SpatialCoordinates d))]
              (fun x => (u : SobolevData Q).1 (T x)) ∧
            (∀ i : Fin d,
              ((u1 : SobolevData Q1).2 i : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict (Q1 : Set (SpatialCoordinates d))]
                (fun x => r * (u : SobolevData Q).2 i (T x))) ∧
            (∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho →
              localGradientEnergy a1
                  (s := Metric.ball x rho ∩ (Q1 : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter Q1.isOpen.measurableSet)
                  (sobolevGradient (u1 : SobolevData Q1)) =
                r ^ ((2 : ℝ) - (d : ℝ)) *
                  localGradientEnergy a
                    (s := Metric.ball (T x) (r * rho) ∩ (Q : Set (SpatialCoordinates d)))
                    (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                    (sobolevGradient (u : SobolevData Q))) ) ∧
    (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf →
      AEMeasurable F (volume.restrict (Q : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
        |F x| ≤ Kf) →
      (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph Q,
        SolvesNeumann a F v →
        ∃ (F1 : SpatialCoordinates d → ℝ) (v1 : meanZeroSobolevGraph Q1),
          F1 = (fun x => r ^ 2 * F (T x)) ∧
          AEMeasurable F1 (volume.restrict (Q1 : Set (SpatialCoordinates d))) ∧
          (∀ᵐ x ∂(volume.restrict (Q1 : Set (SpatialCoordinates d))),
            |F1 x| ≤ r ^ 2 * Kf) ∧
          (∫ x in (Q1 : Set (SpatialCoordinates d)), F1 x) = 0 ∧
          SolvesNeumann a1 F1 v1 ∧
          ((v1 : SobolevData Q1).1 : SpatialCoordinates d → ℝ) =ᵐ[
            volume.restrict (Q1 : Set (SpatialCoordinates d))]
            (fun x => (v : SobolevData Q).1 (T x)) ∧
          (∀ i : Fin d,
            ((v1 : SobolevData Q1).2 i : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (Q1 : Set (SpatialCoordinates d))]
              (fun x => r * (v : SobolevData Q).2 i (T x))) ∧
          (∀ (x : SpatialCoordinates d) (rho : ℝ), 0 < rho →
            localGradientEnergy a1
                (s := Metric.ball x rho ∩ (Q1 : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter Q1.isOpen.measurableSet)
                (sobolevGradient (v1 : SobolevData Q1)) =
              r ^ ((2 : ℝ) - (d : ℝ)) *
                localGradientEnergy a
                  (s := Metric.ball (T x) (r * rho) ∩ (Q : Set (SpatialCoordinates d)))
                  (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
                  (sobolevGradient (v : SobolevData Q)))) := by
  dsimp
  obtain ⟨a1, ha1⟩ := lane4_dilation_coefficient_transport d z
    (fun _ => (1 / 2 : ℝ)) r hr one_pos
    (cutoffPositiveCoefficient M H omega N z hr)
  refine ⟨a1, ?_, ?_, ?_⟩
  · simpa [unitNeumannCube] using! ha1
  · intro F Kf hKf hF hFbound phi Cphi hphi hCphi b u htrace hsolve
    let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
    obtain ⟨b1, hbval, hbgrad⟩ :=
      aux_lem_as_regularity_affine_transport_weak_pullback d z z0 r hr one_pos b
    obtain ⟨u1, huval, hugrad⟩ :=
      aux_lem_as_regularity_affine_transport_weak_pullback d z z0 r hr one_pos u
    let F1 : SpatialCoordinates d → ℝ := fun x => r ^ 2 * F (cubeDilation z z0 r x)
    let phi1 : SpatialCoordinates d → ℝ := fun x => phi (cubeDilation z z0 r x)
    have hq := lane4_dilation_quasi_measure_preserving d z z0 r hr one_pos
    have hF1 : AEMeasurable F1
        (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))) := by
      have hcomp := hF.comp_quasiMeasurePreserving hq
      simpa [F1, Function.comp_def] using! hcomp.const_mul (r ^ 2)
    have hFbound1 : ∀ᵐ x ∂volume.restrict
        (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        |F1 x| ≤ r ^ 2 * Kf := by
      filter_upwards [hq.ae hFbound] with x hx
      simp only [F1, abs_mul, abs_of_nonneg (sq_nonneg r)]
      exact mul_le_mul_of_nonneg_left hx (sq_nonneg r)
    have hphi1 := aux_lem_as_regularity_affine_transport_c2_chain_rule
      d z z0 r hr phi hphi
    have hCphi1 := aux_lem_as_regularity_affine_transport_c2_norm_bound
      d z z0 r hr one_pos phi hphi Cphi hCphi
    have htrace1 :
        ((b1 : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ) =ᵐ[
          volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))] phi1 := by
      filter_upwards [hbval, hq.ae htrace] with x hbx htx
      rw [hbx, htx]
    let k : killedSobolevGraph (centeredCube z r hr) :=
      ⟨(u : SobolevData (centeredCube z r hr)) - (b : SobolevData (centeredCube z r hr)),
        hsolve.1⟩
    obtain ⟨k1, hkval, hkgrad⟩ :=
      aux_lem_as_regularity_affine_transport_killed_pullback d z z0 r hr one_pos k
    have hdiff :
        ((u1 : SobolevData (centeredCube z0 1 one_pos)) -
          (b1 : SobolevData (centeredCube z0 1 one_pos))) = (k1 : SobolevData (centeredCube z0 1 one_pos)) := by
      apply aux_lem_as_regularity_affine_transport_sobolevData_eq_of_ae
      · filter_upwards [Lp.coeFn_sub
            ((u1 : SobolevData (centeredCube z0 1 one_pos)).1)
            ((b1 : SobolevData (centeredCube z0 1 one_pos)).1),
          huval, hbval, hkval,
          hq.ae (Lp.coeFn_sub (u : SobolevData (centeredCube z r hr)).1
            (b : SobolevData (centeredCube z r hr)).1)] with x hux huT hbT hkx hsub
        have hux' : ((u1 : SobolevData (centeredCube z0 1 one_pos)) -
            (b1 : SobolevData (centeredCube z0 1 one_pos))).1 x =
            ((u1 : SobolevData (centeredCube z0 1 one_pos)).1 -
              (b1 : SobolevData (centeredCube z0 1 one_pos)).1) x := by
          simpa only [Prod.fst_sub] using! hux
        rw [hux', hux]
        simp only [Pi.sub_apply]
        rw [huT, hbT, hkx]
        simpa [k] using! hsub.symm
      · intro i
        filter_upwards [Lp.coeFn_sub
            ((u1 : SobolevData (centeredCube z0 1 one_pos)).2 i)
            ((b1 : SobolevData (centeredCube z0 1 one_pos)).2 i),
          hugrad i, hbgrad i, hkgrad i,
          hq.ae (Lp.coeFn_sub ((u : SobolevData (centeredCube z r hr)).2 i)
            ((b : SobolevData (centeredCube z r hr)).2 i))] with x hux huT hbT hkx hsub
        have hux' : ((u1 : SobolevData (centeredCube z0 1 one_pos)) -
            (b1 : SobolevData (centeredCube z0 1 one_pos))).2 i x =
            ((u1 : SobolevData (centeredCube z0 1 one_pos)).2 i -
              (b1 : SobolevData (centeredCube z0 1 one_pos)).2 i) x := by
          simpa only [Prod.snd_sub, Pi.sub_apply] using! hux
        rw [hux', hux]
        simp only [Pi.sub_apply]
        rw [huT, hbT, hkx]
        calc
          r * ((u : SobolevData (centeredCube z r hr)).2 i) (cubeDilation z z0 r x) -
              r * ((b : SobolevData (centeredCube z r hr)).2 i) (cubeDilation z z0 r x) =
              r * (((u : SobolevData (centeredCube z r hr)).2 i) (cubeDilation z z0 r x) -
                ((b : SobolevData (centeredCube z r hr)).2 i) (cubeDilation z z0 r x)) := by ring
          _ = r * ((k : SobolevData (centeredCube z r hr)).2 i) (cubeDilation z z0 r x) := by
            exact congrArg (fun q : ℝ => r * q) (by simpa [k] using! hsub.symm)
    have hkill :
        (u1 : SobolevData (centeredCube z0 1 one_pos)) -
            (b1 : SobolevData (centeredCube z0 1 one_pos)) ∈
          killedSobolevGraph (centeredCube z0 1 one_pos) := by
      rw [hdiff]
      exact k1.property
    have hsolve1 : SolvesDirichlet a1 F1 b1 u1 := by
      refine ⟨hkill, ?_⟩
      intro psi1
      obtain ⟨psi, hpsival⟩ :=
        aux_lem_as_regularity_affine_transport_killed_pushforward
          d z z0 r hr one_pos psi1
      let psiW : weakSobolevGraph (centeredCube z r hr) :=
        ⟨psi.val, killedSobolevGraph_le_weakSobolevGraph psi.property⟩
      let psi1W : weakSobolevGraph (centeredCube z0 1 one_pos) :=
        ⟨psi1.val, killedSobolevGraph_le_weakSobolevGraph psi1.property⟩
      have hform := aux_lem_as_regularity_affine_transport_form_scaling
        d z z0 r hr one_pos
        (cutoffPositiveCoefficient M H omega N z hr) a1 u psiW u1 psi1W ha1 huval hpsival
      let fp : SpatialCoordinates d → ℝ := fun y =>
        F y * (psi : SobolevData (centeredCube z r hr)).1 y
      have hsolvePsi :
          sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr)
              (u : SobolevData (centeredCube z r hr))
              (psiW : SobolevData (centeredCube z r hr)) =
            ∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y := by
        simpa [psiW, fp] using! hsolve.2 psi
      have hfp : AEMeasurable fp
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
        exact hF.mul (Lp.aestronglyMeasurable
          (psi : SobolevData (centeredCube z r hr)).1).aemeasurable
      have hscale := aux_lem_as_regularity_affine_transport_integral_scaling
        d z z0 r hr one_pos fp hfp
      let psi1val : SpatialCoordinates d → ℝ := fun y =>
        (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y
      have hbase :
          (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
            F (cubeDilation z z0 r y) *
              (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y) =
            ∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
              fp (cubeDilation z z0 r y) := by
        apply integral_congr_ae
        refine hpsival.mono ?_
        intro y hy
        dsimp [fp]
        rw [hy]
      have hsource :
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y) =
            r ^ d *
              (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
                F (cubeDilation z z0 r y) * psi1.val.1 y) := by
        calc
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y) =
              r ^ d * ((r ^ d)⁻¹ *
                (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), fp y)) := by
            exact aux_lem_as_regularity_affine_transport_pow_inv_mul d r _ hr
          _ = r ^ d *
              (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
                fp (cubeDilation z z0 r y)) := by rw [hscale]
          _ = r ^ d *
              (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
                F (cubeDilation z z0 r y) * psi1.val.1 y) := by
            exact congrArg (fun q : ℝ => r ^ d * q) hbase.symm
      have hpow := aux_lem_as_regularity_affine_transport_pow_split d r hr
      have hR : r ^ ((d : ℝ) - 2) ≠ 0 :=
        (Real.rpow_pos_of_pos hr _).ne'
      have hform' :
          sobolevCoefficientForm a1 (u1 : SobolevData (centeredCube z0 1 one_pos))
              (psi1 : SobolevData (centeredCube z0 1 one_pos)) =
            r ^ 2 *
              (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
                F (cubeDilation z z0 r y) * psi1.val.1 y) := by
        apply mul_left_cancel₀ hR
        calc
          r ^ ((d : ℝ) - 2) *
              sobolevCoefficientForm a1
                (u1 : SobolevData (centeredCube z0 1 one_pos))
                (psi1 : SobolevData (centeredCube z0 1 one_pos)) =
              sobolevCoefficientForm
                (cutoffPositiveCoefficient M H omega N z hr)
                (u : SobolevData (centeredCube z r hr))
                (psi : SobolevData (centeredCube z r hr)) := hform.symm
          _ = r ^ ((d : ℝ) - 2) * (r ^ 2 *
              (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
                F (cubeDilation z z0 r y) *
                  (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y)) := by
            rw [hsolvePsi, hsource, hpow] <;> ring
      calc
        sobolevCoefficientForm a1 (u1 : SobolevData (centeredCube z0 1 one_pos))
            (psi1 : SobolevData (centeredCube z0 1 one_pos)) =
            r ^ 2 *
              (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
                F (cubeDilation z z0 r y) *
                  (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y) := hform'
        _ = ∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
            F1 y * (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y := by
          change r ^ 2 * (∫ y in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
            F (cubeDilation z z0 r y) *
              (psi1 : SobolevData (centeredCube z0 1 one_pos)).1 y) = _
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with y
          dsimp [F1]
          ring
    refine ⟨F1, phi1, b1, u1, rfl, hF1, hFbound1, rfl, hphi1.1,
      ⟨(1 + r + r ^ 2) * Cphi, hCphi1, le_rfl⟩, htrace1, hsolve1,
      hbval, huval, hugrad, ?_⟩
    intro x rho hrho
    exact aux_lem_as_regularity_affine_transport_local_energy_scaling
      d z z0 r hr one_pos (cutoffPositiveCoefficient M H omega N z hr) a1
      (sobolevGradient (u : SobolevData (centeredCube z r hr)))
      (sobolevGradient (u1 : SobolevData (centeredCube z0 1 one_pos))) ha1 hugrad x rho hrho
  · intro F Kf hKf hF hFbound hFint v hsolve
    let z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
    have hvpull := aux_lem_as_regularity_affine_transport_meanzero_pullback
      d z z0 r hr one_pos v
    obtain ⟨v1, hvval, hvgrad⟩ := hvpull
    let F1 : SpatialCoordinates d → ℝ := fun x => r ^ 2 * F (cubeDilation z z0 r x)
    have hq := lane4_dilation_quasi_measure_preserving d z z0 r hr one_pos
    have hF1 : AEMeasurable F1
        (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))) := by
      have hcomp := hF.comp_quasiMeasurePreserving hq
      simpa [F1, Function.comp_def] using! hcomp.const_mul (r ^ 2)
    have hFbound1 : ∀ᵐ x ∂volume.restrict
        (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        |F1 x| ≤ r ^ 2 * Kf := by
      filter_upwards [hq.ae hFbound] with x hx
      simp only [F1, abs_mul, abs_of_nonneg (sq_nonneg r)]
      exact mul_le_mul_of_nonneg_left hx (sq_nonneg r)
    have hFzero :
        (∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), F1 x) = 0 := by
      have hs := aux_lem_as_regularity_affine_transport_integral_scaling
        d z z0 r hr one_pos F hF
      change ∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        r ^ 2 * F (cubeDilation z z0 r x) = 0
      rw [integral_const_mul, hs, hFint]
      simp
    have hsolve1 : SolvesNeumann a1 F1 v1 := by
      simpa only [F1] using!
        aux_lem_as_regularity_affine_transport_neumann_solve
          d M H omega N z r hr z0 a1 ha1 F hF v hsolve v1 hvval hvgrad
    refine ⟨F1, v1, rfl, hF1, hFbound1, hFzero, hsolve1,
      hvval, hvgrad, ?_⟩
    intro x rho hrho
    have hlocal :
        localGradientEnergy a1
            (s := Metric.ball x rho ∩
              (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter
              (centeredCube z0 1 one_pos).isOpen.measurableSet)
            (sobolevGradient (v1 : SobolevData (centeredCube z0 1 one_pos))) =
          r ^ ((2 : ℝ) - (d : ℝ)) *
            localGradientEnergy (cutoffPositiveCoefficient M H omega N z hr)
              (s := Metric.ball (cubeDilation z z0 r x) (r * rho) ∩
                (centeredCube z r hr : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter
                (centeredCube z r hr).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (centeredCube z r hr))) :=
      aux_lem_as_regularity_affine_transport_local_energy_scaling
        d z z0 r hr one_pos (cutoffPositiveCoefficient M H omega N z hr) a1
        (sobolevGradient (v : SobolevData (centeredCube z r hr)))
        (sobolevGradient (v1 : SobolevData (centeredCube z0 1 one_pos)))
        ha1 hvgrad x rho hrho
    exact hlocal

end Paper
