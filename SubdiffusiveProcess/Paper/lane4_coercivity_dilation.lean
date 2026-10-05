module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.lane4_dilation_coefficient_transport
public import SubdiffusiveProcess.Paper.lane4_gagliardo_dilation_scaling
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import Homogenization.Sobolev.H1.Translation
public import SubdiffusiveProcess.Paper.lane4_dilation_quasi_measure_preserving
public import SubdiffusiveProcess.Paper.lane4_energy_dilation_scaling
public import SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_cube_geometry
public import SubdiffusiveProcess.Paper.aux_lane4_coercivity_dilation_sqnorm_bound

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lane4_coercivity_dilation_cube_translate (d : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) := by
  ext x
  rw [Homogenization.mem_translateSet_iff_sub_mem]
  rw [centeredCube_eq_pi, centeredCube_eq_pi]
  constructor
  · intro hx i _
    have hi := hx i (Set.mem_univ i)
    simp only [Set.mem_Ioo, Pi.sub_apply, Pi.zero_apply] at hi ⊢
    constructor <;> linarith [hi.1, hi.2]
  · intro hx i _
    have hi := hx i (Set.mem_univ i)
    simp only [Set.mem_Ioo, Pi.sub_apply, Pi.zero_apply] at hi ⊢
    constructor <;> linarith [hi.1, hi.2]

theorem aux_lane4_coercivity_dilation_cube_scale (d : ℕ)
    (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1) :
    (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
      r • (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)) := by
  ext x
  rw [centeredCube_eq_pi] at ⊢
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  constructor
  · intro hx
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne' (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)) x]
    rw [centeredCube_eq_pi]
    intro i _
    have hi := hx i (Set.mem_univ i)
    simp only [Set.mem_Ioo, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
    have hlow := mul_lt_mul_of_pos_left hi.1 hrinv
    have hupp := mul_lt_mul_of_pos_left hi.2 hrinv
    constructor
    · calc
        0 - 1 / 2 = r⁻¹ * (0 - r / 2) := by field_simp ; ring
        _ < r⁻¹ * x i := hlow
    · calc
        r⁻¹ * x i < r⁻¹ * (0 + r / 2) := hupp
        _ = 0 + 1 / 2 := by field_simp ; ring
  · intro hx i
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne' (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)) x] at hx
    rw [centeredCube_eq_pi] at hx
    intro _
    have hi := hx i (Set.mem_univ i)
    simp only [Set.mem_Ioo, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
    have hlow := mul_lt_mul_of_pos_left hi.1 hr
    have hupp := mul_lt_mul_of_pos_left hi.2 hr
    constructor
    · calc
        0 - r / 2 = r * (0 - 1 / 2) := by ring
        _ < r * (r⁻¹ * x i) := hlow
        _ = x i := by field_simp
    · calc
        x i = r * (r⁻¹ * x i) := by field_simp
        _ < r * (0 + 1 / 2) := hupp
        _ = 0 + r / 2 := by ring

theorem aux_lane4_coercivity_dilation_h1_cast_toFun
    {d : ℕ} {U V : Set (SpatialCoordinates d)} (h : U = V)
    (u : Homogenization.H1Function U) :
    (h ▸ u).toFun = u.toFun := by
  cases h
  rfl

theorem aux_lane4_coercivity_dilation_h1_cast_grad
    {d : ℕ} {U V : Set (SpatialCoordinates d)} (h : U = V)
    (u : Homogenization.H1Function U) :
    (h ▸ u).grad = u.grad := by
  cases h
  rfl

theorem aux_lane4_coercivity_dilation_h10_cast_toFun
    {d : ℕ} {U V : Set (SpatialCoordinates d)} (h : U = V)
    (u : Homogenization.H10Function U) :
    (h ▸ u).toH1Function.toFun = u.toH1Function.toFun := by
  cases h
  rfl

theorem aux_lane4_coercivity_dilation_h10_cast_grad
    {d : ℕ} {U V : Set (SpatialCoordinates d)} (h : U = V)
    (u : Homogenization.H10Function U) :
    (h ▸ u).toH1Function.grad = u.toH1Function.grad := by
  cases h
  rfl

theorem aux_lane4_coercivity_dilation_weak_pullback
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
  obtain ⟨u, hu⟩ := SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph v
  let U0 : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))
  let U1 : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))
  have htrans : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z U0 := by
    simpa [U0] using aux_lane4_coercivity_dilation_cube_translate d z r hr
  have hscale : U0 = r • U1 := by
    simpa [U0, U1] using aux_lane4_coercivity_dilation_cube_scale d r hr h1
  let uT : Homogenization.H1Function (Homogenization.translateSet z U0) := htrans ▸ u
  let u0 : Homogenization.H1Function U0 := Homogenization.H1Function.untranslate z uT
  let u0T : Homogenization.H1Function (r • U1) := hscale ▸ u0
  let up : Homogenization.H1Function U1 := Homogenization.H1Function.unscale hr u0T
  obtain ⟨w, hw, hwgrad⟩ := _root_.SubdiffusiveProcess.EllipticRegularity.exists_weakSobolevGraph_of_nativeH1
    (Om := centeredCube (0 : SpatialCoordinates d) 1 h1) up
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw] with x hx
    rw [hx]
    change up.toFun x = (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x)
    simp [up, u0T, u0, uT, aux_lane4_coercivity_dilation_h1_cast_toFun,
      Homogenization.H1Function.unscale_toFun,
      Homogenization.H1Function.untranslate_toFun]
    have hmap : z + r • x = cubeDilation z 0 r x := by
      funext i
      simp [cubeDilation, smul_eq_mul]
    have hmap' : r • x + z = cubeDilation z 0 r x := by
      rw [add_comm]
      exact hmap
    rw [hmap']
    exact congrFun hu.1 (cubeDilation z 0 r x)
  · intro i
    filter_upwards [hwgrad i] with x hx
    rw [hx]
    change up.grad x i = r *
      ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
        (cubeDilation z 0 r x)
    change (Homogenization.H1Function.unscale hr u0T).grad x i = _
    rw [Homogenization.H1Function.unscale_grad]
    have hu0Tgrad : u0T.grad = u0.grad := by
      simpa [u0T] using aux_lane4_coercivity_dilation_h1_cast_grad hscale u0
    have huTgrad : uT.grad = u.grad := by
      simpa [uT] using aux_lane4_coercivity_dilation_h1_cast_grad htrans u
    rw [hu0Tgrad]
    change (r • u0.grad (r • x)) i = _
    change (r • (Homogenization.H1Function.untranslate z uT).grad (r • x)) i = _
    rw [Homogenization.H1Function.untranslate_grad, huTgrad]
    rw [hu.2]
    have hmap : z + r • x = cubeDilation z 0 r x := by
      funext j
      simp [cubeDilation, smul_eq_mul]
    have hmap' : r • x + z = cubeDilation z 0 r x := by
      rw [add_comm]
      exact hmap
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hmap']

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
  obtain ⟨u, hu⟩ := SubdiffusiveProcess.exists_nativeH10Function_of_killedSobolevGraph v
  let U0 : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))
  let U1 : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))
  have htrans : (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z U0 := by
    simpa [U0] using aux_lane4_coercivity_dilation_cube_translate d z r hr
  have hscale : U0 = r • U1 := by
    simpa [U0, U1] using aux_lane4_coercivity_dilation_cube_scale d r hr h1
  let uT : Homogenization.H10Function (Homogenization.translateSet z U0) := htrans ▸ u
  let u0 : Homogenization.H10Function U0 := Homogenization.H10Function.untranslate z uT
  let u0T : Homogenization.H10Function (r • U1) := hscale ▸ u0
  let up : Homogenization.H10Function U1 := Homogenization.H10Function.unscale hr u0T
  obtain ⟨w, hw, hwgrad⟩ :=
    _root_.SubdiffusiveProcess.EllipticRegularity.exists_killedSobolevGraph_of_nativeH10 up
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw] with x hx
    rw [hx]
    change up.toH1Function.toFun x =
      (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x)
    change (Homogenization.H1Function.unscale hr u0T.toH1Function).toFun x =
      (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x)
    rw [Homogenization.H1Function.unscale_toFun]
    change u0T.toH1Function (r • x) =
      (v : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x)
    have hu0T : u0T.toH1Function.toFun = u0.toH1Function.toFun := by
      simpa [u0T] using aux_lane4_coercivity_dilation_h10_cast_toFun hscale u0
    have hu0 : u0.toH1Function.toFun =
        (Homogenization.H10Function.untranslate z uT).toH1Function.toFun := by
      rfl
    have huT : uT.toH1Function.toFun = u.toH1Function.toFun := by
      simpa [uT] using aux_lane4_coercivity_dilation_h10_cast_toFun htrans u
    rw [hu0T, hu0, Homogenization.H10Function.untranslate_toH1Function,
      Homogenization.H1Function.untranslate_toFun]
    have huT' : uT.toFun = u.toFun := huT
    rw [huT']
    have hmap : z + r • x = cubeDilation z 0 r x := by
      funext i
      simp [cubeDilation, smul_eq_mul]
    have hmap' : r • x + z = cubeDilation z 0 r x := by
      rw [add_comm]
      exact hmap
    rw [hmap']
    exact congrFun hu.1 (cubeDilation z 0 r x)
  · intro i
    filter_upwards [hwgrad i] with x hx
    rw [hx]
    change up.toH1Function.grad x i =
      r * ((v : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
        (cubeDilation z 0 r x)
    change (Homogenization.H1Function.unscale hr u0T.toH1Function).grad x i = _
    rw [Homogenization.H1Function.unscale_grad]
    have hu0Tgrad : u0T.toH1Function.grad = u0.toH1Function.grad := by
      simpa [u0T] using aux_lane4_coercivity_dilation_h10_cast_grad hscale u0
    have huTgrad : uT.toH1Function.grad = u.toH1Function.grad := by
      simpa [uT] using aux_lane4_coercivity_dilation_h10_cast_grad htrans u
    rw [hu0Tgrad]
    change (r • u0.toH1Function.grad (r • x)) i = _
    change (r • (Homogenization.H10Function.untranslate z uT).toH1Function.grad (r • x)) i = _
    rw [Homogenization.H10Function.untranslate_toH1Function,
      Homogenization.H1Function.untranslate_grad, huTgrad]
    rw [hu.2]
    have hmap : z + r • x = cubeDilation z 0 r x := by
      funext j
      simp [cubeDilation, smul_eq_mul]
    have hmap' : r • x + z = cubeDilation z 0 r x := by
      rw [add_comm]
      exact hmap
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hmap']

theorem aux_lane4_coercivity_dilation_meanZero_pullback
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
  obtain ⟨w, hw⟩ := aux_lane4_coercivity_dilation_weak_pullback d z r hr h1
    (⟨v.1, (inf_le_left : meanZeroSobolevGraph (centeredCube z r hr) ≤
      weakSobolevGraph (centeredCube z r hr)) v.2⟩)
  let f : SpatialCoordinates d → ℝ :=
    (v : SobolevData (centeredCube z r hr)).1
  let μ₁ : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d))
  let μr : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  have hf : Integrable f μr := by
    exact (Lp.memLp ((v : SobolevData (centeredCube z r hr)).1)).integrable (by norm_num)
  have hmap : Measure.map (cubeDilation z 0 r) μ₁ =
      ENNReal.ofReal |(r ^ d)⁻¹| • μr := by
    simpa [μ₁, μr] using map_cubeDilation_restrict z 0 hr h1
  have hfm : AEStronglyMeasurable f (Measure.map (cubeDilation z 0 r) μ₁) := by
    rw [hmap]
    exact hf.aestronglyMeasurable.mono_ac Measure.smul_absolutelyContinuous
  have hmapint :
      (∫ y, f y ∂Measure.map (cubeDilation z 0 r) μ₁) =
        ∫ x, f (cubeDilation z 0 r x) ∂μ₁ := by
    exact MeasureTheory.integral_map
      (continuous_cubeDilation z 0 r).aemeasurable hfm
  have hchange :
      (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)), f (cubeDilation z 0 r x)) =
        (ENNReal.ofReal |(r ^ d)⁻¹|).toReal •
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), f y) := by
    change (∫ x, f (cubeDilation z 0 r x) ∂μ₁) = _
    rw [← hmapint, hmap, MeasureTheory.integral_smul_measure]
  have hvzero : (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), f y) = 0 := by
    exact ((mem_meanZeroSobolevGraph_iff (v : SobolevData (centeredCube z r hr))).mp v.2).2
  have hwzero :
      (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x) = 0 := by
    calc
      _ = ∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
        f (cubeDilation z 0 r x) := by
        apply integral_congr_ae
        exact hw.1
      _ = (ENNReal.ofReal |(r ^ d)⁻¹|).toReal •
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), f y) := hchange
      _ = 0 := by rw [hvzero, smul_zero]
  refine ⟨⟨w, ?_⟩, hw.1, ?_⟩
  · exact (mem_meanZeroSobolevGraph_iff (w : SobolevData
      (centeredCube (0 : SpatialCoordinates d) 1 h1))).2 ⟨w.2, hwzero⟩
  · simpa using hw.2

theorem aux_lane4_coercivity_dilation_integral_scaling
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) (F : SpatialCoordinates d → ℝ)
    (hF : AEStronglyMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y) =
      r ^ d *
        (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)), F (cubeDilation z 0 r x)) := by
  let μ₁ : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d))
  let μr : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  have hmap : Measure.map (cubeDilation z 0 r) μ₁ =
      ENNReal.ofReal |(r ^ d)⁻¹| • μr := by
    simpa [μ₁, μr] using map_cubeDilation_restrict z 0 hr h1
  have hFm : AEStronglyMeasurable F (Measure.map (cubeDilation z 0 r) μ₁) := by
    rw [hmap]
    exact hF.mono_ac Measure.smul_absolutelyContinuous
  have hmapint :
      (∫ y, F y ∂Measure.map (cubeDilation z 0 r) μ₁) =
        ∫ x, F (cubeDilation z 0 r x) ∂μ₁ := by
    exact MeasureTheory.integral_map
      (continuous_cubeDilation z 0 r).aemeasurable hFm
  have hc : (ENNReal.ofReal |(r ^ d)⁻¹|).toReal = (r ^ d)⁻¹ := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos]
    positivity
  have hchange :
      (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)), F (cubeDilation z 0 r x)) =
        (r ^ d)⁻¹ *
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y) := by
    change (∫ x, F (cubeDilation z 0 r x) ∂μ₁) = _
    rw [← hmapint, hmap, MeasureTheory.integral_smul_measure, hc, smul_eq_mul]
  have hp : 0 < r ^ d := pow_pos hr d
  calc
    (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y) =
        r ^ d * ((r ^ d)⁻¹ *
          (∫ y in (centeredCube z r hr : Set (SpatialCoordinates d)), F y)) := by
      field_simp
    _ = r ^ d *
        (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)), F (cubeDilation z 0 r x)) := by
      rw [hchange]

theorem aux_lane4_coercivity_dilation_sqNorm_bound
    (d k : ℕ) (hd : 2 ≤ d) (z z' : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1) (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr))
    (g : Fin k → DomainL2 (centeredCube z' 1 h1)) (R : ℝ)
    (hsemi : cubeFractionalVecSeminormSq hd z r hr s f =
      R * cubeFractionalVecSeminormSq hd z' 1 h1 s g)
    (hL2 : (∑ i : Fin k, ‖f i‖ ^ 2) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (∑ i : Fin k, ‖g i‖ ^ 2) /
        volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))
    (hR : 1 ≤ R) :
    cubeFractionalVecSqNorm hd z r hr s f ≤
      R * cubeFractionalVecSqNorm hd z' 1 h1 s g := by
  unfold cubeFractionalVecSqNorm
  rw [hsemi, hL2]
  have hnonneg : 0 ≤
      (∑ i : Fin k, ‖g i‖ ^ 2) /
        volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) := by
    positivity
  have hL2nonneg :
      (∑ i : Fin k, ‖g i‖ ^ 2) /
        volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) ≤
      R * ((∑ i : Fin k, ‖g i‖ ^ 2) /
        volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by
    calc
      _ = 1 * ((∑ i : Fin k, ‖g i‖ ^ 2) /
          volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hR hnonneg
  calc
    R * cubeFractionalVecSeminormSq hd z' 1 h1 s g +
        (∑ i : Fin k, ‖g i‖ ^ 2) /
          volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) ≤
      R * cubeFractionalVecSeminormSq hd z' 1 h1 s g +
        R * ((∑ i : Fin k, ‖g i‖ ^ 2) /
          volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by
      exact add_le_add_right hL2nonneg _
    _ = R * cubeFractionalVecSqNorm hd z' 1 h1 s g := by
      simp only [cubeFractionalVecSqNorm]
      ring

theorem aux_lane4_coercivity_dilation_energy_scaling
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (u : SobolevData (centeredCube z r hr))
    (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (hcoeff : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)), b.val x = a.val (cubeDilation z 0 r x))
    (_hvalue : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)), w.1 x = u.1 (cubeDilation z 0 r x))
    (hgrad : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)), w.2 i x = r * u.2 i (cubeDilation z 0 r x)) :
    sobolevCoefficientForm a u u =
      r ^ ((d : ℝ) - 2) * sobolevCoefficientForm b w w := by
  rw [_root_.SubdiffusiveProcess.EllipticRegularity.sobolevCoefficientForm_eq_sum_integral,
    _root_.SubdiffusiveProcess.EllipticRegularity.sobolevCoefficientForm_eq_sum_integral]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let F : SpatialCoordinates d → ℝ := fun y =>
    a.val y * (u.2 i y * u.2 i y)
  have hF : AEStronglyMeasurable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    exact (Lp.aestronglyMeasurable a.val).mul
      ((Lp.aestronglyMeasurable (u.2 i)).mul (Lp.aestronglyMeasurable (u.2 i)))
  have hscale := aux_lane4_coercivity_dilation_integral_scaling d z r hr h1 F hF
  have hunit :
      (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
        b.val x * (w.2 i x * w.2 i x)) =
        r ^ 2 *
          (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
            F (cubeDilation z 0 r x)) := by
    calc
      _ = ∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
          r ^ 2 * F (cubeDilation z 0 r x) := by
        apply integral_congr_ae
        filter_upwards [hcoeff, hgrad i] with x hax hix
        rw [hax, hix]
        simp [F]
        ring
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  have hrpow : r ^ ((d : ℝ) - 2) * r ^ 2 = r ^ d := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_natCast r d,
      ← Real.rpow_add hr]
    congr 1
    norm_num
  calc
    ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        a.val x * (u.2 i x * u.2 i x) =
      r ^ d * (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)), F (cubeDilation z 0 r x)) := hscale
    _ = r ^ ((d : ℝ) - 2) *
        (∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)), b.val x * (w.2 i x * w.2 i x)) := by
      rw [hunit, ← hrpow]
      ring



theorem lane4_coercivity_dilation :
  ∀ (d : ℕ) (hd : 2 ≤ d) (E : in_J d) (s : ℝ), s ∈ Set.Ioo (0 : ℝ) (1 / 4) →
  ∀ C : ℝ, 0 < C →
    -- the hypothesis is on the **origin-centred** unit cube `𝕔₀` only, as the paper's
    -- sentence has it ("we give the argument for `Q = 𝕔₀`"); translation to every other
    
    (∀ (hr : (0 : ℝ) < 1)
      (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 hr)),
      (∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 hr),
        cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 hr threeQuarterOrder
            (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr)).1 ≤
          C * (E.lam (0 : SpatialCoordinates d) 1 hr a (0 : SpatialCoordinates d) 1 s 1)⁻¹ *
            sobolevCoefficientForm a
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr))
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr))) ∧
      (∀ v : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 hr),
        cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 hr threeQuarterOrder
            (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr)).1 ≤
          C * (E.lam (0 : SpatialCoordinates d) 1 hr a (0 : SpatialCoordinates d) 1 s 1)⁻¹ *
            sobolevCoefficientForm a
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr))
              (v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 hr)))) →
  ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
  ∃ C' : ℝ, 0 < C' ∧
    ∀ a : PositiveCoefficient (centeredCube z r hr),
      (∀ v : killedSobolevGraph (centeredCube z r hr),
        cubeFractionalSqNorm hd z r hr threeQuarterOrder
            (v : SobolevData (centeredCube z r hr)).1 ≤
          C' * (E.lam z r hr a z r s 1)⁻¹ *
            sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr))) ∧
      (∀ v : meanZeroSobolevGraph (centeredCube z r hr),
        cubeFractionalSqNorm hd z r hr threeQuarterOrder
            (v : SobolevData (centeredCube z r hr)).1 ≤
          C' * (E.lam z r hr a z r s 1)⁻¹ *
            sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
              (v : SobolevData (centeredCube z r hr))) := by
  intro d hd E s hs C hC hunit z r hr hrle
  let h1 : (0 : ℝ) < 1 := by norm_num
  let C' : ℝ := C * r ^ ((1 / 2 : ℝ) - (d : ℝ))
  have hC' : 0 < C' := by
    dsimp [C']
    exact mul_pos hC (Real.rpow_pos_of_pos hr _)
  have hR : 1 ≤ r ^ (-(3 / 2 : ℝ)) := by
    have hp : 0 < r ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hr _
    have hple : r ^ (3 / 2 : ℝ) ≤ 1 := by
      simpa using (Real.rpow_le_rpow hr.le hrle (by norm_num : 0 ≤ (3 / 2 : ℝ)))
    rw [Real.rpow_neg hr.le]
    exact (one_le_inv₀ hp).2 hple
  have hpow : r ^ ((1 / 2 : ℝ) - (d : ℝ)) * r ^ ((d : ℝ) - 2) =
      r ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hr]
    congr 1
    norm_num
  refine ⟨C', hC', ?_⟩
  intro a
  obtain ⟨b, hb⟩ :=
    _root_.SubdiffusiveProcess.Paper.lane4_dilation_coefficient_transport d z 0 r hr h1 a
  have hlam : E.lam z r hr a z r s 1 =
      E.lam (0 : SpatialCoordinates d) 1 h1 b (0 : SpatialCoordinates d) 1 s 1 := by
    apply E.lam_dilation z r hr a 0 h1 b
    filter_upwards [hb] with x hx
    have hT : cubeDilation z 0 r x =
        (fun i => z i + r * (x i - (0 : SpatialCoordinates d) i)) := by
      rfl
    rw [hT] at hx
    simpa using hx
  constructor
  · intro v
    obtain ⟨w, hwval, hwgrad⟩ :=
      aux_lane4_coercivity_dilation_killed_pullback d z r hr h1 v
    have hfg : ∀ i : Fin 1, ∀ᵐ x ∂volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
        (fun _ : Fin 1 => (w : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) i x =
          (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) i
            (cubeDilation z 0 r x) := by
      intro i
      simpa using hwval
    have hnorm :=
      _root_.SubdiffusiveProcess.Paper.lane4_gagliardo_dilation_scaling d 1 hd z 0 r hr h1
        threeQuarterOrder
        (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1)
        (fun _ : Fin 1 => (w : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) hfg
    have hsemi : cubeFractionalVecSeminormSq hd z r hr threeQuarterOrder
          (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) =
        r ^ (-(3 / 2 : ℝ)) * cubeFractionalVecSeminormSq hd
          (0 : SpatialCoordinates d) 1 h1 threeQuarterOrder
          (fun _ : Fin 1 => (w : SobolevData
            (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) := by
      dsimp [cubeFractionalVecSeminormSq]
      have hpos : 0 ≤ r ^ (-(3 / 2 : ℝ)) := (Real.rpow_pos_of_pos hr _).le
      have h := congrArg ENNReal.toReal hnorm.1
      simpa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos,
        show (-(2 * (threeQuarterOrder : ℝ))) = (-(3 / 2 : ℝ)) by
          dsimp [threeQuarterOrder]; ring] using h
    have hsq := aux_lane4_coercivity_dilation_sqNorm_bound d 1 hd z 0 r hr h1
      threeQuarterOrder
      (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1)
      (fun _ : Fin 1 => (w : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 h1)).1)
      (r ^ (-(3 / 2 : ℝ))) hsemi hnorm.2 hR
    have hN : cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        r ^ (-(3 / 2 : ℝ)) *
          cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 h1
            threeQuarterOrder
            (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 := by
      simpa [cubeFractionalSqNorm] using hsq
    have hE := aux_lane4_coercivity_dilation_energy_scaling d z r hr h1 a b
      (v : SobolevData (centeredCube z r hr))
      (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) hb hwval hwgrad
    have h0 := (hunit h1 b).1 w
    calc
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
          r ^ (-(3 / 2 : ℝ)) *
            cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 h1
              threeQuarterOrder
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 := hN
      _ ≤ r ^ (-(3 / 2 : ℝ)) *
          (C * (E.lam (0 : SpatialCoordinates d) 1 h1 b
            (0 : SpatialCoordinates d) 1 s 1)⁻¹ *
            sobolevCoefficientForm b
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))) := by
        exact mul_le_mul_of_nonneg_left h0
          (le_of_lt (Real.rpow_pos_of_pos hr _))
      _ = C' * (E.lam z r hr a z r s 1)⁻¹ *
          sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)) := by
        dsimp [C']
        rw [hlam, hE, ← hpow]
        ring
  · intro v
    obtain ⟨w, hwval, hwgrad⟩ :=
      aux_lane4_coercivity_dilation_meanZero_pullback d z r hr h1 v
    have hfg : ∀ i : Fin 1, ∀ᵐ x ∂volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
        (fun _ : Fin 1 => (w : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) i x =
          (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) i
            (cubeDilation z 0 r x) := by
      intro i
      simpa using hwval
    have hnorm :=
      _root_.SubdiffusiveProcess.Paper.lane4_gagliardo_dilation_scaling d 1 hd z 0 r hr h1
        threeQuarterOrder
        (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1)
        (fun _ : Fin 1 => (w : SobolevData
          (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) hfg
    have hsemi : cubeFractionalVecSeminormSq hd z r hr threeQuarterOrder
          (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1) =
        r ^ (-(3 / 2 : ℝ)) * cubeFractionalVecSeminormSq hd
          (0 : SpatialCoordinates d) 1 h1 threeQuarterOrder
          (fun _ : Fin 1 => (w : SobolevData
            (centeredCube (0 : SpatialCoordinates d) 1 h1)).1) := by
      dsimp [cubeFractionalVecSeminormSq]
      have hpos : 0 ≤ r ^ (-(3 / 2 : ℝ)) := (Real.rpow_pos_of_pos hr _).le
      have h := congrArg ENNReal.toReal hnorm.1
      simpa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos,
        show (-(2 * (threeQuarterOrder : ℝ))) = (-(3 / 2 : ℝ)) by
          dsimp [threeQuarterOrder]; ring] using h
    have hsq := aux_lane4_coercivity_dilation_sqNorm_bound d 1 hd z 0 r hr h1
      threeQuarterOrder
      (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1)
      (fun _ : Fin 1 => (w : SobolevData
        (centeredCube (0 : SpatialCoordinates d) 1 h1)).1)
      (r ^ (-(3 / 2 : ℝ))) hsemi hnorm.2 hR
    have hN : cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
        r ^ (-(3 / 2 : ℝ)) *
          cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 h1
            threeQuarterOrder
            (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 := by
      simpa [cubeFractionalSqNorm] using hsq
    have hE := aux_lane4_coercivity_dilation_energy_scaling d z r hr h1 a b
      (v : SobolevData (centeredCube z r hr))
      (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) hb hwval hwgrad
    have h0 := (hunit h1 b).2 w
    calc
      cubeFractionalSqNorm hd z r hr threeQuarterOrder
          (v : SobolevData (centeredCube z r hr)).1 ≤
          r ^ (-(3 / 2 : ℝ)) *
            cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 h1
              threeQuarterOrder
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 := hN
      _ ≤ r ^ (-(3 / 2 : ℝ)) *
          (C * (E.lam (0 : SpatialCoordinates d) 1 h1 b
            (0 : SpatialCoordinates d) 1 s 1)⁻¹ *
            sobolevCoefficientForm b
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
              (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))) := by
        exact mul_le_mul_of_nonneg_left h0
          (le_of_lt (Real.rpow_pos_of_pos hr _))
      _ = C' * (E.lam z r hr a z r s 1)⁻¹ *
          sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
            (v : SobolevData (centeredCube z r hr)) := by
        dsimp [C']
        rw [hlam, hE, ← hpow]
        ring

end SubdiffusiveProcess.Paper

