module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Sobolev.NativeH1
public import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapPoincare
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.OverlapCoordinateBridge
public import Homogenization.Besov.Negative.ExactFiniteBridge
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff Pointwise

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_inputs_Sf_besov_finite_centeredCube_translate (d : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    (centeredCube z r hr : Set (SpatialCoordinates d)) =
      Homogenization.translateSet z (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) := by
  ext x
  rw [Homogenization.mem_translateSet_iff_sub_mem]
  rw [centeredCube_eq_pi z hr, centeredCube_eq_pi (0 : SpatialCoordinates d) hr]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Pi.sub_apply, Pi.zero_apply]
  constructor
  · intro hx i
    rcases hx i with ⟨hlo, hhi⟩
    constructor <;> linarith
  · intro hx i
    rcases hx i with ⟨hlo, hhi⟩
    constructor <;> linarith

theorem aux_inputs_Sf_besov_finite_castH1_toFun {d : ℕ}
    {U V : Set (SpatialCoordinates d)} (hUV : U = V)
    (w : Homogenization.H1Function U) (x : SpatialCoordinates d) :
    (hUV ▸ w : Homogenization.H1Function V).toFun x = w.toFun x := by
  cases hUV
  rfl

theorem aux_inputs_Sf_besov_finite_centeredCube_scale (d : ℕ)
    (r : ℝ) (hr : 0 < r) :
    (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) =
      r • Homogenization.openCubeSet (Homogenization.originCube d 0) := by
  ext y
  have hr_pos : 0 < r := hr
  constructor
  · intro hy
    rw [centeredCube_eq_pi (0 : SpatialCoordinates d) hr] at hy
    rw [Set.mem_smul_set]
    refine ⟨r⁻¹ • y, ?_, ?_⟩
    · apply Homogenization.mem_openCubeSet_originCube_iff.mpr
      intro i
      have hyi := hy i (Set.mem_univ i)
      rcases hyi with ⟨hlo, hhi⟩
      simp only [Pi.zero_apply] at hlo hhi
      constructor
      · have hlow : (-(1 / 2 : ℝ)) < y i / r := (lt_div_iff₀ hr_pos).mpr (by nlinarith)
        simpa [div_eq_mul_inv, mul_comm] using hlow
      · have hhigh : y i / r < (1 / 2 : ℝ) := (div_lt_iff₀ hr_pos).mpr (by nlinarith)
        simpa [div_eq_mul_inv, mul_comm] using hhigh
    · ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hr_pos.ne', one_mul]
  · intro hy
    rw [Set.mem_smul_set] at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [centeredCube_eq_pi (0 : SpatialCoordinates d) hr]
    intro i _
    have hxi := (Homogenization.mem_openCubeSet_originCube_iff.mp hx) i
    constructor
    · have hlo := mul_lt_mul_of_pos_left hxi.1 hr_pos
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using! hlo
    · have hhi := mul_lt_mul_of_pos_left hxi.2 hr_pos
      simpa [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using! hhi

theorem aux_inputs_Sf_besov_finite_affineH1 (d : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) :
    ∃ H : Homogenization.H1Function
        (Homogenization.openCubeSet (Homogenization.originCube d 0)),
      ∀ x, H.toFun x =
        (u : SobolevData (centeredCube z r hr)).1 (fun i : Fin d => z i + r * x i) := by
  obtain ⟨V, hV, -⟩ := SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph u
  let hphysical : Homogenization.H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) := V
  have htranslate := aux_inputs_Sf_besov_finite_centeredCube_translate d z r hr
  let hcenter : Homogenization.H1Function
      (Homogenization.translateSet z (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))) :=
    htranslate ▸ hphysical
  let h0r : Homogenization.H1Function (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) :=
    hcenter.untranslate z
  have hcenter_apply (x : SpatialCoordinates d) : hcenter.toFun x = V.toFun x := by
    change (htranslate ▸ hphysical).toFun x = V.toFun x
    exact aux_inputs_Sf_besov_finite_castH1_toFun htranslate hphysical x
  have h0r_apply (x : SpatialCoordinates d) : h0r.toFun x = V.toFun (x + z) := by
    change (hcenter.untranslate z).toFun x = V.toFun (x + z)
    rw [Homogenization.H1Function.untranslate_toFun]
    exact hcenter_apply (x + z)
  have hscale := aux_inputs_Sf_besov_finite_centeredCube_scale d r hr
  let hscaled : Homogenization.H1Function
      (r • Homogenization.openCubeSet (Homogenization.originCube d 0)) := hscale ▸ h0r
  have hscaled_apply (x : SpatialCoordinates d) : hscaled.toFun x = h0r.toFun x := by
    change (hscale ▸ h0r).toFun x = h0r.toFun x
    exact aux_inputs_Sf_besov_finite_castH1_toFun hscale h0r x
  let hpull : Homogenization.H1Function
      (Homogenization.openCubeSet (Homogenization.originCube d 0)) :=
    hscaled.undilateSet hr rfl
  let H : Homogenization.H1Function
      (Homogenization.openCubeSet (Homogenization.originCube d 0)) := r • hpull
  refine ⟨H, ?_⟩
  intro x
  simp only [H, hpull, Homogenization.H1Function.smul_toFun,
    Homogenization.H1Function.undilateSet_toFun]
  rw [hscaled_apply, h0r_apply, hV]
  have harg : r • x + z = (fun i : Fin d => z i + r * x i) := by
    ext i
    simp [Pi.smul_apply, smul_eq_mul, add_comm]
  rw [harg]
  rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

theorem aux_inputs_Sf_besov_finite_exactTerm_eq {d : ℕ}
    (Q : Homogenization.TriadicCube d) (s : ℝ) (f : Homogenization.Vec d → ℝ)
    (hu : Homogenization.ExactOverlapIntegrable Q f)
    (hmem : MemLp f (2 : ℝ≥0∞) (Homogenization.normalizedCubeMeasure Q))
    (j : ℕ) :
    Homogenization.exactOverlapDepthTerm Q s 2 f hu j =
      ENNReal.ofReal (Homogenization.cubeBesovOverlapDepthSeminorm Q s 2 f j) := by
  have hmem' : MemLp f (ENNReal.ofReal (2 : ℝ))
      (Homogenization.normalizedCubeMeasure Q) := by simpa using hmem
  let hu' := Homogenization.exactDualOverlapIntegrable Q 2 (by norm_num) hmem'
  have hcert : hu = hu' := by
    exact Subsingleton.elim _ _
  have hp : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  rw [hcert,
    Homogenization.exactOverlapDepthTerm_eq_ofReal_cubeBesovOverlapDepthSeminorm
      Q s 2 (by norm_num) f hmem' j,
    hp]

theorem inputs_Sf_besov_finite (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (u : weakSobolevGraph (centeredCube z r hr)) :
    (iSup fun j : ℕ =>
      Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) t 2
        (fun x => (u : SobolevData (centeredCube z r hr)).1 (fun i : Fin d => z i + r * x i))
        (inputs_poincare_positive_integrable d hd z r hr (u : SobolevData (centeredCube z r hr)).1) j) < ⊤ := by
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let f : Homogenization.Vec d → ℝ := fun x =>
    (u : SobolevData (centeredCube z r hr)).1 (fun i : Fin d => z i + r * x i)
  let hu := inputs_poincare_positive_integrable d hd z r hr
    (u : SobolevData (centeredCube z r hr)).1
  obtain ⟨H, hH⟩ := aux_inputs_Sf_besov_finite_affineH1 d z r hr u
  let i₀ : Fin d := ⟨0, by omega⟩
  let G : Homogenization.CubeVectorH1Function Q :=
    ⟨fun i => if i = i₀ then H else 0⟩
  have hcoordFun : (fun x => G.toField x i₀) = f := by
    funext x
    change (if i₀ = i₀ then H else 0).toFun x = f x
    exact hH x
  have hmemVec := G.memLp_toField_normalizedCubeMeasure
  have hmem : MemLp f (2 : ℝ≥0∞) (Homogenization.normalizedCubeMeasure Q) := by
    rw [← hcoordFun]
    exact hmemVec.eval i₀
  have hscaleW : Homogenization.cubeBesovScaleWeight t Q = 1 := by
    dsimp [Q, Homogenization.cubeBesovScaleWeight]
    simp
  have hK : 0 ≤ Homogenization.cubeVectorH1OverlapPoincareConstant d *
      G.relativeGradientCoordL2NormSum :=
    mul_nonneg (Homogenization.cubeVectorH1OverlapPoincareConstant_nonneg d)
      G.relativeGradientCoordL2NormSum_nonneg
  have hdepth : ∀ j : ℕ,
      Homogenization.cubeBesovOverlapDepthSeminorm Q t (2 : ℝ≥0∞) f j ≤
        Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
          (Homogenization.cubeVectorH1OverlapPoincareConstant d *
            G.relativeGradientCoordL2NormSum) := by
    intro j
    have hPoincare := Homogenization.cubeVectorH1OverlapPoincareEstimate d Q j G
    have hmul : Real.rpow (3 : ℝ) (t * (j : ℝ)) *
        Real.rpow (3 : ℝ) (-(j : ℝ)) =
        Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) := by
      have h := Real.rpow_add (show (0 : ℝ) < 3 by norm_num)
        (t * (j : ℝ)) (-(j : ℝ))
      have he : t * (j : ℝ) + -(j : ℝ) = (t - 1) * (j : ℝ) := by ring
      rw [he] at h
      exact h.symm
    have hvector :
        Homogenization.cubeBesovOverlappingPositiveVectorDepthSeminorm Q t G.toField j ≤
          Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
            (Homogenization.cubeVectorH1OverlapPoincareConstant d *
              G.relativeGradientCoordL2NormSum) := by
      unfold Homogenization.cubeBesovOverlappingPositiveVectorDepthSeminorm
      calc
        Real.rpow (3 : ℝ) (t * (j : ℝ)) *
            Real.sqrt (Homogenization.cubeBesovOverlappingPositiveVectorDepthAverage Q G.toField j)
            ≤ Real.rpow (3 : ℝ) (t * (j : ℝ)) *
                (Homogenization.cubeVectorH1OverlapPoincareConstant d *
                  Real.rpow (3 : ℝ) (-(j : ℝ)) * G.relativeGradientCoordL2NormSum) :=
          mul_le_mul_of_nonneg_left hPoincare
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
        _ = Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
              (Homogenization.cubeVectorH1OverlapPoincareConstant d *
                G.relativeGradientCoordL2NormSum) := by
          rw [← hmul]
          ring
    calc
      Homogenization.cubeBesovOverlapDepthSeminorm Q t (2 : ℝ≥0∞) f j =
          Homogenization.cubeBesovOverlapDepthSeminorm Q t (2 : ℝ≥0∞)
            (fun x => G.toField x i₀) j := by rw [hcoordFun]
      _ ≤ Homogenization.cubeBesovScaleWeight t Q *
            Homogenization.cubeBesovOverlappingPositiveVectorDepthSeminorm
              Q t G.toField j := by
        exact Homogenization.cubeBesovOverlapDepthSeminorm_two_coordinate_le_vector
          Q t G.toField i₀ j hmemVec
      _ ≤ Homogenization.cubeBesovScaleWeight t Q *
            (Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
              (Homogenization.cubeVectorH1OverlapPoincareConstant d *
                G.relativeGradientCoordL2NormSum)) :=
        mul_le_mul_of_nonneg_left hvector
          (Homogenization.cubeBesovScaleWeight_nonneg t Q)
      _ = Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
            (Homogenization.cubeVectorH1OverlapPoincareConstant d *
              G.relativeGradientCoordL2NormSum) := by rw [hscaleW, one_mul]
  have hgeom : ∀ j : ℕ, Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) ≤ 1 := by
    intro j
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) (Nat.cast_nonneg j)
  have hbound : ∀ j : ℕ,
      Homogenization.exactOverlapDepthTerm Q t 2 f hu j ≤
        ENNReal.ofReal (Homogenization.cubeVectorH1OverlapPoincareConstant d *
          G.relativeGradientCoordL2NormSum) := by
    intro j
    rw [aux_inputs_Sf_besov_finite_exactTerm_eq Q t f hu hmem j]
    apply ENNReal.ofReal_le_ofReal
    calc
      Homogenization.cubeBesovOverlapDepthSeminorm Q t (2 : ℝ≥0∞) f j ≤
          Real.rpow (3 : ℝ) ((t - 1) * (j : ℝ)) *
            (Homogenization.cubeVectorH1OverlapPoincareConstant d *
              G.relativeGradientCoordL2NormSum) := hdepth j
      _ ≤ 1 * (Homogenization.cubeVectorH1OverlapPoincareConstant d *
            G.relativeGradientCoordL2NormSum) :=
        mul_le_mul_of_nonneg_right (hgeom j) hK
      _ = Homogenization.cubeVectorH1OverlapPoincareConstant d *
            G.relativeGradientCoordL2NormSum := one_mul _
  have hsup : (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm Q t 2 f hu j) ≤
      ENNReal.ofReal (Homogenization.cubeVectorH1OverlapPoincareConstant d *
        G.relativeGradientCoordL2NormSum) := iSup_le hbound
  exact lt_of_le_of_lt hsup ENNReal.ofReal_lt_top

end SubdiffusiveProcess.Paper

