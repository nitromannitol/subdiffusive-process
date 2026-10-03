module

public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
public import SubdiffusiveProcess.Paper.inputs_J_root_locality
public import SubdiffusiveProcess.Sobolev.NativeH1
public import SubdiffusiveProcess.Lane4.CubeDilation
public import SubdiffusiveProcess.Lane4.Bridge
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicCovariance
public import Homogenization.Sobolev.Fractional.ContinuousInterpolation.ContinuousDiscreteKBridge
public import SubdiffusiveProcess.Frozen.Section2.CoarseGrainedPoincare

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

open Homogenization Homogenization.Book

/-- Symmetrize the supplied chart cube by cube. Its ellipticity constants are
adjusted to the symmetric part's operator bound. -/
noncomputable def aux_inputs_poincare_gradient_symmFamily {d : ℕ}
    (A : Ch02.TriadicCoeffFamily d) : Ch02.TriadicCoeffFamily d where
  coeffOn Q :=
    let a := A.coeffOn Q
    { toCoeffField := fun x => Homogenization.symmPart (a.toCoeffField x)
      lam := a.lam
      Lam := a.Lam ^ 2 * a.lam⁻¹
      lam_pos := a.lam_pos
      lam_le_Lam := by
        have hsq : a.lam ^ 2 ≤ a.Lam ^ 2 :=
          (sq_le_sq₀ a.lam_pos.le (le_of_lt (lt_of_lt_of_le a.lam_pos a.lam_le_Lam))).2
            a.lam_le_Lam
        have h := mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr a.lam_pos.le)
        convert h using 1; field_simp [a.lam_pos.ne']
      aeStronglyMeasurable := by
        intro i j
        have hcoord :
            (fun x : Vec d =>
              Homogenization.restrictCoeffField
                (Ch02.cubeDomain Q : Set (Vec d))
                (fun y => Homogenization.symmPart (a.toCoeffField y)) x i j) =
              fun x => (1 / 2 : ℝ) *
                (Homogenization.restrictCoeffField
                    (Ch02.cubeDomain Q : Set (Vec d)) a.toCoeffField x i j +
                  Homogenization.restrictCoeffField
                    (Ch02.cubeDomain Q : Set (Vec d)) a.toCoeffField x j i) := by
          funext x
          by_cases hx : x ∈ (Ch02.cubeDomain Q : Set (Vec d))
          · change x ∈ openCubeSet Q at hx
            simp [Homogenization.restrictCoeffField, Homogenization.symmPart, hx]
            ring
          · change x ∉ openCubeSet Q at hx
            simp [Homogenization.restrictCoeffField, hx]
        rw [hcoord]
        exact (a.aeStronglyMeasurable i j).add
          (a.aeStronglyMeasurable j i) |>.const_smul (1 / 2 : ℝ)
      aeElliptic := by
        filter_upwards [a.aeElliptic] with x hx
        have hLampos : 0 < a.Lam := lt_of_lt_of_le a.lam_pos a.lam_le_Lam
        have hinv : (a.Lam ^ 2 * a.lam⁻¹)⁻¹ = a.lam * (a.Lam⁻¹ * a.Lam⁻¹) := by
          field_simp [a.lam_pos.ne', hLampos.ne']
        refine ⟨a.lam_pos, ?_, ?_, ?_⟩
        · have hsq : a.lam ^ 2 ≤ a.Lam ^ 2 :=
            (sq_le_sq₀ a.lam_pos.le
              (le_of_lt (lt_of_lt_of_le a.lam_pos a.lam_le_Lam))).2 a.lam_le_Lam
          have h := mul_le_mul_of_nonneg_right hsq (inv_nonneg.mpr a.lam_pos.le)
          convert h using 1; field_simp [a.lam_pos.ne']
        · exact Homogenization.lowerBound_symmPart_of_isEllipticMatrix hx
        · rw [hinv]
          exact Homogenization.lowerBound_symmPartInv_of_isEllipticMatrix hx }
  restrictsTo_of_subset := by
    intro Q R hQR
    have h := A.restrictsTo_of_subset hQR
    filter_upwards [h] with x hx
    exact congrArg Homogenization.symmPart hx

theorem aux_inputs_poincare_gradient_symmFamily_symmetric {d : ℕ}
    (A : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) :
    Ch02.CoeffOn.IsSymmetric
      ((aux_inputs_poincare_gradient_symmFamily A).coeffOn Q) := by
  exact Filter.Eventually.of_forall fun x => by
    change Homogenization.matTranspose
        (Homogenization.symmPart ((A.coeffOn Q).toCoeffField x)) =
      Homogenization.symmPart ((A.coeffOn Q).toCoeffField x)
    exact Homogenization.matTranspose_symmPart _

theorem aux_inputs_poincare_gradient_chart_descendant_aeeq {d : ℕ}
    (Jc : Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) :
    ∀ (k : ℤ) (S : TriadicCube d),
      S ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) k →
      Ch02.CoeffOn.AEEq
        ((aux_inputs_poincare_gradient_symmFamily (Jc.chart z r hr a z r)).coeffOn S)
        ((Jc.chart z r hr a z r).coeffOn S) := by
  intro k S hS
  have hk : k ≤ (Homogenization.originCube d 0).scale :=
    Homogenization.scale_le_of_mem_descendantsAtScale hS
  have hsubset : Homogenization.openCubeSet S ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0) :=
    Homogenization.openCubeSet_subset_of_mem_descendantsAtScale hk hS
  have heq := Jc.chart_eq z r hr a z r hr Set.Subset.rfl S hsubset
  filter_upwards [heq] with x hx
  calc
    Homogenization.symmPart (((Jc.chart z r hr a z r).coeffOn S).toCoeffField x) =
        Homogenization.symmPart
          (Homogenization.scalarMatrix (a.val (fun i => z i + r * x i))) :=
      congrArg Homogenization.symmPart hx
    _ = Homogenization.scalarMatrix (a.val (fun i => z i + r * x i)) :=
      Ch02.symmPart_scalarMatrix _
    _ = ((Jc.chart z r hr a z r).coeffOn S).toCoeffField x := hx.symm

theorem aux_inputs_poincare_gradient_lambda_symm {d : ℕ}
    (Jc : Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (s : ℝ)
    (hs : s ∈ Set.Ioc (0 : ℝ) 1) (q : ℝ≥0∞) (hq : 1 ≤ q) :
    Jc.lam z r hr a z r s q =
      SubdiffusiveProcess.CoarseGrainingVocab.lambda (Homogenization.originCube d 0) s
        (if q = ⊤ then .infinity else .finite q.toReal)
        (aux_inputs_poincare_gradient_symmFamily (Jc.chart z r hr a z r)) := by
  calc
    Jc.lam z r hr a z r s q =
        Ch02.lambdaSq (Homogenization.originCube d 0) s
          (if q = ⊤ then .infinity else .finite q.toReal)
          (Jc.chart z r hr a z r) :=
      Jc.lam_eq z r hr a z r hr Set.Subset.rfl s hs q hq
    _ = SubdiffusiveProcess.CoarseGrainingVocab.lambda (Homogenization.originCube d 0) s
          (if q = ⊤ then .infinity else .finite q.toReal)
          (aux_inputs_poincare_gradient_symmFamily (Jc.chart z r hr a z r)) := by
      rw [← SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport.lambdaSq_eq_of_descendantAEEq
        (Homogenization.originCube d 0)
        (aux_inputs_poincare_gradient_chart_descendant_aeeq Jc z r hr a)
        s (if q = ⊤ then .infinity else .finite q.toReal)]

theorem aux_inputs_poincare_gradient_pullback {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) :
    ∃ v : Homogenization.H1Function
        (Homogenization.openCubeSet (Homogenization.originCube d 0)),
      ∀ x i, v.grad x i = (u : SobolevData (centeredCube z r hr)).2 i
        (fun j => z j + r * x j) := by
  let w : SpatialCoordinates d := fun i => z i - r / 2
  have hset : Homogenization.axisCube w r =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [centeredCube_eq_pi z hr]
    ext x
    simp [Homogenization.axisCube, w]
    constructor <;> intro hx i <;>
      have h := hx i <;> exact ⟨h.1, by linarith⟩
  obtain ⟨uH, _hfun, hgrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph u
  let uA : Homogenization.H1Function (Homogenization.axisCube w r) := hset.symm ▸ uH
  have hgradA : uA.grad =
      (fun x i => (u : SobolevData (centeredCube z r hr)).2 i x) := by
    calc
      uA.grad = uH.grad := Homogenization.H1Function.grad_castDomain hset.symm uH
      _ = _ := hgrad
  refine ⟨Homogenization.CubeCalderonZygmund.axisCubeHarmonicPullback w hr uA, ?_⟩
  intro x i
  rw [Homogenization.CubeCalderonZygmund.axisCubeHarmonicPullback_grad, hgradA]
  congr 1
  funext j
  simp [Homogenization.CubeCalderonZygmund.axisCubeAffine,
    Homogenization.CubeCalderonZygmund.axisCubeCenter, w]
  ring

theorem aux_inputs_poincare_gradient_gradient_component {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (u : SobolevData Ω) (i : Fin d) (x : SpatialCoordinates d) :
    (SubdiffusiveProcess.sobolevGradient u i : DomainL2 Ω) x = u.2 i x := by
  rfl

theorem aux_inputs_poincare_gradient_energy {d : ℕ}
    (Jc : Paper.in_J d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (u : weakSobolevGraph (centeredCube z r hr))
    (v : Homogenization.H1Function
      (Homogenization.openCubeSet (Homogenization.originCube d 0)))
    (hv : ∀ x i, v.grad x i = (u : SobolevData (centeredCube z r hr)).2 i
      (fun j => z j + r * x j)) :
    SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm
        (Homogenization.originCube d 0)
        (aux_inputs_poincare_gradient_symmFamily (Jc.chart z r hr a z r)) v.grad =
      normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) := by
  let Q0 : TriadicCube d := Homogenization.originCube d 0
  let Ω := centeredCube z r hr
  let T : SpatialCoordinates d → SpatialCoordinates d :=
    SubdiffusiveProcess.Lane4.cubeDilation z 0 r
  let μ0 : Measure (SpatialCoordinates d) :=
    volume.restrict (Homogenization.openCubeSet Q0)
  let μ1 : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set _)
  let μr : Measure (SpatialCoordinates d) := volume.restrict (Ω : Set _)
  have hrootSet :
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) =
        Homogenization.openCubeSet Q0 := by
    simpa [Q0] using
      SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube
        (d := d) (m := 0) (by norm_num : (0 : ℝ) < (3 : ℝ) ^ (0 : ℤ))
  have hμ0 : μ0 = μ1 := by
    simp [μ0, μ1, hrootSet]
  have hmap : Measure.map T μ1 =
      ENNReal.ofReal ((r ^ d)⁻¹) • μr := by
    simpa [T, μr, Ω, abs_of_pos (inv_pos.mpr (pow_pos hr d))] using
      (SubdiffusiveProcess.Lane4.map_cubeDilation_restrict
        z (0 : SpatialCoordinates d) hr (by norm_num : (0 : ℝ) < 1))
  have hnorm : Homogenization.normalizedCubeMeasure Q0 = μ0 := by
    rw [Homogenization.normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
  have hTpoint (x : SpatialCoordinates d) :
      T x = fun j => z j + r * x j := by
    funext j
    simp [T]
  have hchart : ∀ᵐ x ∂μ0,
      ((Jc.chart z r hr a z r).coeffOn Q0).toCoeffField x =
        Homogenization.scalarMatrix (a.val (T x)) := by
    have h := Jc.chart_eq z r hr a z r hr Set.Subset.rfl Q0 (by simp [Q0])
    filter_upwards [h] with x hx
    rw [hTpoint x]
    exact hx
  have hcoef : ∀ᵐ x ∂μ0,
      ((aux_inputs_poincare_gradient_symmFamily
        (Jc.chart z r hr a z r)).coeffOn Q0).toCoeffField x =
          Homogenization.scalarMatrix (a.val (T x)) := by
    filter_upwards [hchart] with x hx
    change Homogenization.symmPart
        (((Jc.chart z r hr a z r).coeffOn Q0).toCoeffField x) = _
    rw [hx, Homogenization.Book.Ch02.symmPart_scalarMatrix]
  have hden :
      (fun x => Homogenization.vecDot (v.grad x)
        (Homogenization.matVecMul
          (((aux_inputs_poincare_gradient_symmFamily
            (Jc.chart z r hr a z r)).coeffOn Q0).toCoeffField x) (v.grad x))) =ᵐ[μ0]
      (fun x => a.val (T x) * ∑ i : Fin d, (v.grad x i) ^ 2) := by
    filter_upwards [hcoef] with x hx
    rw [hx, Homogenization.matVecMul_scalarMatrix,
      Homogenization.vecDot_smul_right]
    simp [Homogenization.vecDot, pow_two, mul_comm]
  have hrad :
      (∫ x, Homogenization.vecDot (v.grad x)
        (Homogenization.matVecMul
          (((aux_inputs_poincare_gradient_symmFamily
            (Jc.chart z r hr a z r)).coeffOn Q0).toCoeffField x) (v.grad x))
        ∂Homogenization.normalizedCubeMeasure Q0) =
      ∫ x, a.val (T x) * ∑ i : Fin d, (v.grad x i) ^ 2 ∂μ0 := by
    rw [hnorm]
    exact MeasureTheory.integral_congr_ae hden
  let g : HilbertGradient Ω :=
    sobolevGradient (u : SobolevData Ω)
  have hcomp : ∀ i : Fin d, (fun x => v.grad x i) =ᵐ[μ0]
      (fun x => (g i) (T x)) := by
    intro i
    exact Filter.Eventually.of_forall fun x => by
      change v.grad x i = (g i) (T x)
      rw [hv x i]
      rw [← hTpoint x]
      exact (aux_inputs_poincare_gradient_gradient_component
        (u : SobolevData Ω) i (T x)).symm
  have hcomp1 : ∀ i : Fin d, (fun x => v.grad x i) =ᵐ[μ1]
      (fun x => (g i) (T x)) := by
    intro i
    simpa only [μ0, μ1, hμ0] using hcomp i
  have hphysInt : ∀ i : Fin d,
      Integrable (fun y => a.val y * ((g i) y) ^ 2) μr := by
    intro i
    have hi := SubdiffusiveProcess.integrable_weighted_coordinates
      a.val g g i
    simpa [μr, Ω, pow_two, mul_assoc, mul_left_comm, mul_comm] using hi
  have hrootInt : ∀ i : Fin d,
      Integrable (fun x => a.val (T x) * (v.grad x i) ^ 2) μ0 := by
    intro i
    have hscaled : Integrable (fun y => a.val y * ((g i) y) ^ 2)
        (ENNReal.ofReal ((r ^ d)⁻¹) • μr) :=
      (hphysInt i).smul_measure ENNReal.ofReal_ne_top
    have hmapInt : Integrable (fun y => a.val y * ((g i) y) ^ 2)
        (Measure.map T μ1) := by
      simpa [hmap] using hscaled
    have hcompInt : Integrable
        (fun x => a.val (T x) * ((g i) (T x)) ^ 2) μ1 := by
      exact hmapInt.comp_aemeasurable
        (SubdiffusiveProcess.Lane4.cubeDilationEquiv z 0 hr.ne').measurable.aemeasurable
    have heq : (fun x => a.val (T x) * (v.grad x i) ^ 2) =ᵐ[μ1]
        (fun x => a.val (T x) * ((g i) (T x)) ^ 2) := by
      filter_upwards [hcomp1 i] with x hx
      rw [hx]
    have hci := hcompInt.congr heq.symm
    simpa [μ0, μ1, hμ0] using hci
  have hsetInt (i : Fin d) :
      ∫ y in (Ω : Set (SpatialCoordinates d)), a.val y * ((g i) y) ^ 2
          ∂volume.restrict (Ω : Set (SpatialCoordinates d)) =
        ∫ y, a.val y * ((g i) y) ^ 2 ∂μr := by
    change ∫ y, a.val y * ((g i) y) ^ 2 ∂
        (volume.restrict (Ω : Set (SpatialCoordinates d))).restrict
          (Ω : Set (SpatialCoordinates d)) = _
    rw [Measure.restrict_restrict_of_subset (Set.Subset.rfl)]
  have hIntMap : ∀ i : Fin d,
      ∫ x, a.val (T x) * ((g i) (T x)) ^ 2 ∂μ1 =
        (r ^ d)⁻¹ * ∫ y, a.val y * ((g i) y) ^ 2 ∂μr := by
    intro i
    have htoReal : (ENNReal.ofReal ((r ^ d)⁻¹)).toReal = (r ^ d)⁻¹ :=
      ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos hr d).le)
    calc
      _ = ∫ y, a.val y * ((g i) y) ^ 2 ∂Measure.map T μ1 := by
        symm
        exact MeasureTheory.integral_map_equiv
          (SubdiffusiveProcess.Lane4.cubeDilationEquiv z 0 hr.ne') _
      _ = (r ^ d)⁻¹ * ∫ y, a.val y * ((g i) y) ^ 2 ∂μr := by
        rw [hmap, MeasureTheory.integral_smul_measure, htoReal]
        rfl
  have hsum :
      ∫ x, a.val (T x) * ∑ i : Fin d, (v.grad x i) ^ 2 ∂μ0 =
        (r ^ d)⁻¹ * SubdiffusiveProcess.localGradientEnergy a
          (centeredCube z r hr).isOpen.measurableSet g := by
    calc
      _ = ∑ i : Fin d, ∫ x, a.val (T x) * (v.grad x i) ^ 2 ∂μ0 := by
        rw [← MeasureTheory.integral_finset_sum Finset.univ]
        · congr 1
          funext x
          rw [Finset.mul_sum]
        · intro i hi
          exact hrootInt i
      _ = ∑ i : Fin d,
          (r ^ d)⁻¹ * ∫ y, a.val y * ((g i) y) ^ 2 ∂μr := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∫ x, a.val (T x) * ((g i) (T x)) ^ 2 ∂μ1 := by
            rw [hμ0]
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hcomp1 i] with x hx
            rw [hx]
          _ = _ := hIntMap i
      _ = _ := by
        rw [SubdiffusiveProcess.localGradientEnergy_eq_integral,
          ← Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simpa [μr, Ω] using (hsetInt i).symm
  have hvol : volume.real (Ω : Set (SpatialCoordinates d)) = r ^ d := by
    simpa [Ω] using SubdiffusiveProcess.centeredCube_volume_real z hr
  have hrootRad :
        (∫ x, Homogenization.vecDot (v.grad x)
        (Homogenization.matVecMul
          ((((aux_inputs_poincare_gradient_symmFamily
            (Jc.chart z r hr a z r)).coeffOn Q0).toCoeffField x)) (v.grad x))
        ∂Homogenization.normalizedCubeMeasure Q0) =
        SubdiffusiveProcess.localGradientEnergy a
          (centeredCube z r hr).isOpen.measurableSet g /
            volume.real (Ω : Set (SpatialCoordinates d)) := by
    rw [hrad, hsum, hvol]
    field_simp [ne_of_gt (pow_pos hr d)]
  unfold SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm
    SubdiffusiveProcess.Lane4.normalizedEnergyNorm
  rw [hrootRad]

theorem inputs_poincare_gradient (d : ℕ) (hd : 2 ≤ d) (Jc : Paper.in_J d) :
    (let besovGradSeminorm : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    SobolevData (centeredCube z r hr) → ℝ → ℝ≥0∞ → ℝ) := fun z r hr u s q =>
      r ^ s * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
        (Homogenization.originCube d 0) s (if q = ⊤ then .infinity else .finite q.toReal)
        (fun x i => u.2 i (fun j => z j + r * x j));
let cssPow : ℝ → ℝ≥0∞ → ℝ := fun s q =>
      SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor s
        (if q = ⊤ then .infinity else .finite q.toReal);
∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 → ∀ (q : ℝ≥0∞), 1 ≤ q →
    ∀ u : weakSobolevGraph (centeredCube z r hr),
      r ^ (-s) * besovGradSeminorm z r hr (u : SobolevData _) s q ≤
        cssPow s q * (Jc.lam z r hr a z r s q) ^ (-(1 / 2) : ℝ) *
          normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
            (sobolevGradient (u : SobolevData _))) := by
  intro besovGradSeminorm cssPow z r hr a s hs q hq u
  letI : NeZero d := ⟨by omega⟩
  let Q0 : TriadicCube d := Homogenization.originCube d 0
  let A : Ch02.TriadicCoeffFamily d := Jc.chart z r hr a z r
  let As : Ch02.TriadicCoeffFamily d := aux_inputs_poincare_gradient_symmFamily A
  obtain ⟨v, hv⟩ := aux_inputs_poincare_gradient_pullback z r hr u
  have hsymm : ∀ Q, Ch02.CoeffOn.IsSymmetric (As.coeffOn Q) := by
    intro Q
    exact aux_inputs_poincare_gradient_symmFamily_symmetric A Q
  let qN : Ch02.MultiscaleExponent :=
    if q = ⊤ then .infinity else .finite q.toReal
  have hqN : qN.IsAdmissible := by
    by_cases hqt : q = ⊤
    · simp [qN, hqt]
    · have hqr : 1 ≤ q.toReal := by
        have hh := ENNReal.toReal_mono hqt hq
        simpa using hh
      simpa [qN, hqt] using hqr
  have hzeroMem : Homogenization.MemVectorL2
      (Homogenization.openCubeSet Q0) (0 : Vec d → Vec d) := by
    change MeasureTheory.MemLp (fun _ : Vec d => (0 : Vec d)) 2
      (Homogenization.volumeMeasureOn (Homogenization.openCubeSet Q0))
    exact MeasureTheory.MemLp.zero'
  have hzeroSol : Homogenization.IsSolenoidalOn
      (Homogenization.openCubeSet Q0) (0 : Vec d → Vec d) := by
    intro φ
    simp [Homogenization.vecDot]
  have hsharp := SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare
    hd As hsymm s hs.1 hs.2 qN hqN 0 v (0 : Vec d → Vec d) hzeroMem hzeroSol
  have hLam := aux_inputs_poincare_gradient_lambda_symm Jc z r hr a s hs q hq
  have hEnergy : SubdiffusiveProcess.CoarseGrainingVocab.coefficientEnergyNorm Q0 As v.grad =
      normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
        (sobolevGradient (u : SobolevData (centeredCube z r hr))) := by
    exact aux_inputs_poincare_gradient_energy Jc z r hr a u v hv
  have hgradEq : v.grad = fun x i =>
      (u : SobolevData (centeredCube z r hr)).2 i (fun j => z j + r * x j) := by
    funext x i
    exact hv x i
  rw [hEnergy] at hsharp
  rw [hgradEq] at hsharp
  change r ^ (-s) * (r ^ s *
      SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
        Q0 s qN (fun x i => (u : SobolevData (centeredCube z r hr)).2 i
          (fun j => z j + r * x j))) ≤
    SubdiffusiveProcess.CoarseGrainingVocab.paperPoincareGeometricFactor s qN *
      (Jc.lam z r hr a z r s q) ^ (-(1 / 2) : ℝ) *
        normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
          (sobolevGradient (u : SobolevData (centeredCube z r hr)))
  have hrpow : r ^ (-s : ℝ) * r ^ s = 1 := by
    rw [← Real.rpow_add hr]
    simp
  rw [← mul_assoc, hrpow, one_mul, hLam]
  have hexp : (-(1 / 2 : ℝ)) = (-1 / 2 : ℝ) := by ring
  rw [hexp]
  simpa [A, As, qN, Q0] using hsharp.1

end Paper

