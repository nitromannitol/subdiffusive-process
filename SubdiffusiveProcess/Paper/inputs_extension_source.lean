module

public import SubdiffusiveProcess.Paper.inputs_extension_transport
public import SubdiffusiveProcess.Paper.inputs_extension_seminorm
public import SubdiffusiveProcess.Paper.inputs_extension_ellipticity
public import SubdiffusiveProcess.Analysis.AffineSobolevNorms
public import SubdiffusiveProcess.Analysis.FractionalAECongruence
public import Homogenization.Book.Ch03.Theorems.EnergyRHS.Theory
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.DatumPricing
public import SubdiffusiveProcess.Paper.in_extension

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_inputs_extension_source_fractional {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (m : ℕ) (hr : (0 : ℝ) < (3 : ℝ) ^ m)
    (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin d → DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr)) :
    SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
      (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) s.1
        (fun y i => -(f i (y + z))) =
      cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr s f := by
  let U := Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))
  let G : Homogenization.Vec d → Homogenization.Vec d := fun x i => f i x
  have hneg : SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s.1 (fun x => -(G x)) =
      SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel s.1 G := by
    funext xy
    unfold SubdiffusiveProcess.CoarseGrainingVocab.fractionalKernel
    have hv : -G xy.1 - (-G xy.2) = -(G xy.1 - G xy.2) := by abel
    rw [hv, Homogenization.euclideanNorm_neg]
  calc
    _ = SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn (Homogenization.translateSet z U) s.1
          (fun x => -(G x)) :=
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.fractionalSeminormOn_translateSet
        z U s.1 (fun x => -(G x))).symm
    _ = SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
          (centeredCube z ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d)) s.1
          (fun x => -(G x)) := by
      rw [← SubdiffusiveProcess.AffineSobolevNorms.centeredCube_eq_translate_originCube z m hr]
    _ = SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
          (centeredCube z ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d)) s.1 G := by
      unfold SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
      rw [hneg]
    _ = _ := inputs_extension_seminorm hd z ((3 : ℝ) ^ m) hr s f

theorem inputs_extension_source (d : ℕ) (hd : 2 ≤ d) (Jc : _root_.SubdiffusiveProcess.Paper.in_J d) :
    (∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (m : ℕ) (hr : (0 : ℝ) < 3 ^ m)
      (a : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hr))
      (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1),
      ∀ (g : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hr)),
        cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
          (fun i => g i) ≠ ⊤ →
      ∀ (v : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr)),
        (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr),
          sobolevCoefficientForm a (v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) =
            -inner ℝ g (subspaceGradient (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr)) φ)) →
      normalizedEnergyNorm a
          (centeredCube z ((3 : ℝ) ^ m) hr).isOpen.measurableSet
          (sobolevGradient (v : SobolevData _)) ≤
        C * s ^ (-3 : ℝ) *
            (Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ (-(1 / 2) : ℝ) *
            (3 : ℝ) ^ (s * (m : ℝ)) *
            Real.sqrt (cubeFractionalVecSeminormSq hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
              (fun i => g i))) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hC, hDir, _⟩ :=
    (Homogenization.Book.Ch03.energyConsequencesRHSTheory (d := d)).exists_constant
  let D := SubdiffusiveProcess.CoarseGrainingVocab.caccioppoliExactDatumConstant d
  have hD : 0 < D := SubdiffusiveProcess.CoarseGrainingVocab.caccioppoliExactDatumConstant_pos d
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro z m hr a s hs g hg v hweak
  let Ω := centeredCube z ((3 : ℝ) ^ m) hr
  let Q := Homogenization.originCube d (m : ℤ)
  let A := Homogenization.Book.Ch02.TriadicCoeffFamily.dilate (m : ℤ)
    (Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m))
  let gs : Homogenization.Vec d → Homogenization.Vec d := fun y i => -(g i (y + z))
  let vw : weakSobolevGraph Ω := ⟨v, killedSobolevGraph_le_weakSobolevGraph v.property⟩
  have hzero : (fun x i => sobolevGradient (0 : SobolevData Ω) i x) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] (0 : SpatialCoordinates d → SpatialCoordinates d) := by
    have hi (i : Fin d) : (fun x => sobolevGradient (0 : SobolevData Ω) i x) =ᵐ[
        volume.restrict (Ω : Set (SpatialCoordinates d))] 0 := Lp.coeFn_zero ℝ 2 _
    filter_upwards [ae_all_iff.2 hi] with x hx
    exact funext hx
  have hz : cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
      (fun i => sobolevGradient (0 : SobolevData Ω) i) ≠ ⊤ := by
    rw [← inputs_extension_seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩,
      SubdiffusiveProcess.FractionalAECongruence.fractionalSeminormOn_congr _ _ hzero,
      SubdiffusiveProcess.FractionalAECongruence.fractionalSeminormOn_zero]
    exact ENNReal.zero_ne_top
  obtain ⟨hFull, sol, hbd, hgrad, he⟩ := inputs_extension_transport d hd Jc
    z m hr a s hs g hg 0 vw hz hweak (by simp [vw])
  have hbd0 : Homogenization.Book.Ch03.dirichletBoundaryGradientField sol =ᵐ[
      volume.restrict (Homogenization.cubeSet Q)] 0 := by
    apply Homogenization.ae_restrict_cubeSet_iff.mpr
    rw [hbd]
    have hμ : volume.restrict (Homogenization.translateSet z (Homogenization.openCubeSet Q)) =
        volume.restrict (Ω : Set (SpatialCoordinates d)) :=
      congrArg (fun U : Set (SpatialCoordinates d) => volume.restrict U)
        (SubdiffusiveProcess.AffineSobolevNorms.centeredCube_eq_translate_originCube z m hr).symm
    have hzT := hzero.filter_mono (ae_mono hμ.le)
    exact (Homogenization.measurePreserving_addRight_restrict_translateSet z
      (Homogenization.openCubeSet Q)).quasiMeasurePreserving.ae_eq_comp hzT
  let W : Homogenization.CubeEuclideanWspField Q ⟨s, hs.1, hs.2⟩
      Homogenization.FiniteLpExponent.two :=
    { toField := gs, euclideanMemLp := hFull.1, euclideanMemWsp := hFull.2 }
  have hgB := (SubdiffusiveProcess.CoarseGrainingVocab.cubeEuclideanWspField_forceSobolevRegularity
    ⟨s, hs.1, hs.2⟩ W).toForceBesovRegularity hs.1 hs.2.le
  have hzB : Homogenization.Book.Ch03.ForceBesovRegularity Q s
      (Homogenization.Book.Ch03.dirichletBoundaryGradientField sol) :=
    SubdiffusiveProcess.FractionalAECongruence.regularity_of_ae_zero Q s hbd0
  have hn := hDir sol hs.1 hs.2 hgB hzB
  unfold Homogenization.Book.Ch03.dirichletEnergyWithRHSRHS at hn
  rw [SubdiffusiveProcess.FractionalAECongruence.positiveNorm_congr Q s hbd0,
    SubdiffusiveProcess.FractionalAECongruence.positiveNorm_zero, mul_zero, add_zero] at hn
  have hp := SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.scaleNormalizedPositiveBesovVectorSeminormTwo_le_fractionalSeminormOn
    Q ⟨s, hs.1, hs.2⟩ gs hFull
  have hfrac := aux_inputs_extension_source_fractional hd z m hr ⟨s, hs.1, hs.2⟩ (fun i => g i)
  have hweight : Homogenization.cubeBesovScaleWeight (-s) Q = (3 : ℝ) ^ (s * (m : ℝ)) := by
    simp only [Homogenization.cubeBesovScaleWeight, Homogenization.cubeScaleFactor, Q,
      Homogenization.originCube, neg_neg]
    rw [← Real.rpow_intCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hlam := (inputs_extension_ellipticity d Jc z m hr a (s / 2)
    ⟨by linarith [hs.1], by linarith [hs.2]⟩).1
  have hlamF : Homogenization.Book.Ch03.poincareLowerEllipticityFactor Q A (s / 2) (.finite 2) =
      (Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ (-(1 / 2) : ℝ) := by
    change Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2 =
      Homogenization.Book.Ch02.lambdaSq Q (s / 2) (.finite 2) A at hlam
    unfold Homogenization.Book.Ch03.poincareLowerEllipticityFactor
    rw [← hlam]
    rfl
  let H := Real.sqrt (cubeFractionalVecSeminormSq hd z ((3 : ℝ) ^ m) hr
    ⟨s, hs.1, hs.2⟩ (fun i => g i))
  have hH : H = (cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr
      ⟨s, hs.1, hs.2⟩ (fun i => g i)).toReal := by
    exact Real.sqrt_sq ENNReal.toReal_nonneg
  change Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s gs ≤
    D * Homogenization.cubeBesovScaleWeight (-s) Q *
      (s ^ (-(1 / 2) : ℝ) * (SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
        (Homogenization.openCubeSet Q) s gs).toReal) at hp
  rw [hweight, hfrac, ← hH] at hp
  rw [hlamF] at hn
  have hL : 0 ≤ (Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^
      (-(1 / 2) : ℝ) := Real.rpow_nonneg (Jc.lam_pos _ _ _ _ _ _ _ _).le _
  have hpow : s ^ (-(3 / 2) : ℝ) * s ^ (-(1 / 2) : ℝ) ≤ s ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hs.1]
    exact Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le (by norm_num)
  have hb := (he.trans hn).trans (mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hs.1.le _)) hL))
  have hnon : 0 ≤ C * D *
      ((Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ (-(1 / 2) : ℝ) *
        (3 : ℝ) ^ (s * (m : ℝ)) * H) := by
    exact mul_nonneg (mul_nonneg hC.le hD.le)
      (mul_nonneg (mul_nonneg hL (Real.rpow_nonneg (by norm_num) _)) (Real.sqrt_nonneg _))
  calc
    _ ≤ C * s ^ (-(3 / 2) : ℝ) *
        (Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ (-(1 / 2) : ℝ) *
        (D * (3 : ℝ) ^ (s * (m : ℝ)) * (s ^ (-(1 / 2) : ℝ) * H)) := hb
    _ = (C * D *
        ((Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ (-(1 / 2) : ℝ) *
          (3 : ℝ) ^ (s * (m : ℝ)) * H)) *
        (s ^ (-(3 / 2) : ℝ) * s ^ (-(1 / 2) : ℝ)) := by ring
    _ ≤ (C * D *
        ((Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ (-(1 / 2) : ℝ) *
          (3 : ℝ) ^ (s * (m : ℝ)) * H)) * s ^ (-3 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow hnon
    _ = _ := by ring

end SubdiffusiveProcess.Paper

