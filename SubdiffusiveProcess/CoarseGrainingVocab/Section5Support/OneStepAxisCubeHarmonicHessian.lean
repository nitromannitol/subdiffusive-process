import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHarmonicGainCarrier
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepCellLocalization
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHarmonicCellEstimate
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepHessianObservableMeasurability
import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicGain
import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalScaledDatumEnergy
import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeakPoissonDerivative




open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Ratio between the probability normalization of a triadic cell and that
of a containing positive axis cube. -/
noncomputable def triadicAxisNormalizedMeasureRatio {d : ℕ}
    (R : TriadicCube d) (L : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (cubeVolume R)⁻¹ / ENNReal.ofReal ((L ^ d)⁻¹)

/-- A normalized triadic-cell measure is dominated by the normalized measure
of any containing positive axis cube, with the exact volume-ratio factor. -/
theorem normalizedCubeMeasure_le_ratio_smul_axisCubeNormalizedMeasure
    {d : ℕ} (R : TriadicCube d) (z : Vec d) (L : ℝ) (hL : 0 < L)
    (hsub : openCubeSet R ⊆ axisCube z L) :
    normalizedCubeMeasure R ≤
      triadicAxisNormalizedMeasureRatio R L •
        CubeCalderonZygmund.axisCubeNormalizedMeasure z L := by
  let cR : ℝ≥0∞ := ENNReal.ofReal (cubeVolume R)⁻¹
  let cD : ℝ≥0∞ := ENNReal.ofReal ((L ^ d)⁻¹)
  have hcD0 : cD ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (pow_pos hL d))
  have hcDtop : cD ≠ ∞ := ENNReal.ofReal_ne_top
  have hcoeff : (cR / cD) * cD = cR := ENNReal.div_mul_cancel hcD0 hcDtop
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    CubeCalderonZygmund.axisCubeNormalizedMeasure_eq_smul_volume_restrict
      z L hL]
  change cR • MeasureTheory.volume.restrict (openCubeSet R) ≤
    (cR / cD) • (cD • MeasureTheory.volume.restrict (axisCube z L))
  rw [← mul_smul, hcoeff]
  rw [Measure.le_iff]
  intro S hS
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right
    (Measure.restrict_mono_set MeasureTheory.volume hsub S) cR

/-- Normalized `L^p` restriction from a positive axis cube to any contained
triadic cell.  This is the arbitrary-center counterpart of the central
descendant restriction formula. -/
theorem eLpNorm_triadic_le_ratio_rpow_mul_axisCube
    {d : ℕ} (R : TriadicCube d) (z : Vec d) (L : ℝ) (hL : 0 < L)
    (hsub : openCubeSet R ⊆ axisCube z L) (p : FiniteLpExponent)
    (f : Vec d → ℝ)
    (hf : MemLp f p.exponent
      (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)) :
    MemLp f p.exponent (normalizedCubeMeasure R) ∧
      eLpNorm f p.exponent (normalizedCubeMeasure R) ≤
        (triadicAxisNormalizedMeasureRatio R L) ^
            (1 / p.exponent).toReal *
          eLpNorm f p.exponent
            (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) := by
  let c := triadicAxisNormalizedMeasureRatio R L
  have hc0 : c ≠ 0 := by
    change triadicAxisNormalizedMeasureRatio R L ≠ 0
    rw [triadicAxisNormalizedMeasureRatio, ENNReal.div_ne_zero]
    exact ⟨ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (cubeVolume_pos R)),
      ENNReal.ofReal_ne_top⟩
  have hctop : c ≠ ∞ := by
    apply ENNReal.div_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (pow_pos hL d))
  have hmeasure :=
    normalizedCubeMeasure_le_ratio_smul_axisCubeNormalizedMeasure R z L hL hsub
  have hfscaled : MemLp f p.exponent
      (c • CubeCalderonZygmund.axisCubeNormalizedMeasure z L) :=
    hf.smul_measure hctop
  refine ⟨hfscaled.mono_measure hmeasure, ?_⟩
  calc
    eLpNorm f p.exponent (normalizedCubeMeasure R) ≤
        eLpNorm f p.exponent
          (c • CubeCalderonZygmund.axisCubeNormalizedMeasure z L) :=
      eLpNorm_mono_measure f hmeasure
    _ = c ^ (1 / p.exponent).toReal *
        eLpNorm f p.exponent
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) := by
      simpa only [smul_eq_mul] using
        eLpNorm_smul_measure_of_ne_zero hc0 f p.exponent
          (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)

/-- Euclidean-vector packaging of the selected scalar harmonic gain. -/
noncomputable def oneStepHarmonicEuclideanGain (d : ℕ) (hd : 3 ≤ d) :
    CubeCalderonZygmund.INTERNAL.HarmonicEuclideanGradientGain d
      (oneStepHarmonicExponent d hd) (oneStepHarmonicGainDepth d hd) :=
  CubeCalderonZygmund.INTERNAL.HarmonicEuclideanGradientGain.fromScalar
    (oneStepHarmonicGain d hd)

/-- A weak-Hessian row of a harmonic function on an arbitrary positive axis
cube has the selected normalized `L^(16d)` interior gain. -/
theorem axisCube_harmonicHessianRow_highExponent
    {d : ℕ} (hd : 3 ≤ d) (z : Vec d) (L : ℝ) (hL : 0 < L)
    (u : H1Function (axisCube z L))
    (H : HasWeakHessianOn (axisCube z L) u)
    (hu : WeakPoissonEquationOn (axisCube z L) u (fun _ ↦ 0))
    (i : Fin d) :
    MemLp
        (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
        (oneStepHarmonicExponent d hd).exponent
        (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L
            (oneStepHarmonicGainDepth d hd))
          (CubeCalderonZygmund.axisCubeConcentricDepthSide L
            (oneStepHarmonicGainDepth d hd))) ∧
      eLpNorm
          (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x))
          (oneStepHarmonicExponent d hd).exponent
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L
              (oneStepHarmonicGainDepth d hd))
            (CubeCalderonZygmund.axisCubeConcentricDepthSide L
              (oneStepHarmonicGainDepth d hd))) ≤
        ((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
          eLpNorm
            (fun x ↦ HilbertVec.ofVec (fun j ↦ H.hess i j x)) 2
            (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) := by
  let v : H1Function (axisCube z L) := H.gradCoordH1Function i
  have hv : WeakPoissonEquationOn (axisCube z L) v (fun _ ↦ 0) :=
    hu.gradCoordH1Function_harmonic (isOpen_axisCube z L) H i
  have hgain :=
    CubeCalderonZygmund.axisCube_harmonicEuclideanGradientGain
      (oneStepHarmonicEuclideanGain d hd) z L hL v hv
  simpa only [v, HasWeakHessianOn.gradCoordH1Function_grad_apply] using hgain

/-- Coordinate form of `axisCube_harmonicHessianRow_highExponent`, ready for
the coordinate-sum definition of the manuscript's `B_z`. -/
theorem axisCube_harmonicHessianCoord_highExponent
    {d : ℕ} (hd : 3 ≤ d) (z : Vec d) (L : ℝ) (hL : 0 < L)
    (u : H1Function (axisCube z L))
    (H : HasWeakHessianOn (axisCube z L) u)
    (hu : WeakPoissonEquationOn (axisCube z L) u (fun _ ↦ 0))
    (i j : Fin d) :
    MemLp (fun x ↦ H.hess i j x)
        (oneStepHarmonicExponent d hd).exponent
        (CubeCalderonZygmund.axisCubeNormalizedMeasure
          (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L
            (oneStepHarmonicGainDepth d hd))
          (CubeCalderonZygmund.axisCubeConcentricDepthSide L
            (oneStepHarmonicGainDepth d hd))) ∧
      eLpNorm (fun x ↦ H.hess i j x)
          (oneStepHarmonicExponent d hd).exponent
          (CubeCalderonZygmund.axisCubeNormalizedMeasure
            (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L
              (oneStepHarmonicGainDepth d hd))
            (CubeCalderonZygmund.axisCubeConcentricDepthSide L
              (oneStepHarmonicGainDepth d hd))) ≤
        ((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
          eLpNorm
            (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
            (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) := by
  let μ := CubeCalderonZygmund.axisCubeNormalizedMeasure
    (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L
      (oneStepHarmonicGainDepth d hd))
    (CubeCalderonZygmund.axisCubeConcentricDepthSide L
      (oneStepHarmonicGainDepth d hd))
  have hrow := axisCube_harmonicHessianRow_highExponent hd z L hL u H hu i
  have hcoord :
      MemLp (fun x ↦ H.hess i j x)
        (oneStepHarmonicExponent d hd).exponent μ := by
    rw [memLp_piLp_iff] at hrow
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hrow.1 j
  refine ⟨hcoord, ?_⟩
  calc
    eLpNorm (fun x ↦ H.hess i j x)
        (oneStepHarmonicExponent d hd).exponent μ ≤
      eLpNorm (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x))
        (oneStepHarmonicExponent d hd).exponent μ :=
      coordinate_eLpNorm_le_euclidean μ (oneStepHarmonicExponent d hd)
        (fun x k ↦ H.hess i k x) j
    _ ≤ ((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
          eLpNorm
            (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
            (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) := hrow.2

/-- The arbitrary-axis estimate read on a literal triadic cell which is the
prescribed concentric contraction.  The two geometry equalities are exactly
what the one-step choice `Q_z = z + cube_n ⊂ z + cube_(m-h)` supplies. -/
theorem axisCube_harmonicHessianCoord_highExponent_on_triadicCube
    {d : ℕ} (hd : 3 ≤ d) (z : Vec d) (L : ℝ) (hL : 0 < L)
    (u : H1Function (axisCube z L))
    (H : HasWeakHessianOn (axisCube z L) u)
    (hu : WeakPoissonEquationOn (axisCube z L) u (fun _ ↦ 0))
    (R : TriadicCube d)
    (hcorner :
      CubeCalderonZygmund.axisCubeConcentricDepthCorner z L
          (oneStepHarmonicGainDepth d hd) =
        CubeCalderonZygmund.triadicCubeAxisCorner R)
    (hside :
      CubeCalderonZygmund.axisCubeConcentricDepthSide L
          (oneStepHarmonicGainDepth d hd) = cubeScaleFactor R)
    (i j : Fin d) :
    MemLp (fun x ↦ H.hess i j x)
        (oneStepHarmonicExponent d hd).exponent
        (normalizedCubeMeasure R) ∧
      eLpNorm (fun x ↦ H.hess i j x)
          (oneStepHarmonicExponent d hd).exponent
          (normalizedCubeMeasure R) ≤
        ((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
          eLpNorm
            (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
            (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) := by
  have h := axisCube_harmonicHessianCoord_highExponent hd z L hL u H hu i j
  rw [hcorner, hside,
    CubeCalderonZygmund.axisCubeNormalizedMeasure_triadicCube R] at h
  exact h

/-- Literal `B_z` bound for a triadic cell which is the selected concentric
contraction of an arbitrary axis cube.  This is the deterministic translated
Neumann-remainder estimate: its right side uses only the parent normalized
`L²` Hessian rows. -/
theorem axisCube_harmonicCellB_le_parentHessianRows
    {d : ℕ} (hd : 3 ≤ d) (z : Vec d) (L : ℝ) (hL : 0 < L)
    (u : H1Function (axisCube z L))
    (H : HasWeakHessianOn (axisCube z L) u)
    (hu : WeakPoissonEquationOn (axisCube z L) u (fun _ ↦ 0))
    (R : TriadicCube d)
    (hRU : openCubeSet R ⊆ axisCube z L)
    (hcorner :
      CubeCalderonZygmund.axisCubeConcentricDepthCorner z L
          (oneStepHarmonicGainDepth d hd) =
        CubeCalderonZygmund.triadicCubeAxisCorner R)
    (hside :
      CubeCalderonZygmund.axisCubeConcentricDepthSide L
          (oneStepHarmonicGainDepth d hd) = cubeScaleFactor R) :
    oneStepCellB R (H.restrict (isOpen_openCubeSet R) hRU) ≤
      cubeScaleFactor R *
        ∑ i : Fin d, ∑ _j : Fin d,
          (((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
            eLpNorm
              (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
              (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal := by
  letI : IsProbabilityMeasure (normalizedCubeMeasure R) :=
    ⟨normalizedCubeMeasure_apply_univ R⟩
  let HR : HasWeakHessianOn (openCubeSet R)
      (u.restrict (isOpen_openCubeSet R) hRU) :=
    H.restrict (isOpen_openCubeSet R) hRU
  have hq : ∀ i j : Fin d,
      MemLp (fun x ↦ HR.hess i j x)
          (oneStepHarmonicExponent d hd).exponent
          (normalizedCubeMeasure R) ∧
        eLpNorm (fun x ↦ HR.hess i j x)
            (oneStepHarmonicExponent d hd).exponent
            (normalizedCubeMeasure R) ≤
          ((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
            eLpNorm
              (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
              (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) := by
    intro i j
    simpa only [HR, HasWeakHessianOn.restrict] using
      axisCube_harmonicHessianCoord_highExponent_on_triadicCube
        hd z L hL u H hu R hcorner hside i j
  have hfour : ∀ i j : Fin d,
      MemLp (fun x ↦ HR.hess i j x) 4 (normalizedCubeMeasure R) := by
    intro i j
    exact (hq i j).1.mono_exponent (four_le_oneStepHarmonicExponent d hd)
  have hcoord : ∀ i j : Fin d,
      cubeLpNorm R 4 (fun x ↦ HR.hess i j x) ≤
        (((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
          eLpNorm
            (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
            (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal := by
    intro i j
    let v : H1Function (axisCube z L) := H.gradCoordH1Function i
    have hparentRaw : MemHilbertVectorL2 (axisCube z L)
        (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) := by
      simpa only [v, HasWeakHessianOn.gradCoordH1Function_grad_apply] using
        memHilbertVectorL2_hilbertifyVecField v.grad_memVectorL2
    have hparent :=
      CubeCalderonZygmund.memHilbertVectorL2_axisCubeNormalizedMeasure
        z hL hparentRaw
    have htop :
        ((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
          eLpNorm
            (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
            (CubeCalderonZygmund.axisCubeNormalizedMeasure z L) ≠ ∞ :=
      ENNReal.mul_ne_top
        (CubeCalderonZygmund.axisCube_harmonicEuclideanGradientGain_coefficient_ne_top
          (oneStepHarmonicEuclideanGain d hd))
        hparent.eLpNorm_ne_top
    unfold cubeLpNorm
    apply ENNReal.toReal_mono htop
    exact (eLpNorm_le_eLpNorm_of_exponent_le
      (four_le_oneStepHarmonicExponent d hd) (hq i j).1.aestronglyMeasurable).trans
        (hq i j).2
  unfold oneStepCellB
  calc
    cubeScaleFactor R * oneStepCellNormalizedHessianSize R HR ≤
        cubeScaleFactor R * oneStepCellHessianFourSize R HR :=
      mul_le_mul_of_nonneg_left
        (oneStepCellNormalizedHessianSize_le_hessianFourSize R HR hfour)
        (cubeScaleFactor_nonneg R)
    _ ≤ cubeScaleFactor R *
        ∑ i : Fin d, ∑ _j : Fin d,
          (((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
            eLpNorm
              (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
              (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)).toReal := by
      apply mul_le_mul_of_nonneg_left _ (cubeScaleFactor_nonneg R)
      unfold oneStepCellHessianFourSize
      exact Finset.sum_le_sum fun i _ ↦
        Finset.sum_le_sum fun j _ ↦ hcoord i j

/-- Literal `B_z` estimate on any triadic cell contained in the fixed
concentric harmonic-gain cube.  The only loss beyond the parent estimate is
the exact normalized-volume ratio to the power `1/(16d)`. -/
theorem axisCube_harmonicCellB_le_parentHessianRows_of_subset
    {d : ℕ} (hd : 3 ≤ d) (z : Vec d) (L : ℝ) (hL : 0 < L)
    (u : H1Function (axisCube z L))
    (H : HasWeakHessianOn (axisCube z L) u)
    (hu : WeakPoissonEquationOn (axisCube z L) u (fun _ ↦ 0))
    (R : TriadicCube d)
    (hRU : openCubeSet R ⊆ axisCube z L)
    (hRinner : openCubeSet R ⊆
      axisCube
        (CubeCalderonZygmund.axisCubeConcentricDepthCorner z L
          (oneStepHarmonicGainDepth d hd))
        (CubeCalderonZygmund.axisCubeConcentricDepthSide L
          (oneStepHarmonicGainDepth d hd))) :
    oneStepCellB R (H.restrict (isOpen_openCubeSet R) hRU) ≤
      cubeScaleFactor R *
        ∑ i : Fin d, ∑ _j : Fin d,
          ((triadicAxisNormalizedMeasureRatio R
              (CubeCalderonZygmund.axisCubeConcentricDepthSide L
                (oneStepHarmonicGainDepth d hd))) ^
              (1 / (oneStepHarmonicExponent d hd).exponent).toReal *
            (((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
              eLpNorm
                (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
                (CubeCalderonZygmund.axisCubeNormalizedMeasure z L))).toReal := by
  let zInner := CubeCalderonZygmund.axisCubeConcentricDepthCorner z L
    (oneStepHarmonicGainDepth d hd)
  let LInner := CubeCalderonZygmund.axisCubeConcentricDepthSide L
    (oneStepHarmonicGainDepth d hd)
  let HR : HasWeakHessianOn (openCubeSet R)
      (u.restrict (isOpen_openCubeSet R) hRU) :=
    H.restrict (isOpen_openCubeSet R) hRU
  letI : IsProbabilityMeasure (normalizedCubeMeasure R) :=
    ⟨normalizedCubeMeasure_apply_univ R⟩
  have hLInner : 0 < LInner :=
    CubeCalderonZygmund.axisCubeConcentricDepthSide_pos hL _
  have hq : ∀ i j : Fin d,
      MemLp (fun x ↦ HR.hess i j x)
          (oneStepHarmonicExponent d hd).exponent
          (normalizedCubeMeasure R) ∧
        eLpNorm (fun x ↦ HR.hess i j x)
            (oneStepHarmonicExponent d hd).exponent
            (normalizedCubeMeasure R) ≤
          (triadicAxisNormalizedMeasureRatio R LInner) ^
              (1 / (oneStepHarmonicExponent d hd).exponent).toReal *
            (((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
              eLpNorm
                (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
                (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)) := by
    intro i j
    have haxis := axisCube_harmonicHessianCoord_highExponent hd z L hL u H hu i j
    have hrestrict := eLpNorm_triadic_le_ratio_rpow_mul_axisCube
      R zInner LInner hLInner hRinner (oneStepHarmonicExponent d hd)
      (fun x ↦ H.hess i j x) haxis.1
    constructor
    · simpa only [HR, HasWeakHessianOn.restrict] using hrestrict.1
    · simpa only [HR, HasWeakHessianOn.restrict] using
        hrestrict.2.trans (mul_le_mul_of_nonneg_left haxis.2 (by positivity))
  have hfour : ∀ i j : Fin d,
      MemLp (fun x ↦ HR.hess i j x) 4 (normalizedCubeMeasure R) := by
    intro i j
    exact (hq i j).1.mono_exponent (four_le_oneStepHarmonicExponent d hd)
  have hcoord : ∀ i j : Fin d,
      cubeLpNorm R 4 (fun x ↦ HR.hess i j x) ≤
        ((triadicAxisNormalizedMeasureRatio R LInner) ^
            (1 / (oneStepHarmonicExponent d hd).exponent).toReal *
          (((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
            eLpNorm
              (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
              (CubeCalderonZygmund.axisCubeNormalizedMeasure z L))).toReal := by
    intro i j
    have hdown := eLpNorm_le_eLpNorm_of_exponent_le
      (four_le_oneStepHarmonicExponent d hd) (hq i j).1.aestronglyMeasurable
    have htop :
        (triadicAxisNormalizedMeasureRatio R LInner) ^
            (1 / (oneStepHarmonicExponent d hd).exponent).toReal *
          (((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
            eLpNorm
              (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
              (CubeCalderonZygmund.axisCubeNormalizedMeasure z L)) ≠ ∞ := by
      have hratioTop : triadicAxisNormalizedMeasureRatio R LInner ≠ ∞ := by
        unfold triadicAxisNormalizedMeasureRatio
        exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
          (ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (pow_pos hLInner d)))
      have hrowRaw : MemHilbertVectorL2 (axisCube z L)
          (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) := by
        let v : H1Function (axisCube z L) := H.gradCoordH1Function i
        simpa only [v, HasWeakHessianOn.gradCoordH1Function_grad_apply] using
          memHilbertVectorL2_hilbertifyVecField v.grad_memVectorL2
      have hrow := CubeCalderonZygmund.memHilbertVectorL2_axisCubeNormalizedMeasure
        z hL hrowRaw
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hratioTop)
        (ENNReal.mul_ne_top
          (CubeCalderonZygmund.axisCube_harmonicEuclideanGradientGain_coefficient_ne_top
            (oneStepHarmonicEuclideanGain d hd)) hrow.eLpNorm_ne_top)
    simpa only [cubeLpNorm] using
      ENNReal.toReal_mono htop (hdown.trans (hq i j).2)
  change cubeScaleFactor R * oneStepCellNormalizedHessianSize R HR ≤ _
  calc
    cubeScaleFactor R * oneStepCellNormalizedHessianSize R HR ≤
        cubeScaleFactor R * oneStepCellHessianFourSize R HR :=
      mul_le_mul_of_nonneg_left
        (oneStepCellNormalizedHessianSize_le_hessianFourSize R HR hfour)
        (cubeScaleFactor_nonneg R)
    _ ≤ cubeScaleFactor R *
        ∑ i : Fin d, ∑ _j : Fin d,
          ((triadicAxisNormalizedMeasureRatio R LInner) ^
              (1 / (oneStepHarmonicExponent d hd).exponent).toReal *
            (((oneStepHarmonicEuclideanGain d hd).constant * (d : ℝ≥0∞)) *
              eLpNorm
                (fun x ↦ HilbertVec.ofVec (fun k ↦ H.hess i k x)) 2
                (CubeCalderonZygmund.axisCubeNormalizedMeasure z L))).toReal := by
      apply mul_le_mul_of_nonneg_left _ (cubeScaleFactor_nonneg R)
      unfold oneStepCellHessianFourSize
      exact Finset.sum_le_sum fun i _ ↦
        Finset.sum_le_sum fun j _ ↦ hcoord i j

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
