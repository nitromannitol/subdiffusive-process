module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryAdaptiveForcedEquation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCanonicalDensityPrices

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A canonical cutoff cannot increase the scalar comparison-field energy.
The right side is expressed through the public coefficient representative
used by the rest of the Chapter-3 energy API. -/
theorem volumeAverage_boundaryCoerciveDatumDensity_localCanonicalFun_le_energy
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (h : H1Function (openCubeSet Q)) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveDatumDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter)
          h.grad) ≤
      cubeAverage Q (coefficientEnergyDensity
        (publicCoeffField Q (aCutoffFamily M L omega)) h.grad) := by
  let eta := coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter
  let e : Vec d → ℝ := fun x =>
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (h.grad x)
  have hdatum : IntegrableOn
      (boundaryCoerciveDatumDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta h.grad)
      (openCubeSet Q) := by
    simpa only [boundaryCoerciveDatumDensity, eta] using!
      integrableOn_aCutoff_sqCutoff_vecNormSq M L omega h.grad_memVectorL2
        (coarseCaccioppoliLocalCanonicalFun_smooth R center hinner hinnerOuter)
        (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport R center hinner
          hinnerOuter)
  have he : IntegrableOn e (openCubeSet Q) := by
    simpa only [e] using! integrableOn_aCutoff_energy M L omega Q h
  have hle : volumeAverage (openCubeSet Q)
      (boundaryCoerciveDatumDensity
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega) eta h.grad) ≤
      volumeAverage (openCubeSet Q) e := by
    apply volumeAverage_le_volumeAverage_of_le_on
      (measurableSet_openCubeSet Q) hdatum he
    intro x _
    have heta0 : 0 ≤ eta x :=
      coarseCaccioppoliLocalCanonicalFun_nonneg R center rhoInner rhoOuter x
    have heta1 : eta x ≤ 1 :=
      coarseCaccioppoliLocalCanonicalFun_le_one R center rhoInner rhoOuter x
    have ha0 : 0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x :=
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x).le
    have hnorm : 0 ≤ vecNormSq (h.grad x) := vecNormSq_nonneg _
    have hetaSq : eta x ^ 2 ≤ 1 := by nlinarith only [heta0, heta1]
    have henergy0 :
        0 ≤ SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (h.grad x) :=
      mul_nonneg ha0 hnorm
    dsimp only [boundaryCoerciveDatumDensity, e, eta]
    calc
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x *
          coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter x ^ 2 *
          vecNormSq (h.grad x) =
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (h.grad x)) *
          eta x ^ 2 := by ring
      _ ≤ (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (h.grad x)) * 1 :=
        mul_le_mul_of_nonneg_left hetaSq henergy0
      _ = SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x * vecNormSq (h.grad x) :=
        mul_one _
  calc
    _ ≤ volumeAverage (openCubeSet Q) e := hle
    _ = cubeAverage Q e := volumeAverage_openCubeSet_eq_cubeAverage Q e
    _ = cubeAverage Q (coefficientEnergyDensity
          (publicCoeffField Q (aCutoffFamily M L omega)) h.grad) := by
      apply cubeAverage_eq_of_ae_eq_on_cubeSet
      filter_upwards
        [publicCoeffField_ae_eq_cubeSet Q (aCutoffFamily M L omega)] with x hx
      dsimp only [e]
      unfold coefficientEnergyDensity
      rw [hx]
      simp [aCutoffFamily, aCutoffTriadicData,
        ScalarTriadicCoeffData.toTriadicCoeffFamily, aCutoffCoeffOnData,
        ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
        Ch02.symmPart_scalarMatrix, matVecMul_scalarMatrix,
        vecDot_smul_right, vecNormSq]

/-- An upper bound on the normalized inverse coefficient prices the canonical
force density.  This is the deterministic interface consumed by the
good-event shell-ratio estimate. -/
theorem volumeAverage_boundaryCoerciveForceDensity_localCanonicalFun_le_ratio
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q R : TriadicCube d) (center : Vec d) {rhoInner rhoOuter sigma B : ℝ}
    (hinner : 0 < rhoInner) (hinnerOuter : rhoInner < rhoOuter)
    (hsigma : 0 < sigma)
    (g : Vec d → Vec d) (hg : MemVectorL2 (openCubeSet Q) g)
    (hratio : ∀ x ∈ openCubeSet Q,
      sigma / SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x ≤ B) :
    volumeAverage (openCubeSet Q)
        (boundaryCoerciveForceDensity
          (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
          (coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter) g) ≤
      volumeAverage (openCubeSet Q)
        (fun x => sigma⁻¹ * B * vecNormSq (g x)) := by
  apply volumeAverage_le_volumeAverage_of_le_on (measurableSet_openCubeSet Q)
  · exact integrableOn_aCutoff_boundaryCoerciveForceDensity M L omega hg
      (coarseCaccioppoliLocalCanonicalFun_smooth R center hinner hinnerOuter)
      (coarseCaccioppoliLocalCanonicalFun_hasCompactSupport R center hinner
        hinnerOuter)
  · exact (by
      have hsq : IntegrableOn (fun x => vecNormSq (g x)) (openCubeSet Q) := by
        simpa [vecNormSq] using! integrableOn_vecDot_of_memVectorL2 hg hg
      exact hsq.const_mul (sigma⁻¹ * B))
  · intro x hx
    let a := SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x
    let eta := coarseCaccioppoliLocalCanonicalFun R center rhoInner rhoOuter
    have ha : 0 < a := SubdiffusiveProcess.Frozen.Assumptions.aCutoff_pos M L omega x
    have heta0 : 0 ≤ eta x :=
      coarseCaccioppoliLocalCanonicalFun_nonneg R center rhoInner rhoOuter x
    have heta1 : eta x ≤ 1 :=
      coarseCaccioppoliLocalCanonicalFun_le_one R center rhoInner rhoOuter x
    have hinv : a⁻¹ ≤ sigma⁻¹ * B := by
      calc
        a⁻¹ = sigma⁻¹ * (sigma / a) := by field_simp
        _ ≤ sigma⁻¹ * B :=
          mul_le_mul_of_nonneg_left (hratio x hx) (inv_nonneg.mpr hsigma.le)
    have hsq : eta x ^ 2 ≤ 1 := by nlinarith only [heta0, heta1]
    have hnorm : 0 ≤ vecNormSq (g x) := vecNormSq_nonneg _
    have hleft : a⁻¹ * eta x ^ 2 ≤ sigma⁻¹ * B := by
      calc
        a⁻¹ * eta x ^ 2 ≤ a⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr ha.le)
        _ = a⁻¹ := mul_one _
        _ ≤ sigma⁻¹ * B := hinv
    dsimp only [boundaryCoerciveForceDensity, a, eta]
    exact mul_le_mul_of_nonneg_right hleft hnorm



theorem volumeAverage_vecNormSq_eq_boundaryNormalizedEuclideanL2_sq
    (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    volumeAverage (openCubeSet Q) (fun x ↦ vecNormSq (F x)) =
      boundaryNormalizedEuclideanL2 Q F ^ 2 := by
  have hbase := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
    (Q := Q) (p := (2 : ℝ≥0∞))
    (f := fun x ↦ HilbertVec.ofVec (F x))
    (by norm_num) (by norm_num) hF
  rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num] at hbase
  simp only [Real.rpow_natCast] at hbase
  rw [volumeAverage_openCubeSet_eq_cubeAverage, boundaryNormalizedEuclideanL2,
    hbase]
  apply congrArg (cubeAverage Q)
  funext x
  rw [HilbertVec.norm_sq_ofVec]
  rfl

/-- A nonnegative constant coefficient can be pulled through the normalized
force-density average and read as the square of the Euclidean `L²` carrier. -/
theorem volumeAverage_const_mul_vecNormSq_eq_boundaryNormalizedEuclideanL2_sq
    (Q : TriadicCube d) (F : Vec d → Vec d) (c : ℝ)
    (hF : MemLp (fun x ↦ HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q)) :
    volumeAverage (openCubeSet Q) (fun x ↦ c * vecNormSq (F x)) =
      c * boundaryNormalizedEuclideanL2 Q F ^ 2 := by
  unfold volumeAverage
  rw [integral_const_mul]
  change (volume (openCubeSet Q)).toReal⁻¹ *
      (c * ∫ x in openCubeSet Q, vecNormSq (F x) ∂volume) = _
  rw [← mul_assoc, mul_comm (volume (openCubeSet Q)).toReal⁻¹ c,
    mul_assoc]
  change c * volumeAverage (openCubeSet Q) (fun x ↦ vecNormSq (F x)) = _
  rw [volumeAverage_vecNormSq_eq_boundaryNormalizedEuclideanL2_sq Q F hF]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
