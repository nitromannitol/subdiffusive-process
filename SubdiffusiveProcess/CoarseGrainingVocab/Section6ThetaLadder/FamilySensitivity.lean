module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.LocalizedFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ResponseSquareRoot
public import SubdiffusiveProcess.Frozen.Vocab.PaperScalarProbeMax

@[expose] public section

/-!
# Theta-perturbed cutoff Hölder ladder: family response

The collar extension turns the local sensitivity estimate into a statement on
the exact `TriadicCoeffFamily` carrier consumed by the multiscale
homogenization error.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Homogenization Homogenization.Book
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- Unsquared scalar-probe form of the family sensitivity estimate. -/
theorem paperScalarProbe_localizedTheta_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon alpha : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (Q : TriadicCube d) (e : Vec d)
    (he : vecNormSq e = 1) :
    paperScalarProbe Q
        (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha e ≤
      (1 + 16 * epsilon) *
          paperScalarProbe Q (aCutoffFamily M L omega) alpha e +
        15 * epsilon := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let a : Vec d → ℝ := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  let t : Vec d → ℝ := localizedNormalizedMultiplier B b theta
  let haData : ScalarCoeffOnData U a := aCutoffCoeffOnData M L omega U
  let hatData : ScalarCoeffOnData U (fun x ↦ a x * t x) :=
    (localizedThetaTriadicCoeffData M L omega hB theta htheta hepsilon.le
      (hepsilonHalf.trans_lt (by norm_num)) hnear).onCube Q
  have ha : ∀ x ∈ (U : Set (Vec d)), 0 < a x := by
    intro x _
    exact _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x
  have ht : ∀ x ∈ (U : Set (Vec d)), |t x - 1| ≤ epsilon := by
    intro x _
    exact localizedNormalizedMultiplier_near_one hepsilon.le hnear x
  have hsqrt : 0 < Real.sqrt alpha := Real.sqrt_pos.2 halpha
  have hdot : vecDot ((Real.sqrt alpha)⁻¹ • e)
      (Real.sqrt alpha • e) = 1 := by
    rw [vecDot_smul_left, vecDot_smul_right]
    change (Real.sqrt alpha)⁻¹ * (Real.sqrt alpha * vecNormSq e) = 1
    rw [he]
    field_simp
  have hmain := responseJ_mul_nearOne_le haData hatData hepsilon
    hepsilonHalf ha ht ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e)
    (by rw [hdot]; norm_num)
  change J U hatData.toCoeffOn ((Real.sqrt alpha)⁻¹ • e)
      (Real.sqrt alpha • e) ≤ _
  simpa only [hdot, mul_one] using! hmain

/-- Every scalar probe of the localized theta family satisfies the manuscript
square-root sensitivity estimate. -/
theorem sqrt_paperScalarProbe_localizedTheta_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon alpha : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (Q : TriadicCube d) (e : Vec d)
    (he : vecNormSq e = 1) :
    Real.sqrt (paperScalarProbe Q
        (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha e) ≤
      Real.sqrt (1 + 16 * epsilon) *
          Real.sqrt (paperScalarProbe Q (aCutoffFamily M L omega) alpha e) +
        Real.sqrt (15 * epsilon) := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let a : Vec d → ℝ := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  let t : Vec d → ℝ := localizedNormalizedMultiplier B b theta
  let haData : ScalarCoeffOnData U a := aCutoffCoeffOnData M L omega U
  let hatData : ScalarCoeffOnData U (fun x ↦ a x * t x) :=
    (localizedThetaTriadicCoeffData M L omega hB theta htheta hepsilon.le
      (hepsilonHalf.trans_lt (by norm_num)) hnear).onCube Q
  have ha : ∀ x ∈ (U : Set (Vec d)), 0 < a x := by
    intro x _
    exact _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x
  have ht : ∀ x ∈ (U : Set (Vec d)), |t x - 1| ≤ epsilon := by
    intro x _
    exact localizedNormalizedMultiplier_near_one hepsilon.le hnear x
  have hmain := sqrt_responseJ_normalizedProbe_mul_nearOne_le
    haData hatData hepsilon hepsilonHalf halpha ha ht e he
  change Real.sqrt (J U hatData.toCoeffOn
      ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e)) ≤ _
  exact hmain

/-- The unit-sphere maximum pays the same additive sensitivity price once,
not once per direction. -/
theorem paperScalarProbeMax_localizedTheta_le
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {B : Set (Vec d)} (hB : MeasurableSet B) {b epsilon alpha : ℝ}
    (theta : Vec d → ℝ) (htheta : ContinuousOn theta B)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon)
    (halpha : 0 < alpha) (Q : TriadicCube d) :
    paperScalarProbeMax Q
        (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha ≤
      ENNReal.ofReal (1 + 16 * epsilon) *
          paperScalarProbeMax Q (aCutoffFamily M L omega) alpha +
        ENNReal.ofReal (15 * epsilon) := by
  unfold paperScalarProbeMax
  refine iSup_le fun e => ?_
  have hprobe := paperScalarProbe_localizedTheta_le M L omega hB theta htheta
    hepsilon hepsilonHalf hnear halpha Q e e.property
  have hbase0 : 0 ≤ paperScalarProbe Q (aCutoffFamily M L omega) alpha e :=
    Ch02.responseJ_nonneg _ _ _ _
  have hA0 : 0 ≤ 1 + 16 * epsilon := by positivity
  have hB0 : 0 ≤ 15 * epsilon := by positivity
  calc
    ENNReal.ofReal (paperScalarProbe Q
        (localizedThetaCoeffFamily M L omega hB theta htheta hepsilon.le
          (hepsilonHalf.trans_lt (by norm_num)) hnear) alpha e) ≤
        ENNReal.ofReal ((1 + 16 * epsilon) *
          paperScalarProbe Q (aCutoffFamily M L omega) alpha e +
          15 * epsilon) := ENNReal.ofReal_le_ofReal hprobe
    _ = ENNReal.ofReal (1 + 16 * epsilon) *
          ENNReal.ofReal (paperScalarProbe Q (aCutoffFamily M L omega) alpha e) +
        ENNReal.ofReal (15 * epsilon) := by
      rw [ENNReal.ofReal_add (mul_nonneg hA0 hbase0) hB0,
        ENNReal.ofReal_mul hA0]
    _ ≤ ENNReal.ofReal (1 + 16 * epsilon) *
          (⨆ e : {e : Vec d // vecNormSq e = 1},
            ENNReal.ofReal (paperScalarProbe Q
              (aCutoffFamily M L omega) alpha e)) +
        ENNReal.ofReal (15 * epsilon) := by
      gcongr
      exact le_iSup (fun e : {e : Vec d // vecNormSq e = 1} ↦
        ENNReal.ofReal (paperScalarProbe Q
          (aCutoffFamily M L omega) alpha e)) e

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
