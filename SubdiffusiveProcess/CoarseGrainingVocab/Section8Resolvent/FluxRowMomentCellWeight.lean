import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowMomentGeometric
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepEllipticityFactorMoment




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A separated nonnegative majorant for the real cell weight. -/
def fluxRowMomentCellMajorant (E1 E2 alambda : ℝ≥0∞) : ℝ≥0∞ :=
  3 * (1 + E1 ^ 4 + E2 ^ 4) + E1 ^ 2 * alambda ^ 2

/-- The square of a three-term sum is bounded by three times the sum of
squares. -/
theorem fluxRowRieszCellWeight_le_quartic_majorant
    (E1 E2 ahom lambdaInv : ℝ) :
    fluxRowRieszCellWeight E1 E2 ahom lambdaInv ≤
      3 * (1 + E1 ^ 4 + E2 ^ 4) + E1 ^ 2 * (ahom * lambdaInv) ^ 2 := by
  unfold fluxRowRieszCellWeight
  have h1 : 2 * E1 ^ 2 ≤ E1 ^ 4 + 1 := by
    nlinarith [sq_nonneg (E1 ^ 2 - 1)]
  have h2 : 2 * E2 ^ 2 ≤ E2 ^ 4 + 1 := by
    nlinarith [sq_nonneg (E2 ^ 2 - 1)]
  have h12 : 2 * E1 ^ 2 * E2 ^ 2 ≤ E1 ^ 4 + E2 ^ 4 := by
    nlinarith [sq_nonneg (E1 ^ 2 - E2 ^ 2)]
  nlinarith [h1, h2, h12]

/-- `ENNReal.ofReal` form of the quartic cell-weight majorant. -/
theorem ofReal_fluxRowRieszCellWeight_le_fluxRowMomentCellMajorant
    (E1 E2 ahom lambdaInv : ℝ) (hE1 : 0 ≤ E1) (hE2 : 0 ≤ E2)
    (halambda : 0 ≤ ahom * lambdaInv) :
    ENNReal.ofReal (fluxRowRieszCellWeight E1 E2 ahom lambdaInv) ≤
      fluxRowMomentCellMajorant (ENNReal.ofReal E1) (ENNReal.ofReal E2)
        (ENNReal.ofReal (ahom * lambdaInv)) := by
  have heq :
      ENNReal.ofReal
          (3 * (1 + E1 ^ 4 + E2 ^ 4) + E1 ^ 2 * (ahom * lambdaInv) ^ 2) =
        fluxRowMomentCellMajorant (ENNReal.ofReal E1) (ENNReal.ofReal E2)
          (ENNReal.ofReal (ahom * lambdaInv)) := by
    have hA : 0 ≤ 3 * (1 + E1 ^ 4 + E2 ^ 4) := by positivity
    have hB : 0 ≤ E1 ^ 2 * (ahom * lambdaInv) ^ 2 := by positivity
    have hC : 0 ≤ 1 + E1 ^ 4 := by positivity
    rw [fluxRowMomentCellMajorant, ENNReal.ofReal_add hA hB,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ENNReal.ofReal_mul (sq_nonneg E1),
      ENNReal.ofReal_add hC (by positivity),
      ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow hE1 4, ENNReal.ofReal_pow hE2 4,
      ENNReal.ofReal_pow hE1 2, ENNReal.ofReal_pow halambda 2]
  rw [← heq]
  exact ENNReal.ofReal_le_ofReal
    (fluxRowRieszCellWeight_le_quartic_majorant E1 E2 ahom lambdaInv)

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- Fourth powers turn a `p`-moment into a `4p`-moment in the paper carrier. -/
theorem paperENNRealLpNorm_pow_four_eq
    {p : ℝ} (hp : 0 < p) (X : Omega → ℝ≥0∞) :
    paperENNRealLpNorm mu p (fun omega ↦ X omega ^ 4) =
      (paperENNRealLpNorm mu (4 * p) X) ^ 4 := by
  have h2p : 0 < 2 * p := mul_pos (by norm_num) hp
  calc
    paperENNRealLpNorm mu p (fun omega ↦ X omega ^ 4) =
        paperENNRealLpNorm mu p (fun omega ↦ (X omega ^ 2) ^ 2) := by
          congr 2
          funext omega
          ring
    _ = (paperENNRealLpNorm mu (2 * p) (fun omega ↦ X omega ^ 2)) ^ 2 :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_sq
        mu hp (fun omega ↦ X omega ^ 2)
    _ = ((paperENNRealLpNorm mu (2 * (2 * p)) X) ^ 2) ^ 2 := by
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_sq
        mu h2p X]
    _ = (paperENNRealLpNorm mu (4 * p) X) ^ 4 := by ring_nf

/-- Moment algebra for the separated cell majorant.  The conclusion makes the
required order `4 * p` explicit for all three basic observables. -/
theorem paperENNRealLpNorm_fluxRowMomentCellMajorant_le
    [IsProbabilityMeasure mu]
    {p : ℝ} (hp : 1 ≤ p)
    (E1 E2 alambda : Omega → ℝ≥0∞)
    (hE1 : Measurable E1) (hE2 : Measurable E2)
    (halambda : Measurable alambda) :
    paperENNRealLpNorm mu p
        (fun omega ↦ fluxRowMomentCellMajorant
          (E1 omega) (E2 omega) (alambda omega)) ≤
      3 * (1 + (paperENNRealLpNorm mu (4 * p) E1) ^ 4 +
          (paperENNRealLpNorm mu (4 * p) E2) ^ 4) +
        (paperENNRealLpNorm mu (4 * p) E1) ^ 2 *
          (paperENNRealLpNorm mu (4 * p) alambda) ^ 2 := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have h2p : 0 < 2 * p := mul_pos (by norm_num) hp0
  let A : Omega → ℝ≥0∞ :=
    fun omega ↦ 3 * (1 + E1 omega ^ 4 + E2 omega ^ 4)
  let B : Omega → ℝ≥0∞ :=
    fun omega ↦ E1 omega ^ 2 * alambda omega ^ 2
  have hA : Measurable A := by
    exact measurable_const.mul
      ((measurable_const.add (hE1.pow_const 4)).add (hE2.pow_const 4))
  have hB : Measurable B := (hE1.pow_const 2).mul (halambda.pow_const 2)
  have hadd := paperENNRealLpNorm_add_le mu hp hA.aemeasurable hB.aemeasurable
  have hsum1 :
      paperENNRealLpNorm mu p (fun omega ↦ 1 + E1 omega ^ 4) ≤
        paperENNRealLpNorm mu p (fun _ : Omega ↦ 1) +
          paperENNRealLpNorm mu p (fun omega ↦ E1 omega ^ 4) :=
    paperENNRealLpNorm_add_le mu hp
      measurable_const.aemeasurable (hE1.pow_const 4).aemeasurable
  have hsum2 :
      paperENNRealLpNorm mu p
          (fun omega ↦ (1 + E1 omega ^ 4) + E2 omega ^ 4) ≤
        paperENNRealLpNorm mu p (fun omega ↦ 1 + E1 omega ^ 4) +
          paperENNRealLpNorm mu p (fun omega ↦ E2 omega ^ 4) :=
    paperENNRealLpNorm_add_le mu hp
      (measurable_const.add (hE1.pow_const 4)).aemeasurable
      (hE2.pow_const 4).aemeasurable
  rw [paperENNRealLpNorm_one mu p] at hsum1
  have hAnorm : paperENNRealLpNorm mu p A ≤
      3 * (1 + paperENNRealLpNorm mu p (fun omega ↦ E1 omega ^ 4) +
        paperENNRealLpNorm mu p (fun omega ↦ E2 omega ^ 4)) := by
    rw [paperENNRealLpNorm_const_mul_eq mu hp0 3 _
      ((measurable_const.add (hE1.pow_const 4)).add (hE2.pow_const 4))]
    exact mul_le_mul_right (hsum2.trans (add_le_add hsum1 le_rfl)) 3
  have hBnorm : paperENNRealLpNorm mu p B ≤
      paperENNRealLpNorm mu (2 * p) (fun omega ↦ E1 omega ^ 2) *
        paperENNRealLpNorm mu (2 * p) (fun omega ↦ alambda omega ^ 2) :=
    paperENNRealLpNorm_mul_le_two_mul mu hp0
      (hE1.pow_const 2).aemeasurable (halambda.pow_const 2).aemeasurable
  calc
    paperENNRealLpNorm mu p
        (fun omega ↦ fluxRowMomentCellMajorant
          (E1 omega) (E2 omega) (alambda omega)) =
        paperENNRealLpNorm mu p (fun omega ↦ A omega + B omega) := rfl
    _ ≤ paperENNRealLpNorm mu p A + paperENNRealLpNorm mu p B := hadd
    _ ≤ 3 * (1 + paperENNRealLpNorm mu p (fun omega ↦ E1 omega ^ 4) +
          paperENNRealLpNorm mu p (fun omega ↦ E2 omega ^ 4)) +
        paperENNRealLpNorm mu (2 * p) (fun omega ↦ E1 omega ^ 2) *
          paperENNRealLpNorm mu (2 * p) (fun omega ↦ alambda omega ^ 2) := by
      exact add_le_add hAnorm hBnorm
    _ = 3 * (1 + (paperENNRealLpNorm mu (4 * p) E1) ^ 4 +
          (paperENNRealLpNorm mu (4 * p) E2) ^ 4) +
        (paperENNRealLpNorm mu (4 * p) E1) ^ 2 *
          (paperENNRealLpNorm mu (4 * p) alambda) ^ 2 := by
      rw [paperENNRealLpNorm_pow_four_eq hp0 E1,
        paperENNRealLpNorm_pow_four_eq hp0 E2,
        SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_sq
          mu h2p E1,
        SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.paperENNRealLpNorm_sq
          mu h2p alambda]
      ring_nf

/-- A fixed-cell weight moment from its three component moments.  The third
component is exactly the combined ellipticity observable
`ahom * lambdaInv`; no untranslated ellipticity estimate is hidden here. -/
theorem paperENNRealLpNorm_fluxRowRieszCellWeight_le_of_component_bounds
    [IsProbabilityMeasure mu]
    {p : ℝ} (hp : 1 ≤ p)
    (E1 E2 lambdaInv : Omega → ℝ) (ahom : ℝ)
    (hE1 : Measurable E1) (hE2 : Measurable E2)
    (hlambdaInv : Measurable lambdaInv)
    (hE1nonneg : ∀ omega, 0 ≤ E1 omega)
    (hE2nonneg : ∀ omega, 0 ≤ E2 omega)
    (halambdaNonneg : ∀ omega, 0 ≤ ahom * lambdaInv omega)
    {B1 B2 BA : ℝ≥0∞}
    (hB1 : paperENNRealLpNorm mu (4 * p)
      (fun omega ↦ ENNReal.ofReal (E1 omega)) ≤ B1)
    (hB2 : paperENNRealLpNorm mu (4 * p)
      (fun omega ↦ ENNReal.ofReal (E2 omega)) ≤ B2)
    (hBA : paperENNRealLpNorm mu (4 * p)
      (fun omega ↦ ENNReal.ofReal (ahom * lambdaInv omega)) ≤ BA) :
    paperENNRealLpNorm mu p (fun omega ↦ ENNReal.ofReal
        (fluxRowRieszCellWeight
          (E1 omega) (E2 omega) ahom (lambdaInv omega))) ≤
      3 * (1 + B1 ^ 4 + B2 ^ 4) + B1 ^ 2 * BA ^ 2 := by
  let X1 : Omega → ℝ≥0∞ := fun omega ↦ ENNReal.ofReal (E1 omega)
  let X2 : Omega → ℝ≥0∞ := fun omega ↦ ENNReal.ofReal (E2 omega)
  let XA : Omega → ℝ≥0∞ :=
    fun omega ↦ ENNReal.ofReal (ahom * lambdaInv omega)
  have hX1 : Measurable X1 := ENNReal.measurable_ofReal.comp hE1
  have hX2 : Measurable X2 := ENNReal.measurable_ofReal.comp hE2
  have hXA : Measurable XA :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hlambdaInv)
  have hpoint : ∀ᵐ omega ∂mu,
      ENNReal.ofReal (fluxRowRieszCellWeight
          (E1 omega) (E2 omega) ahom (lambdaInv omega)) ≤
        fluxRowMomentCellMajorant (X1 omega) (X2 omega) (XA omega) :=
    Filter.Eventually.of_forall fun omega ↦
      ofReal_fluxRowRieszCellWeight_le_fluxRowMomentCellMajorant
        (E1 omega) (E2 omega) ahom (lambdaInv omega)
          (hE1nonneg omega) (hE2nonneg omega) (halambdaNonneg omega)
  have hmono := paperENNRealLpNorm_mono_ae mu (zero_le_one.trans hp) hpoint
  have hmajorant := paperENNRealLpNorm_fluxRowMomentCellMajorant_le
    (mu := mu) hp X1 X2 XA hX1 hX2 hXA
  refine hmono.trans (hmajorant.trans ?_)
  dsimp only [X1, X2, XA] at hB1 hB2 hBA ⊢
  gcongr

/-! At `p = 2`, the three hypotheses above are literally eighth-moment
hypotheses because `4 * (2 : ℝ) = 8`. -/

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
