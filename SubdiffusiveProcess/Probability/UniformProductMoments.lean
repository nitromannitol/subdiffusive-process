import SubdiffusiveProcess.Probability.LayerInfluenceTransfer
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Explicit product moment bounds

Hölder and the triangle inequality preserve supplied deterministic constants.
These estimates do not supply any model-specific moment hypothesis.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace SubdiffusiveProcess.Probability

/-- Two moments at twice the target order bound the moment of a product. -/
theorem eLpNorm_mul_le_of_doubled_bounds
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P)
    {BX BY : ℝ} (hx : eLpNorm X (2 * p) P ≤ ENNReal.ofReal BX)
    (hy : eLpNorm Y (2 * p) P ≤ ENNReal.ofReal BY) :
    eLpNorm (fun om => X om * Y om) p P ≤ ENNReal.ofReal BX * ENNReal.ofReal BY := by
  apply eLpNorm_le_of_ae_abs_le_mul hX.norm hY.norm
    (Eventually.of_forall fun om => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]) hp hpt
  · simpa only [eLpNorm_norm] using hx
  · simpa only [eLpNorm_norm] using hy

/-- Adding one to a scalar multiple costs at most one plus the scaled moment bound. -/
theorem eLpNorm_one_add_const_mul_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hX : AEStronglyMeasurable X P) {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hx : eLpNorm X p P ≤ ENNReal.ofReal B) :
    eLpNorm (fun om => 1 + a * X om) p P ≤ ENNReal.ofReal (1 + a * B) := by
  have hn1 : eLpNorm (fun _ : Ω => (1 : ℝ)) p P ≤ 1 := by
    simpa only [measure_univ, ENNReal.one_rpow, mul_one, ENNReal.coe_one,
      ENNReal.ofReal_one] using
      (eLpNorm_le_of_ae_bound (μ := P) (p := p) (f := fun _ : Ω => (1 : ℝ))
        (C := 1) (Eventually.of_forall fun _ => by rw [norm_one]))
  calc
    _ ≤ eLpNorm (fun _ : Ω => (1 : ℝ)) p P + eLpNorm (fun om => a * X om) p P :=
      eLpNorm_add_le aestronglyMeasurable_const (hX.const_mul a) hp
    _ ≤ 1 + ENNReal.ofReal a * ENNReal.ofReal B := by
      have hs : eLpNorm (fun om => a * X om) p P = ENNReal.ofReal a * eLpNorm X p P := by
        change eLpNorm (a • X) p P = _
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal ha]
      rw [hs]
      exact add_le_add hn1 (mul_le_mul_right hx _)
    _ = ENNReal.ofReal (1 + a * B) := by
      rw [ENNReal.ofReal_add zero_le_one (mul_nonneg ha hB), ENNReal.ofReal_one,
        ENNReal.ofReal_mul ha]

/-- Three supplied moment bounds control a product with an affine third factor. -/
theorem eLpNorm_mul_mul_one_add_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y Z : Ω → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P)
    (hZ : AEStronglyMeasurable Z P)
    {a BX BY BZ : ℝ} (ha : 0 ≤ a) (hBX : 0 ≤ BX) (hBY : 0 ≤ BY) (hBZ : 0 ≤ BZ)
    (hx : eLpNorm X (4 * p) P ≤ ENNReal.ofReal BX)
    (hy : eLpNorm Y (4 * p) P ≤ ENNReal.ofReal BY)
    (hz : eLpNorm Z (2 * p) P ≤ ENNReal.ofReal BZ) :
    eLpNorm (fun om => X om * Y om * (1 + a * Z om)) p P ≤
      ENNReal.ofReal (BX * BY * (1 + a * BZ)) := by
  have hp2 : 1 ≤ 2 * p := one_le_mul_of_one_le_of_one_le (by norm_num) hp
  have hp2t : 2 * p ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hpt
  have hfour : (2 : ℝ≥0∞) * (2 * p) = 4 * p := by rw [← mul_assoc]; norm_num
  have hxy : eLpNorm (fun om => X om * Y om) (2 * p) P ≤ ENNReal.ofReal (BX * BY) := by
    rw [ENNReal.ofReal_mul hBX]
    apply eLpNorm_mul_le_of_doubled_bounds hp2 hp2t hX hY
    · simpa only [hfour] using hx
    · simpa only [hfour] using hy
  have hz' := eLpNorm_one_add_const_mul_le hp2 hZ ha hBZ hz
  have hprod := eLpNorm_mul_le_of_doubled_bounds hp hpt (hX.mul hY)
    ((hZ.const_mul a).const_add 1) hxy hz'
  exact hprod.trans_eq (ENNReal.ofReal_mul (mul_nonneg hBX hBY)).symm

end SubdiffusiveProcess.Probability
