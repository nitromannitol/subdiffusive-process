module

public import SubdiffusiveProcess.Static.HarmonicCellBoundaryEnergy
public import SubdiffusiveProcess.Static.HarmonicCellGradientReadout
public import SubdiffusiveProcess.Static.HarmonicCellMicroscopicPrice

@[expose] public section

/-! # Polynomially priced microscopic native cell energy -/

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal

noncomputable section
namespace SubdiffusiveProcess.Static

/-- Dimension-only native small-contrast price. -/
def harmonicCellCorrectionPrice (d : ℕ) (delta : ℝ) : ℝ :=
  let V := (volume (smallContrastUnitBall d)).toReal
  let J := 4 * V ^ ((ENNReal.ofReal (schauderSourceExponent d (3 / 4 : ℝ))).toReal)⁻¹
  ((1 + delta) * V * (smallContrastGradientConstant d) ^ 2) *
    (4 * (3 : ℝ) ^ d + 4 * (3 : ℝ) ^ d * (d : ℝ) ^ 2 * (2 : ℝ) ^ d +
      2 * J ^ 2 * (d : ℝ) ^ 2)

theorem harmonicCellCorrectionPrice_nonneg (d : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta) :
    0 ≤ harmonicCellCorrectionPrice d delta := by
  unfold harmonicCellCorrectionPrice
  positivity

/-- The actual reflected correction, on every face and corner, has a
polynomial coefficient-envelope price with a quarter-power radius gain. -/
theorem harmonicCell_correction_energy_le {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (a : Vec d → ℝ) (u h : H1Function (openCubeSet (originCube d 0)))
    {eps T R G D delta B : ℝ}
    (ha : Continuous a) (hapos : ∀ y, 0 < a y)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hT : 2 ≤ T)
    (hR : 1 ≤ R) (hG : 1 ≤ G) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hacoef : ∀ y ∈ Metric.closedBall (0 : Vec d) (1 / 2), R⁻¹ ≤ a y ∧ a y ≤ R)
    (hhgrad : ∀ y, euclideanNorm (h.grad y) ≤ (d : ℝ) * B)
    (hlog : ∀ y ∈ Metric.closedBall (0 : Vec d) (1 / 2),
      ∀ w ∈ Metric.closedBall (0 : Vec d) (1 / 2),
        |Real.log (a y) - Real.log (a w)| ≤ D * ‖y - w‖)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d (3 / 4 : ℝ))
    (hsmall : 2 * D * (eps / T) ≤ delta)
    (hu : IsWeaklyHarmonicOn a (openCubeSet (originCube d 0)) u)
    (htr : HasZeroTraceDifferenceOn (openCubeSet (originCube d 0)) u h)
    (x : Vec d) (hx : x ∈ openCubeSet (originCube d 0))
    (hmacro : ∫⁻ y in Metric.ball x (eps / T) ∩ openCubeSet (originCube d 0),
      ENNReal.ofReal (a y * vecNormSq (u.grad y)) ≤
      ENNReal.ofReal (G * B ^ 2 * eps ^ ((d : ℝ) - 1 / 4)))
    (r : ℝ) (hr : 0 < r) (hrsmall : (d : ℝ) * r ≤ (eps / T) / 2) :
    ∫⁻ y in Metric.ball x r ∩ openCubeSet (originCube d 0),
      ENNReal.ofReal (a y * vecNormSq (u.grad y - h.grad y)) ≤
      ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) - 1 / 2) *
        harmonicCellCorrectionPrice d delta *
        (eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d) * B ^ 2 *
        r ^ ((d : ℝ) - 1 / 2)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hR0 := zero_lt_one.trans_le hR
  have hT0 : 0 < T := by linarith
  have hrho : 0 < eps / T := div_pos heps hT0
  have hrhohalf : eps / T ≤ 1 / 2 := (div_le_iff₀ hT0).mpr (by linarith)
  have hEll := isEllipticFieldOn_scalarCoeffField_of_continuousOn
    (isOpen_openCubeSet _).measurableSet ha.continuousOn (inv_pos.mpr hR0)
    (fun y hy => hacoef y (unitCell_mem_closedBall hy))
  have hlocal := local_boundaryCorrection_budget u h a hR0 (by positivity) (by positivity)
    hrho (fun y hy => (hacoef y (unitCell_mem_closedBall hy)).1) hhgrad x hmacro
  have hraw := boundaryCorrection_energy_growth hd a u h ha hapos hEll hu htr hR0.le
    (by positivity) (by positivity) hD (fun y hy => (hacoef y hy).2) hhgrad hlog
    hdelta0 hdelta hrho hrhohalf hsmall x hx hlocal ((d : ℝ) * r) (by positivity) hrsmall
  let V := (volume (smallContrastUnitBall d)).toReal
  let J := 4 * V ^ ((ENNReal.ofReal (schauderSourceExponent d (3 / 4 : ℝ))).toReal)⁻¹
  let C := (1 + delta) * V * (smallContrastGradientConstant d) ^ 2
  have hkinv : (a x)⁻¹ ≤ R :=
    (inv_le_comm₀ (hapos x) hR0).mpr (hacoef x (unitCell_mem_closedBall hx)).1
  have hp := harmonicCell_nativeMicroscopicPrice_le d (C := C) (J := J)
    (by dsimp only [C, V]; positivity) (by dsimp only [J]; positivity)
    heps heps1 (by linarith : 1 ≤ T) hR hG (hapos x)
    (hacoef x (unitCell_mem_closedBall hx)).2 hkinv hB
  have hprice : a x * (eps / T) ^ (1 / 2 : ℝ) * (1 + delta) * V *
      (smallContrastGradientConstant d *
        (Real.sqrt (((eps / T) ^ d)⁻¹ * ((3 : ℝ) ^ d *
          (2 * (R * (G * B ^ 2 * eps ^ ((d : ℝ) - 1 / 4)) +
            ((d : ℝ) * B) ^ 2 * (2 * (eps / T)) ^ d)))) +
          4 * V ^ ((ENNReal.ofReal (schauderSourceExponent d (3 / 4 : ℝ))).toReal)⁻¹ *
            ((a x)⁻¹ * (R * ((d : ℝ) * B))))) ^ 2 ≤
      harmonicCellCorrectionPrice d delta *
        (eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d) * B ^ 2 := by
    convert hp using 1 <;> dsimp only [C, J, harmonicCellCorrectionPrice, V] ;
      simp only [mul_assoc, mul_pow]
  calc
    _ ≤ ∫⁻ y in euclideanBall x ((d : ℝ) * r) ∩ openCubeSet (originCube d 0),
        ENNReal.ofReal (a y * vecNormSq (u.grad y - h.grad y)) :=
      lintegral_mono_set (Set.inter_subset_inter_left _
        (metricBall_subset_euclideanBall_dim (by omega) x hr))
    _ ≤ _ := hraw.trans (ENNReal.ofReal_le_ofReal (by
      have heq : ((d : ℝ) * r) ^ ((d : ℝ) - 1 / 2) =
          (d : ℝ) ^ ((d : ℝ) - 1 / 2) * r ^ ((d : ℝ) - 1 / 2) :=
        Real.mul_rpow (Nat.cast_nonneg _) hr.le
      rw [heq]
      have h := mul_le_mul_of_nonneg_right hprice
        (by positivity : 0 ≤ (d : ℝ) ^ ((d : ℝ) - 1 / 2) * r ^ ((d : ℝ) - 1 / 2))
      dsimp only [V] at h
      nlinarith only [h]))

end SubdiffusiveProcess.Static
