module

public import SubdiffusiveProcess.Static.HarmonicCellMicroscopicEnergy
public import SubdiffusiveProcess.Static.HarmonicCellJoiningBounds

@[expose] public section

/-! # Native all-radius cell energy from a macroscopic budget -/
open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Fixed dimension price for the correction, smooth and transition ranges. -/
def harmonicCellJoiningPrice (d : ℕ) (delta : ℝ) : ℝ :=
  (2 * (d : ℝ)) ^ ((d : ℝ) - 1 / 2) +
    2 * ((d : ℝ) ^ ((d : ℝ) - 1 / 2) * harmonicCellCorrectionPrice d delta +
      (2 : ℝ) ^ d * (d : ℝ) ^ 2)

theorem harmonicCellJoiningPrice_nonneg (d : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta) :
    0 ≤ harmonicCellJoiningPrice d delta := by
  have hP := harmonicCellCorrectionPrice_nonneg d hdelta
  unfold harmonicCellJoiningPrice
  positivity

/-- The macroscopic quarter-exponent margin absorbs the complete native
microscopic estimate and gives literal all-radius half-exponent growth. -/
theorem harmonicCell_all_radius_energy_le {d : ℕ} [NeZero d] (hd : 2 ≤ d)
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
    (hmacro : ∀ x ∈ openCubeSet (originCube d 0), ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫⁻ y in Metric.ball x r ∩ openCubeSet (originCube d 0),
        ENNReal.ofReal (a y * vecNormSq (u.grad y)) ≤
        ENNReal.ofReal (G * B ^ 2 * (max r eps) ^ ((d : ℝ) - 1 / 4))) :
    ∀ x ∈ openCubeSet (originCube d 0), ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∫⁻ y in Metric.ball x r ∩ openCubeSet (originCube d 0),
        ENNReal.ofReal (a y * vecNormSq (u.grad y)) ≤
        ENNReal.ofReal ((G + harmonicCellJoiningPrice d delta *
          (eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d)) * B ^ 2 *
          r ^ ((d : ℝ) - 1 / 2)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hR0 := zero_lt_one.trans_le hR
  have hG0 := zero_lt_one.trans_le hG
  have hrho : 0 < eps / T := div_pos heps hT0
  have hrhoeps : eps / T ≤ eps := (div_le_iff₀ hT0).mpr (by nlinarith)
  have hrho1 : eps / T ≤ 1 := hrhoeps.trans heps1
  let S := eps ^ (1 / 4 : ℝ) * R ^ 5 * G * T ^ d
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hQ := harmonicCellJoiningPrice_nonneg d hdelta0
  have hP := harmonicCellCorrectionPrice_nonneg d hdelta0
  have htransition : (2 * (d : ℝ)) ^ ((d : ℝ) - 1 / 2) ≤ harmonicCellJoiningPrice d delta := by
    unfold harmonicCellJoiningPrice
    exact le_add_of_nonneg_right (by positivity)
  have hmicro : 2 * ((d : ℝ) ^ ((d : ℝ) - 1 / 2) * harmonicCellCorrectionPrice d delta +
      (2 : ℝ) ^ d * (d : ℝ) ^ 2) ≤ harmonicCellJoiningPrice d delta := by
    unfold harmonicCellJoiningPrice
    exact le_add_of_nonneg_left (by positivity)
  intro x hx r hr hr1
  by_cases hlarge : eps ≤ r
  · refine (hmacro x hx r hr hr1).trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := harmonicCell_large_radius_power_le (d := d) hr hr1 hlarge
    calc
      _ ≤ G * B ^ 2 * r ^ ((d : ℝ) - 1 / 2) := by gcongr
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
        exact le_add_of_nonneg_right (mul_nonneg hQ hS)
  have hrs : r ≤ eps := (lt_of_not_ge hlarge).le
  by_cases hmiddle : eps / T / (2 * (d : ℝ)) ≤ r
  · refine (hmacro x hx r hr hr1).trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := harmonicCell_transition_price_le d (by omega) heps hT1 hR hG hr hrs hmiddle
    have hpB := mul_le_mul_of_nonneg_right hp (sq_nonneg B)
    have hQbound := mul_le_mul_of_nonneg_right htransition
      (mul_nonneg (mul_nonneg hS (sq_nonneg B)) (by positivity : 0 ≤ r ^ ((d : ℝ) - 1 / 2)))
    change _ ≤ (G + harmonicCellJoiningPrice d delta * S) * B ^ 2 * r ^ ((d : ℝ) - 1 / 2)
    dsimp only [S] at hQbound
    nlinarith only [hpB, hQbound, mul_nonneg (mul_nonneg hG0.le (sq_nonneg B))
      (Real.rpow_nonneg hr.le ((d : ℝ) - 1 / 2))]
  have hrsmall : (d : ℝ) * r ≤ (eps / T) / 2 := by
    have h := lt_of_not_ge hmiddle
    have h' := (lt_div_iff₀ (by linarith : 0 < 2 * (d : ℝ))).mp h
    nlinarith only [h']
  have hrrho : r ≤ eps / T := by nlinarith only [hrsmall, hrho.le, mul_le_mul_of_nonneg_right hdR hr.le]
  have hmacrolocal := hmacro x hx (eps / T) hrho hrho1
  rw [max_eq_right hrhoeps] at hmacrolocal
  have hcorrection := harmonicCell_correction_energy_le hd a u h ha hapos heps heps1 hT hR hG
    hD hB hacoef hhgrad hlog hdelta0 hdelta hsmall hu htr x hx hmacrolocal r hr hrsmall
  have hsmooth := truncated_metric_cell_smooth_energy_le a h.grad x hr hR0.le (by positivity)
    (fun y hy => (hacoef y (unitCell_mem_closedBall hy)).2) hhgrad
  have hsprice := harmonicCell_smooth_price_le d (B := B) heps heps1 hT1 hR hG hr hrrho
  have hsmooth' := hsmooth.trans (ENNReal.ofReal_le_ofReal hsprice)
  let W := Metric.ball x r ∩ openCubeSet (originCube d 0)
  have hm : volume.restrict W ≤ volume.restrict (openCubeSet (originCube d 0)) :=
    Measure.restrict_mono Set.inter_subset_right le_rfl
  have hcsm := (aemeasurable_ofReal_weighted_vecSq a ha.measurable _
    (u.grad_memVectorL2.sub h.grad_memVectorL2)).mono_measure hm
  have hhsm := (aemeasurable_ofReal_weighted_vecSq a ha.measurable h.grad
    h.grad_memVectorL2).mono_measure hm
  have hsplit := lintegral_energy_add_le W a (fun y => u.grad y - h.grad y) h.grad
    (fun y => (hapos y).le) hcsm hhsm
  simp only [sub_add_cancel] at hsplit
  have hsum := add_le_add hcorrection hsmooth'
  have hENN : 2 * ((∫⁻ y in W, ENNReal.ofReal (a y * vecNormSq (u.grad y - h.grad y))) +
      ∫⁻ y in W, ENNReal.ofReal (a y * vecNormSq (h.grad y))) ≤
      ENNReal.ofReal (2 * (((d : ℝ) ^ ((d : ℝ) - 1 / 2) * harmonicCellCorrectionPrice d delta +
        (2 : ℝ) ^ d * (d : ℝ) ^ 2) * S * B ^ 2 * r ^ ((d : ℝ) - 1 / 2))) := by
    refine (mul_le_mul_right hsum 2).trans_eq ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    dsimp only [S]
    ring
  refine (hsplit.trans hENN).trans (ENNReal.ofReal_le_ofReal ?_)
  have h := mul_le_mul_of_nonneg_right hmicro
    (by positivity : 0 ≤ S * B ^ 2 * r ^ ((d : ℝ) - 1 / 2))
  change _ ≤ (G + harmonicCellJoiningPrice d delta * S) * B ^ 2 * r ^ ((d : ℝ) - 1 / 2)
  nlinarith only [h, mul_nonneg (mul_nonneg hG0.le (sq_nonneg B))
    (Real.rpow_nonneg hr.le ((d : ℝ) - 1 / 2))]

end SubdiffusiveProcess.Static
