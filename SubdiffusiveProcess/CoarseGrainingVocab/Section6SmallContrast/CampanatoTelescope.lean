import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.BallCampanato
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanControlReduction
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The repaired Campanato telescope

D-054 restricts `alpha` to `[1/2,1)`.  Consequently the dyadic ratio
`2^{-alpha}` is uniformly below `3/4`, so the geometric tail costs at most
`4`, independently of `alpha`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

open MeasureTheory Homogenization Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

noncomputable section

variable {d : ℕ}

def smallContrastCampanatoRatio (alpha : ℝ) : ℝ := (1 / 2 : ℝ) ^ alpha

theorem smallContrastCampanatoRatio_nonneg (alpha : ℝ) :
    0 ≤ smallContrastCampanatoRatio alpha :=
  Real.rpow_nonneg (by norm_num) _

theorem smallContrastCampanatoRatio_lt_one {alpha : ℝ} (halpha : 0 < alpha) :
    smallContrastCampanatoRatio alpha < 1 := by
  exact Real.rpow_lt_one (by norm_num) (by norm_num) halpha

theorem smallContrastCampanatoRatio_le_three_quarters
    {alpha : ℝ} (halpha : (1 / 2 : ℝ) ≤ alpha) :
    smallContrastCampanatoRatio alpha ≤ 3 / 4 := by
  have hmono : smallContrastCampanatoRatio alpha ≤ (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) halpha
  have hsquare : ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hsqrt : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) ≤ 3 / 4 := by
    nlinarith [hsquare]
  exact hmono.trans hsqrt

theorem inv_one_sub_smallContrastCampanatoRatio_le_four
    {alpha : ℝ} (halpha : (1 / 2 : ℝ) ≤ alpha) :
    (1 - smallContrastCampanatoRatio alpha)⁻¹ ≤ 4 := by
  have hq := smallContrastCampanatoRatio_le_three_quarters halpha
  have hden : 1 / 4 ≤ 1 - smallContrastCampanatoRatio alpha := by linarith
  have hdenpos : 0 < 1 - smallContrastCampanatoRatio alpha := by linarith
  have h := (inv_le_inv₀ hdenpos (by norm_num : (0 : ℝ) < 1 / 4)).2 hden
  norm_num at h ⊢
  exact h

theorem smallContrastDyadicRadius_rpow
    {R alpha : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    smallContrastDyadicRadius R n ^ alpha =
      R ^ alpha * smallContrastCampanatoRatio alpha ^ n := by
  rw [smallContrastDyadicRadius, Real.mul_rpow hR (by positivity)]
  unfold smallContrastCampanatoRatio
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 2
  ring

def smallContrastCampanatoAverage (u : Vec d → ℝ) (x : Vec d) (n : ℕ) : ℝ :=
  volumeAverage
    (Metric.ball x (smallContrastDyadicRadius (smallContrastCampanatoRadius d) n)) u

def smallContrastCampanatoRepresentative
    (u : Vec d → ℝ) (x : Vec d) : ℝ :=
  limUnder atTop (smallContrastCampanatoAverage (d := d) u x)

theorem metricBall_dyadic_subset_unit [NeZero d]
    {x : Vec d} (hx : x ∈ smallContrastBall d (1 / 2)) (n : ℕ) :
    Metric.ball x (smallContrastDyadicRadius (smallContrastCampanatoRadius d) n) ⊆
      smallContrastUnitBall d := by
  have hR := smallContrastCampanatoRadius_pos (d := d)
  have hrle : smallContrastDyadicRadius (smallContrastCampanatoRadius d) n ≤
      smallContrastCampanatoRadius d := smallContrastDyadicRadius_le hR.le n
  have hdr : (d : ℝ) * smallContrastDyadicRadius (smallContrastCampanatoRadius d) n < 1 / 2 := by
    have hthree : 3 * (d : ℝ) * smallContrastCampanatoRadius d = 1 / 4 :=
      three_mul_dimension_mul_campanatoRadius (d := d)
    have hdpos : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    have := mul_le_mul_of_nonneg_left hrle hdpos.le
    nlinarith
  exact subset_trans (metricBall_subset_euclideanBall_dimension x _)
    (subset_trans (euclideanBall_subset_euclideanBall
      (mul_nonneg (Nat.cast_nonneg d)
        (smallContrastDyadicRadius_pos hR n).le) hdr)
      (euclideanBall_half_subset_unit_of_mem_half hx))

private theorem memLp_toFun_on_dyadicBall [NeZero d]
    (u : H1Function (smallContrastUnitBall d))
    {x : Vec d} (hx : x ∈ smallContrastBall d (1 / 2)) (n : ℕ) :
    MemLp u.toFun 2 (volume.restrict
      (Metric.ball x (smallContrastDyadicRadius (smallContrastCampanatoRadius d) n))) :=
  u.memL2.mono_measure
    (Measure.restrict_mono (metricBall_dyadic_subset_unit hx n) le_rfl)

/-- Consecutive means differ by the Campanato oscillation on the parent ball. -/
theorem dist_smallContrastCampanatoAverage_succ_le [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u)
    {x : Vec d} (hx : x ∈ smallContrastBall d (1 / 2)) (n : ℕ) :
    dist (smallContrastCampanatoAverage (d := d) u.toFun x n)
        (smallContrastCampanatoAverage (d := d) u.toFun x (n + 1)) ≤
      (halfBallVolumePrice d * smallContrastCampanatoConstant d * K *
        smallContrastCampanatoRadius d ^ alpha) *
          smallContrastCampanatoRatio alpha ^ n := by
  let r := smallContrastDyadicRadius (smallContrastCampanatoRadius d) n
  let W := Metric.ball x r
  let V := Metric.ball x (r / 2)
  have hR := smallContrastCampanatoRadius_pos (d := d)
  have hr : 0 < r := smallContrastDyadicRadius_pos hR n
  have hV : 0 < r / 2 := by positivity
  have hsub : V ⊆ W := Metric.ball_subset_ball (by linarith)
  have huW := memLp_toFun_on_dyadicBall u hx n
  have huV : MemLp u.toFun 2 (volume.restrict V) := by
    exact huW.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hWtop : volume W ≠ ⊤ := by
    dsimp only [W]
    rw [Real.volume_pi_ball x hr]
    exact ENNReal.ofReal_ne_top
  have hVtop : volume V ≠ ⊤ := by
    dsimp only [V]
    rw [Real.volume_pi_ball x hV]
    exact ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (volume.restrict W) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hWtop⟩
  letI : IsFiniteMeasure (volume.restrict V) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hVtop⟩
  have hdiffW : MemLp (fun y => u.toFun y - volumeAverage W u.toFun) 2
      (volume.restrict W) := huW.sub (memLp_const _)
  have hdiffV : MemLp (fun y => u.toFun y - volumeAverage W u.toFun) 2
      (volume.restrict V) := huV.sub (memLp_const _)
  have hmean := abs_volumeAverage_sub_windowAverage_le
    (measurableSet_ball : MeasurableSet V) hsub
    (volume_metricBall_toReal_pos x hr) (volume_metricBall_toReal_pos x hV)
    hVtop
    (huV.integrable one_le_two) hdiffV.integrable_sq hdiffW.integrable_sq
  rw [sqrt_volume_metricBall_div_halfBall x hr] at hmean
  have hrTop : r ≤ 3 * smallContrastCampanatoRadius d := by
    exact (smallContrastDyadicRadius_le hR.le n).trans
      (by linarith [hR] : smallContrastCampanatoRadius d ≤
        3 * smallContrastCampanatoRadius d)
  have hosc := hcamp x hx r hr hrTop
  have hprice : 0 ≤ halfBallVolumePrice d := halfBallVolumePrice_nonneg d
  have hcombine := mul_le_mul_of_nonneg_left hosc hprice
  have hfactor := smallContrastDyadicRadius_rpow (alpha := alpha) hR.le n
  rw [Real.dist_eq, smallContrastCampanatoAverage,
    smallContrastCampanatoAverage, smallContrastDyadicRadius_succ, abs_sub_comm]
  refine hmean.trans (hcombine.trans_eq ?_)
  rw [hfactor]
  ring

theorem cauchySeq_smallContrastCampanatoAverage [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u)
    {x : Vec d} (hx : x ∈ smallContrastBall d (1 / 2)) :
    CauchySeq (smallContrastCampanatoAverage (d := d) u.toFun x) := by
  refine cauchySeq_of_le_geometric (smallContrastCampanatoRatio alpha)
    (halfBallVolumePrice d * smallContrastCampanatoConstant d * K *
      smallContrastCampanatoRadius d ^ alpha)
    (smallContrastCampanatoRatio_lt_one (lt_of_lt_of_le (by norm_num) halpha.1)) ?_
  exact dist_smallContrastCampanatoAverage_succ_le hcamp hx

theorem tendsto_smallContrastCampanatoAverage [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u)
    {x : Vec d} (hx : x ∈ smallContrastBall d (1 / 2)) :
    Tendsto (smallContrastCampanatoAverage (d := d) u.toFun x) atTop
      (𝓝 (smallContrastCampanatoRepresentative (d := d) u.toFun x)) :=
  (cauchySeq_smallContrastCampanatoAverage halpha hcamp hx).tendsto_limUnder

/-- Uniform tail of the dyadic mean telescope; the denominator is absorbed by
D-054 into the literal factor `4`. -/
theorem dist_average_representative_le [NeZero d]
    {alpha K : ℝ} {u : H1Function (smallContrastUnitBall d)}
    (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1) (hK : 0 ≤ K)
    (hcamp : HasSmallContrastBallCampanatoBound alpha K u)
    {x : Vec d} (hx : x ∈ smallContrastBall d (1 / 2)) (n : ℕ) :
    dist (smallContrastCampanatoAverage (d := d) u.toFun x n)
        (smallContrastCampanatoRepresentative (d := d) u.toFun x) ≤
      4 * halfBallVolumePrice d * smallContrastCampanatoConstant d * K *
        smallContrastDyadicRadius (smallContrastCampanatoRadius d) n ^ alpha := by
  let q := smallContrastCampanatoRatio alpha
  let C := halfBallVolumePrice d * smallContrastCampanatoConstant d * K *
    smallContrastCampanatoRadius d ^ alpha
  have hraw := dist_le_of_le_geometric_of_tendsto q C
    (smallContrastCampanatoRatio_lt_one (lt_of_lt_of_le (by norm_num) halpha.1))
    (dist_smallContrastCampanatoAverage_succ_le hcamp hx)
    (tendsto_smallContrastCampanatoAverage halpha hcamp hx) n
  have hdenpos : 0 < 1 - q := by
    dsimp only [q]
    linarith [smallContrastCampanatoRatio_lt_one
      (lt_of_lt_of_le (by norm_num) halpha.1)]
  have hinv := inv_one_sub_smallContrastCampanatoRatio_le_four halpha.1
  have hC : 0 ≤ C * q ^ n := by
    dsimp only [C, q]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (halfBallVolumePrice_nonneg d)
            (smallContrastCampanatoConstant_nonneg d)) hK)
          (Real.rpow_nonneg (smallContrastCampanatoRadius_pos (d := d)).le _))
      (pow_nonneg (smallContrastCampanatoRatio_nonneg alpha) n)
  have hprice : C * q ^ n / (1 - q) ≤ 4 * (C * q ^ n) := by
    rw [div_eq_mul_inv]
    have hinv' : (1 - q)⁻¹ ≤ 4 := by simpa only [q] using hinv
    calc
      C * q ^ n * (1 - q)⁻¹ ≤ C * q ^ n * 4 :=
        mul_le_mul_of_nonneg_left hinv' hC
      _ = 4 * (C * q ^ n) := by ring
  refine hraw.trans (hprice.trans_eq ?_)
  rw [smallContrastDyadicRadius_rpow
    (alpha := alpha) (smallContrastCampanatoRadius_pos (d := d)).le]
  dsimp only [C, q]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
