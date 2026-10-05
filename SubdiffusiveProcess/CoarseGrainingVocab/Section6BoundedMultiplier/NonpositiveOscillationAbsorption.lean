module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveDeepReadout

@[expose] public section

/-!
# Exponent and shallow-case absorption at nonpositive scales
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Topology Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

/-- Dimension-only prefactor in the deep square-root decay. -/
def boundedMultiplierNonpositiveDeepDecayConst (d : ℕ) : ℝ :=
  smallContrastSchauderConstant d *
    boundedMultiplierCaccioppoliEndpointConst d *
      Real.sqrt (18 * (d : ℝ) /
        boundedMultiplierNonpositiveRadiusFloor d)

/-- Crude finite-depth price for the branch in which the first deterministic
small-contrast ball does not yet contain the target. -/
def boundedMultiplierNonpositiveShallowDecayConst (d : ℕ) (c : ℝ) : ℝ :=
  (3 : ℝ) ^ (c *
    (6 * (d : ℝ) / boundedMultiplierNonpositiveRadiusFloor d))

/-- One constant for the deep and shallow nonpositive-scale branches. -/
def boundedMultiplierNonpositiveOscillationConst (d : ℕ) (c : ℝ) : ℝ :=
  max (boundedMultiplierNonpositiveDeepDecayConst d)
    (boundedMultiplierNonpositiveShallowDecayConst d c)

theorem boundedMultiplierNonpositiveOscillationConst_pos (d : ℕ) (c : ℝ) :
    0 < boundedMultiplierNonpositiveOscillationConst d c := by
  exact lt_of_lt_of_le
    (Real.rpow_pos_of_pos (by norm_num)
      (c * (6 * (d : ℝ) / boundedMultiplierNonpositiveRadiusFloor d)))
    (le_max_right _ _)

theorem oscillationOn_nonneg_of_nonempty {S : Set (Vec d)} {f : Vec d → ℝ}
    (hS : S.Nonempty) :
    0 ≤ oscillationOn S f := by
  obtain ⟨x, hx⟩ := hS
  unfold oscillationOn
  exact Real.sSup_nonneg' ⟨0, ⟨x, hx, x, hx, by simp⟩, le_rfl⟩

theorem sqrt_nonpositive_targetRadius_ratio
    [NeZero d] (m : ℤ) (j : ℕ) :
    Real.sqrt
        (36 * (d : ℝ) * (1 / 2 * (3 : ℝ) ^ (m - j)) /
          (boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m)) =
      Real.sqrt (18 * (d : ℝ) /
          boundedMultiplierNonpositiveRadiusFloor d) *
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) := by
  have hfloor : 0 < boundedMultiplierNonpositiveRadiusFloor d :=
    boundedMultiplierNonpositiveRadiusFloor_pos d
  have hmPow : 0 < (3 : ℝ) ^ m := by positivity
  have hjPow : 0 < (3 : ℝ) ^ j := by positivity
  have hinside :
      36 * (d : ℝ) * (1 / 2 * (3 : ℝ) ^ (m - j)) /
          (boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m) =
        (18 * (d : ℝ) / boundedMultiplierNonpositiveRadiusFloor d) /
          (3 : ℝ) ^ j := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    field_simp [hfloor.ne', hmPow.ne', hjPow.ne']
    ring_nf
  rw [hinside, Real.sqrt_div (by positivity)
    ((3 : ℝ) ^ j)]
  have hsqrtj : Real.sqrt ((3 : ℝ) ^ j) =
      (3 : ℝ) ^ ((1 / 2 : ℝ) * (j : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring_nf
  rw [hsqrtj, div_eq_mul_inv,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring_nf

private theorem natCast_le_three_pow (j : ℕ) :
    (j : ℝ) ≤ (3 : ℝ) ^ j := by
  have hnat : j ≤ (3 : ℕ) ^ j := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ]
        have hpow : 1 ≤ (3 : ℕ) ^ j := Nat.one_le_pow _ _ (by norm_num)
        omega
  exact_mod_cast hnat

private theorem one_le_shallowDecay_mul_decay
    [NeZero d] {j : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hdepth : (3 : ℝ) ^ j <
      6 * (d : ℝ) / boundedMultiplierNonpositiveRadiusFloor d) :
    1 ≤ boundedMultiplierNonpositiveShallowDecayConst d c *
      (3 : ℝ) ^ (-c * (j : ℝ)) := by
  have hj : (j : ℝ) ≤
      6 * (d : ℝ) / boundedMultiplierNonpositiveRadiusFloor d :=
    (natCast_le_three_pow j).trans hdepth.le
  rw [boundedMultiplierNonpositiveShallowDecayConst,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), ← Real.rpow_zero]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

private theorem bddAbove_oscillationValues_of_compact
    {S : Set (Vec d)} {f : Vec d → ℝ}
    (hcompact : IsCompact S) (hcont : ContinuousOn f S) :
    BddAbove {q : ℝ | ∃ x ∈ S, ∃ y ∈ S, q = |f x - f y|} := by
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont.norm
  refine ⟨2 * C, ?_⟩
  rintro q ⟨x, hx, y, hy, rfl⟩
  have hxC : |f x| ≤ C := by
    simpa only [Real.norm_eq_abs, abs_abs] using hC x hx
  have hyC : |f y| ≤ C := by
    simpa only [Real.norm_eq_abs, abs_abs] using hC y hy
  exact (abs_sub (f x) (f y)).trans (by linarith)

/-- Complete `m ≤ 0` oscillation endpoint, including both the deep
small-contrast contraction and the dimension-only shallow-depth branch. -/
theorem nonpositive_middleHalfSubcube_oscillation_decay
    [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ)
    {m : ℤ} (hm : m ≤ 0) (z : Vec d) {j : ℕ} (hj : 0 < j)
    {B' : Set (Vec d)} (hB' : IsMiddleHalfSubcube m z j B')
    (omega : PotentialSample d)
    (hgood : omega ∈ coveringRestrictedGradientGood M L m z)
    {theta : Vec d → ℝ}
    (hthetaCont : ContinuousOn theta (translatedCube d m z))
    (hthetaPos : ∀ y ∈ translatedCube d m z, 0 < theta y)
    {b : ℝ} (hb : 0 < b)
    (hthetaClose : ∀ y ∈ translatedCube d m z,
      |b⁻¹ * theta y - 1| ≤ boundedMultiplierEpsilonStar d)
    {h : H1Function (translatedCube d m z)}
    (hharm : IsWeaklyHarmonicOn
      (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d m z) h)
    {c : ℝ} (hc : 0 ≤ c) (hcHalf : c ≤ 1 / 2) :
    oscillationOn B' (euclideanBallAverageRepresentative h.toFun) ≤
      boundedMultiplierNonpositiveOscillationConst d c *
        (3 : ℝ) ^ (-c * (j : ℝ)) *
          oscillationOn {y : Vec d | ‖y - z‖ ≤
            3 * (3 : ℝ) ^ m / 8}
            (euclideanBallAverageRepresentative h.toFun) := by
  have _hjOne : 1 ≤ j := hj
  obtain ⟨zCenter, hB'eq, hB'collar⟩ := hB'
  have hB'full : IsMiddleHalfSubcube m z j B' :=
    ⟨zCenter, hB'eq, hB'collar⟩
  let hRep := euclideanBallAverageRepresentative h.toFun
  let D := {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ m / 8}
  have hDcompact : IsCompact D := by
    have hDeq : D = Metric.closedBall z (3 * (3 : ℝ) ^ m / 8) := by
      ext y
      simp only [D, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm]
    rw [hDeq]
    exact isCompact_closedBall z _
  have hDsub : D ⊆ translatedCube d m z := by
    rw [translatedCube_eq_metricBall]
    intro y hy
    have hy' : ‖y - z‖ ≤ 3 * (3 : ℝ) ^ m / 8 := hy
    have hpow : 0 < (3 : ℝ) ^ m := by positivity
    have hylt : ‖y - z‖ < 1 / 2 * (3 : ℝ) ^ m := by
      nlinarith
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hylt
  let s : Vec d → ℝ := fun y ↦ aCutoff M L omega y * theta y
  have hsCont : ContinuousOn s (translatedCube d m z) :=
    (continuous_aCutoff M L omega).continuousOn.mul hthetaCont
  have hsPos : ∀ y ∈ translatedCube d m z, 0 < s y := by
    intro y hy
    exact mul_pos (aCutoff_pos M L omega y) (hthetaPos y hy)
  have hcubeOpen : IsOpen (translatedCube d m z) := by
    rw [translatedCube_eq_metricBall]
    exact Metric.isOpen_ball
  have hrep := continuousOn_and_ae_eq_euclideanBallAverageRepresentative
    hd hcubeOpen hsCont hsPos hharm
  have hDcont : ContinuousOn hRep D := hrep.1.mono hDsub
  have hDne : D.Nonempty := by
    refine ⟨z, ?_⟩
    dsimp only [D]
    simp
    positivity
  have hOsc0 : 0 ≤ oscillationOn D hRep :=
    oscillationOn_nonneg_of_nonempty hDne
  have hB'ne : B'.Nonempty := by
    refine ⟨zCenter, ?_⟩
    rw [hB'eq, translatedCube_eq_metricBall]
    exact Metric.mem_ball_self (by positivity)
  have hB'D : B' ⊆ D := by
    intro x hx
    dsimp only [D]
    exact (hB'collar x hx).trans (by
      have hpow : 0 < (3 : ℝ) ^ m := by positivity
      nlinarith)
  have hbddD : BddAbove {q : ℝ | ∃ x ∈ D, ∃ y ∈ D,
      q = |hRep x - hRep y|} :=
    bddAbove_oscillationValues_of_compact hDcompact hDcont
  let R := boundedMultiplierNonpositiveRadiusFloor d * (3 : ℝ) ^ m
  let r := 1 / 2 * (3 : ℝ) ^ (m - j)
  by_cases hfirst : r ≤ R / (12 * (d : ℝ))
  · obtain ⟨n, hdeep, hdecay⟩ :=
      exists_middleHalfSubcube_nonpositiveDeepOscillation
        hd M L hm z j hB'full omega hgood hthetaCont hthetaPos hb hthetaClose
          hharm (by simpa only [R, r] using hfirst)
    have hratio := sqrt_nonpositive_targetRadius_ratio (d := d) m j
    rw [hratio] at hdecay
    have hpowCompare : (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) ≤
        (3 : ℝ) ^ (-c * (j : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith
    have hpref0 : 0 ≤ smallContrastSchauderConstant d *
        boundedMultiplierCaccioppoliEndpointConst d * oscillationOn D hRep :=
      mul_nonneg
        (mul_nonneg (smallContrastSchauderConstant_nonneg d)
          (boundedMultiplierCaccioppoliEndpointConst_nonneg d)) hOsc0
    have hdecay' := hdecay.trans
      (mul_le_mul_of_nonneg_left hpowCompare
        (Real.sqrt_nonneg _))
    have hscale := mul_le_mul_of_nonneg_left hdecay' hpref0
    have hdeepConst : boundedMultiplierNonpositiveDeepDecayConst d ≤
        boundedMultiplierNonpositiveOscillationConst d c :=
      le_max_left _ _
    have hright0 : 0 ≤ (3 : ℝ) ^ (-c * (j : ℝ)) * oscillationOn D hRep :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hOsc0
    calc
      oscillationOn B' hRep ≤
          smallContrastSchauderConstant d *
            boundedMultiplierCaccioppoliEndpointConst d *
            oscillationOn D hRep *
              (3 : ℝ) ^ (-(1 / 2 : ℝ) * (n : ℝ)) := by
        simpa only [hRep, D] using hdeep
      _ ≤ boundedMultiplierNonpositiveDeepDecayConst d *
          (3 : ℝ) ^ (-c * (j : ℝ)) * oscillationOn D hRep := by
        simpa only [boundedMultiplierNonpositiveDeepDecayConst, mul_assoc,
          mul_left_comm, mul_comm] using hscale
      _ ≤ boundedMultiplierNonpositiveOscillationConst d c *
          (3 : ℝ) ^ (-c * (j : ℝ)) * oscillationOn D hRep := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdeepConst
            (Real.rpow_nonneg (by norm_num) _)) hOsc0
  · have hshallow : R / (12 * (d : ℝ)) < r := lt_of_not_ge hfirst
    have hdepth := three_pow_depth_lt_of_nonpositiveFirstSubunitBall_lt
      (d := d) (m := m) (R := R) (le_rfl) (by
        simpa only [R, r] using hshallow)
    have hmono : oscillationOn B' hRep ≤ oscillationOn D hRep :=
      oscillationOn_le_of_subset_of_bddAbove hB'ne hB'D hbddD
    have hone := one_le_shallowDecay_mul_decay (d := d) hc hdepth
    have hscaled := mul_le_mul_of_nonneg_right hone hOsc0
    have hshallowConst : boundedMultiplierNonpositiveShallowDecayConst d c ≤
        boundedMultiplierNonpositiveOscillationConst d c :=
      le_max_right _ _
    have hright0 : 0 ≤ (3 : ℝ) ^ (-c * (j : ℝ)) * oscillationOn D hRep :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hOsc0
    calc
      oscillationOn B' hRep ≤ oscillationOn D hRep := hmono
      _ ≤ boundedMultiplierNonpositiveShallowDecayConst d c *
          (3 : ℝ) ^ (-c * (j : ℝ)) * oscillationOn D hRep := by
        simpa only [one_mul, mul_assoc] using hscaled
      _ ≤ boundedMultiplierNonpositiveOscillationConst d c *
          (3 : ℝ) ^ (-c * (j : ℝ)) * oscillationOn D hRep :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hshallowConst
            (Real.rpow_nonneg (by norm_num) _)) hOsc0

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
