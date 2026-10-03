module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.StoppedRowsAtVariableTop
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ReadoutAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ScaleZeroPriceAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ArbitraryTargetMeanTelescope
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.ShallowOscillationReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.GlobalRepresentative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.ConditionalProviderAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveOscillationAbsorption

@[expose] public section

/-!
# Theta ladder: pathwise finite-telescope readout

This module converts the stopped point-centred normalized-`L²` rows into the
two rows of `BoundedMultiplierPathwiseEstimate`.  The target oscillation uses
the finite triadic telescope in the deep branch and monotonicity in the fixed
shallow branch.  The parent-mean row is never assigned geometric decay.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Topology Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open scoped ENNReal

noncomputable section

/-- The two point-centred stopped rows after all recurrence parameters have
been selected. -/
def AmbientProductOffGridRows {d : ℕ}
    (M : GMCModel d) (L m : ℕ) (z : Vec d)
    (omega : PotentialSample d) (j0 : ℕ) (Krow epsilon : ℝ) : Prop :=
  ∀ s : ℕ, s + 4 ≤ m → j0 ≤ m - s →
  ∀ x : Vec d, ‖x - z‖ ≤ (3 : ℝ) ^ m / 4 →
  ∀ b : ℝ, 0 < b →
  ∀ theta : Vec d → ℝ,
    ContinuousOn theta (translatedCube d (m : ℤ) z) →
    (∀ y ∈ translatedCube d (m : ℤ) z,
      |b⁻¹ * theta y - 1| ≤ epsilon) →
  ∀ h : H1Function (translatedCube d (m : ℤ) z),
    IsWeaklyHarmonicOn
        (fun y ↦ aCutoff M L omega y * theta y)
        (translatedCube d (m : ℤ) z) h →
  ∀ hRep : Vec d → ℝ,
    ContinuousOn hRep (translatedCube d (m : ℤ) z) →
    hRep =ᵐ[volume.restrict (translatedCube d (m : ℤ) z)] h.toFun →
    normalizedL2On (translatedCube d (s : ℤ) x)
        (fun y ↦ h.toFun y - averageOn
          (translatedCube d (s : ℤ) x) h.toFun) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        (Krow * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
          (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
        oscillationOn {y : Vec d | ‖y - z‖ ≤
          3 * (3 : ℝ) ^ (m : ℤ) / 8} hRep) ∧
    normalizedL2On (translatedCube d (s : ℤ) x)
        (fun y ↦ h.toFun y - averageOn
          (translatedCube d (s : ℤ) x) h.toFun) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        (Krow * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
          (((m : ℝ) - 2) - ((s : ℝ) + 1))) *
        (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          normalizedL2On (translatedCube d (m : ℤ) z)
            (fun y ↦ h.toFun y - averageOn
              (translatedCube d (m : ℤ) z) h.toFun)))

/-- Explicit dimension-only coefficient used by the pathwise readout. -/
def thetaLadderPathwiseConstant
    (d J : ℕ) (Krow Kpoint : ℝ) : ℝ :=
  let Qosc := Real.sqrt ((3 : ℝ) ^ d) * Krow *
    (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((J : ℝ) - 3))
  let Qparent := Qosc * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) +
    Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d)
  let R := (3 : ℝ) ^ (((J : ℝ) + 1) / 2)
  2 * (Kpoint * Qosc + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qosc +
      Real.sqrt ((3 : ℝ) ^ d) * Qosc) * R +
    (Kpoint * Qparent * R +
      5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent * R +
      Real.sqrt ((3 : ℝ) ^ d) * Qparent * R +
      5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent + Qparent) +
    (Kpoint * (3 : ℝ) ^ ((J : ℝ) / 8) + 1) *
      Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d) +
    (3 : ℝ) ^ ((J : ℝ) / 4) + 1

theorem thetaLadderPathwiseConstant_pos
    (d J : ℕ) {Krow Kpoint : ℝ} (hKrow : 0 ≤ Krow)
    (hKpoint : 0 ≤ Kpoint) :
    0 < thetaLadderPathwiseConstant d J Krow Kpoint := by
  unfold thetaLadderPathwiseConstant
  positivity

private theorem translatedUnitCube_subset_parent_of_collar
    {d m : ℕ} (hm : 0 < m) {z x : Vec d}
    (hx : ‖x - z‖ ≤ (3 : ℝ) ^ m / 4) :
    translatedCube d 0 x ⊆ translatedCube d (m : ℤ) z := by
  rw [translatedCube_eq_metricBall, translatedCube_eq_metricBall]
  apply Metric.ball_subset_ball'
  rw [dist_eq_norm, zpow_natCast]
  have hp : (3 : ℝ) ≤ (3 : ℝ) ^ m := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hm
  norm_num
  nlinarith

private theorem abs_averageOn_unit_sub_parent_le
    {d m : ℕ} {z x : Vec d} {f : Vec d → ℝ}
    (hsub : translatedCube d 0 x ⊆ translatedCube d (m : ℤ) z)
    (hf : IntegrableOn f (translatedCube d (m : ℤ) z))
    (hf2 : IntegrableOn (fun y ↦ f y ^ 2)
      (translatedCube d (m : ℤ) z)) :
    |averageOn (translatedCube d 0 x) f -
        averageOn (translatedCube d (m : ℤ) z) f| ≤
      Real.sqrt (((3 : ℝ) ^ (m : ℤ)) ^ d) *
        normalizedL2On (translatedCube d (m : ℤ) z)
          (fun y ↦ f y - averageOn (translatedCube d (m : ℤ) z) f) := by
  have hraw := abs_averageOn_natSub_sub_parent_le
    (d := d) (m := m) (J := m) (z := z) (x := x) (f := f)
      le_rfl (by simpa using hsub) hf hf2
  simpa using hraw

/-- Each positive coefficient in the pathwise readout is bounded by its common sum. -/
private theorem aux_pathwise_coefficient_bounds (d J : ℕ) (Krow Kpoint : ℝ)
    (hKrow : 0 ≤ Krow) (hKpoint : 0 ≤ Kpoint) :
    let Qosc := Real.sqrt ((3 : ℝ) ^ d) * Krow *
      (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((J : ℝ) - 3))
    let Qparent := Qosc * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) +
      Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d)
    (2 * (Kpoint * Qosc + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qosc +
            Real.sqrt ((3 : ℝ) ^ d) * Qosc) *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) ≤ thetaLadderPathwiseConstant d J Krow Kpoint) ∧
    (Kpoint * Qparent * (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            Real.sqrt ((3 : ℝ) ^ d) * Qparent *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent + Qparent ≤ thetaLadderPathwiseConstant d J Krow Kpoint) ∧
    ((3 : ℝ) ^ ((J : ℝ) / 4) ≤ thetaLadderPathwiseConstant d J Krow Kpoint) ∧
    (Kpoint * Qparent *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent + Qparent ≤ thetaLadderPathwiseConstant d J Krow Kpoint) ∧
    ((Kpoint * (3 : ℝ) ^ ((J : ℝ) / 8) + 1) *
            Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d) ≤ thetaLadderPathwiseConstant d J Krow Kpoint) := by
  dsimp only
  set Qosc := Real.sqrt ((3 : ℝ) ^ d) * Krow *
    (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((J : ℝ) - 3))
  set Qparent := Qosc * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) +
    Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d)
  have hQosc : 0 ≤ Qosc := by dsimp only [Qosc]; positivity
  have hQparent : 0 ≤ Qparent := by dsimp only [Qparent]; positivity
  let A : ℝ := 2 * (Kpoint * Qosc + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qosc +
            Real.sqrt ((3 : ℝ) ^ d) * Qosc) *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2)
  let B : ℝ := Kpoint * Qparent * (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            Real.sqrt ((3 : ℝ) ^ d) * Qparent *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent + Qparent
  let E : ℝ := (3 : ℝ) ^ ((J : ℝ) / 4)
  let Short : ℝ := Kpoint * Qparent *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent + Qparent
  let D : ℝ := (Kpoint * (3 : ℝ) ^ ((J : ℝ) / 8) + 1) *
            Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hsum : thetaLadderPathwiseConstant d J Krow Kpoint = A + B + D + E + 1 := rfl
  have hshort : Short ≤ B := by
    have hrest : 0 ≤ 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent *
        (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
        Real.sqrt ((3 : ℝ) ^ d) * Qparent * (3 : ℝ) ^ (((J : ℝ) + 1) / 2) := by
      positivity
    dsimp only [Short, B]
    linarith only [hrest]
  change A ≤ _ ∧ B ≤ _ ∧ E ≤ _ ∧ Short ≤ _ ∧ D ≤ _
  rw [hsum]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hA, hB, hD, hE, hshort]

/-- The complete pathwise `j ≤ m` readout from one parent-uniform stopped
row event. -/
theorem boundedMultiplierPathwiseEstimate_of_ambientProductOffGridRows
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (M : GMCModel d) (L m : ℕ) (hm : 0 < m) (z : Vec d)
    (omega : PotentialSample d) (j : ℕ) (hj : 0 < j) (hjm : j ≤ m)
    {B' : Set (Vec d)} (hB' : IsMiddleHalfSubcube (m : ℤ) z j B')
    (j0 : ℕ) {Krow Kpoint epsilon C c : ℝ}
    (hKrow : 0 ≤ Krow) (hKpoint : 0 ≤ Kpoint)
    (hpointPrice : ∀ n : ℕ, 0 < n →
      positiveScaleZeroPointPrice d n ≤
        Kpoint * (3 : ℝ) ^ ((n : ℝ) / 8))
    (hepsilonSmall : epsilon ≤ boundedMultiplierEpsilonStar d)
    (hc : 0 ≤ c) (hcQuarter : c ≤ 1 / 4)
    (hC : thetaLadderPathwiseConstant d (max 4 j0) Krow Kpoint ≤ C)
    (hgood : omega ∈ coveringRestrictedGradientGood M L (m : ℤ) z)
    (hrows : AmbientProductOffGridRows M L m z omega j0 Krow epsilon) :
    BoundedMultiplierPathwiseEstimate
      M L (m : ℤ) z j B' epsilon C c omega := by
  intro theta hthetaCont hthetaPos hthetaClose h hharm
  obtain ⟨b, hb, hnear⟩ := hthetaClose
  let hRep := euclideanBallAverageRepresentative h.toFun
  have hsCont : ContinuousOn
      (fun y ↦ aCutoff M L omega y * theta y)
      (translatedCube d (m : ℤ) z) :=
    (continuous_aCutoff M L omega).continuousOn.mul hthetaCont
  have hsPos : ∀ y ∈ translatedCube d (m : ℤ) z,
      0 < aCutoff M L omega y * theta y := by
    intro y hy
    exact mul_pos (aCutoff_pos M L omega y) (hthetaPos y hy)
  have hparentOpen : IsOpen (translatedCube d (m : ℤ) z) := by
    rw [translatedCube_eq_metricBall]
    exact Metric.isOpen_ball
  have hRepData :=
    continuousOn_and_ae_eq_euclideanBallAverageRepresentative
      hd hparentOpen hsCont hsPos hharm
  refine ⟨hRep, hRepData.1, hRepData.2, ?_⟩
  let collar : Set (Vec d) :=
    {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8}
  let Osc := oscillationOn collar hRep
  let Parent := normalizedL2On (translatedCube d (m : ℤ) z)
    (fun y ↦ h.toFun y - averageOn (translatedCube d (m : ℤ) z) h.toFun)
  let J := max 4 j0
  let Qosc := Real.sqrt ((3 : ℝ) ^ d) * Krow *
    (3 : ℝ) ^ (-(1 / 2 : ℝ) * ((J : ℝ) - 3))
  let Qparent := Qosc * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) +
    Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d)
  have hJ4 : 4 ≤ J := le_max_left _ _
  have hj0J : j0 ≤ J := le_max_right _ _
  have hQosc : 0 ≤ Qosc := by dsimp only [Qosc]; positivity
  have hQparent : 0 ≤ Qparent := by dsimp only [Qparent]; positivity
  obtain ⟨hCoeffOsc, hCoeffParent, hCoeffDepth, hCoeffShort, hCoeffDirect⟩ :=
    aux_pathwise_coefficient_bounds d J Krow Kpoint hKrow hKpoint
  have hParent : 0 ≤ Parent := Section6Iteration.normalizedL2On_nonneg _ _
  have hcollarNe : collar.Nonempty := by
    refine ⟨z, ?_⟩
    dsimp only [collar]
    simp only [Set.mem_setOf_eq, sub_self, norm_zero]
    positivity
  have hOsc : 0 ≤ Osc := oscillationOn_nonneg_of_nonempty hcollarNe
  have hB'Ne : B'.Nonempty := by
    obtain ⟨z', hz', _hz, _⟩ := exists_middleHalfSubcube_center_and_subset_ball hB'
    refine ⟨z', ?_⟩
    rw [hz', translatedCube_eq_metricBall]
    exact Metric.mem_ball_self (by positivity)
  have hB'collar : B' ⊆ collar := by
    intro x hx
    dsimp only [collar]
    have hsmall := hB'.choose_spec.2 x hx
    have hp : 0 < (3 : ℝ) ^ (m : ℤ) := by positivity
    have hquarter : (3 : ℝ) ^ (m : ℤ) / 4 ≤
        3 * (3 : ℝ) ^ (m : ℤ) / 8 := by linarith only [hp]
    exact hsmall.trans hquarter
  have hparentMem := h.memL2
  letI : IsFiniteMeasure (volume.restrict (translatedCube d (m : ℤ) z)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_top_iff_ne_top.mpr
          (volume_translatedCube_ne_top (m : ℤ) z)⟩
  have hfParent : IntegrableOn h.toFun (translatedCube d (m : ℤ) z) :=
    hparentMem.integrable one_le_two
  have hf2Parent : IntegrableOn (fun y ↦ h.toFun y ^ 2)
      (translatedCube d (m : ℤ) z) := hparentMem.integrable_sq
  have hpoint0 : ∀ x ∈ B',
      |hRep x - averageOn (translatedCube d 0 x) h.toFun| ≤
        positiveScaleZeroPointPrice d m *
          normalizedL2On (translatedCube d 0 x)
            (fun y ↦ h.toFun y - averageOn
              (translatedCube d 0 x) h.toFun) := by
    intro x hx
    exact positiveParent_point_sub_scaleZeroMean_le_price hd M L m hm z omega
      hgood (hB'.choose_spec.2 x hx) hthetaCont hb
      (fun y hy ↦ (hnear y hy).trans hepsilonSmall) hharm
  have hPbound := hpointPrice m hm
  have hrepAvg : averageOn (translatedCube d (m : ℤ) z) hRep =
      averageOn (translatedCube d (m : ℤ) z) h.toFun :=
    averageOn_eq_of_ae_eq hRepData.2
  have hparentRep : normalizedL2On (translatedCube d (m : ℤ) z)
      (fun y ↦ hRep y - averageOn (translatedCube d (m : ℤ) z) hRep) =
      Parent := by
    dsimp only [Parent]
    exact normalizedL2On_sub_average_eq_of_ae_eq hRepData.2
  have hparentRepToFun : normalizedL2On (translatedCube d (m : ℤ) z)
      (fun y ↦ hRep y - averageOn (translatedCube d (m : ℤ) z) h.toFun) =
      Parent := by
    rw [← hrepAvg]
    exact hparentRep
  have hCnonneg : 0 ≤ C :=
    (thetaLadderPathwiseConstant_pos d J hKrow hKpoint).le.trans hC
  have hrowFamilies : J ≤ m →
      (∀ x ∈ B', ∀ s : ℕ, s ≤ m - J →
        normalizedL2On (translatedCube d (s : ℤ) x)
            (fun y ↦ h.toFun y - averageOn
              (translatedCube d (s : ℤ) x) h.toFun) ≤
          Qosc * Osc * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
            (((m - J : ℕ) : ℝ) - (s : ℝ)))) ∧
      (∀ x ∈ B', ∀ s : ℕ, s ≤ m - J →
        normalizedL2On (translatedCube d (s : ℤ) x)
            (fun y ↦ h.toFun y - averageOn
              (translatedCube d (s : ℤ) x) h.toFun) ≤
          Qparent * Parent * (3 : ℝ) ^ (-(1 / 2 : ℝ) *
            (((m - J : ℕ) : ℝ) - (s : ℝ)))) := by
    intro hJm
    constructor
    · intro x hx s hs
      have hs4 : s + 4 ≤ m := by omega
      have hdepth : j0 ≤ m - s := by omega
      have hr := (hrows s hs4 hdepth x (hB'.choose_spec.2 x hx)
        b hb theta hthetaCont hnear h hharm hRep hRepData.1 hRepData.2).1
      simpa only [Qosc, Osc, collar] using
        offGridStoppedRow_rebase_variableTop hJm hr
    · intro x hx s hs
      have hs4 : s + 4 ≤ m := by omega
      have hdepth : j0 ≤ m - s := by omega
      have hr := (hrows s hs4 hdepth x (hB'.choose_spec.2 x hx)
        b hb theta hthetaCont hnear h hharm hRep hRepData.1 hRepData.2).2
      have hrebased := offGridStoppedRow_rebase_variableTop hJm hr
      have hcoef : Qosc *
          (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * Parent) ≤
          Qparent * Parent := by
        dsimp only [Qparent]
        have hJroot : 0 ≤ Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d) :=
          Real.sqrt_nonneg _
        nlinarith only [hQosc, hParent, hJroot]
      have hp := (3 : ℝ) ^ (-(1 / 2 : ℝ) *
        (((m - J : ℕ) : ℝ) - (s : ℝ)))
      exact hrebased.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))
  by_cases hdeep : J + 1 ≤ j
  · have hJm : J ≤ m := by omega
    obtain ⟨hrowsOsc, hrowsParent⟩ := hrowFamilies hJm
    have htopParent : ∀ x ∈ B',
        |averageOn (translatedCube d ((m - J : ℕ) : ℤ) x) h.toFun -
            averageOn (translatedCube d (m : ℤ) z) h.toFun| ≤
          Qparent * Parent := by
      intro x hx
      have hsub := translatedCube_natSub_subset_parent_of_middleHalf
        hJm hJ4 hB' hx
      have hraw := abs_averageOn_natSub_sub_parent_le
        hJm hsub hfParent hf2Parent
      have hroot : Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d) ≤ Qparent := by
        dsimp only [Qparent]
        have hnonneg : 0 ≤ Qosc * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) :=
          mul_nonneg hQosc (Real.sqrt_nonneg _)
        linarith only [hnonneg]
      exact hraw.trans (mul_le_mul_of_nonneg_right hroot hParent)
    have hraw := variableTop_finiteCampanato_readouts hJ4 hJm hdeep hjm hB'
      hRepData.2 (mul_nonneg hQosc hOsc) (mul_nonneg hQparent hParent)
      (positiveScaleZeroPointPrice_nonneg d m) hrowsOsc hrowsParent hpoint0
      htopParent
    dsimp only at hraw
    have habs := finiteCampanato_readouts_absorbed hJm hdeep hjm hOsc hParent
      hKpoint hQosc hQparent hPbound hraw.1 hraw.2
    dsimp only at habs
    constructor
    · have hconst :
          2 * (Kpoint * Qosc + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qosc +
            Real.sqrt ((3 : ℝ) ^ d) * Qosc) *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) ≤ C := by
        exact hCoeffOsc.trans hC
      have hpow : (3 : ℝ) ^ (-(j : ℝ) / 4) ≤
          (3 : ℝ) ^ (-c * (j : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hjR : 0 ≤ (j : ℝ) := by positivity
        nlinarith only [hcQuarter, hjR]
      exact habs.1.trans (by
        have hmul := mul_le_mul hconst hpow (by positivity) hCnonneg
        dsimp only [Osc, collar]
        nlinarith only [hmul, hOsc])
    · have hconst :
          Kpoint * Qparent * (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            Real.sqrt ((3 : ℝ) ^ d) * Qparent *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent + Qparent ≤ C := by
        exact hCoeffParent.trans hC
      have hout := habs.2.trans
        (mul_le_mul_of_nonneg_right hconst hParent)
      simpa only [hparentRep] using hout
  · have hshallow : j ≤ J := by omega
    have hcollarCompact : IsCompact collar := by
      dsimp only [collar]
      rw [show {y : Vec d | ‖y - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8} =
          Metric.closedBall z (3 * (3 : ℝ) ^ (m : ℤ) / 8) by
        ext y; simp [dist_eq_norm]]
      exact isCompact_closedBall z _
    have hcollarSub : collar ⊆ translatedCube d (m : ℤ) z := by
      intro x hx
      rw [translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm]
      have hp : 0 < (3 : ℝ) ^ (m : ℤ) := by positivity
      dsimp only [collar] at hx
      have hstrict : 3 * (3 : ℝ) ^ (m : ℤ) / 8 <
          (1 / 2 : ℝ) * (3 : ℝ) ^ (m : ℤ) := by linarith only [hp]
      exact hx.trans_lt hstrict
    obtain ⟨K, hK⟩ := hcollarCompact.exists_bound_of_continuousOn
      (hRepData.1.mono hcollarSub).norm
    have hbdd : BddAbove {q : ℝ | ∃ x ∈ collar, ∃ y ∈ collar,
        q = |hRep x - hRep y|} := by
      refine ⟨2 * K, ?_⟩
      rintro q ⟨x, hx, y, hy, rfl⟩
      have hxK : |hRep x| ≤ K := by
        simpa only [Real.norm_eq_abs, abs_abs] using hK x hx
      have hyK : |hRep y| ≤ K := by
        simpa only [Real.norm_eq_abs, abs_abs] using hK y hy
      exact (abs_sub _ _).trans (by linarith only [hxK, hyK])
    constructor
    · have hfactor : 1 ≤ C * (3 : ℝ) ^ (-c * (J : ℝ)) := by
        have hCJ : (3 : ℝ) ^ ((J : ℝ) / 4) ≤ C := by
          exact hCoeffDepth.trans hC
        have hpow : (3 : ℝ) ^ (-c * (J : ℝ)) ≥
            (3 : ℝ) ^ (-(J : ℝ) / 4) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hJR : 0 ≤ (J : ℝ) := by positivity
          nlinarith only [hcQuarter, hJR]
        have hprod : (3 : ℝ) ^ ((J : ℝ) / 4) *
            (3 : ℝ) ^ (-(J : ℝ) / 4) = 1 := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          rw [show (J : ℝ) / 4 + -(J : ℝ) / 4 = 0 by ring]
          exact Real.rpow_zero 3
        nlinarith only [hprod, mul_le_mul hCJ hpow (by positivity) hCnonneg]
      exact oscillationOn_le_decay_of_boundedDepth hB'Ne hcollarNe hB'collar
        hbdd hc hshallow hfactor
    · by_cases hJm : J ≤ m
      · obtain ⟨_hrowsOsc, hrowsParent⟩ := hrowFamilies hJm
        have hInt : ∀ x ∈ B',
            IntegrableOn h.toFun (translatedCube d ((m - J : ℕ) : ℤ) x) ∧
            IntegrableOn (fun y ↦ h.toFun y ^ 2)
              (translatedCube d ((m - J : ℕ) : ℤ) x) := by
          intro x hx
          have hsub := translatedCube_natSub_subset_parent_of_middleHalf
            hJm hJ4 hB' hx
          exact ⟨hfParent.mono_set hsub, hf2Parent.mono_set hsub⟩
        have htop : ∀ x ∈ B',
            |averageOn (translatedCube d ((m - J : ℕ) : ℤ) x) h.toFun -
              averageOn (translatedCube d (m : ℤ) z) h.toFun| ≤
                Qparent * Parent := by
          intro x hx
          have hsub := translatedCube_natSub_subset_parent_of_middleHalf
            hJm hJ4 hB' hx
          have hraw := abs_averageOn_natSub_sub_parent_le
            hJm hsub hfParent hf2Parent
          have hroot : Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d) ≤ Qparent := by
            dsimp only [Qparent]
            have hn : 0 ≤ Qosc * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) :=
              mul_nonneg hQosc (Real.sqrt_nonneg _)
            linarith only [hn]
          exact hraw.trans (mul_le_mul_of_nonneg_right hroot hParent)
        have hmean := sSup_point_sub_parentMean_le_of_halfDecay hB'Ne
          (mul_nonneg hQparent hParent)
          (positiveScaleZeroPointPrice_nonneg d m) hInt hrowsParent hpoint0 htop
        have hp0 := three_rpow_pointTerm_le hJm (Nat.zero_le m)
        have hpointAbs : positiveScaleZeroPointPrice d m *
              (Qparent * Parent * (3 : ℝ) ^
                (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ))) ≤
            Kpoint * Qparent * (3 : ℝ) ^ (((J : ℝ) + 1) / 2) * Parent := by
          calc
            _ ≤ (Kpoint * (3 : ℝ) ^ ((m : ℝ) / 8)) *
                (Qparent * Parent * (3 : ℝ) ^
                  (-(1 / 2 : ℝ) * ((m - J : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_right hPbound (by positivity)
            _ ≤ _ := by
              have hm := mul_le_mul_of_nonneg_left hp0
                (mul_nonneg (mul_nonneg hKpoint hQparent) hParent)
              nlinarith only [hm]
        have hconst : Kpoint * Qparent *
              (3 : ℝ) ^ (((J : ℝ) + 1) / 2) +
            5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Qparent + Qparent ≤ C := by
            exact hCoeffShort.trans hC
        rw [hrepAvg, hparentRepToFun]
        refine hmean.trans ?_
        have hsum :
            Kpoint * Qparent * (3 : ℝ) ^ (((J : ℝ) + 1) / 2) * Parent +
                5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * (Qparent * Parent) +
                Qparent * Parent ≤ C * Parent := by
          have hm := mul_le_mul_of_nonneg_right hconst hParent
          nlinarith only [hm]
        have hout := (add_le_add (add_le_add hpointAbs
          (mul_le_mul_of_nonneg_left le_rfl (by positivity))) le_rfl).trans hsum
        simpa only [hparentRepToFun] using hout
      · have hmJ : m < J := lt_of_not_ge hJm
        have hpointwise : ∀ x ∈ B',
            |hRep x - averageOn (translatedCube d (m : ℤ) z) h.toFun| ≤
              (positiveScaleZeroPointPrice d m + 1) *
                Real.sqrt (((3 : ℝ) ^ (m : ℤ)) ^ d) * Parent := by
          intro x hx
          have hunitSub := translatedUnitCube_subset_parent_of_collar hm
            (hB'.choose_spec.2 x hx)
          have hmean := abs_averageOn_unit_sub_parent_le hunitSub hfParent hf2Parent
          have htri := abs_sub_le (hRep x)
            (averageOn (translatedCube d 0 x) h.toFun)
            (averageOn (translatedCube d (m : ℤ) z) h.toFun)
          have hp := hpoint0 x hx
          -- The direct subset price is sharper than the fixed two-scale helper.
          have hunitCentered : normalizedL2On (translatedCube d 0 x)
              (fun y ↦ h.toFun y - averageOn (translatedCube d 0 x) h.toFun) ≤
              Real.sqrt (((3 : ℝ) ^ (m : ℤ)) ^ d) * Parent := by
            have hraw := Section6Iteration.normalizedL2On_sub_volumeAverage_le
              (by rw [translatedCube_eq_metricBall]; exact measurableSet_ball)
              (volume_translatedCube_toReal_pos 0 x)
              (volume_translatedCube_ne_top 0 x)
              (hfParent.mono_set hunitSub) (hf2Parent.mono_set hunitSub)
              (averageOn (translatedCube d (m : ℤ) z) h.toFun)
            have hrestrict := Section6Iteration.normalizedL2On_le_of_subset
              hunitSub (volume_translatedCube_toReal_pos (m : ℤ) z)
              (volume_translatedCube_toReal_pos 0 x)
              (by
                have hc : IntegrableOn (fun y ↦
                    (h.toFun y - averageOn (translatedCube d (m : ℤ) z) h.toFun) ^ 2)
                    (translatedCube d (m : ℤ) z) := by
                  exact (hparentMem.sub (memLp_const _)).integrable_sq
                exact hc)
            have hratio : Real.sqrt
                ((volume (translatedCube d (m : ℤ) z)).toReal /
                  (volume (translatedCube d 0 x)).toReal) =
                Real.sqrt (((3 : ℝ) ^ (m : ℤ)) ^ d) := by
              rw [volume_translatedCube_toReal, volume_translatedCube_toReal]
              norm_num
            rw [hratio] at hrestrict
            exact hraw.trans hrestrict
          exact htri.trans (by
            have hp' := hp.trans
              (mul_le_mul_of_nonneg_left hunitCentered
                (positiveScaleZeroPointPrice_nonneg d m))
            nlinarith only [hp', hmean, hParent])
        have hsup := sSup_point_sub_common_le hB'Ne hpointwise
        have hpowM : (3 : ℝ) ^ ((m : ℝ) / 8) ≤
            (3 : ℝ) ^ ((J : ℝ) / 8) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by
              have hmJR : (m : ℝ) ≤ (J : ℝ) := by
                exact_mod_cast (Nat.le_of_lt hmJ)
              linarith only [hmJR])
        have hpriceJ : positiveScaleZeroPointPrice d m ≤
            Kpoint * (3 : ℝ) ^ ((J : ℝ) / 8) :=
          hPbound.trans (mul_le_mul_of_nonneg_left hpowM hKpoint)
        have hrootM : Real.sqrt (((3 : ℝ) ^ (m : ℤ)) ^ d) ≤
            Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d) := by
          apply Real.sqrt_le_sqrt
          apply pow_le_pow_left₀ (by positivity)
          exact zpow_le_zpow_right₀ (by norm_num) (by exact_mod_cast hmJ.le)
        have hconst : (Kpoint * (3 : ℝ) ^ ((J : ℝ) / 8) + 1) *
            Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d) ≤ C := by
            exact hCoeffDirect.trans hC
        rw [hrepAvg, hparentRepToFun]
        refine hsup.trans ?_
        have hcoef : (positiveScaleZeroPointPrice d m + 1) *
            Real.sqrt (((3 : ℝ) ^ (m : ℤ)) ^ d) ≤ C := by
          have hpriceJ' : positiveScaleZeroPointPrice d m + 1 ≤
              Kpoint * (3 : ℝ) ^ ((J : ℝ) / 8) + 1 :=
            by linarith only [hpriceJ]
          exact (mul_le_mul hpriceJ' hrootM (Real.sqrt_nonneg _)
            (by positivity)).trans hconst
        have hout := mul_le_mul_of_nonneg_right hcoef hParent
        simpa only [hparentRepToFun] using hout

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
