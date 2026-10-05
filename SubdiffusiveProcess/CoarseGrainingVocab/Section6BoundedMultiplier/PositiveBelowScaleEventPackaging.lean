module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.AmbientCellEvents
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveEventPackaging

@[expose] public section

/-!
# Positive-parent below-scale event

For `0 < m < j`, the theta ladder is stopped at its depth-`m` unit cube and
the established nonpositive-scale contraction is appended below that cube.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Topology Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

/-- A crude common constant for the theta-ladder and sub-unit rows. -/
def boundedMultiplierSealConstant (d : ℕ) (c C₀ : ℝ) : ℝ :=
  2 + C₀ + boundedMultiplierNonpositiveOscillationConst d c * C₀ +
    boundedMultiplierNonpositiveL2Const d

theorem boundedMultiplierSealConstant_pos
    (d : ℕ) {c C₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < boundedMultiplierSealConstant d c C₀ := by
  unfold boundedMultiplierSealConstant
  have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
  have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d
  positivity

theorem boundedMultiplierSealConstant_base_lt
    (d : ℕ) {c C₀ : ℝ} (hC₀ : 0 < C₀) :
    C₀ < boundedMultiplierSealConstant d c C₀ := by
  unfold boundedMultiplierSealConstant
  have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
  have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d
  nlinarith

private theorem targetCentre_mem {d : ℕ} {m : ℤ} {z' : Vec d}
    {j : ℕ} {B' : Set (Vec d)}
    (hB' : B' = translatedCube d (m - j) z') : z' ∈ B' := by
  rw [hB', translatedCube_eq_metricBall]
  exact Metric.mem_ball_self (by positivity)

private theorem scaleZeroCollar_subset_unitCube {d : ℕ} (z : Vec d) :
    {x : Vec d | ‖x - z‖ ≤ (3 / 8 : ℝ)} ⊆ translatedCube d 0 z := by
  rw [translatedCube_eq_metricBall]
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm]
  change ‖x - z‖ ≤ (3 / 8 : ℝ) at hx
  simpa only [norm_sub_rev, zpow_zero, mul_one] using hx.trans_lt (by norm_num)

private theorem middleHalfSubcube_rebase_zero
    {d m j : ℕ} (hmj : m < j) {z' : Vec d} {B' : Set (Vec d)}
    (hB'eq : B' = translatedCube d ((m : ℤ) - j) z') :
    IsMiddleHalfSubcube 0 z' (j - m) B' := by
  refine ⟨z', ?_, ?_⟩
  · have hcast : (0 : ℤ) - ((j - m : ℕ) : ℤ) = (m : ℤ) - (j : ℤ) := by
      omega
    simpa only [hcast] using hB'eq
  · intro x hx
    rw [hB'eq, translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm] at hx
    have hp : (3 : ℝ) ^ ((m : ℤ) - (j : ℤ)) ≤ 1 / 3 := by
      have he : (m : ℤ) - (j : ℤ) ≤ -1 := by omega
      have ht := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) he
      norm_num at ht ⊢
      exact ht
    simpa only [zpow_zero, div_one, norm_sub_rev] using hx.le.trans (by nlinarith)

theorem aux_dedup_d205_bddAbove_oscillationValues_of_compact
    {d : ℕ} {K : Set (Vec d)} {f : Vec d → ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    BddAbove {q : ℝ | ∃ x ∈ K, ∃ y ∈ K, q = |f x - f y|} := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.norm
  refine ⟨2 * C, ?_⟩
  rintro q ⟨x, hx, y, hy, rfl⟩
  have hxC : |f x| ≤ C := by
    simpa only [Real.norm_eq_abs, abs_abs] using hC x hx
  have hyC : |f y| ≤ C := by
    simpa only [Real.norm_eq_abs, abs_abs] using hC y hy
  exact (abs_sub (f x) (f y)).trans (by linarith)

private theorem bddAbove_oscillationValues_of_compact
    {d : ℕ} {K : Set (Vec d)} {f : Vec d → ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    BddAbove {q : ℝ | ∃ x ∈ K, ∃ y ∈ K, q = |f x - f y|} := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.aux_dedup_d205_bddAbove_oscillationValues_of_compact (d := d) (K := K) (f := f) (hK := hK) (hf := hf)

private theorem bddAbove_pointValues_of_closedBall
    {d : ℕ} {B : Set (Vec d)} {z : Vec d} {f : Vec d → ℝ} (a : ℝ)
    (hsub : Metric.closedBall z (1 / 2 : ℝ) ⊆ B)
    (hf : ContinuousOn f B) :
    BddAbove {r : ℝ | ∃ x ∈ translatedCube d 0 z, r = |f x - a|} := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall z (1 / 2 : ℝ)).exists_bound_of_continuousOn
    ((hf.mono hsub).norm)
  refine ⟨K + |a|, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  have hxclosed : x ∈ Metric.closedBall z (1 / 2 : ℝ) := by
    rw [translatedCube_eq_metricBall] at hx
    simpa only [zpow_zero, mul_one] using Metric.ball_subset_closedBall hx
  have hxK : |f x| ≤ K := by
    simpa only [Real.norm_eq_abs, abs_abs] using hK x hxclosed
  exact (abs_sub (f x) a).trans (by linarith [abs_nonneg a])

private theorem compose_positiveBelowScale_oscillation
    {d m j : ℕ} (hmj : m < j) {c C₀ : ℝ} {f : Vec d → ℝ}
    {B' Q S₀ S : Set (Vec d)}
    (hsmall : oscillationOn B' f ≤
      boundedMultiplierNonpositiveOscillationConst d c *
        (3 : ℝ) ^ (-c * ((j - m : ℕ) : ℝ)) * oscillationOn S₀ f)
    (h₀Q : oscillationOn S₀ f ≤ oscillationOn Q f)
    (hLarge : oscillationOn Q f ≤
      C₀ * (3 : ℝ) ^ (-c * (m : ℝ)) * oscillationOn S f)
    (hC₀ : 0 < C₀) (hS : 0 ≤ oscillationOn S f) :
    oscillationOn B' f ≤
      boundedMultiplierSealConstant d c C₀ *
        (3 : ℝ) ^ (-(c * ((((j : ℤ) - (m : ℤ) : ℤ) : ℝ)))) *
          ((3 : ℝ) ^ (-(c * (m : ℝ))) * oscillationOn S f) := by
  have hcoef : boundedMultiplierNonpositiveOscillationConst d c * C₀ ≤
      boundedMultiplierSealConstant d c C₀ := by
    unfold boundedMultiplierSealConstant
    have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
    have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d
    nlinarith
  calc
    oscillationOn B' f ≤ boundedMultiplierNonpositiveOscillationConst d c *
        (3 : ℝ) ^ (-c * ((j - m : ℕ) : ℝ)) * oscillationOn S₀ f := hsmall
    _ ≤ boundedMultiplierNonpositiveOscillationConst d c *
        (3 : ℝ) ^ (-c * ((j - m : ℕ) : ℝ)) * oscillationOn Q f :=
      mul_le_mul_of_nonneg_left h₀Q
        (mul_nonneg (boundedMultiplierNonpositiveOscillationConst_pos d c).le
          (Real.rpow_nonneg (by norm_num) _))
    _ ≤ boundedMultiplierNonpositiveOscillationConst d c *
        (3 : ℝ) ^ (-c * ((j - m : ℕ) : ℝ)) *
          (C₀ * (3 : ℝ) ^ (-c * (m : ℝ)) * oscillationOn S f) :=
      mul_le_mul_of_nonneg_left hLarge
        (mul_nonneg (boundedMultiplierNonpositiveOscillationConst_pos d c).le
          (Real.rpow_nonneg (by norm_num) _))
    _ = (boundedMultiplierNonpositiveOscillationConst d c * C₀) *
        (3 : ℝ) ^ (-c * ((j - m : ℕ) : ℝ)) *
          ((3 : ℝ) ^ (-c * (m : ℝ)) * oscillationOn S f) := by ring
    _ ≤ boundedMultiplierSealConstant d c C₀ *
        (3 : ℝ) ^ (-c * ((j - m : ℕ) : ℝ)) *
          ((3 : ℝ) ^ (-c * (m : ℝ)) * oscillationOn S f) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by norm_num) _))
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hS)
    _ = _ := by
      have hcast : ((j - m : ℕ) : ℝ) = (j : ℝ) - (m : ℝ) := by
        rw [Nat.cast_sub (Nat.le_of_lt hmj)]
      rw [hcast]
      norm_num

/-- Increasing the deterministic constant preserves a pathwise readout. -/
theorem boundedMultiplierPathwiseEstimate_mono_constant
    {d : ℕ} (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d)
    (j : ℕ) (B' : Set (Vec d)) (epsilon c C₀ C : ℝ)
    (hC₀C : C₀ ≤ C) (omega : Sample d)
    (hout : BoundedMultiplierPathwiseEstimate
      M L m z j B' epsilon C₀ c omega) :
    BoundedMultiplierPathwiseEstimate M L m z j B' epsilon C c omega := by
  intro theta hthetaCont hthetaPos hthetaClose h hharm
  obtain ⟨hRep, hRepCont, hRepAE, hosc, hsup⟩ :=
    hout theta hthetaCont hthetaPos hthetaClose h hharm
  refine ⟨hRep, hRepCont, hRepAE, ?_, ?_⟩
  · have hOsc : 0 ≤ oscillationOn
        {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ m / 8} hRep := by
      apply oscillationOn_nonneg_of_nonempty
      exact ⟨z, by simp; positivity⟩
    exact hosc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₀C (Real.rpow_nonneg (by norm_num) _)) hOsc)
  · exact hsup.trans (mul_le_mul_of_nonneg_right hC₀C
      (normalizedL2On_nonneg _ _))

/-- Append the sub-unit contraction to a depth-`m` theta-ladder readout. -/
theorem positiveBelowScalePathwise_of_scaleOne
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (M : GMCModel d) (L m : ℕ) (hm : 1 ≤ m) (z z' : Vec d)
    (j : ℕ) (hmj : m < j) {B' : Set (Vec d)}
    (hB'eq : B' = translatedCube d ((m : ℤ) - j) z')
    (hz'collar : ‖z' - z‖ ≤ (3 : ℝ) ^ (m : ℤ) / 4)
    (omega : Sample d) {epsilon C₀ c : ℝ}
    (hepsilon : epsilon ≤ boundedMultiplierEpsilonStar d)
    (hc0 : 0 ≤ c) (hcHalf : c ≤ 1 / 2) (hC₀ : 0 < C₀)
    (hgood0 : omega ∈ coveringRestrictedGradientGood M L 0 z')
    (hscaleOne : BoundedMultiplierPathwiseEstimate M L (m : ℤ)
      z m (translatedCube d 0 z') epsilon C₀ c omega) :
    BoundedMultiplierBelowScalePathwiseEstimate M L (m : ℤ) z j B'
      epsilon (boundedMultiplierSealConstant d c C₀) c omega := by
  intro theta hthetaCont hthetaPos hthetaClose h hharm
  obtain ⟨b, hb, hclose⟩ := hthetaClose
  obtain ⟨hLarge, hLargeCont, hLargeAE, hLargeOsc, hLargeSup⟩ :=
    hscaleOne theta hthetaCont hthetaPos ⟨b, hb, hclose⟩ h hharm
  let B := translatedCube d (m : ℤ) z
  let Q := translatedCube d 0 z'
  have hQsub : Q ⊆ B := by
    intro x hx
    change x ∈ translatedCube d 0 z' at hx
    change x ∈ translatedCube d (m : ℤ) z
    rw [translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm] at hx ⊢
    have htri : ‖x - z‖ ≤ ‖x - z'‖ + ‖z' - z‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (x - z') (z' - z)
    have hp : (3 : ℝ) ≤ (3 : ℝ) ^ m := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hm
    have hpz : (3 : ℝ) ≤ (3 : ℝ) ^ (m : ℤ) := by
      simpa only [zpow_natCast] using hp
    have hx' : ‖x - z'‖ < (1 / 2 : ℝ) := by
      simpa only [zpow_zero, mul_one] using hx
    simpa only [zpow_zero, mul_one, norm_sub_rev] using htri.trans_lt (by nlinarith)
  have hBopen : IsOpen B := by
    dsimp only [B]
    rw [translatedCube_eq_metricBall]
    exact Metric.isOpen_ball
  have hQopen : IsOpen Q := by
    dsimp only [Q]
    rw [translatedCube_eq_metricBall]
    exact Metric.isOpen_ball
  let hRep := euclideanBallAverageRepresentative h.toFun
  have hsCont : ContinuousOn (fun x ↦ aCutoff M L omega x * theta x) B :=
    (continuous_aCutoff M L omega).continuousOn.mul hthetaCont
  have hsPos : ∀ x ∈ B, 0 < aCutoff M L omega x * theta x := by
    intro x hx
    exact mul_pos (aCutoff_pos M L omega x) (hthetaPos x hx)
  obtain ⟨hRepCont, hRepAE⟩ :=
    continuousOn_and_ae_eq_euclideanBallAverageRepresentative
      hd hBopen hsCont hsPos (by simpa only [B] using hharm)
  have hEqLarge : Set.EqOn hLarge hRep B :=
    Measure.eqOn_open_of_ae_eq (hLargeAE.trans hRepAE.symm) hBopen
      hLargeCont hRepCont
  have hcollarSub :
      {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8} ⊆ B := by
    dsimp only [B]
    rw [translatedCube_eq_metricBall]
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖x - z‖ ≤ _ at hx
    simpa only [norm_sub_rev] using hx.trans_lt (by
      have hp : 0 < (3 : ℝ) ^ (m : ℤ) := by positivity
      nlinarith)
  have hLargeOsc' : oscillationOn Q hRep ≤
      C₀ * (3 : ℝ) ^ (-c * (m : ℝ)) *
        oscillationOn {x : Vec d | ‖x - z‖ ≤
          3 * (3 : ℝ) ^ (m : ℤ) / 8} hRep := by
    rw [← oscillationOn_congr_of_eqOn (hEqLarge.mono hQsub)]
    rw [← oscillationOn_congr_of_eqOn (hEqLarge.mono hcollarSub)]
    exact hLargeOsc
  let hQ : H1Function Q := h.restrict hQopen hQsub
  have hharmQ : IsWeaklyHarmonicOn
      (fun x ↦ aCutoff M L omega x * theta x) Q hQ :=
    Section6BoundaryL2.isWeaklyHarmonicOn_restrict hBopen hQopen hQsub hharm
  have hB'zero : IsMiddleHalfSubcube 0 z' (j - m) B' :=
    middleHalfSubcube_rebase_zero hmj hB'eq
  have hsmallOsc := nonpositive_middleHalfSubcube_oscillation_decay
    hd M L (m := (0 : ℤ)) le_rfl z' (by omega : 0 < j - m) hB'zero
      omega hgood0 (hthetaCont.mono hQsub) (fun x hx ↦ hthetaPos x (hQsub hx))
      hb (fun x hx ↦ (hclose x (hQsub hx)).trans hepsilon) hharmQ hc0 hcHalf
  have hcollar0sub :
      {x : Vec d | ‖x - z'‖ ≤ 3 * (3 : ℝ) ^ (0 : ℤ) / 8} ⊆ Q := by
    simpa only [zpow_zero, mul_one, Q] using scaleZeroCollar_subset_unitCube z'
  have hclosedQsub : Metric.closedBall z' (1 / 2 : ℝ) ⊆ B := by
    intro x hx
    dsimp only [B]
    rw [translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    have htri : ‖x - z‖ ≤ ‖x - z'‖ + ‖z' - z‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (x - z') (z' - z)
    have hp : (3 : ℝ) ≤ (3 : ℝ) ^ m := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hm
    have hpz : (3 : ℝ) ≤ (3 : ℝ) ^ (m : ℤ) := by
      simpa only [zpow_natCast] using hp
    simpa only [norm_sub_rev] using htri.trans_lt (by nlinarith)
  have hosc0Q : oscillationOn
      {x : Vec d | ‖x - z'‖ ≤ 3 * (3 : ℝ) ^ (0 : ℤ) / 8} hRep ≤
      oscillationOn Q hRep := by
    apply oscillationOn_le_of_subset_of_bddAbove
    · exact ⟨z', by simp; norm_num⟩
    · exact hcollar0sub
    · have hbdd := bddAbove_oscillationValues_of_compact
          (isCompact_closedBall z' (1 / 2 : ℝ)) (hRepCont.mono hclosedQsub)
      rcases hbdd with ⟨K, hK⟩
      refine ⟨K, ?_⟩
      rintro q ⟨x, hx, y, hy, rfl⟩
      apply hK
      refine ⟨x, ?_, y, ?_, rfl⟩
      · dsimp only [Q] at hx
        rw [translatedCube_eq_metricBall] at hx
        simpa only [zpow_zero, mul_one] using Metric.ball_subset_closedBall hx
      · dsimp only [Q] at hy
        rw [translatedCube_eq_metricBall] at hy
        simpa only [zpow_zero, mul_one] using Metric.ball_subset_closedBall hy
  have hOscParent : 0 ≤ oscillationOn
      {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8} hRep := by
    apply oscillationOn_nonneg_of_nonempty
    exact ⟨z, by simp; positivity⟩
  have hsmallOsc' : oscillationOn B' hRep ≤
      boundedMultiplierNonpositiveOscillationConst d c *
        (3 : ℝ) ^ (-c * ((j - m : ℕ) : ℝ)) *
          oscillationOn {x : Vec d | ‖x - z'‖ ≤
            3 * (3 : ℝ) ^ (0 : ℤ) / 8} hRep := by
    simpa only [hRep, hQ, H1Function.restrict, sub_zero, Int.cast_natCast,
      Nat.cast_sub (Nat.le_of_lt hmj)] using hsmallOsc
  have hosc := compose_positiveBelowScale_oscillation hmj hsmallOsc' hosc0Q
    hLargeOsc' hC₀ hOscParent
  have havg : averageOn B hLarge = averageOn B hRep :=
    averageOn_eq_of_ae_eq (hLargeAE.trans hRepAE.symm)
  have hnorm : normalizedL2On B
      (fun x ↦ hLarge x - averageOn B hLarge) =
        normalizedL2On B (fun x ↦ hRep x - averageOn B hRep) :=
    normalizedL2On_sub_average_eq_of_ae_eq (hLargeAE.trans hRepAE.symm)
  have hbddLarge := bddAbove_pointValues_of_closedBall
    (B := B) (z := z') (f := hLarge) (averageOn B hLarge) hclosedQsub hLargeCont
  have hB'subQ : B' ⊆ Q := by
    rw [hB'eq]
    exact translatedCube_subset_translatedCube_sameCenter (by omega) z'
  have hpoint : ∀ x ∈ B',
      |hRep x - averageOn B hRep| ≤ C₀ *
        normalizedL2On B (fun y ↦ hRep y - averageOn B hRep) := by
    intro x hx
    have hxQ := hB'subQ hx
    have hxLarge : |hLarge x - averageOn B hLarge| ≤
        sSup {r : ℝ | ∃ y ∈ Q, r = |hLarge y - averageOn B hLarge|} :=
      le_csSup hbddLarge ⟨x, hxQ, rfl⟩
    calc
      |hRep x - averageOn B hRep| =
          |hLarge x - averageOn B hLarge| := by
        rw [hEqLarge (hQsub hxQ), havg]
      _ ≤ C₀ * normalizedL2On B
          (fun y ↦ hLarge y - averageOn B hLarge) := hxLarge.trans hLargeSup
      _ = C₀ * normalizedL2On B
          (fun y ↦ hRep y - averageOn B hRep) := by rw [hnorm]
  have hz'mem : z' ∈ B' := targetCentre_mem hB'eq
  have hC₀Seal : C₀ ≤ boundedMultiplierSealConstant d c C₀ :=
    (boundedMultiplierSealConstant_base_lt d hC₀).le
  have henergy := mul_le_mul_of_nonneg_right hC₀Seal
    (normalizedL2On_nonneg B (fun y ↦ hRep y - averageOn B hRep))
  have hsup := (pointwiseConclusions_of_commonReference ⟨z', hz'mem⟩ hRep
    (averageOn B hRep)
    (C₀ * normalizedL2On B (fun y ↦ hRep y - averageOn B hRep))
    (2 * (C₀ * normalizedL2On B (fun y ↦ hRep y - averageOn B hRep)))
    (boundedMultiplierSealConstant d c C₀ *
      normalizedL2On B (fun y ↦ hRep y - averageOn B hRep))
    hpoint le_rfl henergy).2
  exact ⟨hRep, hRepCont, hRepAE, hosc, hsup⟩

/-- Union the depth-`m` theta event with the target unit-cell gradient event. -/
theorem exists_bad_positiveBelowScale_of_scaleOneEvent
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (M : GMCModel d) (L m : ℕ) (hm : 1 ≤ m) (z z' : Vec d)
    (j : ℕ) (hmj : m < j) {B' : Set (Vec d)}
    (hB'eq : B' = translatedCube d ((m : ℤ) - j) z')
    (hz'collar : ‖z' - z‖ ≤ (3 : ℝ) ^ (m : ℤ) / 4)
    {epsilon C₀ c : ℝ} (hepsilon : epsilon ≤ boundedMultiplierEpsilonStar d)
    (hc0 : 0 ≤ c) (hcHalf : c ≤ 1 / 2) (hC₀ : 1 ≤ C₀)
    (hscaleEvent : ∃ badTheta : Set (Sample d),
      MeasurableSet badTheta ∧
      M.P.toMeasure badTheta ≤ ENNReal.ofReal
        ((C₀ - 1) * Real.exp
          (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
      ∀ omega ∉ badTheta,
        omega ∈ coveringRestrictedGradientGood M L (m : ℤ) z →
          BoundedMultiplierPathwiseEstimate M L (m : ℤ) z m
            (translatedCube d 0 z') epsilon C₀ c omega) :
    ∃ bad : Set (Sample d), MeasurableSet bad ∧
      M.P.toMeasure bad ≤ ENNReal.ofReal
        ((boundedMultiplierSealConstant d c C₀ - 1) * Real.exp
          (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
      ∀ omega ∉ bad,
        omega ∈ coveringRestrictedGradientGood M L (m : ℤ) z →
          BoundedMultiplierBelowScalePathwiseEstimate M L (m : ℤ) z j B'
            epsilon (boundedMultiplierSealConstant d c C₀) c omega := by
  obtain ⟨badTheta, hbadThetaMeas, hbadThetaTail, hscale⟩ := hscaleEvent
  let badGradient : Set (Sample d) :=
    (coveringRestrictedGradientGood M L 0 z')ᶜ
  have hbadGradientMeas : MeasurableSet badGradient :=
    (restrictedCoefficientSigma_le
      (fun x _hx ↦ measurable_aCutoff M L x)) _
        (measurableSet_coveringRestrictedGradientGood M L 0 z').compl
  refine ⟨badTheta ∪ badGradient, hbadThetaMeas.union hbadGradientMeas, ?_, ?_⟩
  · have hlog : Real.log M.delta < 0 :=
      Real.log_neg M.shellPrefix.delta_pos
        (M.shellPrefix.delta_le_half.trans_lt (by norm_num))
    have hden : 0 < M.delta ^ 2 * |Real.log M.delta| ^ 2 :=
      mul_pos (sq_pos_of_pos M.shellPrefix.delta_pos)
        (sq_pos_of_pos (abs_pos.mpr hlog.ne))
    have hc1 : c ≤ 1 := hcHalf.trans (by norm_num)
    have hexp : Real.exp
        (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) ≤
        Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have hdiv := div_le_div_of_nonneg_right hc1 hden.le
      simpa only [neg_div] using neg_le_neg hdiv
    have hcoef : C₀ ≤ boundedMultiplierSealConstant d c C₀ - 1 := by
      unfold boundedMultiplierSealConstant
      have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
      have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d
      nlinarith
    have hsum :
        (C₀ - 1) * Real.exp
            (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) +
          Real.exp (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) ≤
        (boundedMultiplierSealConstant d c C₀ - 1) *
          Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) := by
      nlinarith [Real.exp_pos
        (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))]
    calc
      M.P.toMeasure (badTheta ∪ badGradient) ≤
          M.P.toMeasure badTheta + M.P.toMeasure badGradient := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((C₀ - 1) * Real.exp
            (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) +
          ENNReal.ofReal (Real.exp
            (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) :=
        add_le_add hbadThetaTail
          (measure_compl_coveringRestrictedGradientGood_le M L 0 z')
      _ = ENNReal.ofReal
          ((C₀ - 1) * Real.exp
              (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2)) +
            Real.exp (-1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) := by
        rw [ENNReal.ofReal_add
          (mul_nonneg (sub_nonneg.mpr hC₀) (Real.exp_pos _).le)
          (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal
          ((boundedMultiplierSealConstant d c C₀ - 1) *
            Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) :=
        ENNReal.ofReal_le_ofReal hsum
  · intro omega homega hgoodParent
    have homegaTheta : omega ∉ badTheta := by
      intro hmem
      exact homega (Set.mem_union_left badGradient hmem)
    have hgood0 : omega ∈ coveringRestrictedGradientGood M L 0 z' := by
      by_contra hnot
      exact homega (Set.mem_union_right badTheta hnot)
    exact positiveBelowScalePathwise_of_scaleOne hd M L m hm z z' j hmj
      hB'eq hz'collar omega hepsilon hc0 hcHalf (zero_lt_one.trans_le hC₀) hgood0
        (hscale omega homegaTheta hgoodParent)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
