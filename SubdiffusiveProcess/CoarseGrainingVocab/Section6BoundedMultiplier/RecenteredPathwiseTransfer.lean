module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.PositiveBelowScaleEventPackaging
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.TriadicMeanComparison

@[expose] public section

/-!
# Transfer from a target-centred predecessor cube
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Topology Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

def recenteredTransferConstant (d : ℕ) (c C : ℝ) : ℝ :=
  C * (3 : ℝ) ^ c + (C + 1) * Real.sqrt ((3 : ℝ) ^ d) + 1

theorem recenteredTransferConstant_pos
    (d : ℕ) {c C : ℝ} (hC : 0 ≤ C) :
    0 < recenteredTransferConstant d c C := by
  unfold recenteredTransferConstant
  positivity

private theorem predecessor_subset_parent {d m : ℕ} (hm : 1 ≤ m)
    {z z' : Vec d} (hz' : ‖z' - z‖ ≤ (3 : ℝ) ^ (m : ℤ) / 4) :
    translatedCube d ((m - 1 : ℕ) : ℤ) z' ⊆ translatedCube d (m : ℤ) z := by
  rw [translatedCube_eq_metricBall, translatedCube_eq_metricBall]
  apply Metric.ball_subset_ball'
  rw [dist_eq_norm]
  have hp : (3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) = (3 : ℝ) ^ (m : ℤ) / 3 := by
    rw [Nat.cast_sub hm, Nat.cast_one, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  rw [hp]
  have hpos : 0 < (3 : ℝ) ^ (m : ℤ) := by positivity
  nlinarith

private theorem predecessorCollar_subset_parentCollar {d m : ℕ} (hm : 1 ≤ m)
    {z z' : Vec d} (hz' : ‖z' - z‖ ≤ (3 : ℝ) ^ (m : ℤ) / 4) :
    {x : Vec d | ‖x - z'‖ ≤ 3 * (3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) / 8} ⊆
      {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8} := by
  intro x hx
  have htri : ‖x - z‖ ≤ ‖x - z'‖ + ‖z' - z‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (x - z') (z' - z)
  have hp : (3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) = (3 : ℝ) ^ (m : ℤ) / 3 := by
    rw [Nat.cast_sub hm, Nat.cast_one, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  change ‖x - z'‖ ≤ _ at hx
  rw [hp] at hx
  have hx' : ‖x - z'‖ ≤ (3 : ℝ) ^ (m : ℤ) / 8 := by nlinarith
  exact htri.trans (by linarith)

private theorem normalizedL2_predecessor_le_parent
    {d n : ℕ} {z z' : Vec d} {f : Vec d → ℝ}
    (hsub : translatedCube d (n : ℤ) z' ⊆ translatedCube d (n + 1 : ℕ) z)
    (hf : IntegrableOn f (translatedCube d (n + 1 : ℕ) z))
    (hf2 : IntegrableOn (fun x ↦ f x ^ 2) (translatedCube d (n + 1 : ℕ) z)) :
    normalizedL2On (translatedCube d (n : ℤ) z')
        (fun x ↦ f x - averageOn (translatedCube d (n : ℤ) z') f) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On (translatedCube d (n + 1 : ℕ) z)
          (fun x ↦ f x - averageOn (translatedCube d (n + 1 : ℕ) z) f) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.normalizedL2On_centered_le_sqrt_three_of_subset_succ
      (ell := (n : ℤ)) (zInner := z') (zOuter := z) hsub hf hf2

private theorem bddAbove_pointValues_on_target
    {d m j : ℕ} (hmj : m < j) {z' : Vec d}
    {B' : Set (Vec d)} (hB' : B' = translatedCube d ((m : ℤ) - j) z')
    {f : Vec d → ℝ}
    (hf : ContinuousOn f (translatedCube d ((m - 1 : ℕ) : ℤ) z')) (a : ℝ) :
    BddAbove {r : ℝ | ∃ x ∈ B', r = |f x - a|} := by
  let K := Metric.closedBall z' (1 / 3 : ℝ)
  have hKB : K ⊆ translatedCube d ((m - 1 : ℕ) : ℤ) z' := by
    rw [translatedCube_eq_metricBall]
    exact Metric.closedBall_subset_ball (by
      have hp : (1 : ℝ) ≤ (3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) := by
        rw [zpow_natCast]
        exact one_le_pow₀ (by norm_num)
      nlinarith)
  have hB'K : B' ⊆ K := by
    rw [hB', translatedCube_eq_metricBall]
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    have he : (m : ℤ) - (j : ℤ) ≤ -1 := by omega
    have hp := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) he
    norm_num at hp
    simpa only [norm_sub_rev] using hx.le.trans (by nlinarith)
  obtain ⟨A, hA⟩ := (isCompact_closedBall z' (1 / 3 : ℝ)).exists_bound_of_continuousOn
    ((hf.mono hKB).norm)
  refine ⟨A + |a|, ?_⟩
  rintro r ⟨x, hx, rfl⟩
  have hxA : |f x| ≤ A := by
    simpa only [Real.norm_eq_abs, abs_abs] using hA x (hB'K hx)
  exact (abs_sub (f x) a).trans (by linarith [abs_nonneg a])

private theorem bddAbove_oscillationValues_of_compact
    {d : ℕ} {K : Set (Vec d)} {f : Vec d → ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    BddAbove {q : ℝ | ∃ x ∈ K, ∃ y ∈ K, q = |f x - f y|} := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.aux_dedup_d205_bddAbove_oscillationValues_of_compact (d := d) (K := K) (f := f) (hK := hK) (hf := hf)

private theorem predecessor_exponent_transfer
    {m j : ℕ} (hm : 1 ≤ m) (hmj : m < j) {c C O₀ O : ℝ}
    (hC : 0 ≤ C) (hO₀O : O₀ ≤ O) :
    C * (3 : ℝ) ^
        (-(c * (((((j - 1 : ℕ) : ℤ) - ((m - 1 : ℕ) : ℤ) : ℤ) : ℝ)))) *
        ((3 : ℝ) ^ (-(c * ((m - 1 : ℕ) : ℝ))) * O₀) ≤
      (C * (3 : ℝ) ^ c) *
        (3 : ℝ) ^ (-(c * ((((j : ℤ) - (m : ℤ) : ℤ) : ℝ)))) *
        ((3 : ℝ) ^ (-(c * (m : ℝ))) * O) := by
  have hdepth : ((j - 1 : ℕ) : ℤ) - ((m - 1 : ℕ) : ℤ) =
      (j : ℤ) - (m : ℤ) := by omega
  have hpow : (3 : ℝ) ^ (-(c * ((m - 1 : ℕ) : ℝ))) =
      (3 : ℝ) ^ c * (3 : ℝ) ^ (-(c * (m : ℝ))) := by
    rw [Nat.cast_sub hm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    norm_num
    ring
  rw [hdepth, hpow]
  ring_nf
  exact mul_le_mul_of_nonneg_left hO₀O (by positivity)

/-- Transfer the target-centred predecessor conclusion to the original parent. -/
theorem boundedMultiplierBelowScalePathwiseEstimate_of_recentered
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) (M : GMCModel d) (L m : ℕ)
    (hm : 1 ≤ m) (z z' : Vec d) (j : ℕ) (hmj : m < j)
    {B' : Set (Vec d)} (hB' : B' = translatedCube d ((m : ℤ) - j) z')
    (hz' : ‖z' - z‖ ≤ (3 : ℝ) ^ (m : ℤ) / 4)
    (omega : Sample d) {epsilon C c : ℝ} (hC : 0 ≤ C)
    (hlocal : BoundedMultiplierBelowScalePathwiseEstimate M L
      ((m - 1 : ℕ) : ℤ) z' (j - 1) B' epsilon C c omega) :
    BoundedMultiplierBelowScalePathwiseEstimate M L (m : ℤ) z j B' epsilon
      (recenteredTransferConstant d c C) c omega := by
  intro theta hthetaCont hthetaPos hthetaClose h hharm
  let B := translatedCube d (m : ℤ) z
  let P := translatedCube d ((m - 1 : ℕ) : ℤ) z'
  have hPsub : P ⊆ B := predecessor_subset_parent hm hz'
  have hBopen : IsOpen B := by dsimp only [B]; rw [translatedCube_eq_metricBall]; exact Metric.isOpen_ball
  have hPopen : IsOpen P := by dsimp only [P]; rw [translatedCube_eq_metricBall]; exact Metric.isOpen_ball
  let hP : H1Function P := h.restrict hPopen hPsub
  have hharmP := Section6BoundaryL2.isWeaklyHarmonicOn_restrict hBopen hPopen hPsub hharm
  obtain ⟨hLoc, hLocCont, hLocAE, hLocOsc, hLocSup⟩ :=
    hlocal theta (hthetaCont.mono hPsub) (fun x hx ↦ hthetaPos x (hPsub hx))
      (by rcases hthetaClose with ⟨b, hb, ht⟩; exact ⟨b, hb, fun x hx ↦ ht x (hPsub hx)⟩)
      hP hharmP
  let hRep := euclideanBallAverageRepresentative h.toFun
  have hsCont := (continuous_aCutoff M L omega).continuousOn.mul hthetaCont
  have hsPos : ∀ x ∈ B, 0 < aCutoff M L omega x * theta x :=
    fun x hx ↦ mul_pos (aCutoff_pos M L omega x) (hthetaPos x hx)
  obtain ⟨hRepCont, hRepAE⟩ := continuousOn_and_ae_eq_euclideanBallAverageRepresentative
    hd hBopen hsCont hsPos (by simpa only [B] using! hharm)
  have hRepAEP : hRep =ᵐ[volume.restrict P] hP.toFun := by
    have ht := ae_restrict_of_ae_restrict_of_subset hPsub hRepAE
    simpa only [hRep, hP, H1Function.restrict] using! ht
  have hEq : Set.EqOn hLoc hRep P := Measure.eqOn_open_of_ae_eq
    (hLocAE.trans hRepAEP.symm) hPopen hLocCont (hRepCont.mono hPsub)
  have hB'P : B' ⊆ P := by rw [hB']; exact translatedCube_subset_translatedCube_sameCenter (by omega) z'
  let D₀ := {x : Vec d | ‖x - z'‖ ≤ 3 * (3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) / 8}
  let D := {x : Vec d | ‖x - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8}
  have hD₀P : D₀ ⊆ P := by
    intro x hx
    change ‖x - z'‖ ≤ 3 * (3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) / 8 at hx
    dsimp only [P]
    rw [translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm]
    simpa only [norm_sub_rev] using hx.trans_lt (by
      have hp : 0 < (3 : ℝ) ^ ((m - 1 : ℕ) : ℤ) := by positivity
      nlinarith)
  have hD₀D : D₀ ⊆ D := predecessorCollar_subset_parentCollar hm hz'
  have hDB : D ⊆ B := by
    intro x hx
    change ‖x - z‖ ≤ 3 * (3 : ℝ) ^ (m : ℤ) / 8 at hx
    dsimp only [B]
    rw [translatedCube_eq_metricBall, Metric.mem_ball, dist_eq_norm]
    simpa only [norm_sub_rev] using hx.trans_lt (by
      have hp : 0 < (3 : ℝ) ^ (m : ℤ) := by positivity
      nlinarith)
  have hDOsc : 0 ≤ oscillationOn D hRep := oscillationOn_nonneg_of_nonempty ⟨z, by simp [D]; positivity⟩
  have hmono : oscillationOn D₀ hRep ≤ oscillationOn D hRep := by
    apply oscillationOn_le_of_subset_of_bddAbove
    · exact ⟨z', by simp [D₀]; positivity⟩
    · exact hD₀D
    · exact bddAbove_oscillationValues_of_compact
        (by rw [show D = Metric.closedBall z (3 * (3 : ℝ) ^ (m : ℤ) / 8) by ext x; simp [D, dist_eq_norm, norm_sub_rev]]
            exact isCompact_closedBall _ _)
        (hRepCont.mono hDB)
  have hLocOsc' : oscillationOn B' hRep ≤
      C * (3 : ℝ) ^ (-(c * (((((j - 1 : ℕ) : ℤ) - ((m - 1 : ℕ) : ℤ) : ℤ) : ℝ)))) *
        ((3 : ℝ) ^ (-(c * ((m - 1 : ℕ) : ℝ))) * oscillationOn D₀ hRep) := by
    rw [← oscillationOn_congr_of_eqOn (hEq.mono hB'P)]
    rw [← oscillationOn_congr_of_eqOn (hEq.mono hD₀P)]
    exact hLocOsc
  have hoscBase := predecessor_exponent_transfer (c := c) hm hmj hC hmono
  have hcoef : C * (3 : ℝ) ^ c ≤ recenteredTransferConstant d c C := by
    unfold recenteredTransferConstant
    have ht : 0 ≤ (C + 1) * Real.sqrt ((3 : ℝ) ^ d) :=
      mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    linarith
  have hosc : oscillationOn B' hRep ≤ recenteredTransferConstant d c C *
      (3 : ℝ) ^ (-(c * ((((j : ℤ) - (m : ℤ) : ℤ) : ℝ)))) *
        ((3 : ℝ) ^ (-(c * (m : ℝ))) * oscillationOn D hRep) :=
    hLocOsc'.trans (hoscBase.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by norm_num) _))
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hDOsc)))
  letI : IsFiniteMeasure (volume.restrict B) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr (by
        dsimp only [B]
        exact volume_translatedCube_ne_top (m : ℤ) z)⟩
  have hf : IntegrableOn h.toFun B := h.memL2.integrable one_le_two
  have hf2 : IntegrableOn (fun x ↦ h.toFun x ^ 2) B := h.memL2.integrable_sq
  have hn : normalizedL2On P (fun x ↦ h.toFun x - averageOn P h.toFun) ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On B (fun x ↦ h.toFun x - averageOn B h.toFun) := by
    simpa only [P, B, Nat.sub_add_cancel hm] using
      (normalizedL2_predecessor_le_parent (n := m - 1) (z := z) (z' := z')
        (by simpa only [P, B, Nat.sub_add_cancel hm] using hPsub)
        (by simpa only [B, Nat.sub_add_cancel hm] using hf)
        (by simpa only [B, Nat.sub_add_cancel hm] using hf2))
  have ha := abs_averageOn_translatedCube_pred_sub_le_of_subset
    (ell := (m : ℤ)) (zInner := z') (zOuter := z) (f := h.toFun)
    (by simpa only [P, B, Nat.cast_sub hm, Nat.cast_one] using hPsub) hf hf2
  have ha' : |averageOn P h.toFun - averageOn B h.toFun| ≤
      Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On B (fun x ↦ h.toFun x - averageOn B h.toFun) := by
    simpa only [P, B, Nat.cast_sub hm, Nat.cast_one] using ha
  have hLocAEP : hLoc =ᵐ[volume.restrict P] h.toFun := by
    simpa only [P, hP, H1Function.restrict] using hLocAE
  have havgLoc : averageOn P hLoc = averageOn P h.toFun :=
    averageOn_eq_of_ae_eq hLocAEP
  have hnormLoc : normalizedL2On P (fun x ↦ hLoc x - averageOn P hLoc) =
      normalizedL2On P (fun x ↦ h.toFun x - averageOn P h.toFun) :=
    normalizedL2On_sub_average_eq_of_ae_eq hLocAEP
  have havgRep := averageOn_eq_of_ae_eq hRepAE
  have hnormRep := normalizedL2On_sub_average_eq_of_ae_eq hRepAE
  have hbdd := bddAbove_pointValues_on_target hmj hB' hLocCont (averageOn P hLoc)
  have hLocSup' : sSup {r : ℝ | ∃ x ∈ B',
      r = |hLoc x - averageOn P hLoc|} ≤
      C * normalizedL2On P (fun x ↦ hLoc x - averageOn P hLoc) := by
    simpa only [P] using hLocSup
  have hpoint : ∀ x ∈ B', |hRep x - averageOn B hRep| ≤
      (C + 1) * Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On B (fun y ↦ hRep y - averageOn B hRep) := by
    intro x hx
    have hxSup := le_csSup hbdd ⟨x, hx, rfl⟩
    have hxLoc : |hLoc x - averageOn P h.toFun| ≤
        C * normalizedL2On P (fun y ↦ h.toFun y - averageOn P h.toFun) := by
      calc
        |hLoc x - averageOn P h.toFun| = |hLoc x - averageOn P hLoc| := by
          rw [← havgLoc]
        _ ≤ C * normalizedL2On P (fun y ↦ hLoc y - averageOn P hLoc) :=
          hxSup.trans hLocSup'
        _ = C * normalizedL2On P
            (fun y ↦ h.toFun y - averageOn P h.toFun) := by rw [hnormLoc]
    calc
      |hRep x - averageOn B hRep| = |hLoc x - averageOn B h.toFun| := by
        rw [← hEq (hB'P hx), havgRep]
      _ ≤ |hLoc x - averageOn P h.toFun| +
          |averageOn P h.toFun - averageOn B h.toFun| := abs_sub_le _ _ _
      _ ≤ (C + 1) * Real.sqrt ((3 : ℝ) ^ d) *
          normalizedL2On B (fun y ↦ h.toFun y - averageOn B h.toFun) := by
        nlinarith [hxLoc, hn, ha']
      _ = (C + 1) * Real.sqrt ((3 : ℝ) ^ d) *
          normalizedL2On B (fun y ↦ hRep y - averageOn B hRep) := by
        rw [← hnormRep]
  have hpointCoef : (C + 1) * Real.sqrt ((3 : ℝ) ^ d) ≤
      recenteredTransferConstant d c C := by
    unfold recenteredTransferConstant
    have ht : 0 ≤ C * (3 : ℝ) ^ c :=
      mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
    linarith
  have henergy : (C + 1) * Real.sqrt ((3 : ℝ) ^ d) *
        normalizedL2On B (fun y ↦ hRep y - averageOn B hRep) ≤
      recenteredTransferConstant d c C *
        normalizedL2On B (fun y ↦ hRep y - averageOn B hRep) :=
    mul_le_mul_of_nonneg_right hpointCoef
      (normalizedL2On_nonneg B (fun y ↦ hRep y - averageOn B hRep))
  have hB'ne : B'.Nonempty := ⟨z', by rw [hB', translatedCube_eq_metricBall]; exact Metric.mem_ball_self (by positivity)⟩
  have hsup := (pointwiseConclusions_of_commonReference hB'ne hRep (averageOn B hRep)
    ((C + 1) * Real.sqrt ((3 : ℝ) ^ d) * normalizedL2On B (fun y ↦ hRep y - averageOn B hRep))
    (2 * ((C + 1) * Real.sqrt ((3 : ℝ) ^ d) * normalizedL2On B (fun y ↦ hRep y - averageOn B hRep)))
    (recenteredTransferConstant d c C * normalizedL2On B (fun y ↦ hRep y - averageOn B hRep))
    hpoint le_rfl henergy).2
  simpa only [B, D, hRep] using ⟨hRep, hRepCont, hRepAE, hosc, hsup⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
