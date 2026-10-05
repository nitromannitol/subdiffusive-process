module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveL2Endpoint
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveOscillationAbsorption
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RepresentativeReadout

@[expose] public section

/-!
# Restricted-gradient event package at nonpositive scales
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

/-- The complete below-scale conclusion for `m ≤ 0`, with the complement of
the restricted-gradient good event as its sole exceptional set. -/
theorem exists_bad_nonpositive_belowScale
    {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (M : GMCModel d) (L : ℕ)
    {m : ℤ} (hm : m ≤ 0) (z : Vec d)
    (j : ℕ) (hj : 0 < j)
    {B' : Set (Vec d)} (hB' : IsMiddleHalfSubcube m z j B')
    (epsilonStar C c : ℝ)
    (hepsilonLe : epsilonStar ≤ boundedMultiplierEpsilonStar d)
    (hc0 : 0 ≤ c) (hcHalf : c ≤ 1 / 2)
    (hC1 : 1 ≤ C)
    (hCOsc : boundedMultiplierNonpositiveOscillationConst d c ≤ C)
    (hCL2 : boundedMultiplierNonpositiveL2Const d ≤ C) :
    let B := translatedCube d m z
    ∃ bad : Set (Sample d),
      @MeasurableSet (Sample d)
          (restrictedCoefficientSigma (aCutoff M L) B) bad ∧
      M.P.toMeasure bad ≤ ENNReal.ofReal
        (C * Real.exp
          (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
      ∀ omega ∉ bad, ∀ theta : Vec d → ℝ,
        ContinuousOn theta B → (∀ x ∈ B, 0 < theta x) →
        (∃ b > 0, ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilonStar) →
        ∀ h : H1Function B,
          IsWeaklyHarmonicOn (fun x ↦ aCutoff M L omega x * theta x) B h →
            ∃ hRep : Vec d → ℝ,
              ContinuousOn hRep B ∧
              hRep =ᵐ[volume.restrict B] h.toFun ∧
              oscillationOn B' hRep ≤
                C * (3 : ℝ) ^ (-(c * ((((j : ℤ) - m : ℤ) : ℝ)))) *
                  ((3 : ℝ) ^ (-(c * (m : ℝ))) *
                    oscillationOn {x : Vec d | ‖x - z‖ ≤
                      3 * (3 : ℝ) ^ m / 8} hRep) ∧
              sSup {r : ℝ | ∃ x ∈ B',
                r = |hRep x - averageOn B hRep|} ≤
                C * normalizedL2On B
                  (fun x ↦ hRep x - averageOn B hRep) := by
  dsimp only
  let bad := (coveringRestrictedGradientGood M L m z)ᶜ
  refine ⟨bad, (measurableSet_coveringRestrictedGradientGood M L m z).compl,
    ?_, ?_⟩
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
      have hdiv : c / (M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤
          1 / (M.delta ^ 2 * |Real.log M.delta| ^ 2) :=
        div_le_div_of_nonneg_right hc1 hden.le
      simpa only [neg_div] using neg_le_neg hdiv
    calc
      M.P.toMeasure bad ≤ ENNReal.ofReal
          (Real.exp (-1 /
            (M.delta ^ 2 * |Real.log M.delta| ^ 2))) := by
        simpa only [bad] using
          measure_compl_coveringRestrictedGradientGood_le M L m z
      _ ≤ ENNReal.ofReal
          (Real.exp (-c /
            (M.delta ^ 2 * |Real.log M.delta| ^ 2))) :=
        ENNReal.ofReal_le_ofReal hexp
      _ ≤ ENNReal.ofReal
          (C * Real.exp (-c /
            (M.delta ^ 2 * |Real.log M.delta| ^ 2))) := by
        apply ENNReal.ofReal_le_ofReal
        exact (le_mul_iff_one_le_left (Real.exp_pos _)).2 hC1
  · intro omega homega theta hthetaCont hthetaPos hthetaClose h hharm
    have hgood : omega ∈ coveringRestrictedGradientGood M L m z := by
      simpa only [bad, Set.mem_compl_iff, not_not] using homega
    obtain ⟨b, hb, hclose⟩ := hthetaClose
    have hcloseLocal : ∀ x ∈ translatedCube d m z,
        |b⁻¹ * theta x - 1| ≤ boundedMultiplierEpsilonStar d := by
      intro x hx
      exact (hclose x hx).trans hepsilonLe
    obtain ⟨zCenter, hB'eq, hB'collar⟩ := hB'
    have hB'full : IsMiddleHalfSubcube m z j B' :=
      ⟨zCenter, hB'eq, hB'collar⟩
    let hRep := euclideanBallAverageRepresentative h.toFun
    let s : Vec d → ℝ := fun x ↦ aCutoff M L omega x * theta x
    have hsCont : ContinuousOn s (translatedCube d m z) :=
      (continuous_aCutoff M L omega).continuousOn.mul hthetaCont
    have hsPos : ∀ x ∈ translatedCube d m z, 0 < s x := by
      intro x hx
      exact mul_pos (aCutoff_pos M L omega x) (hthetaPos x hx)
    have hcubeOpen : IsOpen (translatedCube d m z) := by
      have hset : translatedCube d m z =
          (fun x : Vec d ↦ x - z) ⁻¹' openCubeSet (originCube d m) := by
        ext x
        constructor
        · rintro ⟨u, hu, rfl⟩
          change u ∈ openCubeSet (originCube d m) at hu
          simpa using hu
        · intro hx
          refine ⟨x - z, ?_, ?_⟩
          · simpa [cube] using hx
          · ext i
            simp
      rw [hset]
      exact (isOpen_openCubeSet (originCube d m)).preimage
        (continuous_id.sub continuous_const)
    have hrep := continuousOn_and_ae_eq_euclideanBallAverageRepresentative
      hd hcubeOpen hsCont hsPos (by simpa only [s] using hharm)
    have hosc := nonpositive_middleHalfSubcube_oscillation_decay
      hd M L hm z hj hB'full omega hgood hthetaCont hthetaPos hb hcloseLocal
        hharm hc0 hcHalf
    have hOsc0 : 0 ≤ oscillationOn {x : Vec d | ‖x - z‖ ≤
        3 * (3 : ℝ) ^ m / 8} hRep := by
      apply oscillationOn_nonneg_of_nonempty
      refine ⟨z, ?_⟩
      simp
      positivity
    have hpow0 : 0 ≤ (3 : ℝ) ^ (-c * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hoscC : oscillationOn B' hRep ≤
        C * (3 : ℝ) ^ (-c * (j : ℝ)) *
          oscillationOn {x : Vec d | ‖x - z‖ ≤
            3 * (3 : ℝ) ^ m / 8} hRep := by
      exact hosc.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCOsc hpow0) hOsc0)
    have hexponent :
        -(c * ((((j : ℤ) - m : ℤ) : ℝ))) + -(c * (m : ℝ)) =
          -(c * (j : ℝ)) := by
      norm_num
      ring
    have hoscSplit : oscillationOn B' hRep ≤
        C * (3 : ℝ) ^ (-(c * ((((j : ℤ) - m : ℤ) : ℝ)))) *
          ((3 : ℝ) ^ (-(c * (m : ℝ))) *
            oscillationOn {x : Vec d | ‖x - z‖ ≤
              3 * (3 : ℝ) ^ m / 8} hRep) := by
      calc
        oscillationOn B' hRep ≤ C * (3 : ℝ) ^ (-c * (j : ℝ)) *
            oscillationOn {x : Vec d | ‖x - z‖ ≤
              3 * (3 : ℝ) ^ m / 8} hRep := hoscC
        _ = _ := by
          have hpowSplit :
              (3 : ℝ) ^ (-(c * ((((j : ℤ) - m : ℤ) : ℝ)))) *
                  (3 : ℝ) ^ (-(c * (m : ℝ))) =
                (3 : ℝ) ^ (-c * (j : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), hexponent]
            congr 1
            ring
          rw [← hpowSplit]
          ring
    have hB'ne : B'.Nonempty := by
      refine ⟨zCenter, ?_⟩
      rw [hB'eq]
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.mem_translatedCube_iff,
        sub_self]
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.zero_mem_cube d (m - j)
    have hpoint : ∀ x ∈ B',
        |hRep x - averageOn (translatedCube d m z) h.toFun| ≤
          boundedMultiplierNonpositiveL2Const d *
            normalizedL2On (translatedCube d m z)
              (fun y ↦ h.toFun y -
                averageOn (translatedCube d m z) h.toFun) := by
      intro x hx
      exact nonpositive_point_sub_parentAverage_le_normalizedL2
        hd M L hm z omega hgood (hB'collar x hx) hthetaCont hb hcloseLocal hharm
    have henergy : boundedMultiplierNonpositiveL2Const d *
          normalizedL2On (translatedCube d m z)
            (fun y ↦ h.toFun y -
              averageOn (translatedCube d m z) h.toFun) ≤
        C * normalizedL2On (translatedCube d m z)
            (fun y ↦ h.toFun y -
              averageOn (translatedCube d m z) h.toFun) :=
      mul_le_mul_of_nonneg_right hCL2 (normalizedL2On_nonneg _ _)
    have hpointConclusions := pointwiseConclusions_of_commonReference hB'ne hRep
      (averageOn (translatedCube d m z) h.toFun)
      (boundedMultiplierNonpositiveL2Const d *
        normalizedL2On (translatedCube d m z)
          (fun y ↦ h.toFun y - averageOn (translatedCube d m z) h.toFun))
      (2 * (boundedMultiplierNonpositiveL2Const d *
        normalizedL2On (translatedCube d m z)
          (fun y ↦ h.toFun y - averageOn (translatedCube d m z) h.toFun)))
      (C * normalizedL2On (translatedCube d m z)
        (fun y ↦ h.toFun y - averageOn (translatedCube d m z) h.toFun))
      hpoint le_rfl henergy
    have hcarrier :
        oscillationOn B' hRep ≤
            C * (3 : ℝ) ^ (-(c * ((((j : ℤ) - m : ℤ) : ℝ)))) *
              ((3 : ℝ) ^ (-(c * (m : ℝ))) *
                oscillationOn {x : Vec d | ‖x - z‖ ≤
                  3 * (3 : ℝ) ^ m / 8} hRep) ∧
          sSup {r : ℝ | ∃ x ∈ B',
            r = |hRep x - averageOn (translatedCube d m z) h.toFun|} ≤
              C * normalizedL2On (translatedCube d m z)
                (fun x ↦ h.toFun x -
                  averageOn (translatedCube d m z) h.toFun) :=
      ⟨hoscSplit, hpointConclusions.2⟩
    have havg := averageOn_eq_of_ae_eq hrep.2
    have hnorm := normalizedL2On_sub_average_eq_of_ae_eq hrep.2
    refine ⟨hRep, hrep.1, hrep.2, hcarrier.1, ?_⟩
    rw [hnorm, havg]
    exact hcarrier.2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
