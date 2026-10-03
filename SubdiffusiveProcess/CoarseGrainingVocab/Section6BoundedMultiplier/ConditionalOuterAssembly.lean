module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.ConditionalBadEventAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.NonpositiveEventPackaging
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.PositiveBelowScaleFamily
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.PrintedShellSigma

@[expose] public section

/-!
# Sigma-field-parametric outer bounded-multiplier assembly

The event sigma-field is an explicit parameter containing the restricted
coefficient sigma-field.  The direct Campanato event is used for `j ≤ m`, the
positive-parent split event for `0 < m < j`, and the landed deterministic
nonpositive package for `m ≤ 0 < j`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal

noncomputable section

private abbrev Sample (d : ℕ) := PotentialSample d

/-- The all-shell sigma-field printed in bounded-multiplier v5 is the ambient
product sigma-field. -/
private theorem boundedMultiplierPrintedShellSigma_eq_ambient (d : ℕ) :
    (⨆ i : ℕ, MeasurableSpace.comap
      (fun omega : Sample d ↦ omega i) inferInstance) =
        (inferInstance : MeasurableSpace (Sample d)) := by
  simpa only [Section6ThetaLadder.thetaLadderPrintedShellSigma,
    Section6ThetaLadder.thetaLadderPrintedShellIndices,
    potentialShellIndexSigma, Set.mem_univ, iSup_true] using
      Section6ThetaLadder.thetaLadderPrintedShellSigma_eq_ambient d

/-- Outer assembly over an abstract event sigma-field.  The only sigma-field
relation used in the proof is inclusion of the restricted coefficient
sigma-field, needed for the gradient event and the nonpositive package. -/
theorem exists_boundedMultiplierEstimate_of_abstractMeasurability
    (d : ℕ) (epsilonTheta cTheta CTheta : ℝ)
    (hepsilonTheta : 0 < epsilonTheta)
    (hcTheta : 0 < cTheta) (hCTheta : 0 < CTheta)
    (Sigma : (M : GMCModel d) → ℕ → ℤ → Vec d →
      MeasurableSpace (Sample d))
    (hSigma : ∀ (M : GMCModel d) (L : ℕ) (m : ℤ) (z : Vec d),
      restrictedCoefficientSigma (aCutoff M L) (translatedCube d m z) ≤
        Sigma M L m z)
    (hcellEvents :
      let epsilonStar := min (boundedMultiplierEpsilonStar d) epsilonTheta
      let c := min cTheta (1 / 2)
      let C := CTheta + 1 +
        boundedMultiplierNonpositiveOscillationConst d c +
        boundedMultiplierNonpositiveL2Const d
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d,
        ∀ j : ℕ, 0 < j → (j : ℤ) ≤ m →
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ badTheta : Set (Sample d),
            @MeasurableSet (Sample d) (Sigma M L m z) badTheta ∧
            boundedMultiplierAmbientMeasure M badTheta ≤ ENNReal.ofReal
              ((C - 1) * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ badTheta,
              omega ∈ coveringRestrictedGradientGood M L m z →
                BoundedMultiplierPathwiseEstimate
                  M L m z j B' epsilonStar C c omega)
    (hpositiveBelowScaleEvents :
      let epsilonStar := min (boundedMultiplierEpsilonStar d) epsilonTheta
      let c := min cTheta (1 / 2)
      let C := CTheta + 1 +
        boundedMultiplierNonpositiveOscillationConst d c +
        boundedMultiplierNonpositiveL2Const d
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, 0 < m → ∀ z : Vec d,
        ∀ j : ℕ, 0 < j → m < (j : ℤ) →
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ badTheta : Set (Sample d),
            @MeasurableSet (Sample d) (Sigma M L m z) badTheta ∧
            boundedMultiplierAmbientMeasure M badTheta ≤ ENNReal.ofReal
              ((C - 1) * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ badTheta,
              omega ∈ coveringRestrictedGradientGood M L m z →
                BoundedMultiplierBelowScalePathwiseEstimate
                  M L m z j B' epsilonStar C c omega) :
    ∃ epsilonStar c C : ℝ,
      0 < epsilonStar ∧ 0 < c ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d, ∀ j : ℕ, 0 < j →
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ bad : Set (Sample d),
            @MeasurableSet (Sample d) (Sigma M L m z) bad ∧
            boundedMultiplierAmbientMeasure M bad ≤ ENNReal.ofReal
              (C * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ bad,
              BoundedMultiplierPathwiseEstimate
                M L m z j B' epsilonStar C c omega := by
  let epsilonStar := min (boundedMultiplierEpsilonStar d) epsilonTheta
  let c := min cTheta (1 / 2)
  let C := CTheta + 1 +
    boundedMultiplierNonpositiveOscillationConst d c +
    boundedMultiplierNonpositiveL2Const d
  have hepsilonStar : 0 < epsilonStar :=
    lt_min (boundedMultiplierEpsilonStar_pos d) hepsilonTheta
  have hc : 0 < c := lt_min hcTheta (by norm_num)
  have hcHalf : c ≤ 1 / 2 := min_le_right _ _
  have hc1 : c ≤ 1 := hcHalf.trans (by norm_num)
  have hoscPos : 0 < boundedMultiplierNonpositiveOscillationConst d c :=
    boundedMultiplierNonpositiveOscillationConst_pos d c
  have hL2nonneg : 0 ≤ boundedMultiplierNonpositiveL2Const d :=
    boundedMultiplierNonpositiveL2Const_nonneg d
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    linarith
  have hCOsc : boundedMultiplierNonpositiveOscillationConst d c ≤ C := by
    dsimp only [C]
    linarith
  have hCL2 : boundedMultiplierNonpositiveL2Const d ≤ C := by
    dsimp only [C]
    linarith
  refine ⟨epsilonStar, c, C, hepsilonStar, hc, hC, ?_⟩
  intro M hdelta L m z j hj B' hB'
  have hd : 2 ≤ d := M.shellPrefix.dimension
  letI : NeZero d := ⟨by omega⟩
  by_cases hjm : (j : ℤ) ≤ m
  · have htheta := hcellEvents M hdelta L m z j hj hjm B' hB'
    exact exists_union_restrictedGradientBad_of_measurability
      M L m z (Sigma M L m z) (hSigma M L m z) C c hC1 hc1
      (BoundedMultiplierPathwiseEstimate
        M L m z j B' epsilonStar C c) htheta
  · have hmj : m < (j : ℤ) := lt_of_not_ge hjm
    by_cases hm0 : m ≤ 0
    · obtain ⟨bad, hbadMeas, hbadTail, hbelow⟩ :=
        exists_bad_nonpositive_belowScale hd M L hm0 z j hj hB'
          epsilonStar C c (min_le_left _ _) hc.le hcHalf hC1 hCOsc hCL2
      refine ⟨bad, hSigma M L m z _ hbadMeas, hbadTail, ?_⟩
      intro omega homega
      exact boundedMultiplierPathwiseEstimate_of_belowScale
        M L m z j B' epsilonStar C c omega (hbelow omega homega)
    · have hmpos : 0 < m := lt_of_not_ge hm0
      have htheta := hpositiveBelowScaleEvents
        M hdelta L m hmpos z j hj hmj B' hB'
      obtain ⟨bad, hbadMeas, hbadTail, hbelow⟩ :=
        exists_union_restrictedGradientBad_of_measurability
          M L m z (Sigma M L m z) (hSigma M L m z) C c hC1 hc1
          (BoundedMultiplierBelowScalePathwiseEstimate
            M L m z j B' epsilonStar C c) htheta
      refine ⟨bad, hbadMeas, hbadTail, ?_⟩
      intro omega homega
      exact boundedMultiplierPathwiseEstimate_of_belowScale
        M L m z j B' epsilonStar C c omega (hbelow omega homega)

/-- Frozen-v5-shaped wrapper.  The abstract sigma field is instantiated by the
literal all-shell product sigma field from D-067; the theta contracts may be
supplied in their ambient form because that field is the ambient product
sigma field. -/
theorem exists_boundedMultiplierEstimate_of_oscillationEvents
    (d : ℕ) (epsilonTheta cTheta CTheta : ℝ)
    (hepsilonTheta : 0 < epsilonTheta)
    (hcTheta : 0 < cTheta) (hCTheta : 0 < CTheta)
    (hcellEvents :
      let epsilonStar := min (boundedMultiplierEpsilonStar d) epsilonTheta
      let c := min cTheta (1 / 2)
      let C := CTheta + 1 +
        boundedMultiplierNonpositiveOscillationConst d c +
        boundedMultiplierNonpositiveL2Const d
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d,
        ∀ j : ℕ, 0 < j → (j : ℤ) ≤ m →
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ badTheta : Set (Sample d),
            MeasurableSet badTheta ∧
            M.P.toMeasure badTheta ≤ ENNReal.ofReal
              ((C - 1) * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ badTheta,
              omega ∈ coveringRestrictedGradientGood M L m z →
                BoundedMultiplierPathwiseEstimate
                  M L m z j B' epsilonStar C c omega)
    (hpositiveBelowScaleEvents :
      let epsilonStar := min (boundedMultiplierEpsilonStar d) epsilonTheta
      let c := min cTheta (1 / 2)
      let C := CTheta + 1 +
        boundedMultiplierNonpositiveOscillationConst d c +
        boundedMultiplierNonpositiveL2Const d
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, 0 < m → ∀ z : Vec d,
        ∀ j : ℕ, 0 < j → m < (j : ℤ) →
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ badTheta : Set (Sample d),
            MeasurableSet badTheta ∧
            M.P.toMeasure badTheta ≤ ENNReal.ofReal
              ((C - 1) * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ badTheta,
              omega ∈ coveringRestrictedGradientGood M L m z →
                BoundedMultiplierBelowScalePathwiseEstimate
                  M L m z j B' epsilonStar C c omega) :
    ∃ epsilonStar c C : ℝ,
      0 < epsilonStar ∧ 0 < c ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d, ∀ j : ℕ, 0 < j →
        let B := translatedCube d m z
          ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ bad : Set (Sample d),
            @MeasurableSet (Sample d)
                (⨆ i : ℕ, MeasurableSpace.comap
                  (fun omega : Sample d ↦ omega i) inferInstance) bad ∧
            M.P.toMeasure bad ≤ ENNReal.ofReal
              (C * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ bad, ∀ theta : Vec d → ℝ,
              ContinuousOn theta B → (∀ x ∈ B, 0 < theta x) →
              (∃ b > 0, ∀ x ∈ B,
                |b⁻¹ * theta x - 1| ≤ epsilonStar) →
              ∀ h : H1Function B,
                IsWeaklyHarmonicOn
                    (fun x ↦ aCutoff M L omega x * theta x) B h →
                  ∃ hRep : Vec d → ℝ,
                    ContinuousOn hRep B ∧
                    hRep =ᵐ[volume.restrict B] h.toFun ∧
                    oscillationOn B' hRep ≤
                      C * (3 : ℝ) ^ (-c * (j : ℝ)) *
                        oscillationOn {x : Vec d | ‖x - z‖ ≤
                          3 * (3 : ℝ) ^ m / 8} hRep ∧
                    sSup {r : ℝ | ∃ x ∈ B',
                      r = |hRep x - averageOn B hRep|} ≤
                      C * normalizedL2On B
                        (fun x ↦ hRep x - averageOn B hRep) := by
  have hSigma := boundedMultiplierPrintedShellSigma_eq_ambient d
  simpa only [BoundedMultiplierPathwiseEstimate,
    boundedMultiplierAmbientMeasure] using
    exists_boundedMultiplierEstimate_of_abstractMeasurability
      d epsilonTheta cTheta CTheta hepsilonTheta hcTheta hCTheta
      (fun _M _L _m _z ↦
        ⨆ i : ℕ, MeasurableSpace.comap
          (fun omega : Sample d ↦ omega i) inferInstance)
      (fun M L _m _z ↦ by
        rw [hSigma]
        exact restrictedCoefficientSigma_le fun x _hx ↦ measurable_aCutoff M L x)
      (by simpa only [hSigma] using hcellEvents)
      (by simpa only [hSigma] using hpositiveBelowScaleEvents)

/-- Internal ambient-sigma variant of the D-067 wrapper. -/
theorem exists_boundedMultiplierEstimate_of_oscillationEvents_ambient
    (d : ℕ) (epsilonTheta cTheta CTheta : ℝ)
    (hepsilonTheta : 0 < epsilonTheta)
    (hcTheta : 0 < cTheta) (hCTheta : 0 < CTheta)
    (hcellEvents :
      let epsilonStar := min (boundedMultiplierEpsilonStar d) epsilonTheta
      let c := min cTheta (1 / 2)
      let C := CTheta + 1 +
        boundedMultiplierNonpositiveOscillationConst d c +
        boundedMultiplierNonpositiveL2Const d
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d,
        ∀ j : ℕ, 0 < j → (j : ℤ) ≤ m →
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ badTheta : Set (Sample d), MeasurableSet badTheta ∧
            M.P.toMeasure badTheta ≤ ENNReal.ofReal
              ((C - 1) * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ badTheta,
              omega ∈ coveringRestrictedGradientGood M L m z →
                BoundedMultiplierPathwiseEstimate
                  M L m z j B' epsilonStar C c omega)
    (hpositiveBelowScaleEvents :
      let epsilonStar := min (boundedMultiplierEpsilonStar d) epsilonTheta
      let c := min cTheta (1 / 2)
      let C := CTheta + 1 +
        boundedMultiplierNonpositiveOscillationConst d c +
        boundedMultiplierNonpositiveL2Const d
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, 0 < m → ∀ z : Vec d,
        ∀ j : ℕ, 0 < j → m < (j : ℤ) →
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ badTheta : Set (Sample d), MeasurableSet badTheta ∧
            M.P.toMeasure badTheta ≤ ENNReal.ofReal
              ((C - 1) * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ badTheta,
              omega ∈ coveringRestrictedGradientGood M L m z →
                BoundedMultiplierBelowScalePathwiseEstimate
                  M L m z j B' epsilonStar C c omega) :
    ∃ epsilonStar c C : ℝ,
      0 < epsilonStar ∧ 0 < c ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d, ∀ j : ℕ, 0 < j →
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ bad : Set (Sample d), MeasurableSet bad ∧
            M.P.toMeasure bad ≤ ENNReal.ofReal
              (C * Real.exp
                (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ bad,
              BoundedMultiplierPathwiseEstimate
                M L m z j B' epsilonStar C c omega := by
  apply exists_boundedMultiplierEstimate_of_abstractMeasurability
    d epsilonTheta cTheta CTheta hepsilonTheta hcTheta hCTheta
    (fun _M _L _m _z ↦ inferInstance)
  · intro M L m z
    exact restrictedCoefficientSigma_le fun x _hx ↦ measurable_aCutoff M L x
  · exact hcellEvents
  · exact hpositiveBelowScaleEvents

/-- Terminal assembly from the ambient theta-ladder contract. -/
theorem exists_boundedMultiplierEstimate (d : ℕ) :
    ∃ epsilonStar c C : ℝ,
      0 < epsilonStar ∧ 0 < c ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ c →
        ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d, ∀ j : ℕ, 0 < j →
        let B := translatedCube d m z
        ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
          ∃ bad : Set (Sample d),
            @MeasurableSet (Sample d)
                (⨆ i : ℕ, MeasurableSpace.comap
                  (fun omega : Sample d ↦ omega i) inferInstance) bad ∧
            M.P.toMeasure bad ≤ ENNReal.ofReal
              (C * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
            ∀ omega ∉ bad, ∀ theta : Vec d → ℝ,
              ContinuousOn theta B → (∀ x ∈ B, 0 < theta x) →
              (∃ b > 0, ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilonStar) →
              ∀ h : H1Function B, IsWeaklyHarmonicOn
                  (fun x ↦ aCutoff M L omega x * theta x) B h →
                ∃ hRep : Vec d → ℝ,
                  ContinuousOn hRep B ∧
                  hRep =ᵐ[volume.restrict B] h.toFun ∧
                  oscillationOn B' hRep ≤ C * (3 : ℝ) ^ (-c * (j : ℝ)) *
                    oscillationOn {x : Vec d | ‖x - z‖ ≤
                      3 * (3 : ℝ) ^ m / 8} hRep ∧
                  sSup {r : ℝ | ∃ x ∈ B',
                    r = |hRep x - averageOn B hRep|} ≤
                    C * normalizedL2On B
                      (fun x ↦ hRep x - averageOn B hRep) := by
  obtain ⟨epsilonTheta, cTheta, CTheta, hepsilonTheta, hcTheta, hCTheta,
      hcellRaw⟩ := Section6ThetaLadder.exists_ambientThetaLadderCellEvents d
  let epsilonStar := min (boundedMultiplierEpsilonStar d) epsilonTheta
  let c := min cTheta (1 / 2)
  let C₀ := CTheta + 1 + boundedMultiplierNonpositiveOscillationConst d c +
    boundedMultiplierNonpositiveL2Const d
  let C := boundedMultiplierFinalConstant d c C₀
  let CThetaFinal := C - 1 - boundedMultiplierNonpositiveOscillationConst d c -
    boundedMultiplierNonpositiveL2Const d
  have hc : 0 < c := lt_min hcTheta (by norm_num)
  have hC₀one : 1 ≤ C₀ := by
    dsimp only [C₀]
    have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
    have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d
    linarith
  have hC₀C : C₀ ≤ C := by
    have hbase : C₀ < boundedMultiplierSealConstant d c C₀ :=
      boundedMultiplierSealConstant_base_lt d (zero_lt_one.trans_le hC₀one)
    have hseal : 0 ≤ boundedMultiplierSealConstant d c C₀ :=
      (boundedMultiplierSealConstant_pos d (zero_lt_one.trans_le hC₀one)).le
    have hrpow : 1 ≤ (3 : ℝ) ^ c := Real.one_le_rpow (by norm_num) hc.le
    have hfirst : boundedMultiplierSealConstant d c C₀ ≤
        boundedMultiplierSealConstant d c C₀ * (3 : ℝ) ^ c := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hrpow hseal
    have hsecond : boundedMultiplierSealConstant d c C₀ * (3 : ℝ) ^ c ≤ C := by
      dsimp only [C, boundedMultiplierFinalConstant, recenteredTransferConstant]
      have hsqrt := Real.sqrt_nonneg ((3 : ℝ) ^ d)
      have hsealOne : 0 ≤ boundedMultiplierSealConstant d c C₀ + 1 := by
        linarith
      nlinarith [mul_nonneg hsealOne hsqrt]
    exact hbase.le.trans (hfirst.trans hsecond)
  have hCThetaFinal : 0 < CThetaFinal := by
    have hosc := boundedMultiplierNonpositiveOscillationConst_pos d c
    have hL2 := boundedMultiplierNonpositiveL2Const_nonneg d
    have hNmul : boundedMultiplierNonpositiveOscillationConst d c ≤
        boundedMultiplierNonpositiveOscillationConst d c * C₀ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hC₀one hosc.le
    have hbase : 1 + boundedMultiplierNonpositiveOscillationConst d c +
        boundedMultiplierNonpositiveL2Const d < boundedMultiplierSealConstant d c C₀ := by
      unfold boundedMultiplierSealConstant
      linarith
    have hseal : 0 ≤ boundedMultiplierSealConstant d c C₀ := by
      linarith
    have hrpow : 1 ≤ (3 : ℝ) ^ c := Real.one_le_rpow (by norm_num) hc.le
    have hsqrt := Real.sqrt_nonneg ((3 : ℝ) ^ d)
    have hfirst : boundedMultiplierSealConstant d c C₀ ≤
        boundedMultiplierSealConstant d c C₀ * (3 : ℝ) ^ c := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hrpow hseal
    have hsealOne : 0 ≤ boundedMultiplierSealConstant d c C₀ + 1 := by linarith
    have hSC : boundedMultiplierSealConstant d c C₀ < C := by
      dsimp only [C, boundedMultiplierFinalConstant, recenteredTransferConstant]
      nlinarith [mul_nonneg hsealOne hsqrt]
    dsimp only [CThetaFinal]
    linarith
  have hCidentity : CThetaFinal + 1 +
      boundedMultiplierNonpositiveOscillationConst d c +
      boundedMultiplierNonpositiveL2Const d = C := by
    dsimp only [CThetaFinal]
    ring
  have hcell : ∀ M : GMCModel d, M.delta ≤ c →
      ∀ L : ℕ, ∀ m : ℤ, ∀ z : Vec d, ∀ j : ℕ, 0 < j →
      (j : ℤ) ≤ m → ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
        ∃ badTheta : Set (Sample d), MeasurableSet badTheta ∧
          M.P.toMeasure badTheta ≤ ENNReal.ofReal
            ((C₀ - 1) * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
          ∀ omega ∉ badTheta, omega ∈ coveringRestrictedGradientGood M L m z →
            BoundedMultiplierPathwiseEstimate M L m z j B' epsilonStar C₀ c omega := by
    simpa only [epsilonStar, c, C₀] using hcellRaw
  have hpositive : ∀ M : GMCModel d, M.delta ≤ c →
      ∀ L : ℕ, ∀ m : ℤ, 0 < m → ∀ z : Vec d,
      ∀ j : ℕ, 0 < j → m < (j : ℤ) →
      ∀ B' : Set (Vec d), IsMiddleHalfSubcube m z j B' →
        ∃ badTheta : Set (Sample d), MeasurableSet badTheta ∧
          M.P.toMeasure badTheta ≤ ENNReal.ofReal
            ((C - 1) * Real.exp (-c / (M.delta ^ 2 * |Real.log M.delta| ^ 2))) ∧
          ∀ omega ∉ badTheta, omega ∈ coveringRestrictedGradientGood M L m z →
            BoundedMultiplierBelowScalePathwiseEstimate M L m z j B' epsilonStar C c omega := by
    by_cases hd : 2 ≤ d
    · letI : NeZero d := ⟨by omega⟩
      simpa only [C] using exists_positiveBelowScaleEvents hd
        (epsilon := epsilonStar) (c := c) (C₀ := C₀)
        (min_le_left _ _) hc (min_le_right _ _) hC₀one hcell
    · intro M
      exact (hd M.shellPrefix.dimension).elim
  apply exists_boundedMultiplierEstimate_of_oscillationEvents
    d epsilonTheta cTheta CThetaFinal hepsilonTheta hcTheta hCThetaFinal
  · dsimp only
    intro M hdelta L m z j hj hjm B' hB'
    obtain ⟨bad, hmeas, htail, hpath⟩ := hcell M hdelta L m z j hj hjm B' hB'
    refine ⟨bad, hmeas, ?_, ?_⟩
    · rw [hCidentity]
      exact htail.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (sub_le_sub_right hC₀C 1) (Real.exp_pos _).le))
    · intro omega homega hgood
      rw [hCidentity]
      exact boundedMultiplierPathwiseEstimate_mono_constant M L m z j B'
        epsilonStar c C₀ C hC₀C omega (hpath omega homega hgood)
  · dsimp only
    have hCexpr : CThetaFinal + 1 +
        boundedMultiplierNonpositiveOscillationConst d (min cTheta (1 / 2)) +
        boundedMultiplierNonpositiveL2Const d = C := by
      simpa only [c] using hCidentity
    simpa only [epsilonStar, c, hCexpr] using hpositive

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
