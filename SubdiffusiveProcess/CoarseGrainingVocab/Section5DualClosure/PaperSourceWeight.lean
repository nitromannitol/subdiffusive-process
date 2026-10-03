module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceThermodynamic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPaperNeumannSource

@[expose] public section




open MeasureTheory Homogenization Homogenization.Book Filter
open scoped BigOperators ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d




theorem paperMemLp_two_vecNormSq_of_memLp_four
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {d : ℕ} (V : Omega → Vec d) (hV : MemLp V 4 mu) :
    MemLp (fun omega ↦ vecNormSq (V omega)) 2 mu := by
  letI : ENNReal.HolderTriple (4 : ℝ≥0∞) (4 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by
    rw [← two_mul]
    have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h4, ENNReal.mul_inv (Or.inl (by norm_num))
      (Or.inl (by norm_num))]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num)
      (by norm_num), one_mul]⟩
  have hcoord : ∀ i : Fin d, MemLp (fun omega ↦ V omega i) 4 mu :=
    fun i ↦ hV.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)
  have hsq : ∀ i : Fin d,
      MemLp (fun omega ↦ V omega i * V omega i) 2 mu :=
    fun i ↦ (hcoord i).mul (hcoord i)
  have hsum : MemLp (fun omega ↦ ∑ i : Fin d,
      V omega i * V omega i) 2 mu :=
    MeasureTheory.memLp_finset_sum Finset.univ fun i _ ↦ hsq i
  simpa only [vecNormSq, vecDot, dotProduct] using hsum

theorem paperIntegrable_mul_of_memLp_two
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu]
    (f g : Omega → ℝ) (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    Integrable (fun omega ↦ f omega * g omega) mu := by
  letI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) := ⟨by
    rw [inv_one, ← two_mul,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩
  have hfg : MemLp (fun omega ↦ f omega * g omega) 1 mu := by
    simpa only [Pi.mul_apply, mul_comm] using!
      hf.mul (r := (1 : ℝ≥0∞)) hg
  exact hfg.integrable (by norm_num)

/-- Integrability of the manuscript-sign parent weighted energy.  The
gradient-sign flip costs exactly four times the constant-gradient pairing
(`cubeAverage_oneStepOriginNeumann_plus_eq_minus_add_cross`), which is itself
integrable, so integrability transfers from the legacy field. -/
theorem integrable_oneStepPaperNeumannFlux_weightedCubeAverage
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Vec d) (K : ℕ) (hh : 0 < h) (hq : vecNormSq q = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    Integrable (fun omega ↦ cubeAverage (originCube d (K : ℤ)) (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq (oneStepPaperNeumannFlux M n h q
          (originCube d (K : ℤ)) omega hh x))) M.P.toMeasure := by
  let minusEnergy : Sample d → ℝ := fun omega ↦
    cubeAverage (originCube d (K : ℤ)) (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq
          (q + oneStepMultiplierAt M n h x omega • q -
            ((oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh)
              |>.toH1Function.grad x)))
  have hminusInt : Integrable minusEnergy M.P.toMeasure := by
    refine (integrable_oneStepNeumannSlopeField_weightedCubeAverage
      M n h q K hh hq hscale).congr ?_
    filter_upwards with omega
    simpa only [minusEnergy] using
      cubeAverage_oneStepNeumannSlopeField_origin_eq_originSolution
        M n h q (K : ℤ) omega hh
  have hcrossInt :=
    integrable_cubeAverage_vecDot_oneStepOriginNeumannGradient
      M n h q (K : ℤ) hh
  refine (hminusInt.add (hcrossInt.const_mul 4)).congr ?_
  filter_upwards with omega
  rw [cubeAverage_oneStepPaperNeumannFlux_origin_eq_originSolution
    M n h q (K : ℤ) omega hh,
    cubeAverage_oneStepOriginNeumann_plus_eq_minus_add_cross
      M n h q (K : ℤ) omega hh]
  rfl



theorem normalized_sum_integral_oneStepPaperNeumannSourceCellWeight_le_parent_add_jensenError
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hq : vecNormSq q = 1)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, oneStepLowerSourceCellWeight M n h R omega *
            vecNormSq (oneStepPaperNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure ≤
      ∫ omega, cubeAverage (originCube d (K : ℤ)) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepPaperNeumannFlux M n h q
            (originCube d (K : ℤ)) omega hh x)) ∂M.P.toMeasure +
      (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, oneStepPaperNeumannSourceCellJensenError
            (K := K) M n h q R omega hh ∂M.P.toMeasure := by
  let Q := originCube d (K : ℤ)
  let s := oneStepSourceCells d K n M.delta
  let W : TriadicCube d → Sample d → ℝ := fun R ↦
    oneStepLowerSourceCellWeight M n h R
  let A : TriadicCube d → Sample d → ℝ := fun R omega ↦
    vecNormSq (oneStepPaperNeumannCellSlope M n h q Q R omega hh)
  let E : TriadicCube d → Sample d → ℝ := fun R omega ↦
    oneStepPaperNeumannSourceCellJensenError (K := K) M n h q R omega hh
  let P : Sample d → ℝ := fun omega ↦ cubeAverage Q (fun x ↦
    Real.exp (-oneStepCenteredShellAt M n h x omega) *
      vecNormSq (oneStepPaperNeumannFlux M n h q Q omega hh x))
  have hA : ∀ R ∈ s, MemLp (A R) 2 M.P.toMeasure := by
    intro R _hR
    exact paperMemLp_two_vecNormSq_of_memLp_four
      (oneStepPaperNeumannCellSlope M n h q Q R · hh)
      (memLp_four_oneStepPaperNeumannCellSlope M n h q Q R hh hq)
  have hWA : ∀ R ∈ s, Integrable (fun omega ↦ W R omega * A R omega)
      M.P.toMeasure := by
    intro R hR
    exact paperIntegrable_mul_of_memLp_two (W R) (A R)
      (by simpa only [W] using
        memLp_two_oneStepLowerSourceCellWeight M n h R hh)
      (hA R hR)
  have hE : ∀ R ∈ s, Integrable (E R) M.P.toMeasure := by
    intro R hR
    let O := oneStepSourceCellShellOscillationEnvelope n h R
    have htriple := (integral_three_nonnegative_le_eLpNorm_four_four_two
      (W R) O
      (fun omega ↦ cubeAverage R (fun x ↦ vecNormSq
        (oneStepPaperNeumannFlux M n h q Q omega hh x)))
      (fun omega ↦ (cutoffRatioSup_pos M n (n + h)
        (Homogenization.Book.Ch02.cubeDomain R) omega).le)
      (fun omega ↦
        oneStepSourceCellShellOscillationEnvelope_nonneg n h R omega)
      (fun _omega ↦ cubeAverage_nonneg_of_nonneg_on fun _x _ ↦
        vecNormSq_nonneg _)
      (memLp_four_oneStepLowerSourceCellWeight_of_block M n h R hK hR hh
        hblock)
      (memLp_four_oneStepSourceCellShellOscillationEnvelope
        M n h R hsource hK hR hh)
      (by
        have hAbudget :=
          ((exists_oneStepPaperNeumannSourceCellEnergy_two_budget
            d).choose_spec.2 M n h K q hh hq hblock).1 R hR
        simpa only [Q] using hAbudget)).1
    have hscaled := htriple.const_mul 2
    refine hscaled.congr ?_
    filter_upwards with omega
    dsimp only [E, W, O, oneStepPaperNeumannSourceCellJensenError, Q]
    ring
  have hLeft : Integrable (fun omega ↦
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, W R omega * A R omega)
      M.P.toMeasure :=
    (MeasureTheory.integrable_finset_sum s hWA).const_mul _
  have hErr : Integrable (fun omega ↦
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, E R omega) M.P.toMeasure :=
    (MeasureTheory.integrable_finset_sum s hE).const_mul _
  have hParent : Integrable P M.P.toMeasure := by
    simpa only [P, Q] using
      integrable_oneStepPaperNeumannFlux_weightedCubeAverage
        M n h q K hh hq hblock
  have hpoint : ∀ omega,
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, W R omega * A R omega ≤
        P omega + ((s.card : ℝ)⁻¹) * ∑ R ∈ s, E R omega := by
    intro omega
    simpa only [s, W, A, E, P, Q] using
      normalized_sum_oneStepPaperNeumannSourceCellWeight_le_parent_add_jensenError
        M n h q hK omega hh
  have hint := integral_mono hLeft (hParent.add hErr) hpoint
  change (∫ omega, ((s.card : ℝ)⁻¹) *
      ∑ R ∈ s, W R omega * A R omega ∂M.P.toMeasure) ≤
    ∫ omega, P omega + ((s.card : ℝ)⁻¹) *
      ∑ R ∈ s, E R omega ∂M.P.toMeasure at hint
  rw [integral_add hParent hErr, integral_const_mul,
    integral_const_mul,
    integral_finset_sum s hWA, integral_finset_sum s hE] at hint
  simpa only [s, W, A, E, P, Q] using hint



theorem exists_eventually_normalized_sum_integral_oneStepPaperNeumannSourceCellWeight_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (q : Vec d)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
        (hh : 0 < h) (_hq : vecNormSq q = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ∀ᶠ K : ℕ in Filter.atTop,
          (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
              ∑ R ∈ oneStepSourceCells d K n M.delta,
                ∫ omega, oneStepLowerSourceCellWeight M n h R omega *
                  vecNormSq (oneStepPaperNeumannCellSlope M n h q
                    (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure ≤
            1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
              C * M.delta ^ 4 * (h : ℝ) ^ 2 + C * M.delta ^ 17 := by
  obtain ⟨Cp, hCp, hp⟩ :=
    exists_eventually_integral_oneStepPaperNeumannFlux_weightedCubeAverage_le d
  obtain ⟨Ce, hCe, he⟩ :=
    exists_normalized_sum_integral_oneStepPaperNeumannSourceCellJensenError_le_delta_seventeen
      d
  let C := max Cp (Ce + 1)
  have hC : 0 < C := hCp.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro M n h q hsource hh hqunit hblock
  have hepsilon : 0 < M.delta ^ 17 := pow_pos M.shellPrefix.delta_pos 17
  filter_upwards [hp M n h q hh hqunit hblock hepsilon,
    Filter.eventually_atTop.2 ⟨oneStepLocalizationScale n M.delta,
      fun K hK ↦ hK⟩] with K hparent hK
  have hsplit :=
    normalized_sum_integral_oneStepPaperNeumannSourceCellWeight_le_parent_add_jensenError
      M n h q hsource hK hh hqunit hblock
  have herr := he M n h K q hsource hK hh hqunit hblock
  have hCpC : Cp ≤ C := le_max_left _ _
  have hCeC : Ce + 1 ≤ C := le_max_right _ _
  have hdelta4 : 0 ≤ M.delta ^ 4 * (h : ℝ) ^ 2 := by positivity
  have hdelta17 : 0 ≤ M.delta ^ 17 := by positivity
  calc
    _ ≤ (∫ omega, cubeAverage (originCube d (K : ℤ)) (fun x ↦
          Real.exp (-oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepPaperNeumannFlux M n h q
              (originCube d (K : ℤ)) omega hh x)) ∂M.P.toMeasure) +
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, oneStepPaperNeumannSourceCellJensenError
              (K := K) M n h q R omega hh ∂M.P.toMeasure := hsplit
    _ ≤ (1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          Cp * M.delta ^ 4 * (h : ℝ) ^ 2 + M.delta ^ 17) +
        Ce * M.delta ^ 17 := add_le_add hparent herr
    _ ≤ 1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          C * M.delta ^ 4 * (h : ℝ) ^ 2 + C * M.delta ^ 17 := by
      have hfirst := mul_le_mul_of_nonneg_right hCpC hdelta4
      have hsecond := mul_le_mul_of_nonneg_right hCeC hdelta17
      nlinarith

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
