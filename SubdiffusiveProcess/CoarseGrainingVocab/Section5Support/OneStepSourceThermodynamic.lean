import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceReplacementMoment
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepParentWeightedEnergy
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepDualPrefixSuffix

/-!
# Integrated source-cell replacement

This module integrates the samplewise source-partition comparison.  Spatial
CZ is applied before this layer; the remaining argument is finite-family
Holder, integrability, and Bochner-integral linearity.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

private theorem memLp_two_vecNormSq_of_memLp_four
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {d : ℕ} (V : Omega → Vec d) (hV : MemLp V 4 mu) :
    MemLp (fun omega => vecNormSq (V omega)) 2 mu := by
  letI : ENNReal.HolderTriple (4 : ℝ≥0∞) (4 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by
    rw [← two_mul]
    have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h4, ENNReal.mul_inv (Or.inl (by norm_num))
      (Or.inl (by norm_num))]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num)
      (by norm_num), one_mul]⟩
  have hcoord : ∀ i : Fin d, MemLp (fun omega => V omega i) 4 mu :=
    fun i => hV.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)
  have hsq : ∀ i : Fin d,
      MemLp (fun omega => V omega i * V omega i) 2 mu :=
    fun i => (hcoord i).mul (hcoord i)
  have hsum : MemLp (fun omega => ∑ i : Fin d,
      V omega i * V omega i) 2 mu := by
    exact MeasureTheory.memLp_finset_sum Finset.univ fun i _ => hsq i
  simpa only [vecNormSq, vecDot, dotProduct] using hsum

private theorem integrable_mul_of_memLp_two
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu]
    (f g : Omega → ℝ) (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    Integrable (fun omega => f omega * g omega) mu := by
  letI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) := ⟨by
    rw [inv_one, ← two_mul,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩
  have hfg : MemLp (fun omega => f omega * g omega) 1 mu := by
    simpa only [Pi.mul_apply, mul_comm] using
      hf.mul (r := (1 : ℝ≥0∞)) hg
  exact hfg.integrable (by norm_num)

theorem normalized_sum_integral_oneStepDirichletSourceCellWeight_le_parent_add_jensenError
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hp : vecNormSq p = 1)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, oneStepUpperSourceCellWeight M n h R omega *
            vecNormSq (oneStepDirichletCellSlope M n h p
              (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure ≤
      ∫ omega, cubeAverage (originCube d (K : ℤ)) (fun x =>
        Real.exp (oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepDirichletSlopeField M n h p
            (originCube d (K : ℤ)) omega hh x)) ∂M.P.toMeasure +
      (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, oneStepDirichletSourceCellJensenError
            (K := K) M n h p R omega hh ∂M.P.toMeasure := by
  let Q := originCube d (K : ℤ)
  let s := oneStepSourceCells d K n M.delta
  let W : TriadicCube d → Sample d → ℝ := fun R =>
    oneStepUpperSourceCellWeight M n h R
  let A : TriadicCube d → Sample d → ℝ := fun R omega =>
    vecNormSq (oneStepDirichletCellSlope M n h p Q R omega hh)
  let E : TriadicCube d → Sample d → ℝ := fun R omega =>
    oneStepDirichletSourceCellJensenError (K := K) M n h p R omega hh
  let P : Sample d → ℝ := fun omega => cubeAverage Q (fun x =>
    Real.exp (oneStepCenteredShellAt M n h x omega) *
      vecNormSq (oneStepDirichletSlopeField M n h p Q omega hh x))
  have hA : ∀ R ∈ s, MemLp (A R) 2 M.P.toMeasure := by
    intro R hR
    exact memLp_two_vecNormSq_of_memLp_four
      (oneStepDirichletCellSlope M n h p Q R · hh)
      (memLp_four_oneStepDirichletCellSlope M n h p Q R hh hp)
  have hWA : ∀ R ∈ s, Integrable (fun omega => W R omega * A R omega)
      M.P.toMeasure := by
    intro R hR
    exact integrable_mul_of_memLp_two (W R) (A R)
      (by simpa only [W] using memLp_two_oneStepUpperSourceCellWeight M n h R hh)
      (hA R hR)
  have hE : ∀ R ∈ s, Integrable (E R) M.P.toMeasure := by
    intro R hR
    let O := oneStepSourceCellShellOscillationEnvelope n h R
    have htriple := (integral_three_nonnegative_le_eLpNorm_four_four_two
      (W R) O
      (fun omega => cubeAverage R (fun x => vecNormSq
        (oneStepDirichletSlopeField M n h p Q omega hh x)))
      (fun omega => (cutoffRatioSup_pos M (n + h) n
        (Homogenization.Book.Ch02.cubeDomain R) omega).le)
      (fun omega => oneStepSourceCellShellOscillationEnvelope_nonneg n h R omega)
      (fun omega => cubeAverage_nonneg_of_nonneg_on fun x _ => vecNormSq_nonneg _)
      (memLp_four_oneStepUpperSourceCellWeight_of_block M n h R hK hR hh hblock)
      (memLp_four_oneStepSourceCellShellOscillationEnvelope
        M n h R hsource hK hR hh)
      (by
        have hAbudget :=
          ((exists_oneStepDirichletSourceCellEnergy_two_budget d).choose_spec.2
            M n h K p hh hp hblock).1 R hR
        simpa only [Q] using hAbudget)).1
    have hscaled := htriple.const_mul 2
    refine hscaled.congr ?_
    filter_upwards with omega
    dsimp only [E, W, O, oneStepDirichletSourceCellJensenError, Q]
    ring
  have hLeft : Integrable (fun omega =>
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, W R omega * A R omega)
      M.P.toMeasure :=
    (MeasureTheory.integrable_finset_sum s hWA).const_mul _
  have hErr : Integrable (fun omega =>
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, E R omega) M.P.toMeasure :=
    (MeasureTheory.integrable_finset_sum s hE).const_mul _
  have hParent : Integrable P M.P.toMeasure := by
    simpa only [P, Q] using
      integrable_oneStepDirichletSlopeField_weightedCubeAverage
        M n h p K hh hp hblock
  have hpoint : ∀ omega,
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, W R omega * A R omega ≤
        P omega + ((s.card : ℝ)⁻¹) * ∑ R ∈ s, E R omega := by
    intro omega
    simpa only [s, W, A, E, P, Q] using
      normalized_sum_oneStepDirichletSourceCellWeight_le_parent_add_jensenError
        M n h p hK omega hh
  have hint := integral_mono hLeft (hParent.add hErr) hpoint
  change (∫ omega, ((s.card : ℝ)⁻¹) *
      ∑ R ∈ s, W R omega * A R omega ∂M.P.toMeasure) ≤
    ∫ omega, P omega + ((s.card : ℝ)⁻¹) *
      ∑ R ∈ s, E R omega ∂M.P.toMeasure at hint
  rw [integral_add hParent hErr, integral_const_mul,
    integral_const_mul,
    integral_finset_sum s hWA, integral_finset_sum s hE] at hint
  simpa only [s, W, A, E, P, Q] using hint

theorem normalized_sum_integral_oneStepNeumannSourceCellWeight_le_parent_add_jensenError
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hq : vecNormSq q = 1)
    (hblock : (h : ℝ) ≤ M.delta⁻¹) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, oneStepLowerSourceCellWeight M n h R omega *
            vecNormSq (oneStepNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure ≤
      ∫ omega, cubeAverage (originCube d (K : ℤ)) (fun x =>
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepNeumannSlopeField M n h q
            (originCube d (K : ℤ)) omega hh x)) ∂M.P.toMeasure +
      (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, oneStepNeumannSourceCellJensenError
            (K := K) M n h q R omega hh ∂M.P.toMeasure := by
  let Q := originCube d (K : ℤ)
  let s := oneStepSourceCells d K n M.delta
  let W : TriadicCube d → Sample d → ℝ := fun R =>
    oneStepLowerSourceCellWeight M n h R
  let A : TriadicCube d → Sample d → ℝ := fun R omega =>
    vecNormSq (oneStepNeumannCellSlope M n h q Q R omega hh)
  let E : TriadicCube d → Sample d → ℝ := fun R omega =>
    oneStepNeumannSourceCellJensenError (K := K) M n h q R omega hh
  let P : Sample d → ℝ := fun omega => cubeAverage Q (fun x =>
    Real.exp (-oneStepCenteredShellAt M n h x omega) *
      vecNormSq (oneStepNeumannSlopeField M n h q Q omega hh x))
  have hA : ∀ R ∈ s, MemLp (A R) 2 M.P.toMeasure := by
    intro R hR
    exact memLp_two_vecNormSq_of_memLp_four
      (oneStepNeumannCellSlope M n h q Q R · hh)
      (memLp_four_oneStepNeumannCellSlope M n h q Q R hh hq)
  have hWA : ∀ R ∈ s, Integrable (fun omega => W R omega * A R omega)
      M.P.toMeasure := by
    intro R hR
    exact integrable_mul_of_memLp_two (W R) (A R)
      (by simpa only [W] using memLp_two_oneStepLowerSourceCellWeight M n h R hh)
      (hA R hR)
  have hE : ∀ R ∈ s, Integrable (E R) M.P.toMeasure := by
    intro R hR
    let O := oneStepSourceCellShellOscillationEnvelope n h R
    have htriple := (integral_three_nonnegative_le_eLpNorm_four_four_two
      (W R) O
      (fun omega => cubeAverage R (fun x => vecNormSq
        (oneStepNeumannSlopeField M n h q Q omega hh x)))
      (fun omega => (cutoffRatioSup_pos M n (n + h)
        (Homogenization.Book.Ch02.cubeDomain R) omega).le)
      (fun omega => oneStepSourceCellShellOscillationEnvelope_nonneg n h R omega)
      (fun omega => cubeAverage_nonneg_of_nonneg_on fun x _ => vecNormSq_nonneg _)
      (memLp_four_oneStepLowerSourceCellWeight_of_block M n h R hK hR hh hblock)
      (memLp_four_oneStepSourceCellShellOscillationEnvelope
        M n h R hsource hK hR hh)
      (by
        have hAbudget :=
          ((exists_oneStepNeumannSourceCellEnergy_two_budget d).choose_spec.2
            M n h K q hh hq hblock).1 R hR
        simpa only [Q] using hAbudget)).1
    have hscaled := htriple.const_mul 2
    refine hscaled.congr ?_
    filter_upwards with omega
    dsimp only [E, W, O, oneStepNeumannSourceCellJensenError, Q]
    ring
  have hLeft : Integrable (fun omega =>
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, W R omega * A R omega)
      M.P.toMeasure :=
    (MeasureTheory.integrable_finset_sum s hWA).const_mul _
  have hErr : Integrable (fun omega =>
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, E R omega) M.P.toMeasure :=
    (MeasureTheory.integrable_finset_sum s hE).const_mul _
  have hParent : Integrable P M.P.toMeasure := by
    simpa only [P, Q] using
      integrable_oneStepNeumannSlopeField_weightedCubeAverage
        M n h q K hh hq hblock
  have hpoint : ∀ omega,
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, W R omega * A R omega ≤
        P omega + ((s.card : ℝ)⁻¹) * ∑ R ∈ s, E R omega := by
    intro omega
    simpa only [s, W, A, E, P, Q] using
      normalized_sum_oneStepNeumannSourceCellWeight_le_parent_add_jensenError
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

/-! ## Signed thermodynamic source budgets -/



theorem exists_eventually_normalized_sum_integral_oneStepDirichletSourceCellWeight_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (p : Vec d)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
        (hh : 0 < h) (_hp : vecNormSq p = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ∀ᶠ K : ℕ in Filter.atTop,
          (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
              ∑ R ∈ oneStepSourceCells d K n M.delta,
                ∫ omega, oneStepUpperSourceCellWeight M n h R omega *
                  vecNormSq (oneStepDirichletCellSlope M n h p
                    (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure ≤
            1 - 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
              C * M.delta ^ 4 * (h : ℝ) ^ 2 + C * M.delta ^ 17 := by
  obtain ⟨Cp, hCp, hp⟩ :=
    exists_eventually_integral_oneStepDirichletSlopeField_weightedCubeAverage_le d
  obtain ⟨Ce, hCe, he⟩ :=
    exists_normalized_sum_integral_oneStepDirichletSourceCellJensenError_le_delta_seventeen d
  let C := max Cp (Ce + 1)
  have hC : 0 < C := hCp.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro M n h p hsource hh hpunit hblock
  have hepsilon : 0 < M.delta ^ 17 := pow_pos M.shellPrefix.delta_pos 17
  filter_upwards [hp M n h p hh hpunit hblock hepsilon,
    Filter.eventually_atTop.2 ⟨oneStepLocalizationScale n M.delta,
      fun K hK ↦ hK⟩] with K hparent hK
  have hsplit :=
    normalized_sum_integral_oneStepDirichletSourceCellWeight_le_parent_add_jensenError
      M n h p hsource hK hh hpunit hblock
  have herr := he M n h K p hsource hK hh hpunit hblock
  have hCpC : Cp ≤ C := le_max_left _ _
  have hCeC : Ce + 1 ≤ C := le_max_right _ _
  have hdelta4 : 0 ≤ M.delta ^ 4 * (h : ℝ) ^ 2 := by positivity
  have hdelta17 : 0 ≤ M.delta ^ 17 := by positivity
  calc
    _ ≤ (∫ omega, cubeAverage (originCube d (K : ℤ)) (fun x ↦
          Real.exp (oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepDirichletSlopeField M n h p
              (originCube d (K : ℤ)) omega hh x)) ∂M.P.toMeasure) +
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, oneStepDirichletSourceCellJensenError
              (K := K) M n h p R omega hh ∂M.P.toMeasure := hsplit
    _ ≤ (1 - 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          Cp * M.delta ^ 4 * (h : ℝ) ^ 2 + M.delta ^ 17) +
        Ce * M.delta ^ 17 := add_le_add hparent herr
    _ ≤ 1 - 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          C * M.delta ^ 4 * (h : ℝ) ^ 2 + C * M.delta ^ 17 := by
      have hfirst := mul_le_mul_of_nonneg_right hCpC hdelta4
      have hsecond := mul_le_mul_of_nonneg_right hCeC hdelta17
      nlinarith

/-- Reciprocal counterpart of
`exists_eventually_normalized_sum_integral_oneStepDirichletSourceCellWeight_le`. -/
theorem exists_eventually_normalized_sum_integral_oneStepNeumannSourceCellWeight_le
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
                  vecNormSq (oneStepNeumannCellSlope M n h q
                    (originCube d (K : ℤ)) R omega hh) ∂M.P.toMeasure ≤
            1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
              C * M.delta ^ 4 * (h : ℝ) ^ 2 + C * M.delta ^ 17 := by
  obtain ⟨Cp, hCp, hp⟩ :=
    exists_eventually_integral_oneStepNeumannSlopeField_weightedCubeAverage_le d
  obtain ⟨Ce, hCe, he⟩ :=
    exists_normalized_sum_integral_oneStepNeumannSourceCellJensenError_le_delta_seventeen d
  let C := max Cp (Ce + 1)
  have hC : 0 < C := hCp.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro M n h q hsource hh hqunit hblock
  have hepsilon : 0 < M.delta ^ 17 := pow_pos M.shellPrefix.delta_pos 17
  filter_upwards [hp M n h q hh hqunit hblock hepsilon,
    Filter.eventually_atTop.2 ⟨oneStepLocalizationScale n M.delta,
      fun K hK ↦ hK⟩] with K hparent hK
  have hsplit :=
    normalized_sum_integral_oneStepNeumannSourceCellWeight_le_parent_add_jensenError
      M n h q hsource hK hh hqunit hblock
  have herr := he M n h K q hsource hK hh hqunit hblock
  have hCpC : Cp ≤ C := le_max_left _ _
  have hCeC : Ce + 1 ≤ C := le_max_right _ _
  have hdelta4 : 0 ≤ M.delta ^ 4 * (h : ℝ) ^ 2 := by positivity
  have hdelta17 : 0 ≤ M.delta ^ 17 := by positivity
  calc
    _ ≤ (∫ omega, cubeAverage (originCube d (K : ℤ)) (fun x ↦
          Real.exp (-oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepNeumannSlopeField M n h q
              (originCube d (K : ℤ)) omega hh x)) ∂M.P.toMeasure) +
        (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, oneStepNeumannSourceCellJensenError
              (K := K) M n h q R omega hh ∂M.P.toMeasure := hsplit
    _ ≤ (1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          Cp * M.delta ^ 4 * (h : ℝ) ^ 2 + M.delta ^ 17) +
        Ce * M.delta ^ 17 := add_le_add hparent herr
    _ ≤ 1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          C * M.delta ^ 4 * (h : ℝ) ^ 2 + C * M.delta ^ 17 := by
      have hfirst := mul_le_mul_of_nonneg_right hCpC hdelta4
      have hsecond := mul_le_mul_of_nonneg_right hCeC hdelta17
      nlinarith

/-- Prefix/suffix factorization turns the signed primal source-slope budget
into the literal random coarse-matrix principal budget.  The finite readout
is at most one, so the localization remainder remains `O(delta^17)`. -/
theorem exists_eventually_normalized_sum_integral_oneStepDirichletSourceCellPrincipal_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (p : Vec d)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
        (hh : 0 < h) (_hp : vecNormSq p = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ∀ᶠ K : ℕ in Filter.atTop,
          (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
              ∑ R ∈ oneStepSourceCells d K n M.delta,
                ∫ omega,
                  oneStepUpperSourceCellWeight M n h R omega *
                    vecDot (oneStepDirichletCellSlope M n h p
                      (originCube d (K : ℤ)) R omega hh)
                      (matVecMul (randomAMatrix M n
                        (Homogenization.Book.Ch02.cubeDomain R) omega)
                        (oneStepDirichletCellSlope M n h p
                          (originCube d (K : ℤ)) R omega hh))
                  ∂M.P.toMeasure ≤
            (1 - 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
                C * M.delta ^ 4 * (h : ℝ) ^ 2) *
              abarScalarReadout M n (oneStepLocalizationScale n M.delta) +
                C * M.delta ^ 17 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eventually_normalized_sum_integral_oneStepDirichletSourceCellWeight_le d
  refine ⟨C, hC, ?_⟩
  intro M n h p hsource hh hp hblock
  filter_upwards [hbound M n h p hsource hh hp hblock,
    Filter.eventually_atTop.2 ⟨oneStepLocalizationScale n M.delta,
      fun K hK ↦ hK⟩] with K hbudget hK
  let cell := abarScalarReadout M n (oneStepLocalizationScale n M.delta)
  have hcell0 : 0 ≤ cell := abarScalarReadout_nonneg M n _
  have hcell1 : cell ≤ 1 := abarScalarReadout_le_one M n _
  have hmul := mul_le_mul_of_nonneg_left hbudget hcell0
  rw [← normalized_sum_integral_upperWeight_mul_dirichletSourceCellSlope_eq
    M n h p hK hh hp] at hmul
  have hdelta17 : 0 ≤ C * M.delta ^ 17 :=
    mul_nonneg hC.le (pow_nonneg M.shellPrefix.delta_pos.le 17)
  have htail : cell * (C * M.delta ^ 17) ≤ C * M.delta ^ 17 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcell1 hdelta17
  dsimp only [cell] at hmul ⊢
  calc
    _ ≤ abarScalarReadout M n (oneStepLocalizationScale n M.delta) *
        (1 - 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          C * M.delta ^ 4 * (h : ℝ) ^ 2 + C * M.delta ^ 17) := hmul
    _ ≤ (1 - 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
          C * M.delta ^ 4 * (h : ℝ) ^ 2) *
          abarScalarReadout M n (oneStepLocalizationScale n M.delta) +
        C * M.delta ^ 17 := by
      rw [mul_add]
      exact add_le_add
        (le_of_eq (mul_comm _ _))
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using htail)

/-- The reciprocal signed source budget, now paired with the genuine
inverse-star block.  The localization remainder remains inside the scalar
factor until the finite-volume inverse-star readout is compared with the
homogenized reciprocal coefficient. -/
theorem exists_eventually_normalized_sum_integral_oneStepNeumannSourceCellPrincipal_le
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
                ∫ omega,
                  oneStepLowerSourceCellWeight M n h R omega *
                    vecDot (oneStepNeumannCellSlope M n h q
                      (originCube d (K : ℤ)) R omega hh)
                      (matVecMul ((randomAStarMatrix M n
                        (Homogenization.Book.Ch02.cubeDomain R) omega)⁻¹)
                        (oneStepNeumannCellSlope M n h q
                          (originCube d (K : ℤ)) R omega hh))
                  ∂M.P.toMeasure ≤
            (1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
                C * M.delta ^ 4 * (h : ℝ) ^ 2 + C * M.delta ^ 17) *
              oneStepAnnealedDualReadout M n
                (oneStepLocalizationScale n M.delta) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eventually_normalized_sum_integral_oneStepNeumannSourceCellWeight_le d
  refine ⟨C, hC, ?_⟩
  intro M n h q hsource hh hq hblock
  filter_upwards [hbound M n h q hsource hh hq hblock,
    Filter.eventually_atTop.2 ⟨oneStepLocalizationScale n M.delta,
      fun K hK ↦ hK⟩] with K hbudget hK
  let cell := oneStepAnnealedDualReadout M n
    (oneStepLocalizationScale n M.delta)
  have hcell0 : 0 ≤ cell := oneStepAnnealedDualReadout_nonneg M n _
  have hmul := mul_le_mul_of_nonneg_left hbudget hcell0
  rw [← normalized_sum_integral_lowerWeight_mul_neumannSourceCellSlope_randomAStarInv_eq
    M n h q hK hh hq] at hmul
  simpa only [cell, mul_comm] using hmul



end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
