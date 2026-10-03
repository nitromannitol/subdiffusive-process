module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPaperNeumannFlux
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepParentWeightedEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepSourceReplacementMoment
public import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Averages

@[expose] public section

/-!
# Source-cell estimates for the correctly signed Neumann flux

This file transports the reciprocal one-step weighted-energy estimates from
the canonical origin solution to the manuscript flux
`exp(H) q - grad W = exp(H) q + grad u`.  The sign change affects only the
constant-gradient cross term, whose expectation is zero.
-/

open MeasureTheory Homogenization Homogenization.Book
open Homogenization.Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal BigOperators

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- Reversing the sign of the Neumann gradient changes the reciprocal
weighted energy by exactly four times the unweighted constant-gradient
pairing. -/
theorem cubeAverage_oneStepOriginNeumann_plus_eq_minus_add_cross
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    cubeAverage (originCube d m) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (q + oneStepMultiplierAt M n h x omega • q +
              ((oneStepOriginNeumannSolution M n h q m omega hh)
                |>.toH1Function.grad x))) =
      cubeAverage (originCube d m) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (q + oneStepMultiplierAt M n h x omega • q -
              ((oneStepOriginNeumannSolution M n h q m omega hh)
                |>.toH1Function.grad x))) +
        4 * cubeAverage (originCube d m) (fun x ↦
          vecDot q ((oneStepOriginNeumannSolution M n h q m omega hh)
            |>.toH1Function.grad x)) := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [← integral_const_mul]
  rw [← integral_add]
  · apply integral_congr_ae
    filter_upwards with x
    rw [oneStepMultiplierAt_eq_exp_centeredShell_sub_one M n h x omega hh]
    have hcancel : Real.exp (-oneStepCenteredShellAt M n h x omega) *
        Real.exp (oneStepCenteredShellAt M n h x omega) = 1 := by
      rw [← Real.exp_add]
      simp
    unfold vecNormSq vecDot
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    let b := Real.exp (oneStepCenteredShellAt M n h x omega)
    let c := Real.exp (-oneStepCenteredShellAt M n h x omega)
    let g := (oneStepOriginNeumannSolution M n h q m omega hh)
      |>.toH1Function.grad x i
    have hplus : q i + (b - 1) * q i + g = b * q i + g := by ring
    have hminus : q i + (b - 1) * q i - g = b * q i - g := by ring
    change c * ((q i + (b - 1) * q i + g) *
        (q i + (b - 1) * q i + g)) =
      c * ((q i + (b - 1) * q i - g) *
        (q i + (b - 1) * q i - g)) + 4 * (q i * g)
    rw [hplus, hminus]
    calc
      c * ((b * q i + g) * (b * q i + g)) =
          c * ((b * q i - g) * (b * q i - g)) +
            4 * (c * b) * (q i * g) := by ring
      _ = _ := by
        rw [show c * b = 1 by exact hcancel]
        ring
  · let Q := originCube d m
    let F : Vec d → Vec d := fun x ↦
      q + oneStepMultiplierAt M n h x omega • q -
        ((oneStepOriginNeumannSolution M n h q m omega hh)
          |>.toH1Function.grad x)
    have hforcing : MemVectorL2 (openCubeSet Q) (fun x ↦
        oneStepMultiplierAt M n h x omega • q) := by
      apply memVectorL2_openCubeSet_of_continuous Q
      exact (continuous_oneStepMultiplierAt_sample M n h omega).smul
        (continuous_const : Continuous fun _ : Vec d ↦ q)
    have hF : MemVectorL2 (openCubeSet Q) F :=
      ((memVectorL2_const q).add hforcing).sub
        ((oneStepOriginNeumannSolution M n h q m omega hh).toH1Function
          |>.grad_memVectorL2)
    have hFsq : IntegrableOn (fun x ↦ vecNormSq (F x))
        (openCubeSet Q) volume := by
      simpa only [vecNormSq] using
        integrableOn_vecDot_of_memVectorL2 hF hF
    apply integrable_normalizedCubeMeasure_of_integrableOn_cubeSet Q
    apply integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr
    exact integrableOn_inverseCenteredShell_mul_vecNormSq
      M n h Q omega hh F hFsq
  · let Q := originCube d m
    have hgrad := (oneStepOriginNeumannSolution M n h q m omega hh)
      |>.toH1Function.grad_memVectorL2
    have hcrossOpen : IntegrableOn (fun x ↦ vecDot q
        ((oneStepOriginNeumannSolution M n h q m omega hh)
          |>.toH1Function.grad x)) (openCubeSet Q) volume :=
      integrableOn_vecDot_of_memVectorL2 (memLp_const q) hgrad
    exact (integrable_normalizedCubeMeasure_of_integrableOn_cubeSet Q
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hcrossOpen)
      ).const_mul 4

/-- On an origin cube, the translated measurable Neumann solver and the
canonical origin solver have the same correctly signed weighted flux. -/
theorem cubeAverage_oneStepPaperNeumannFlux_origin_eq_originSolution
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Vec d) (m : ℤ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    cubeAverage (originCube d m) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepPaperNeumannFlux M n h q
            (originCube d m) omega hh x)) =
      cubeAverage (originCube d m) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq
            (q + oneStepMultiplierAt M n h x omega • q +
              ((oneStepOriginNeumannSolution M n h q m omega hh)
                |>.toH1Function.grad x))) := by
  let Q := originCube d m
  let u := oneStepOriginNeumannGradientL2 M n h q m omega
  let v := H1MeanZeroFunction.gradToHilbertVectorL2
    (oneStepTriadicNeumannSolution M n h q Q omega hh)
  have huv : u = v :=
    oneStepOriginNeumannGradientL2_eq_triadic M n h q m omega hh
  have huCoe : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ HilbertVec.ofVec
        ((oneStepOriginNeumannSolution M n h q m omega hh)
          |>.toH1Function.grad x) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    have hcoe := (oneStepOriginNeumannSolution M n h q m omega hh)
      |>.toH1Function.coeFn_gradToHilbertVectorL2
    have hcoe' : ((oneStepOriginNeumannSolution M n h q m omega hh)
        |>.gradToHilbertVectorL2 : Vec d → HilbertVec d) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
        fun x ↦ HilbertVec.ofVec
          ((oneStepOriginNeumannSolution M n h q m omega hh)
            |>.toH1Function.grad x) := by
      simpa only [H1MeanZeroFunction.gradToHilbertVectorL2] using! hcoe
    rw [oneStepOriginNeumannSolution_gradient_eq M n h q m omega hh] at hcoe'
    simpa only [u] using hcoe'
  have hvCoe : (v : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ HilbertVec.ofVec
        ((oneStepTriadicNeumannSolution M n h q Q omega hh)
          |>.toH1Function.grad x) := by
    apply ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
    simpa only [v, H1MeanZeroFunction.gradToHilbertVectorL2,
      H1Function.gradToHilbertVectorL2, hilbertifyVecField] using!
      (oneStepTriadicNeumannSolution M n h q Q omega hh)
        |>.toH1Function.coeFn_gradToHilbertVectorL2
  have hgrad : (fun x ↦
      (oneStepTriadicNeumannSolution M n h q Q omega hh)
        |>.toH1Function.grad x) =ᵐ[normalizedCubeMeasure Q]
      fun x ↦ (oneStepOriginNeumannSolution M n h q m omega hh)
        |>.toH1Function.grad x := by
    rw [huv] at huCoe
    filter_upwards [hvCoe, huCoe] with x hvx hux
    have hx := congrArg HilbertVec.toVec (hvx.symm.trans hux)
    simpa only [HilbertVec.toVec_ofVec] using hx
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  apply integral_congr_ae
  filter_upwards [hgrad] with x hx
  unfold oneStepPaperNeumannFlux
  rw [hx]

/-- The correctly signed manuscript flux has the same expected parent energy
as the reciprocal principal-factor carrier. -/
theorem integral_oneStepPaperNeumannFlux_weightedCubeAverage_eq_principalFactor
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Vec d) (K : ℕ) (hh : 0 < h) (hq : vecNormSq q = 1)
    (hscale : (h : ℝ) ≤ M.delta⁻¹) :
    ∫ omega, cubeAverage (originCube d (K : ℤ)) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepPaperNeumannFlux M n h q
            (originCube d (K : ℤ)) omega hh x)) ∂M.P.toMeasure =
      ∫ omega, oneStepNeumannWeightedPrincipalFactor
        M n h q (K : ℤ) omega hh ∂M.P.toMeasure := by
  let minusEnergy : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦
    cubeAverage (originCube d (K : ℤ)) (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq
          (q + oneStepMultiplierAt M n h x omega • q -
            ((oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh)
              |>.toH1Function.grad x)))
  let cross : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦
    cubeAverage (originCube d (K : ℤ)) (fun x ↦
      vecDot q ((oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh)
        |>.toH1Function.grad x))
  have hminusInt : Integrable minusEnergy M.P.toMeasure := by
    refine (integrable_oneStepNeumannSlopeField_weightedCubeAverage
      M n h q K hh hq hscale).congr ?_
    filter_upwards with omega
    simpa only [minusEnergy] using
      cubeAverage_oneStepNeumannSlopeField_origin_eq_originSolution
        M n h q (K : ℤ) omega hh
  have hcrossInt : Integrable cross M.P.toMeasure := by
    simpa only [cross] using
      integrable_cubeAverage_vecDot_oneStepOriginNeumannGradient
        M n h q (K : ℤ) hh
  have hcrossZero : ∫ omega, cross omega ∂M.P.toMeasure = 0 := by
    simpa only [cross] using
      integral_cubeAverage_vecDot_oneStepOriginNeumannGradient_eq_zero
        M n h q (K : ℤ) hh
  calc
    _ = ∫ omega, minusEnergy omega + 4 * cross omega ∂M.P.toMeasure := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [cubeAverage_oneStepPaperNeumannFlux_origin_eq_originSolution
        M n h q (K : ℤ) omega hh]
      exact cubeAverage_oneStepOriginNeumann_plus_eq_minus_add_cross
        M n h q (K : ℤ) omega hh
    _ = (∫ omega, minusEnergy omega ∂M.P.toMeasure) +
        4 * ∫ omega, cross omega ∂M.P.toMeasure := by
      rw [integral_add hminusInt (hcrossInt.const_mul 4), integral_const_mul]
    _ = ∫ omega, minusEnergy omega ∂M.P.toMeasure := by
      rw [hcrossZero]
      ring
    _ = _ := by
      simpa only [minusEnergy] using
        integral_oneStepOriginNeumann_weightedCubeAverage_eq_principalFactor
          M n h q (K : ℤ) hh hq hscale

/-- Uniform thermodynamic parent-energy bound for the correctly signed
manuscript flux. -/
theorem exists_eventually_integral_oneStepPaperNeumannFlux_weightedCubeAverage_le
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (q : Vec d) (hh : 0 < h) (_hq : vecNormSq q = 1)
        (_hscale : (h : ℝ) ≤ M.delta⁻¹) {epsilon : ℝ}, 0 < epsilon →
        ∀ᶠ K : ℕ in Filter.atTop,
          ∫ omega, cubeAverage (originCube d (K : ℤ)) (fun x ↦
              Real.exp (-oneStepCenteredShellAt M n h x omega) *
                vecNormSq (oneStepPaperNeumannFlux M n h q
                  (originCube d (K : ℤ)) omega hh x)) ∂M.P.toMeasure ≤
            1 + 2 * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P * (h : ℝ) / (d : ℝ) +
              C * M.delta ^ 4 * (h : ℝ) ^ 2 + epsilon := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_eventually_integral_oneStepNeumannWeightedPrincipalFactor_le d
  refine ⟨C, hC, ?_⟩
  intro M n h q hh hq hscale epsilon hepsilon
  filter_upwards [hbound M n h q hh hq hscale hepsilon] with K hK
  rw [integral_oneStepPaperNeumannFlux_weightedCubeAverage_eq_principalFactor
    M n h q K hh hq hscale]
  exact hK

/-! ## Uniform spatial fourth moment for source-cell Jensen -/

theorem oneStepPaperNeumannFluxL2_eq_legacy_add_grad_add_grad
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepPaperNeumannFluxL2 M n h q Q omega hh =
      (oneStepNeumannSlopeL2 M n h q Q omega hh +
        ((oneStepTriadicNeumannSolution M n h q Q omega hh)
          |>.gradToHilbertVectorL2)) +
        ((oneStepTriadicNeumannSolution M n h q Q omega hh)
          |>.gradToHilbertVectorL2) := by
  unfold oneStepPaperNeumannFluxL2 oneStepNeumannSlopeL2
  module

theorem memLp_four_oneStepTriadicNeumannGradL2_space
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Vec d) (K : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp (((oneStepTriadicNeumannSolution M n h q
      (originCube d (K : ℤ)) omega hh).gradToHilbertVectorL2 :
        Vec d → HilbertVec d)) 4
      (normalizedCubeMeasure (originCube d (K : ℤ))) := by
  obtain ⟨_C, _hC, hcz⟩ := exists_oneStepOriginNeumann_gradient_four_cz d
  rw [← oneStepOriginNeumannGradientL2_eq_triadic
    M n h q (K : ℤ) omega hh]
  have hx := memLp_four_gradToHilbertVectorL2_normalizedCubeMeasure
    (originCube d (K : ℤ))
    (oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh).toH1Function
    (hcz M n h omega q (K : ℤ) hh hq).1
  have hx' : MemLp
      ((oneStepOriginNeumannSolution M n h q (K : ℤ) omega hh)
        |>.gradToHilbertVectorL2 : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure (originCube d (K : ℤ))) := by
    simpa only [H1MeanZeroFunction.gradToHilbertVectorL2] using hx
  rw [oneStepOriginNeumannSolution_gradient_eq
    M n h q (K : ℤ) omega hh] at hx'
  exact hx'

theorem memLp_four_oneStepPaperNeumannFluxL2_space
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Vec d) (K : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    MemLp ((oneStepPaperNeumannFluxL2 M n h q
      (originCube d (K : ℤ)) omega hh) : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure (originCube d (K : ℤ))) := by
  let Q := originCube d (K : ℤ)
  let legacy := oneStepNeumannSlopeL2 M n h q Q omega hh
  let g := (oneStepTriadicNeumannSolution M n h q Q omega hh)
    |>.gradToHilbertVectorL2
  have hlegacy : MemLp (legacy : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    simpa only [legacy, Q] using
      memLp_four_oneStepNeumannSlopeL2_space M n h q K omega hh hq
  have hg : MemLp (g : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    simpa only [g, Q] using
      memLp_four_oneStepTriadicNeumannGradL2_space
        M n h q K omega hh hq
  rw [oneStepPaperNeumannFluxL2_eq_legacy_add_grad_add_grad]
  exact sourceReplacement_memLp_four_coe_add Q (legacy + g) g
    (sourceReplacement_memLp_four_coe_add Q legacy g hlegacy hg) hg

theorem oneStepPaperNeumannFlux_fourthNorm_le_legacy_add_two_grad
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Vec d) (K : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
        (oneStepPaperNeumannFluxL2 M n h q
          (originCube d (K : ℤ)) omega hh) ≤
      oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
          (oneStepNeumannSlopeL2 M n h q
            (originCube d (K : ℤ)) omega hh) +
        oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
          (oneStepOriginNeumannGradientL2 M n h q (K : ℤ) omega) +
        oneStepNormalizedFourthNormBorel (originCube d (K : ℤ))
          (oneStepOriginNeumannGradientL2 M n h q (K : ℤ) omega) := by
  let Q := originCube d (K : ℤ)
  let legacy := oneStepNeumannSlopeL2 M n h q Q omega hh
  let g := (oneStepTriadicNeumannSolution M n h q Q omega hh)
    |>.gradToHilbertVectorL2
  have hlegacy : MemLp (legacy : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    simpa only [legacy, Q] using
      memLp_four_oneStepNeumannSlopeL2_space M n h q K omega hh hq
  have hg : MemLp (g : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    simpa only [g, Q] using
      memLp_four_oneStepTriadicNeumannGradL2_space
        M n h q K omega hh hq
  have hfirst := sourceReplacement_fourthNormBorel_add_le
    Q (legacy + g) g
      (sourceReplacement_memLp_four_coe_add Q legacy g hlegacy hg) hg
  have hsecond := sourceReplacement_fourthNormBorel_add_le
    Q legacy g hlegacy hg
  rw [oneStepPaperNeumannFluxL2_eq_legacy_add_grad_add_grad]
  have hgeq : oneStepNormalizedFourthNormBorel Q g =
      oneStepNormalizedFourthNormBorel Q
        (oneStepOriginNeumannGradientL2 M n h q (K : ℤ) omega) := by
    dsimp only [g, Q]
    rw [← oneStepOriginNeumannGradientL2_eq_triadic
      M n h q (K : ℤ) omega hh]
  calc
    _ ≤ oneStepNormalizedFourthNormBorel Q (legacy + g) +
        oneStepNormalizedFourthNormBorel Q g := hfirst
    _ ≤ (oneStepNormalizedFourthNormBorel Q legacy +
          oneStepNormalizedFourthNormBorel Q g) +
        oneStepNormalizedFourthNormBorel Q g := by gcongr
    _ = _ := by simp only [Q, legacy, hgeq]

/-- Uniform random `L⁴` bound for the normalized spatial `L⁴` norm of
the correctly signed Neumann flux. -/
theorem exists_memLp_four_oneStepPaperNeumannFluxFourthNorm
    (d : ℕ) [NeZero d] :
    ∃ D : ℝ≥0∞, D < ∞ ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
        (q : Vec d) (K : ℕ) (hh : 0 < h) (_hq : vecNormSq q = 1),
        (h : ℝ) ≤ M.delta⁻¹ →
        let S := fun omega ↦ oneStepNormalizedFourthNormBorel
          (originCube d (K : ℤ))
          (oneStepPaperNeumannFluxL2 M n h q
            (originCube d (K : ℤ)) omega hh)
        MemLp S 4 M.P.toMeasure ∧ eLpNorm S 4 M.P.toMeasure ≤ D := by
  obtain ⟨Dlegacy, hDlegacy, hlegacy⟩ :=
    exists_memLp_four_oneStepNeumannSlopeFourthNorm d
  obtain ⟨Cgrad, hCgrad, hgrad⟩ :=
    exists_memLp_four_oneStepOriginNeumannFourthNorm d
  let Agrad : ℝ≥0∞ :=
    (Cgrad * (ENNReal.ofReal oneStepRatioEightUniformConst) ^ (4 : ℝ)) ^
      (1 / 4 : ℝ)
  let D : ℝ≥0∞ := Dlegacy + Agrad + Agrad
  have hAgrad : Agrad < ∞ := by
    dsimp only [Agrad]
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact ENNReal.mul_ne_top hCgrad.ne
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hD : D < ∞ := by
    dsimp only [D]
    finiteness
  refine ⟨D, hD, ?_⟩
  intro M n h q K hh hq hblock
  let Q := originCube d (K : ℤ)
  let L : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦
    oneStepNormalizedFourthNormBorel Q
      (oneStepNeumannSlopeL2 M n h q Q omega hh)
  let G : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦
    oneStepNormalizedFourthNormBorel Q
      (oneStepOriginNeumannGradientL2 M n h q (K : ℤ) omega)
  let S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦
    oneStepNormalizedFourthNormBorel Q
      (oneStepPaperNeumannFluxL2 M n h q Q omega hh)
  let T : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦ L omega + G omega + G omega
  obtain ⟨hL, hLnorm⟩ := hlegacy M n h q K hh hq hblock
  have hGraw := hgrad M n h q (K : ℤ) hh hq
  have hG : MemLp G 4 M.P.toMeasure := by
    simpa only [G, Q] using hGraw.1
  have hratio : ENNReal.ofReal (oneStepRatioMinusOneEightBound M h) ≤
      ENNReal.ofReal oneStepRatioEightUniformConst :=
    ENNReal.ofReal_le_ofReal
      (oneStepRatioMinusOneEightBound_le_uniform M h hblock)
  have hGnorm : eLpNorm G 4 M.P.toMeasure ≤ Agrad := by
    calc
      eLpNorm G 4 M.P.toMeasure ≤
          (Cgrad * (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
            (4 : ℝ)) ^ (1 / 4 : ℝ) := by
        simpa only [G, Q] using hGraw.2
      _ ≤ Agrad := by dsimp only [Agrad]; gcongr
  have hSmeas : AEStronglyMeasurable S M.P.toMeasure := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_oneStepNormalizedFourthNormBorel Q).comp
      ((measurable_oneStepPaperNeumannFluxL2_potentialShellIndexSigma_Ioi
        M n h q Q hh).mono
          (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl)
  have hT : MemLp T 4 M.P.toMeasure := by
    dsimp only [T]
    exact (hL.add hG).add hG
  have hpoint : ∀ omega, S omega ≤ T omega := by
    intro omega
    simpa only [S, T, L, G, Q] using
      oneStepPaperNeumannFlux_fourthNorm_le_legacy_add_two_grad
        M n h q K omega hh hq
  have hS : MemLp S 4 M.P.toMeasure := by
    apply hT.mono' hSmeas
    filter_upwards with omega
    have hS0 : 0 ≤ S omega := ENNReal.toReal_nonneg
    have hT0 : 0 ≤ T omega := by
      dsimp only [T, L, G]
      exact add_nonneg
        (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        ENNReal.toReal_nonneg
    simpa only [Real.norm_eq_abs, abs_of_nonneg hS0, abs_of_nonneg hT0]
      using hpoint omega
  refine ⟨hS, ?_⟩
  have hST : eLpNorm S 4 M.P.toMeasure ≤ eLpNorm T 4 M.P.toMeasure := by
    apply eLpNorm_mono_ae hSmeas
    filter_upwards with omega
    have hS0 : 0 ≤ S omega := ENNReal.toReal_nonneg
    have hT0 : 0 ≤ T omega := by
      dsimp only [T, L, G]
      exact add_nonneg
        (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        ENNReal.toReal_nonneg
    simpa only [Real.norm_eq_abs, abs_of_nonneg hS0, abs_of_nonneg hT0]
      using hpoint omega
  have hadd1 := eLpNorm_add_le (f := L) (g := G) (μ := M.P.toMeasure) (p := (4 : ℝ≥0∞))
    (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hadd2 := eLpNorm_add_le (f := L + G) (g := G) (μ := M.P.toMeasure) (p := (4 : ℝ≥0∞))
    (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hadd1' : eLpNorm (fun omega ↦ L omega + G omega) 4 M.P.toMeasure ≤
      eLpNorm L 4 M.P.toMeasure + eLpNorm G 4 M.P.toMeasure := by
    simpa only [Pi.add_apply] using! hadd1
  calc
    eLpNorm S 4 M.P.toMeasure ≤ eLpNorm T 4 M.P.toMeasure := hST
    _ ≤ eLpNorm (fun omega ↦ L omega + G omega) 4 M.P.toMeasure +
        eLpNorm G 4 M.P.toMeasure := by
      simpa only [T, Pi.add_apply] using! hadd2
    _ ≤ (eLpNorm L 4 M.P.toMeasure + eLpNorm G 4 M.P.toMeasure) +
        eLpNorm G 4 M.P.toMeasure := add_le_add hadd1' le_rfl
    _ ≤ D := by
      dsimp only [D]
      exact add_le_add (add_le_add hLnorm hGnorm) hGnorm

theorem measurable_oneStepPaperNeumannSourceCellEnergy
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (hR : R ∈ oneStepSourceCells d K n M.delta) (hh : 0 < h) :
    Measurable fun omega ↦ cubeAverage R (fun x ↦
      vecNormSq (oneStepPaperNeumannFlux M n h q
        (originCube d (K : ℤ)) omega hh x)) := by
  let Q := originCube d (K : ℤ)
  have hFlux : Measurable
      (oneStepPaperNeumannFluxL2 M n h q Q · hh) :=
    (measurable_oneStepPaperNeumannFluxL2_potentialShellIndexSigma_Ioi
      M n h q Q hh).mono
        (potentialShellIndexSigma_le_borel (d := d) (Set.Ioi n)) le_rfl
  have hwindow : Measurable fun omega ↦
      oneStepWindowL2Norm (openCubeSet Q) (openCubeSet R)
        (oneStepPaperNeumannFluxL2 M n h q Q omega hh) :=
    (continuous_oneStepWindowL2Norm _ _ (measurableSet_openCubeSet R))
      |>.measurable.comp hFlux
  have heq : (fun omega ↦ cubeAverage R (fun x ↦
      vecNormSq (oneStepPaperNeumannFlux M n h q Q omega hh x))) =
      fun omega ↦ (cubeVolume R)⁻¹ *
        oneStepWindowL2Norm (openCubeSet Q) (openCubeSet R)
          (oneStepPaperNeumannFluxL2 M n h q Q omega hh) ^ 2 := by
    funext omega
    rw [oneStepPaperNeumannFluxL2_eq_toHilbertVectorL2OfVecField]
    exact cubeAverage_vecNormSq_eq_oneStepWindowL2Norm_sq
      (mem_oneStepSourceCells hR)
        (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh)
  rw [heq]
  exact measurable_const.mul (hwindow.pow_const 2)

theorem cubeAverage_oneStepPaperNeumannFlux_vecNormSq_sq_eq_fourthNormBorel
    {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ)
    (q : Vec d) (K : ℕ) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hh : 0 < h) (hq : vecNormSq q = 1) :
    cubeAverage (originCube d (K : ℤ)) (fun x ↦
        vecNormSq (oneStepPaperNeumannFlux M n h q
          (originCube d (K : ℤ)) omega hh x) ^ 2) =
      Real.rpow (oneStepNormalizedFourthNormBorel
        (originCube d (K : ℤ))
        (oneStepPaperNeumannFluxL2 M n h q
          (originCube d (K : ℤ)) omega hh)) 4 := by
  let Q := originCube d (K : ℤ)
  let F := oneStepPaperNeumannFlux M n h q Q omega hh
  let u := oneStepPaperNeumannFluxL2 M n h q Q omega hh
  have hu4 : MemLp (u : Vec d → HilbertVec d) 4
      (normalizedCubeMeasure Q) := by
    simpa only [u, Q] using
      memLp_four_oneStepPaperNeumannFluxL2_space
        M n h q K omega hh hq
  have hcoe : (u : Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
      hilbertifyVecField F := by
    rw [show u = toHilbertVectorL2OfVecField
        (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh) by
      exact oneStepPaperNeumannFluxL2_eq_toHilbertVectorL2OfVecField
        M n h q Q omega hh]
    exact ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
      (coeFn_toHilbertVectorL2OfVecField
        (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh))
  exact cubeAverage_vecNormSq_sq_eq_fourthNormBorel_of_ae Q F u hu4 hcoe

/-- Uniform `L²(Ω)` budget for the source-cell energies of the correctly
signed Neumann flux. -/
theorem exists_oneStepPaperNeumannSourceCellEnergy_two_budget
    (d : ℕ) [NeZero d] :
    ∃ a : ℝ, 0 ≤ a ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h K : ℕ)
        (q : Vec d) (hh : 0 < h) (_hq : vecNormSq q = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        (∀ R ∈ oneStepSourceCells d K n M.delta,
          MemLp (fun omega ↦ cubeAverage R (fun x ↦
            vecNormSq (oneStepPaperNeumannFlux M n h q
              (originCube d (K : ℤ)) omega hh x))) 2 M.P.toMeasure) ∧
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, (cubeAverage R (fun x ↦
              vecNormSq (oneStepPaperNeumannFlux M n h q
                (originCube d (K : ℤ)) omega hh x))) ^ 2
              ∂M.P.toMeasure ≤ a ^ 2) := by
  obtain ⟨D, hD, hFlux⟩ :=
    exists_memLp_four_oneStepPaperNeumannFluxFourthNorm d
  let a : ℝ := D.toReal ^ 2 + 1
  refine ⟨a, by dsimp only [a]; positivity, ?_⟩
  intro M n h K q hh hq hblock
  let Q := originCube d (K : ℤ)
  let S : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦
    oneStepNormalizedFourthNormBorel Q
      (oneStepPaperNeumannFluxL2 M n h q Q omega hh)
  let P : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun omega ↦
    cubeAverage Q (fun x ↦
      vecNormSq (oneStepPaperNeumannFlux M n h q Q omega hh x) ^ 2)
  obtain ⟨hSmem, hSnorm⟩ := hFlux M n h q K hh hq hblock
  have hPS : ∀ omega, P omega = Real.rpow (S omega) 4 := by
    intro omega
    simpa only [P, S, Q] using
      cubeAverage_oneStepPaperNeumannFlux_vecNormSq_sq_eq_fourthNormBorel
        M n h q K omega hh hq
  have hSint : Integrable (fun omega ↦ ‖S omega‖ ^ (4 : ℝ))
      M.P.toMeasure := hSmem.integrable_norm_rpow (by norm_num) (by norm_num)
  have hPint : Integrable P M.P.toMeasure := by
    have heq : P = fun omega ↦ ‖S omega‖ ^ (4 : ℝ) := by
      funext omega
      rw [hPS]
      congr 1
      rw [Real.norm_eq_abs]
      exact (abs_of_nonneg (show 0 ≤ S omega by
        exact ENNReal.toReal_nonneg)).symm
    rw [heq]
    exact hSint
  let s := oneStepSourceCells d K n M.delta
  let A : TriadicCube d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun R omega ↦
    cubeAverage R (fun x ↦
      vecNormSq (oneStepPaperNeumannFlux M n h q Q omega hh x))
  have hsNonempty : s.Nonempty := oneStepSourceCells_nonempty d K n M.delta
  have hsCard : (0 : ℝ) < s.card := by exact_mod_cast hsNonempty.card_pos
  have hpoint : ∀ omega,
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, (A R omega) ^ 2 ≤ P omega := by
    intro omega
    have hu := memLp_four_oneStepPaperNeumannFluxL2_space
      M n h q K omega hh hq
    have hcoe : ((oneStepPaperNeumannFluxL2 M n h q Q omega hh) :
        Vec d → HilbertVec d) =ᵐ[normalizedCubeMeasure Q]
        hilbertifyVecField (oneStepPaperNeumannFlux M n h q Q omega hh) := by
      rw [oneStepPaperNeumannFluxL2_eq_toHilbertVectorL2OfVecField]
      exact ae_normalizedCubeMeasure_of_ae_volumeMeasureOn Q
        (coeFn_toHilbertVectorL2OfVecField
          (oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh))
    have hspatial : MemLp (hilbertifyVecField
        (oneStepPaperNeumannFlux M n h q Q omega hh)) 4
        (normalizedCubeMeasure Q) := hu.ae_eq hcoe
    simpa only [s, A, P, Q, oneStepSourceCells] using
      normalized_sum_descendant_cubeAverage_vecNormSq_sq_le_parent
        Q (oneStepPaperNeumannFlux M n h q Q omega hh) hspatial
  have hlocalSqLe : ∀ R ∈ s, ∀ omega,
      (A R omega) ^ 2 ≤ (s.card : ℝ) * P omega := by
    intro R hR omega
    have hterm : (A R omega) ^ 2 ≤ ∑ T ∈ s, (A T omega) ^ 2 :=
      Finset.single_le_sum (fun T hT ↦ sq_nonneg (A T omega)) hR
    have hsum : ∑ T ∈ s, (A T omega) ^ 2 ≤
        (s.card : ℝ) * P omega :=
      (inv_mul_le_iff₀ hsCard).mp (hpoint omega)
    exact hterm.trans hsum
  have hAmem : ∀ R ∈ s, MemLp (A R) 2 M.P.toMeasure := by
    intro R hR
    have hmeas : Measurable (A R) := by
      simpa only [A, Q, s] using
        measurable_oneStepPaperNeumannSourceCellEnergy M n h q R hR hh
    apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    have hmajor : Integrable (fun omega ↦ (s.card : ℝ) * P omega)
        M.P.toMeasure := hPint.const_mul (s.card : ℝ)
    apply hmajor.mono (hmeas.pow_const 2).aestronglyMeasurable
    filter_upwards with omega
    have hA0 : 0 ≤ A R omega := by
      dsimp only [A]
      exact cubeAverage_nonneg_of_nonneg_on fun x _hx ↦ vecNormSq_nonneg _
    have hP0 : 0 ≤ P omega := by
      dsimp only [P]
      exact cubeAverage_nonneg_of_nonneg_on fun x _hx ↦ sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hP0)]
    exact hlocalSqLe R hR omega
  refine ⟨?_, ?_⟩
  · intro R hR
    simpa only [s, A, Q] using hAmem R hR
  have hAvgInt : Integrable (fun omega ↦
      ((s.card : ℝ)⁻¹) * ∑ R ∈ s, (A R omega) ^ 2) M.P.toMeasure := by
    apply Integrable.const_mul
    exact MeasureTheory.integrable_finset_sum s fun R hR ↦
      (memLp_two_iff_integrable_sq (hAmem R hR).aestronglyMeasurable).mp (hAmem R hR)
  have havg := integral_mono hAvgInt hPint hpoint
  have hrewrite :
      ∫ omega, ((s.card : ℝ)⁻¹) * ∑ R ∈ s, (A R omega) ^ 2
          ∂M.P.toMeasure =
        ((s.card : ℝ)⁻¹) * ∑ R ∈ s,
          ∫ omega, (A R omega) ^ 2 ∂M.P.toMeasure := by
    rw [integral_const_mul]
    congr 1
    exact integral_finset_sum s fun R hR ↦
      (memLp_two_iff_integrable_sq (hAmem R hR).aestronglyMeasurable).mp (hAmem R hR)
  rw [hrewrite] at havg
  have hPNat : P = fun omega ↦ S omega ^ 4 := by
    funext omega
    rw [hPS]
    exact Real.rpow_natCast _ 4
  have hPIntegral : ∫ omega, P omega ∂M.P.toMeasure =
      (eLpNorm S 4 M.P.toMeasure).toReal ^ 4 := by
    rw [hPNat]
    exact integral_pow_four_eq_toReal_eLpNorm_pow_four S hSmem
  have hnormReal : (eLpNorm S 4 M.P.toMeasure).toReal ≤ D.toReal :=
    ENNReal.toReal_mono hD.ne hSnorm
  have hPBound : ∫ omega, P omega ∂M.P.toMeasure ≤ a ^ 2 := by
    rw [hPIntegral]
    dsimp only [a]
    have hnorm0 : 0 ≤ (eLpNorm S 4 M.P.toMeasure).toReal :=
      ENNReal.toReal_nonneg
    have hpow4 := pow_le_pow_left₀ hnorm0 hnormReal 4
    have htail : D.toReal ^ 4 ≤ (D.toReal ^ 2 + 1) ^ 2 := by
      nlinarith [sq_nonneg (D.toReal ^ 2)]
    exact hpow4.trans htail
  simpa only [s, A, Q] using havg.trans hPBound

theorem oneStepPaperNeumannFlux_memLp_sourceCell
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (q : Vec d)
    (R : TriadicCube d) (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    MemLp (oneStepPaperNeumannFlux M n h q
      (originCube d (K : ℤ)) omega hh) 2 (normalizedCubeMeasure R) := by
  let Q := originCube d (K : ℤ)
  have hRQ : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth (mem_oneStepSourceCells hR)
  exact memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet R
    ((oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh).mono_measure
      (Measure.restrict_mono hRQ le_rfl))

theorem oneStepLowerSourceCellWeight_mul_paperNeumannCellSlope_le
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hR : R ∈ oneStepSourceCells d K n M.delta)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    oneStepLowerSourceCellWeight M n h R omega *
        vecNormSq (oneStepPaperNeumannCellSlope M n h q
          (originCube d (K : ℤ)) R omega hh) ≤
      cubeAverage R (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepPaperNeumannFlux M n h q
            (originCube d (K : ℤ)) omega hh x)) +
      2 * oneStepLowerSourceCellWeight M n h R omega *
        oneStepSourceCellShellOscillationEnvelope n h R omega *
        cubeAverage R (fun x ↦
          vecNormSq (oneStepPaperNeumannFlux M n h q
            (originCube d (K : ℤ)) omega hh x)) := by
  let F := oneStepPaperNeumannFlux M n h q
    (originCube d (K : ℤ)) omega hh
  let W := oneStepLowerSourceCellWeight M n h R omega
  let E := oneStepSourceCellShellOscillationEnvelope n h R omega
  let w : Vec d → ℝ := fun x ↦
    Real.exp (-oneStepCenteredShellAt M n h x omega)
  have hscale : R.scale ≤ (n : ℤ) := by
    rw [oneStepSourceCells_scale_eq hK hR]
    exact_mod_cast Nat.sub_le n (oneStepLocalizationDepth M.delta)
  have hF : MemLp F 2 (normalizedCubeMeasure R) :=
    oneStepPaperNeumannFlux_memLp_sourceCell M n h q R hR omega hh
  have hbound := weight_mul_vecNormSq_cubeAverageVec_le R W E w F
    (le_of_lt (cutoffRatioSup_pos M n (n + h)
      (Ch02.cubeDomain R) omega)) hF
    ((measurable_oneStepCenteredShellAt_space M n h omega).neg.exp
      |>.aestronglyMeasurable)
    (fun _ _ ↦ (Real.exp_pos _).le)
    (fun x hx ↦
      exp_neg_oneStepCenteredShellAt_le_lowerSourceCellWeight
        M n h R omega hh hx)
    (fun x hx ↦
      oneStepLowerSourceCellWeight_sub_exp_neg_le_two_mul_envelope
        M n h R omega hscale hh hx)
  rw [oneStepPaperNeumannCellSlope_eq_cubeAverageVec
    M n h q (originCube d (K : ℤ)) R omega hh
      (mem_oneStepSourceCells hR)]
  simpa only [F, W, E, w, mul_assoc] using hbound

/-- Jensen-localization error for the correctly signed reciprocal flux. -/
def oneStepPaperNeumannSourceCellJensenError
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (q : Vec d) (R : TriadicCube d)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) : ℝ :=
  2 * oneStepLowerSourceCellWeight M n h R omega *
    oneStepSourceCellShellOscillationEnvelope n h R omega *
    cubeAverage R (fun x ↦
      vecNormSq (oneStepPaperNeumannFlux M n h q
        (originCube d (K : ℤ)) omega hh x))

theorem integrableOn_oneStepPaperNeumannWeightedSlope_parent
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    IntegrableOn (fun x ↦
      Real.exp (-oneStepCenteredShellAt M n h x omega) *
        vecNormSq (oneStepPaperNeumannFlux M n h q
          (originCube d (K : ℤ)) omega hh x))
      (cubeSet (originCube d (K : ℤ))) volume := by
  let Q := originCube d (K : ℤ)
  let F := oneStepPaperNeumannFlux M n h q Q omega hh
  have hF := oneStepPaperNeumannFlux_memVectorL2 M n h q Q omega hh
  have hFsq : IntegrableOn (fun x ↦ vecNormSq (F x))
      (openCubeSet Q) volume := by
    simpa only [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hF hF
  apply integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr
  exact integrableOn_inverseCenteredShell_mul_vecNormSq
    M n h Q omega hh F hFsq

theorem normalized_sum_oneStepPaperNeumannWeightedSlope_eq_parent
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (q : Vec d) (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          cubeAverage R (fun x ↦
            Real.exp (-oneStepCenteredShellAt M n h x omega) *
              vecNormSq (oneStepPaperNeumannFlux M n h q
                (originCube d (K : ℤ)) omega hh x)) =
      cubeAverage (originCube d (K : ℤ)) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepPaperNeumannFlux M n h q
            (originCube d (K : ℤ)) omega hh x)) :=
  normalized_sum_sourceCells_cubeAverage_eq_parent _
    (integrableOn_oneStepPaperNeumannWeightedSlope_parent
      M n h q omega hh)

theorem normalized_sum_oneStepPaperNeumannSourceCellWeight_le_parent_add_jensenError
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (q : Vec d)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (hh : 0 < h) :
    (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          oneStepLowerSourceCellWeight M n h R omega *
            vecNormSq (oneStepPaperNeumannCellSlope M n h q
              (originCube d (K : ℤ)) R omega hh) ≤
      cubeAverage (originCube d (K : ℤ)) (fun x ↦
        Real.exp (-oneStepCenteredShellAt M n h x omega) *
          vecNormSq (oneStepPaperNeumannFlux M n h q
            (originCube d (K : ℤ)) omega hh x)) +
      (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          oneStepPaperNeumannSourceCellJensenError
            (K := K) M n h q R omega hh := by
  have hcells : ∀ R ∈ oneStepSourceCells d K n M.delta,
      oneStepLowerSourceCellWeight M n h R omega *
          vecNormSq (oneStepPaperNeumannCellSlope M n h q
            (originCube d (K : ℤ)) R omega hh) ≤
        cubeAverage R (fun x ↦
          Real.exp (-oneStepCenteredShellAt M n h x omega) *
            vecNormSq (oneStepPaperNeumannFlux M n h q
              (originCube d (K : ℤ)) omega hh x)) +
        oneStepPaperNeumannSourceCellJensenError
          (K := K) M n h q R omega hh := by
    intro R hR
    exact oneStepLowerSourceCellWeight_mul_paperNeumannCellSlope_le
      M n h q R hK hR omega hh
  have hsum := Finset.sum_le_sum hcells
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ (((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) by
      positivity)
  rw [Finset.sum_add_distrib, mul_add,
    normalized_sum_oneStepPaperNeumannWeightedSlope_eq_parent
      M n h q omega hh] at hmul
  exact hmul

/-! ## Integrated Jensen price for the paper-sign flux -/

/-- The normalized paper-sign Jensen errors inherit the same `delta^17`
localization gain as the legacy Neumann carrier.  The only field-dependent
input is the averaged source-cell `L²(Omega)` energy budget proved above. -/
theorem normalized_sum_integral_oneStepPaperNeumannSourceCellJensenError_le
    {d K : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n h : ℕ) (q : Vec d)
    (hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
    (hK : oneStepLocalizationScale n M.delta ≤ K)
    (hh : 0 < h) (hblock : (h : ℝ) ≤ M.delta⁻¹)
    {a : ℝ} (ha0 : 0 ≤ a)
    (hA : ∀ R ∈ oneStepSourceCells d K n M.delta,
      MemLp (fun omega ↦ cubeAverage R (fun x ↦
        vecNormSq (oneStepPaperNeumannFlux M n h q
          (originCube d (K : ℤ)) omega hh x))) 2 M.P.toMeasure)
    (hAsq :
      ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, (cubeAverage R (fun x ↦
            vecNormSq (oneStepPaperNeumannFlux M n h q
              (originCube d (K : ℤ)) omega hh x))) ^ 2
            ∂M.P.toMeasure ≤ a ^ 2)) :
    ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
        ∑ R ∈ oneStepSourceCells d K n M.delta,
          ∫ omega, oneStepPaperNeumannSourceCellJensenError
            (K := K) M n h q R omega hh ∂M.P.toMeasure) ≤
      2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
        (oneStepDerivativeGaugeConst * M.delta ^ (17 : ℕ)) * a := by
  let s := oneStepSourceCells d K n M.delta
  let W : TriadicCube d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun R ↦
    oneStepLowerSourceCellWeight M n h R
  let E : TriadicCube d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun R ↦
    oneStepSourceCellShellOscillationEnvelope n h R
  let A : TriadicCube d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d → ℝ := fun R omega ↦
    cubeAverage R (fun x ↦ vecNormSq (oneStepPaperNeumannFlux
      M n h q (originCube d (K : ℤ)) omega hh x))
  have hraw := normalized_finset_integral_two_mul_three_le
    s (oneStepSourceCells_nonempty d K n M.delta) W E A
    (fun R hR omega ↦ (cutoffRatioSup_pos M n (n + h)
      (Ch02.cubeDomain R) omega).le)
    (fun R hR omega ↦
      oneStepSourceCellShellOscillationEnvelope_nonneg n h R omega)
    (fun R hR omega ↦ cubeAverage_nonneg_of_nonneg_on
      (fun x hx ↦ vecNormSq_nonneg _))
    (fun R hR ↦ memLp_four_oneStepLowerSourceCellWeight_of_block
      M n h R hK hR hh hblock)
    (fun R hR ↦ memLp_four_oneStepSourceCellShellOscillationEnvelope
      M n h R hsource hK hR hh)
    (fun R hR ↦ hA R hR)
    (add_nonneg (oneStepSourceCellWeightFourthRootConst_pos M).le zero_le_one)
    (mul_nonneg oneStepDerivativeGaugeConst_pos.le
      (pow_nonneg M.shellPrefix.delta_pos.le 17)) ha0
    (fun R hR ↦
      (toReal_eLpNorm_oneStepSourceCellWeights_four_le
        M n h R hK hR hh hblock).2)
    (fun R hR ↦
      toReal_eLpNorm_oneStepSourceCellShellOscillationEnvelope_four_le
        M n h R hsource hK hR hh)
    hAsq
  simpa only [s, W, E, A, oneStepPaperNeumannSourceCellJensenError] using hraw

/-- Dimension-only `delta^17` bound for the normalized paper-sign Jensen
price, obtained by inserting the uniform source-cell energy budget. -/
theorem exists_normalized_sum_integral_oneStepPaperNeumannSourceCellJensenError_le_delta_seventeen
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h K : ℕ)
        (q : Vec d)
        (_hsource : 16 * ⌈|Real.log M.delta / Real.log 3|⌉₊ ≤ n)
        (_hK : oneStepLocalizationScale n M.delta ≤ K)
        (hh : 0 < h) (_hq : vecNormSq q = 1)
        (_hblock : (h : ℝ) ≤ M.delta⁻¹),
        ((((oneStepSourceCells d K n M.delta).card : ℝ)⁻¹) *
          ∑ R ∈ oneStepSourceCells d K n M.delta,
            ∫ omega, oneStepPaperNeumannSourceCellJensenError
              (K := K) M n h q R omega hh ∂M.P.toMeasure) ≤
          C * M.delta ^ 17 := by
  obtain ⟨a, ha0, hbudget⟩ := exists_oneStepPaperNeumannSourceCellEnergy_two_budget d
  let B : ℝ := 2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
    oneStepDerivativeGaugeConst * a
  let C : ℝ := |B| + 1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro M n h K q hsource hK hh hq hblock
  obtain ⟨hA, hAsq⟩ := hbudget M n h K q hh hq hblock
  have hraw := normalized_sum_integral_oneStepPaperNeumannSourceCellJensenError_le
    M n h q hsource hK hh hblock ha0 hA hAsq
  calc
    _ ≤ 2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
        (oneStepDerivativeGaugeConst * M.delta ^ 17) * a := hraw
    _ ≤ C * M.delta ^ 17 := by
      have hdelta : 0 ≤ M.delta ^ 17 :=
        pow_nonneg M.shellPrefix.delta_pos.le 17
      have hB0 : 0 ≤ B := by
        dsimp only [B]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num)
            (add_nonneg
              (oneStepSourceCellWeightFourthRootConst_pos M).le zero_le_one))
            oneStepDerivativeGaugeConst_pos.le) ha0
      have hBC : B ≤ C := by
        dsimp only [C]
        rw [abs_of_nonneg hB0]
        linarith
      have heq : 2 * (oneStepSourceCellWeightFourthRootConst d + 1) *
          (oneStepDerivativeGaugeConst * M.delta ^ 17) * a =
          B * M.delta ^ 17 := by dsimp only [B]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hBC hdelta

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
