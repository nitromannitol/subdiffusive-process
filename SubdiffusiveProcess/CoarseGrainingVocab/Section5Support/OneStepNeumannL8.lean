module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepPaperNeumannFlux
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepParentWeightedEnergy
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.FiniteLpAboveTwo

@[expose] public section

/-!
# Exponent-eight realization of the one-step Neumann flux

The measurable Neumann solution is unchanged.  This module applies the
dependency's deterministic above-two cube Calderon--Zygmund estimate to that
solution at exponent eight.
-/

open MeasureTheory Homogenization Homogenization.Book
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

noncomputable def oneStepEightExponent : FiniteLpExponent where
  exponent := 8
  one_lt := by norm_num
  lt_top := by norm_num

@[simp] theorem oneStepEightExponent_exponent :
    oneStepEightExponent.exponent = 8 := rfl

theorem memLp_eight_oneStepMultiplier_spatial
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemLp (fun x ↦ oneStepMultiplierAt M n h x omega) 8
      (normalizedCubeMeasure Q) := by
  have hcont := (oneStepMultiplierContinuousMap M n h omega).continuous
  have hmem := SubdiffusiveProcess.CoarseGrainingVocab.memLp_normalizedCubeMeasure_of_continuous
    Q (8 : ℝ≥0∞) hcont
  convert hmem using 1
  funext x
  rw [oneStepMultiplierContinuousMap_apply M n h omega x hh]

theorem memLp_eight_oneStepShellForcing_spatial
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h) :
    MemLp (fun x ↦ oneStepMultiplierAt M n h x omega • q) 8
      (normalizedCubeMeasure Q) := by
  let L : ℝ →L[ℝ] Vec d := (ContinuousLinearMap.id ℝ ℝ).smulRight q
  simpa only [L, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply] using
    (memLp_eight_oneStepMultiplier_spatial M n h Q omega hh
      ).continuousLinearMap_comp L

theorem eLpNorm_oneStepShellForcing_eight_le_multiplier
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
    (q : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (_hh : 0 < h)
    (hq : vecNormSq q = 1) :
    eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega • q) 8
        (normalizedCubeMeasure Q) ≤
      eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 8
        (normalizedCubeMeasure Q) := by
  apply eLpNorm_mono_ae
    ((continuous_oneStepMultiplierAt_sample M n h omega).aestronglyMeasurable.smul_const q)
  filter_upwards [] with x
  calc
    ‖oneStepMultiplierAt M n h x omega • q‖ =
        |oneStepMultiplierAt M n h x omega| * ‖q‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |oneStepMultiplierAt M n h x omega| * 1 :=
      mul_le_mul_of_nonneg_left (norm_le_one_of_vecNormSq_eq_one hq)
        (abs_nonneg _)
    _ = ‖oneStepMultiplierAt M n h x omega‖ := by
      rw [mul_one, Real.norm_eq_abs]

/-- Samplewise exponent-eight CZ estimate for the literal measurable
Neumann corrector on an arbitrary triadic cube. -/
theorem exists_oneStepTriadicNeumann_gradient_eight_cz
    (d : ℕ) [NeZero d] :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (q : Vec d) (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (hh : 0 < h) (_hq : vecNormSq q = 1),
        MemLp (hilbertifyVecField
            (oneStepTriadicNeumannSolution M n h q Q omega hh
              ).toH1Function.grad)
          8 (normalizedCubeMeasure Q) ∧
        eLpNorm (hilbertifyVecField
            (oneStepTriadicNeumannSolution M n h q Q omega hh
              ).toH1Function.grad)
            8 (normalizedCubeMeasure Q) ≤
          C * eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega)
            8 (normalizedCubeMeasure Q) := by
  obtain ⟨C, hCpos, hCZ⟩ :=
    CubeCalderonZygmund.exists_cubeH1MeanZeroNeumannDivergence_cz
      d oneStepEightExponent
  let C8 : ℝ≥0∞ := ENNReal.ofReal ((d : ℝ) * C)
  refine ⟨C8, ENNReal.ofReal_lt_top, ?_⟩
  intro M n h q Q omega hh hq
  let f : Vec d → Vec d :=
    fun x ↦ oneStepMultiplierAt M n h x omega • q
  let u := oneStepTriadicNeumannSolution M n h q Q omega hh
  have hf : MemLp f 8 (normalizedCubeMeasure Q) := by
    simpa only [f] using
      memLp_eight_oneStepShellForcing_spatial M n h q Q omega hh
  have huweak : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ (1 : Mat d)) (openCubeSet Q) u
      (fun x ↦ -f x) := by
    have ha : identityCoeffField d = (fun _ : Vec d ↦ (1 : Mat d)) := by
      funext x i j
      simp [identityCoeffField, scalarMatrix, Matrix.one_apply]
    rw [← ha]
    simpa only [f, u, neg_smul] using
      oneStepTriadicNeumannSolution_isWeakSolution M n h q Q omega hh
  obtain ⟨hgrad, hbound⟩ := hCZ Q f (by
    simpa only [oneStepEightExponent_exponent] using hf) u huweak
  have hgradHilbert : MemLp (hilbertifyVecField u.toH1Function.grad) 8
      (normalizedCubeMeasure Q) := by
    simpa only [hilbertifyVecField, Function.comp_apply,
      HilbertVec.ofVecL_apply] using!
      (HilbertVec.ofVecL d).comp_memLp' hgrad
  refine ⟨by simpa only [u] using hgradHilbert, ?_⟩
  have hrawENN :
      eLpNorm u.toH1Function.grad 8 (normalizedCubeMeasure Q) ≤
        ENNReal.ofReal C * eLpNorm f 8 (normalizedCubeMeasure Q) := by
    apply (ENNReal.toReal_le_toReal hgrad.eLpNorm_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCpos.le]
    simpa only [cubeLpNorm, oneStepEightExponent_exponent] using hbound
  calc
    eLpNorm (hilbertifyVecField u.toH1Function.grad) 8
        (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal (d : ℝ) *
        eLpNorm u.toH1Function.grad 8 (normalizedCubeMeasure Q) :=
      eLpNorm_hilbertifyVecField_le_dimension_mul_of_aestronglyMeasurable u.toH1Function.grad
        (memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q
          u.toH1Function.grad_memVectorL2).aestronglyMeasurable
    _ ≤ ENNReal.ofReal (d : ℝ) *
        (ENNReal.ofReal C * eLpNorm f 8 (normalizedCubeMeasure Q)) := by
      gcongr
    _ = C8 * eLpNorm f 8 (normalizedCubeMeasure Q) := by
      dsimp only [C8]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg d)]
      ac_rfl
    _ ≤ C8 * eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega)
        8 (normalizedCubeMeasure Q) := by
      gcongr
      exact eLpNorm_oneStepShellForcing_eight_le_multiplier
        M n h q Q omega hh hq

/-- The literal paper-sign Neumann flux has a spatial `L⁸` realization on
every triadic cube. -/
theorem memLp_eight_oneStepPaperNeumannFlux_space
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (hh : 0 < h)
    (hq : vecNormSq q = 1) :
    MemLp (hilbertifyVecField
      (oneStepPaperNeumannFlux M n h q Q omega hh)) 8
      (normalizedCubeMeasure Q) := by
  have hc : MemLp (fun _ : Vec d ↦ HilbertVec.ofVec q) 8
      (normalizedCubeMeasure Q) := memLp_const _
  have hf0 := memLp_eight_oneStepShellForcing_spatial M n h q Q omega hh
  have hf : MemLp (hilbertifyVecField (fun x ↦
      oneStepMultiplierAt M n h x omega • q)) 8
      (normalizedCubeMeasure Q) := by
    simpa only [hilbertifyVecField, Function.comp_apply] using!
      (HilbertVec.ofVecL d).comp_memLp' hf0
  obtain ⟨_C, _hC, hcz⟩ := exists_oneStepTriadicNeumann_gradient_eight_cz d
  have hg := (hcz M n h q Q omega hh hq).1
  simpa only [oneStepPaperNeumannFlux, hilbertifyVecField,
    Function.comp_apply, map_add] using! (hc.add hf).add hg

/-- Fourth-power Jensen estimate for local quadratic energies on a
descendant partition. -/
theorem normalized_sum_descendant_cubeAverage_vecNormSq_pow_four_le_parent
    {d j : ℕ} (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : MemLp (hilbertifyVecField F) 8 (normalizedCubeMeasure Q)) :
    (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j,
          cubeAverage R (fun x ↦ vecNormSq (F x)) ^ (4 : ℕ) ≤
      cubeAverage Q (fun x ↦ vecNormSq (F x) ^ (4 : ℕ)) := by
  let : ENNReal.HolderTriple (8 : ℝ≥0∞) 8 4 := ⟨by
    rw [← two_mul]
    have h8 : (8 : ℝ≥0∞) = 2 * 4 := by norm_num
    rw [h8, ENNReal.mul_inv (Or.inl (by norm_num))
      (Or.inl (by norm_num))]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num)
      (by norm_num), one_mul]⟩
  let : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := ⟨by
    rw [← two_mul]
    have h4 : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
    rw [h4, ENNReal.mul_inv (Or.inl (by norm_num))
      (Or.inl (by norm_num))]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num)
      (by norm_num), one_mul]⟩
  let G : Vec d → HilbertVec d := hilbertifyVecField F
  let e : Vec d → ℝ := fun x ↦ vecNormSq (F x)
  have heq : ∀ x, e x = ‖G x‖ ^ 2 := fun x ↦
    (HilbertVec.norm_sq_ofVec (F x)).symm
  have hcell : ∀ R ∈ descendantsAtDepth Q j,
      cubeAverage R e ^ (4 : ℕ) ≤
        cubeAverage R (fun x ↦ e x ^ (4 : ℕ)) := by
    intro R hR
    have hFR : MemLp G 8 (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic hR hF
    have he4 : MemLp e 4 (normalizedCubeMeasure R) := by
      have hmul : MemLp (fun x ↦ ‖G x‖ * ‖G x‖) 4
          (normalizedCubeMeasure R) := hFR.norm.mul hFR.norm
      convert hmul using 1
      funext x
      rw [heq x]
      ring
    have he2 : MemLp e 2 (normalizedCubeMeasure R) :=
      he4.mono_exponent (by norm_num)
    let e2 : Vec d → ℝ := fun x ↦ e x ^ 2
    have he2two : MemLp e2 2 (normalizedCubeMeasure R) := by
      have hmul : MemLp (fun x ↦ e x * e x) 2
          (normalizedCubeMeasure R) := he4.mul he4
      simpa only [e2, pow_two] using hmul
    have hfirst := sq_cubeAverage_le_cubeAverage_sq_of_memLp R e he2
    have hsecond := sq_cubeAverage_le_cubeAverage_sq_of_memLp R e2 he2two
    have hpow : (fun x ↦ e2 x ^ 2) = fun x ↦ e x ^ (4 : ℕ) := by
      funext x
      dsimp only [e2]
      ring
    rw [hpow] at hsecond
    calc
      cubeAverage R e ^ (4 : ℕ) = (cubeAverage R e ^ 2) ^ 2 := by ring
      _ ≤ cubeAverage R e2 ^ 2 := by
        exact pow_le_pow_left₀ (sq_nonneg _) (by simpa only [e2] using hfirst) 2
      _ ≤ cubeAverage R (fun x ↦ e x ^ (4 : ℕ)) := by
        simpa only [e2] using hsecond
  have he4Q : MemLp e 4 (normalizedCubeMeasure Q) := by
    have hmul : MemLp (fun x ↦ ‖G x‖ * ‖G x‖) 4
        (normalizedCubeMeasure Q) := hF.norm.mul hF.norm
    convert hmul using 1
    funext x
    rw [heq x]
    ring
  let e2 : Vec d → ℝ := fun x ↦ e x ^ 2
  have he2twoQ : MemLp e2 2 (normalizedCubeMeasure Q) := by
    have hmul : MemLp (fun x ↦ e x * e x) 2
        (normalizedCubeMeasure Q) := he4Q.mul he4Q
    simpa only [e2, pow_two] using hmul
  have he4Int : Integrable (fun x ↦ e x ^ (4 : ℕ))
      (normalizedCubeMeasure Q) := by
    have hmul : MemLp (fun x ↦ e2 x * e2 x) 1
        (normalizedCubeMeasure Q) := he2twoQ.mul he2twoQ
    have hint := hmul.integrable (by norm_num)
    convert hint using 1
    funext x
    dsimp only [e2]
    ring
  have hcollapse := cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    Q j (fun x ↦ e x ^ (4 : ℕ))
      (integrableOn_of_integrable_normalizedCubeMeasure Q he4Int)
  calc
    (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j, cubeAverage R e ^ (4 : ℕ) ≤
      (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
        ∑ R ∈ descendantsAtDepth Q j,
          cubeAverage R (fun x ↦ e x ^ (4 : ℕ)) := by
      gcongr with R hR
      exact hcell R hR
    _ = cubeAverage Q (fun x ↦ e x ^ (4 : ℕ)) := hcollapse.symm
    _ = cubeAverage Q (fun x ↦ vecNormSq (F x) ^ (4 : ℕ)) := rfl

/-- Joint spatial--random eighth moment of the suffix multiplier. -/
theorem lintegral_lintegral_oneStepMultiplier_eight_le
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (n h : ℕ) (Q : TriadicCube d) (hh : 0 < h) :
    ∫⁻ omega, ∫⁻ x, ‖oneStepMultiplierAt M n h x omega‖ₑ ^ (8 : ℝ)
        ∂normalizedCubeMeasure Q ∂M.P.toMeasure ≤
      (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^ (8 : ℝ) := by
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d × Vec d → ℝ := fun z ↦
    oneStepMultiplierAt M n h z.2 z.1
  have hX : Measurable X := measurable_oneStepMultiplierAt_uncurry M n h
  have hjoint : AEMeasurable
      (Function.uncurry fun omega x ↦ ‖X (omega, x)‖ₑ ^ (8 : ℝ))
      (M.P.toMeasure.prod (normalizedCubeMeasure Q)) := by
    simpa only [Function.uncurry_apply_pair] using!
      (hX.enorm.pow_const (8 : ℝ)).aemeasurable
  have hswap := lintegral_lintegral_swap hjoint
  rw [hswap]
  have hpoint : ∀ᵐ x ∂normalizedCubeMeasure Q,
      (∫⁻ omega, ‖X (omega, x)‖ₑ ^ (8 : ℝ) ∂M.P.toMeasure) ≤
        (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
          (8 : ℝ) := by
    filter_upwards with x
    let R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega ↦ X (omega, x)
    have h8 : eLpNorm R 8 M.P.toMeasure ≤
        ENNReal.ofReal (oneStepRatioMinusOneEightBound M h) := by
      have hrepr : R = fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦
          Real.exp (cutoffShellSum (n + h) (n : ℤ) x omega -
            (h : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) - 1 := by
        funext omega
        dsimp only [R, X]
        rw [← oneStepMultiplierContinuousMap_apply M n h omega x hh]
        rfl
      rw [hrepr]
      exact eLpNorm_oneStepRatioMinusOne_eight_le M n h x hh
    have hpow := ENNReal.rpow_le_rpow h8 (by norm_num : (0 : ℝ) ≤ 8)
    have hRmeas : AEStronglyMeasurable R M.P.toMeasure := by
      simpa only [R, Function.comp_apply] using!
        (hX.comp (measurable_id.prodMk (measurable_const (a := x)))).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hRmeas] at hpow
    norm_num only [ENNReal.toReal_ofNat] at hpow
    have heighth : (1 / 8 : ℝ) = (8 : ℝ)⁻¹ := by norm_num
    rw [heighth, ENNReal.rpow_inv_rpow (by norm_num : (8 : ℝ) ≠ 0)] at hpow
    simpa only [R, X, ENNReal.rpow_natCast] using! hpow
  calc
    (∫⁻ x, ∫⁻ omega, ‖X (omega, x)‖ₑ ^ (8 : ℝ)
        ∂M.P.toMeasure ∂normalizedCubeMeasure Q) ≤
      ∫⁻ _x, (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
          (8 : ℝ) ∂normalizedCubeMeasure Q := lintegral_mono_ae hpoint
    _ = (ENNReal.ofReal (oneStepRatioMinusOneEightBound M h)) ^
        (8 : ℝ) := by
      rw [lintegral_const]
      simp [normalizedCubeMeasure_apply_univ]

/-- Uniform joint spatial--random eighth moment of the literal paper-sign
Neumann flux. -/
theorem exists_lintegral_lintegral_oneStepPaperNeumannFlux_eight_le
    (d : ℕ) [NeZero d] :
    ∃ D : ℝ≥0∞, D < ∞ ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ)
        (q : Vec d) (Q : TriadicCube d) (hh : 0 < h),
        vecNormSq q = 1 → (h : ℝ) ≤ M.delta⁻¹ →
        ∫⁻ omega, ∫⁻ x,
            ‖hilbertifyVecField
              (oneStepPaperNeumannFlux M n h q Q omega hh) x‖ₑ ^ (8 : ℝ)
              ∂normalizedCubeMeasure Q ∂M.P.toMeasure ≤ D := by
  obtain ⟨C, hCtop, hcz⟩ := exists_oneStepTriadicNeumann_gradient_eight_cz d
  let B : ℝ≥0∞ := ENNReal.ofReal oneStepRatioEightUniformConst
  let A : ℝ≥0∞ := ENNReal.ofReal (d : ℝ) + C
  let D : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (7 : ℝ) *
    (1 + A ^ (8 : ℝ) * B ^ (8 : ℝ))
  have hDtop : D < ∞ := by
    dsimp only [D, A, B]
    finiteness
  refine ⟨D, hDtop, ?_⟩
  intro M n h q Q hh hq hblock
  let X : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ≥0∞ := fun omega ↦
    eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega) 8
      (normalizedCubeMeasure Q)
  have hXint : ∫⁻ omega, X omega ^ (8 : ℝ) ∂M.P.toMeasure ≤
      B ^ (8 : ℝ) := by
    have hraw := lintegral_lintegral_oneStepMultiplier_eight_le M n h Q hh
    have heq : ∀ omega, X omega ^ (8 : ℝ) =
        ∫⁻ x, ‖oneStepMultiplierAt M n h x omega‖ₑ ^ (8 : ℝ)
          ∂normalizedCubeMeasure Q := by
      intro omega
      dsimp only [X]
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (continuous_oneStepMultiplierAt_sample M n h omega).aestronglyMeasurable]
      norm_num only [ENNReal.toReal_ofNat]
      have heighth : (1 / 8 : ℝ) = (8 : ℝ)⁻¹ := by norm_num
      rw [heighth]
      rw [ENNReal.rpow_inv_rpow (by norm_num : (8 : ℝ) ≠ 0)]
    simp_rw [heq]
    exact hraw.trans (ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal
        (oneStepRatioMinusOneEightBound_le_uniform M h hblock))
      (by norm_num))
  have hpoint : ∀ omega,
      (∫⁻ x, ‖hilbertifyVecField
          (oneStepPaperNeumannFlux M n h q Q omega hh) x‖ₑ ^ (8 : ℝ)
          ∂normalizedCubeMeasure Q) ≤
        (2 : ℝ≥0∞) ^ (7 : ℝ) *
          (1 + A ^ (8 : ℝ) * X omega ^ (8 : ℝ)) := by
    intro omega
    let c : Vec d → HilbertVec d := fun _ ↦ HilbertVec.ofVec q
    let f : Vec d → HilbertVec d := hilbertifyVecField (fun x ↦
      oneStepMultiplierAt M n h x omega • q)
    let g : Vec d → HilbertVec d := hilbertifyVecField
      (oneStepTriadicNeumannSolution M n h q Q omega hh).toH1Function.grad
    have hc : MemLp c 8 (normalizedCubeMeasure Q) := memLp_const _
    have hf0 := memLp_eight_oneStepShellForcing_spatial M n h q Q omega hh
    have hf : MemLp f 8 (normalizedCubeMeasure Q) := by
      simpa only [f, hilbertifyVecField, Function.comp_apply] using!
        (HilbertVec.ofVecL d).comp_memLp' hf0
    have hg := (hcz M n h q Q omega hh hq).1
    have hsum : eLpNorm (fun x ↦ c x + f x + g x) 8
        (normalizedCubeMeasure Q) ≤ 1 + A * X omega := by
      have hcNorm : eLpNorm c 8 (normalizedCubeMeasure Q) ≤ 1 := by
        rw [eLpNorm_const (HilbertVec.ofVec q) (by norm_num)
          (normalizedCubeMeasure_ne_zero Q)]
        have hqn : ‖HilbertVec.ofVec q‖ = 1 := by
          have hs := HilbertVec.norm_sq_ofVec q
          have hq' : vecDot q q = 1 := by
            simpa only [vecNormSq] using hq
          rw [hq'] at hs
          nlinarith [norm_nonneg (HilbertVec.ofVec q)]
        rw [← ofReal_norm, hqn]
        norm_num
      have hfNorm : eLpNorm f 8 (normalizedCubeMeasure Q) ≤
          ENNReal.ofReal (d : ℝ) * X omega := by
        calc
          eLpNorm f 8 (normalizedCubeMeasure Q) ≤
              ENNReal.ofReal (d : ℝ) *
                eLpNorm (fun x ↦ oneStepMultiplierAt M n h x omega • q)
                  8 (normalizedCubeMeasure Q) := by
            simpa only [f] using!
              eLpNorm_hilbertifyVecField_le_dimension_mul_of_aestronglyMeasurable
                (fun x ↦ oneStepMultiplierAt M n h x omega • q)
                ((continuous_oneStepMultiplierAt_sample M n h omega).smul
                  (continuous_const : Continuous fun _ : Vec d => q)).aestronglyMeasurable
          _ ≤ ENNReal.ofReal (d : ℝ) * X omega := by
            gcongr
            exact eLpNorm_oneStepShellForcing_eight_le_multiplier
              M n h q Q omega hh hq

      have hgNorm := (hcz M n h q Q omega hh hq).2
      have hadd1 := eLpNorm_add_le (f := c) (g := f)
        (μ := normalizedCubeMeasure Q) (p := (8 : ℝ≥0∞))
      have hadd2 := eLpNorm_add_le (f := c + f) (g := g)
        (μ := normalizedCubeMeasure Q) (p := (8 : ℝ≥0∞))
      calc
        eLpNorm (fun x ↦ c x + f x + g x) 8
            (normalizedCubeMeasure Q) ≤
          eLpNorm (fun x ↦ c x + f x) 8 (normalizedCubeMeasure Q) +
            eLpNorm g 8 (normalizedCubeMeasure Q) := by
          simpa only [Pi.add_apply, g] using! hadd2 (by norm_num)
        _ ≤ (eLpNorm c 8 (normalizedCubeMeasure Q) +
            eLpNorm f 8 (normalizedCubeMeasure Q)) +
              eLpNorm g 8 (normalizedCubeMeasure Q) := by
          gcongr
          simpa only [Pi.add_apply] using! hadd1 (by norm_num)
        _ ≤ 1 + ENNReal.ofReal (d : ℝ) * X omega + C * X omega := by
          gcongr
        _ = 1 + A * X omega := by dsimp only [A]; ring
    have hflux : (fun x ↦ c x + f x + g x) =
        hilbertifyVecField
          (oneStepPaperNeumannFlux M n h q Q omega hh) := by
      funext x
      dsimp only [c, f, g, oneStepPaperNeumannFlux, hilbertifyVecField,
        Function.comp_apply]
      change (HilbertVec.ofVecL d) q +
          (HilbertVec.ofVecL d) (oneStepMultiplierAt M n h x omega • q) +
          (HilbertVec.ofVecL d)
            ((oneStepTriadicNeumannSolution M n h q Q omega hh
              ).toH1Function.grad x) =
        (HilbertVec.ofVecL d)
          (q + oneStepMultiplierAt M n h x omega • q +
            (oneStepTriadicNeumannSolution M n h q Q omega hh
              ).toH1Function.grad x)
      rw [← (HilbertVec.ofVecL d).map_add,
        ← (HilbertVec.ofVecL d).map_add]
    rw [hflux] at hsum
    have hpow := ENNReal.rpow_le_rpow hsum (by norm_num : (0 : ℝ) ≤ 8)
    have hfluxMeas : AEStronglyMeasurable (fun x ↦ c x + f x + g x)
        (normalizedCubeMeasure Q) := by
      simpa only [Pi.add_apply, g] using! ((hc.add hf).add hg).aestronglyMeasurable
    rw [hflux] at hfluxMeas
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfluxMeas] at hpow
    norm_num only [ENNReal.toReal_ofNat] at hpow
    have heighth : (1 / 8 : ℝ) = (8 : ℝ)⁻¹ := by norm_num
    rw [heighth] at hpow
    rw [ENNReal.rpow_inv_rpow (by norm_num : (8 : ℝ) ≠ 0)] at hpow
    refine hpow.trans ?_
    calc
      (1 + A * X omega) ^ (8 : ℝ) ≤
          (2 : ℝ≥0∞) ^ ((8 : ℝ) - 1) *
            (1 ^ (8 : ℝ) + (A * X omega) ^ (8 : ℝ)) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow 1 (A * X omega)
          (by norm_num)
      _ = (2 : ℝ≥0∞) ^ (7 : ℝ) *
          (1 + A ^ (8 : ℝ) * X omega ^ (8 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        norm_num
  calc
    _ ≤ ∫⁻ omega, (2 : ℝ≥0∞) ^ (7 : ℝ) *
        (1 + A ^ (8 : ℝ) * X omega ^ (8 : ℝ)) ∂M.P.toMeasure :=
      lintegral_mono hpoint
    _ = (2 : ℝ≥0∞) ^ (7 : ℝ) *
        (1 + A ^ (8 : ℝ) *
          ∫⁻ omega, X omega ^ (8 : ℝ) ∂M.P.toMeasure) := by
      rw [lintegral_const_mul' _ _ (by finiteness),
        lintegral_add_left measurable_const]
      rw [lintegral_one, measure_univ]
      rw [lintegral_const_mul' _ _ (by finiteness)]
    _ ≤ D := by
      dsimp only [D]
      gcongr

/-- Local exponent-eight strengthening of the cutoff-ratio supremum moment. -/
theorem memLp_eight_cutoffRatioSup_forward
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    {n m : ℕ} (hnm : n < m) (U : Ch02.Domain d) :
    MemLp (cutoffRatioSup M m n U) 8 M.P.toMeasure := by
  obtain ⟨R, hUR⟩ := U.isBoundedDomain.isBounded.subset_closedBall 0
  obtain ⟨N, hNR⟩ := exists_nat_gt R
  have hUk : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (N : ℤ)) := by
    intro x hx
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hxR : dist x 0 ≤ R := by
      simpa only [Metric.mem_closedBall] using hUR hx
    have hxi : |x i| ≤ R := by
      have hi := dist_le_pi_dist x 0 i
      rw [Real.dist_eq] at hi
      simp only [Pi.zero_apply, sub_zero] at hi
      exact hi.trans hxR
    have hNpow : (N : ℝ) ≤ (3 : ℝ) ^ N / (3 - 1) :=
      Nat.cast_le_pow_div_sub (by norm_num) N
    have hhalf : R < (1 / 2 : ℝ) * (3 : ℝ) ^ (N : ℤ) := by
      rw [zpow_natCast]
      norm_num at hNpow ⊢
      linarith
    constructor <;> linarith [le_abs_self (x i), neg_le_of_abs_le hxi]
  obtain ⟨W, _hWm, hW0, hWeight, _hWbound, hWfwd, hWinv⟩ :=
    aman_Linfty_moments M m n (N : ℤ) hnm 8 (by norm_num)
  have hWeight' : Integrable (fun omega ↦ W omega ^ (8 : ℕ))
      M.P.toMeasure := by
    convert hWeight using 1
    funext omega
    exact (Real.rpow_natCast (W omega) 8).symm
  have hmajor : Integrable (fun omega ↦ 128 * (W omega ^ (8 : ℕ) + 1))
      M.P.toMeasure :=
    (hWeight'.add (integrable_const 1)).const_mul 128
  have hdom :=
    (cutoffRatioSup_le_commonMajorant M hnm U hUk hW0 hWfwd hWinv).1
  rw [← integrable_norm_rpow_iff
    (measurable_cutoffRatioSup M m n U).aestronglyMeasurable
    (by norm_num : (8 : ℝ≥0∞) ≠ 0) (by norm_num : (8 : ℝ≥0∞) ≠ ∞)]
  norm_num only [ENNReal.toReal_ofNat]
  apply hmajor.mono'
    ((measurable_cutoffRatioSup M m n U).norm.pow_const 8
      |>.aestronglyMeasurable)
  filter_upwards with omega
  simp only [Real.norm_eq_abs,
    abs_of_pos (cutoffRatioSup_pos M m n U omega)]
  calc
    |cutoffRatioSup M m n U omega ^ (8 : ℝ)| =
        |cutoffRatioSup M m n U omega ^ (8 : ℕ)| := by
      exact congrArg abs (Real.rpow_natCast _ 8)
    _ = cutoffRatioSup M m n U omega ^ (8 : ℕ) :=
      abs_of_nonneg (pow_nonneg (cutoffRatioSup_pos M m n U omega).le 8)
    _ ≤ (W omega + 1) ^ (8 : ℕ) :=
      pow_le_pow_left₀ (cutoffRatioSup_pos M m n U omega).le
        (hdom omega) 8
    _ ≤ 128 * (W omega ^ (8 : ℕ) + 1) := by
      have hadd := add_pow_le (hW0 omega) zero_le_one 8
      norm_num at hadd ⊢
      exact hadd

theorem memLp_eight_oneStepShellForcingL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    MemLp (oneStepShellForcingL2 M n h q Q) 8 M.P.toMeasure := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let R : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := cutoffRatioSup M (n + h) n U
  let C : ℝ :=
    ((volumeMeasureOn (openCubeSet Q)) Set.univ).toReal ^ ((2 : ℝ)⁻¹) *
      ((d : ℝ) * ‖q‖)
  have hR : MemLp R 8 M.P.toMeasure := by
    simpa only [R] using
      memLp_eight_cutoffRatioSup_forward M (Nat.lt_add_of_pos_right hh) U
  have hmajor : MemLp (fun omega ↦ C * (R omega + 1))
      8 M.P.toMeasure := by
    have hsum : MemLp (fun omega ↦ R omega + 1) 8 M.P.toMeasure := by
      simpa only [Pi.add_apply] using! hR.add (memLp_const (1 : ℝ))
    exact hsum.const_mul C
  apply hmajor.mono'
    ((measurable_oneStepShellForcingL2 M n h q Q hh).aestronglyMeasurable)
  filter_upwards with omega
  have hR0 : 0 ≤ R omega :=
    (cutoffRatioSup_pos M (n + h) n U omega).le
  have hbound : ∀ x ∈ openCubeSet Q,
      ‖oneStepMultiplierAt M n h x omega • q‖ ≤ (R omega + 1) * ‖q‖ := by
    intro x hx
    have hxU : x ∈ (U : Set (Vec d)) := by
      simpa only [U, Ch02.cubeDomain_coe] using hx
    have hratio := cutoffRatio_le_cutoffRatioSup M (n + h) n U omega hxU
    have hratio0 : 0 ≤
        _root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
          _root_.SubdiffusiveProcess.Model.aCutoff M n omega x :=
      (div_pos (_root_.SubdiffusiveProcess.Model.aCutoff_pos M (n + h) omega x)
        (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n omega x)).le
    have habs :
        |_root_.SubdiffusiveProcess.Model.aCutoff M (n + h) omega x /
            _root_.SubdiffusiveProcess.Model.aCutoff M n omega x - 1| ≤ R omega + 1 := by
      rw [abs_le]
      constructor <;> nlinarith
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right habs (norm_nonneg q)
  have hfield : MemVectorL2 (openCubeSet Q) (fun x ↦
      oneStepMultiplierAt M n h x omega • q) := by
    apply memVectorL2_openCubeSet_of_continuous Q
    exact (continuous_oneStepMultiplierAt_sample M n h omega).smul
      (continuous_const : Continuous fun _ : Vec d ↦ q)
  rw [oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
    M n h q Q omega hh]
  have hnorm := norm_oneStepToHilbertVectorL2OfVecField_le_of_bound_on
    (measurableSet_openCubeSet Q) hfield
      (mul_nonneg (add_nonneg hR0 zero_le_one) (norm_nonneg q)) hbound
  convert! hnorm using 1; ring

theorem memLp_eight_oneStepTriadicNeumannGradL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    MemLp (fun omega ↦
      (oneStepTriadicNeumannSolution M n h q Q omega hh
        ).gradToHilbertVectorL2) 8 M.P.toMeasure := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet Q
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ (⊤ : ENNReal)) := ⟨by norm_num⟩
  let hEll : IsEllipticFieldOn 1 1 (openCubeSet Q) (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField (measurableSet_openCubeSet Q)
  let D := oneStepNeumannGradientOfForcingCLM
    (translatedCubeMeanZeroH1CoerciveEstimate Q)
    (openCubeSet_nonempty_internal Q) hEll
  have hforce := memLp_eight_oneStepShellForcingL2 M n h q Q hh
  have hmapped : MemLp
      (D ∘ fun omega ↦ -oneStepShellForcingL2 M n h q Q omega)
      8 M.P.toMeasure := D.comp_memLp' hforce.neg
  apply MemLp.ae_eq (Filter.Eventually.of_forall fun omega ↦ ?_) hmapped
  let G := oneStepShellForcingH1 M n h omega q Q hh
  let hG : MemVectorL2 (openCubeSet Q) G.toField :=
    G.memVectorL2_toField_openCubeSet
  have huG : IsMeanZeroNeumannRhsWeakSolution (identityCoeffField d)
      (openCubeSet Q) (oneStepTriadicNeumannSolution M n h q Q omega hh)
      (-G.toField) := by
    simpa only [G, oneStepShellForcingH1, oneStepShellForcingCoord,
      Pi.neg_apply, neg_smul] using!
      oneStepTriadicNeumannSolution_isWeakSolution M n h q Q omega hh
  calc
    D (-oneStepShellForcingL2 M n h q Q omega) =
        D (toHilbertVectorL2OfVecField hG.neg) := by
      apply congrArg D
      rw [toHilbertVectorL2OfVecField_neg_oneStep hG]
      congr 1
      exact oneStepShellForcingL2_eq_toHilbertVectorL2OfVecField
        M n h q Q omega hh
    _ = (oneStepTriadicNeumannSolution M n h q Q omega hh
        ).gradToHilbertVectorL2 := by
      symm
      exact gradToHilbertVectorL2_eq_oneStepNeumannGradientOfForcingClass
        hG.neg (translatedCubeMeanZeroH1CoerciveEstimate Q)
        (openCubeSet_nonempty_internal Q) hEll
        huG

/-- Random exponent-eight moment of the literal paper-sign Neumann flux in
the Hilbert `L²` carrier. -/
theorem memLp_eight_oneStepPaperNeumannFluxL2
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (q : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) (_hq : vecNormSq q = 1) :
    MemLp (oneStepPaperNeumannFluxL2 M n h q Q · hh)
      8 M.P.toMeasure := by
  have hconst : MemLp (fun _ : _root_.SubdiffusiveProcess.Model.PotentialSample d ↦ oneStepConstantVectorL2 Q q)
      8 M.P.toMeasure := memLp_const _
  have hforcing := memLp_eight_oneStepShellForcingL2 M n h q Q hh
  have hgrad := memLp_eight_oneStepTriadicNeumannGradL2 M n h q Q hh
  simpa only [oneStepPaperNeumannFluxL2, Pi.add_apply] using!
    (hconst.add hforcing).add hgrad

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
