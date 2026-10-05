module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.AlmostSureCanonicalEstimates
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.FullResponseMoments
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.RandomFactorMonotonicity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.RescaledCoefficientEllipticity

@[expose] public section

/-!
# Combined cutoff Dirichlet estimate

This file merges the main and zero-source canonical rows under one random
factor and one full-measure event over all cutoff/observation scales.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped _root_.ENNReal

noncomputable section

/-- Complete cutoff Dirichlet conclusion when the ambient dimension lower
bound is supplied explicitly. -/
theorem exists_cutoffDirichletCombinedEstimate_of_two_le
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (vartheta q : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1)
    (hq : 1 ≤ q) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
        ∃ Z : ℕ → ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
          (∀ L N, L ≤ N →
            CoefficientMeasurable
              (fun omega ↦ rescaledCutoffCoefficient M L N omega) (Z L N)) ∧
          (∀ L N omega, L ≤ N → 1 ≤ Z L N omega) ∧
          (∀ L N, L ≤ N →
            eLpNorm (Z L N) (ENNReal.ofReal q) M.P.toMeasure ≤
              ENNReal.ofReal C) ∧
          ∀ᵐ omega ∂M.P.toMeasure, ∀ L N : ℕ, L ≤ N →
            ∀ (f : Vec d → ℝ),
              MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))) →
            ∀ h : H2Datum (originCube d 0),
              (∃ uLM : H1Function (openCubeSet (originCube d 0)),
                IsScalarDirichletSolutionOn
                  (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                  (originCube d 0) uLM h.toH1 f) ∧
              (∀ uLM uLM' : H1Function (openCubeSet (originCube d 0)),
                IsScalarDirichletSolutionOn
                    (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                    (originCube d 0) uLM h.toH1 f →
                IsScalarDirichletSolutionOn
                    (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                    (originCube d 0) uLM' h.toH1 f →
                uLM.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                    uLM'.toFun ∧
                  uLM.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                    uLM'.grad) ∧
              (∃ uHom : H1Function (openCubeSet (originCube d 0)),
                IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                  (originCube d 0) uHom h.toH1 f) ∧
              (∀ uHom uHom' : H1Function (openCubeSet (originCube d 0)),
                IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                    (originCube d 0) uHom h.toH1 f →
                IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                    (originCube d 0) uHom' h.toH1 f →
                uHom.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                    uHom'.toFun ∧
                  uHom.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                    uHom'.grad) ∧
              ∀ (uLM uHom : H1Function (openCubeSet (originCube d 0))),
                IsScalarDirichletSolutionOn
                    (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                    (originCube d 0) uLM h.toH1 f →
                IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                    (originCube d 0) uHom h.toH1 f →
                ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
                  (∀ x, gradDifference.toFun x = uLM.grad x - uHom.grad x) ∧
                  (∀ x, fluxDifference.toFun x =
                    rescaledCutoffCoefficient M L N omega x • uLM.grad x -
                      uHom.grad x) ∧
                  l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                        ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                      ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                    ENNReal.ofReal (Z L N omega * M.delta ^ vartheta) *
                      (l2Size (originCube d 0) f + h.norm) ∧
                    (f = 0 →
                    l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                          ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                        ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                      ENNReal.ofReal (Z L N omega * C * M.delta) * h.norm) := by
  obtain ⟨CcgMain, CenergyMain, hCcgMain, hCenergyMain, hmain⟩ :=
    exists_ae_cutoffDirichletCanonicalMainEstimate d hd
  obtain ⟨CcgZero, CenergyZero, hCcgZero, hCenergyZero, hzero⟩ :=
    exists_ae_cutoffDirichletCanonicalZeroSourceEstimate d hd
  let s1 := dirichletS1 vartheta
  let xi := 1 + 4 * (d : ℝ) * (s1 / 2)⁻¹
  have hs1 : 0 < s1 := (dirichlet_parameter_orders
    hvartheta.1 hvartheta.2).1
  have hs1One : s1 ≤ 1 := by
    have horders := dirichlet_parameter_orders hvartheta.1 hvartheta.2
    exact ((horders.2.1.trans horders.2.2.1).trans horders.2.2.2).le
  have hxiOne : 1 ≤ xi := by
    dsimp only [xi]
    have hterm : 0 ≤ 4 * (d : ℝ) * (s1 / 2)⁻¹ := by positivity
    linarith
  have hdim : 4 * (d : ℝ) * (s1 / 2)⁻¹ ≤ xi := by
    dsimp only [xi]
    linarith
  obtain ⟨deltaResponse, R, hdeltaResponse, hR, hresponses⟩ :=
    exists_dirichletFullResponse_paper_moment_bound
      hs1 hs1One hxiOne hdim
  let Cmain := cutoffDirichletSourceCoefficient d CcgMain CenergyMain
    vartheta hvartheta
  let Czero := cutoffDirichletSourceCoefficient d CcgZero CenergyZero
    vartheta hvartheta
  let Cfactor := max Cmain Czero
  have hCmain : 0 ≤ Cmain :=
    cutoffDirichletSourceCoefficient_nonneg d hvartheta
      hCcgMain.le hCenergyMain.le
  have hCzero : 0 ≤ Czero :=
    cutoffDirichletSourceCoefficient_nonneg d hvartheta
      hCcgZero.le hCenergyZero.le
  have hCfactor : 0 ≤ Cfactor := hCmain.trans (le_max_left _ _)
  obtain ⟨deltaFactor, B, hdeltaFactor, hB, hfactorMoment⟩ :=
    exists_cutoffDirichletRandomFactor_moment_bound d hvartheta hq hCfactor
  let G := Real.rpow 3 s1
  have hG : 0 < G := Real.rpow_pos_of_pos (by norm_num) _
  let C := max B G
  have hC : 0 < C := hB.trans_le (le_max_left _ _)
  let delta0 := min deltaResponse deltaFactor
  have hdelta0 : 0 < delta0 := lt_min hdeltaResponse hdeltaFactor
  refine ⟨delta0, C, hdelta0, ?_⟩
  intro M hM
  have hMResponse : M.delta ≤ deltaResponse :=
    hM.trans (min_le_left deltaResponse deltaFactor)
  have hMFactor : M.delta ≤ deltaFactor :=
    hM.trans (min_le_right deltaResponse deltaFactor)
  let Z : ℕ → ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ :=
    fun L N ↦ cutoffDirichletRandomFactor M L N Cfactor vartheta hvartheta
  refine ⟨Z, ?_, ?_, ?_, ?_⟩
  · intro L N hLN
    exact coefficientMeasurable_cutoffDirichletRandomFactor
      M L N Cfactor vartheta hvartheta
  · intro L N omega hLN
    exact one_le_cutoffDirichletRandomFactor M L N hCfactor
      hvartheta omega
  · intro L N hLN
    exact (hfactorMoment M hMFactor L N hLN).trans
      (ENNReal.ofReal_le_ofReal (le_max_left B G))
  · rw [ae_all_iff]
    intro L
    rw [ae_all_iff]
    intro N
    by_cases hLN : L ≤ N
    · obtain ⟨hOne, hTwo⟩ := hresponses M hMResponse L N hLN
      have hmainAE := hmain vartheta hvartheta M L N
        (show 0 < xi from zero_lt_one.trans_le hxiOne) hOne hTwo
      have hzeroAE := hzero vartheta hvartheta M L N
        (show 0 < xi from zero_lt_one.trans_le hxiOne) hOne hTwo
      filter_upwards [hmainAE, hzeroAE] with omega hmainOmega hzeroOmega
      intro _hLN f hf h
      obtain ⟨hexLM, huniqLM, hexHom, huniqHom⟩ :=
        cutoffDirichlet_wellPosed M L N omega f hf h
      refine ⟨hexLM, huniqLM, hexHom, huniqHom, ?_⟩
      intro uLM uHom huLM huHom
      let gradDifference := cutoffDirichletGradientDifference N uLM uHom
      let fluxDifference := cutoffDirichletFluxDifference M L N omega uLM uHom
      refine ⟨gradDifference, fluxDifference, ?_, ?_, ?_, ?_⟩
      · exact cutoffDirichletGradientDifference_toFun N uLM uHom
      · exact cutoffDirichletFluxDifference_toFun M L N omega uLM uHom
      · have hbase := hmainOmega f hf h uLM uHom huLM huHom
        have hmono := cutoffDirichletRandomFactor_mono_coefficient
          M L N hvartheta omega (show Cmain ≤ Cfactor from le_max_left _ _)
        have hpow : 0 ≤ Real.rpow M.delta vartheta :=
          Real.rpow_nonneg M.shellPrefix.delta_pos.le _
        have hfactor : ENNReal.ofReal
              (cutoffDirichletRandomFactor M L N Cmain vartheta hvartheta omega *
                Real.rpow M.delta vartheta) ≤
            ENNReal.ofReal (Z L N omega * Real.rpow M.delta vartheta) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right hmono hpow
        exact hbase.trans (mul_le_mul_left hfactor _)
      · intro hfzero
        subst f
        have hbase := hzeroOmega h uLM uHom huLM huHom
        have hmono := cutoffDirichletRandomFactor_mono_coefficient
          M L N hvartheta omega (show Czero ≤ Cfactor from le_max_right _ _)
        have hZ : 0 ≤ Z L N omega := zero_le_one.trans
          (one_le_cutoffDirichletRandomFactor M L N hCfactor hvartheta omega)
        have hreal :
            cutoffDirichletRandomFactor M L N Czero vartheta hvartheta omega *
                G * M.delta ≤
              Z L N omega * C * M.delta := by
          calc
            _ ≤ Z L N omega * G * M.delta := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hmono hG.le)
                M.shellPrefix.delta_pos.le
            _ ≤ Z L N omega * C * M.delta := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (le_max_right B G) hZ)
                M.shellPrefix.delta_pos.le
        have hfactor := ENNReal.ofReal_le_ofReal hreal
        exact hbase.trans (mul_le_mul_left hfactor _)
    · filter_upwards [] with omega
      intro hcontra
      exact (hLN hcontra).elim

/-- The complete cutoff Dirichlet conclusion with the unrestricted
dimension spelling.  If the model type is inhabited, its structural dimension
field supplies `2 ≤ d`; otherwise the model-universal conclusion is vacuous. -/
theorem exists_cutoffDirichletCombinedEstimate
    (d : ℕ) [NeZero d]
    (vartheta q : ℝ) (hvartheta : vartheta ∈ Set.Ioo (0 : ℝ) 1)
    (hq : 1 ≤ q) :
    ∃ delta0 C : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
        ∃ Z : ℕ → ℕ → _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ,
          (∀ L N, L ≤ N →
            CoefficientMeasurable
              (fun omega ↦ rescaledCutoffCoefficient M L N omega) (Z L N)) ∧
          (∀ L N omega, L ≤ N → 1 ≤ Z L N omega) ∧
          (∀ L N, L ≤ N →
            eLpNorm (Z L N) (ENNReal.ofReal q) M.P.toMeasure ≤
              ENNReal.ofReal C) ∧
          ∀ᵐ omega ∂M.P.toMeasure, ∀ L N : ℕ, L ≤ N →
            ∀ (f : Vec d → ℝ),
              MemLp f 2 (volume.restrict (openCubeSet (originCube d 0))) →
            ∀ h : H2Datum (originCube d 0),
              (∃ uLM : H1Function (openCubeSet (originCube d 0)),
                IsScalarDirichletSolutionOn
                  (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                  (originCube d 0) uLM h.toH1 f) ∧
              (∀ uLM uLM' : H1Function (openCubeSet (originCube d 0)),
                IsScalarDirichletSolutionOn
                    (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                    (originCube d 0) uLM h.toH1 f →
                IsScalarDirichletSolutionOn
                    (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                    (originCube d 0) uLM' h.toH1 f →
                uLM.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                    uLM'.toFun ∧
                  uLM.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                    uLM'.grad) ∧
              (∃ uHom : H1Function (openCubeSet (originCube d 0)),
                IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                  (originCube d 0) uHom h.toH1 f) ∧
              (∀ uHom uHom' : H1Function (openCubeSet (originCube d 0)),
                IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                    (originCube d 0) uHom h.toH1 f →
                IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                    (originCube d 0) uHom' h.toH1 f →
                uHom.toFun =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                    uHom'.toFun ∧
                  uHom.grad =ᵐ[volume.restrict (openCubeSet (originCube d 0))]
                    uHom'.grad) ∧
              ∀ (uLM uHom : H1Function (openCubeSet (originCube d 0))),
                IsScalarDirichletSolutionOn
                    (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
                    (originCube d 0) uLM h.toH1 f →
                IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
                    (originCube d 0) uHom h.toH1 f →
                ∃ gradDifference fluxDifference : L2VectorField (originCube d 0),
                  (∀ x, gradDifference.toFun x = uLM.grad x - uHom.grad x) ∧
                  (∀ x, fluxDifference.toFun x =
                    rescaledCutoffCoefficient M L N omega x • uLM.grad x -
                      uHom.grad x) ∧
                  l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                        ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                      ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                    ENNReal.ofReal (Z L N omega * M.delta ^ vartheta) *
                      (l2Size (originCube d 0) f + h.norm) ∧
                    (f = 0 →
                    l2Size (originCube d 0) (fun x ↦ uLM.toFun x - uHom.toFun x) +
                          ordinaryVectorHMinusOne (originCube d 0) gradDifference +
                        ordinaryVectorHMinusOne (originCube d 0) fluxDifference ≤
                      ENNReal.ofReal (Z L N omega * C * M.delta) * h.norm) := by
  classical
  by_cases hmodel : Nonempty (_root_.SubdiffusiveProcess.Model.GMCModel d)
  · obtain ⟨M⟩ := hmodel
    exact exists_cutoffDirichletCombinedEstimate_of_two_le d
      M.shellPrefix.dimension vartheta q hvartheta hq
  · refine ⟨1, 1, zero_lt_one, ?_⟩
    intro M
    exact (hmodel ⟨M⟩).elim

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
