/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Probability.IdentDistrib

import SubdiffusiveProcess.Section9.CutoffLogTail
import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.CubeMoments

/-! # Logarithmic tails for arbitrarily translated cutoff cubes -/

namespace SubdiffusiveProcess.Section9

open MeasureTheory Homogenization
open SubdiffusiveProcess.Frozen.Assumptions SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

private theorem ogammaLE_of_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {A : ℝ} {X Y : Ω → ℝ}
    (hXY : ProbabilityTheory.IdentDistrib X Y μ μ) (hY : SubdiffusiveProcess.OGammaLE μ 1 A Y) :
    SubdiffusiveProcess.OGammaLE μ 1 A X := by
  let F : ℝ → ℝ := fun r ↦ Real.exp (A⁻¹ * max r 0)
  have hFm : Measurable F := by
    exact Real.measurable_exp.comp
      (measurable_const.mul (measurable_id.max measurable_const))
  have hF := hXY.comp hFm
  simp only [SubdiffusiveProcess.OGammaLE, Real.rpow_one] at hY ⊢
  dsimp only [F, Function.comp_apply] at hF
  exact ⟨hF.integrable_iff.mpr hY.1, hF.integral_eq.trans_le hY.2⟩

/-- The literal normalized cutoff mass on an arbitrary axis cube. -/
noncomputable def cutoffTranslatedAxisCubeAverage {d : ℕ} (M : GMCModel d)
    (m : ℕ) (z : Homogenization.Vec d) (omega : PotentialSample d) : ℝ :=
  (∫⁻ y in axisCube z ((3 : ℝ) ^ m), ENNReal.ofReal (aCutoff M m omega y) ∂volume).toReal /
    (volume (axisCube (0 : Homogenization.Vec d) ((3 : ℝ) ^ m))).toReal

private theorem axisCube_eq_image_add_axisCubeCenter_originCube {d : ℕ}
    (z : Homogenization.Vec d) (m : ℕ) :
    axisCube z ((3 : ℝ) ^ m) =
      (fun x ↦ x + fun i ↦ z i + (3 : ℝ) ^ m / 2) ''
        openCubeSet (originCube d (m : ℤ)) := by
  ext y
  simp only [axisCube, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioo,
    Set.mem_image, mem_openCubeSet_originCube_iff, zpow_natCast]
  constructor
  · intro hy
    refine ⟨y - (fun i ↦ z i + (3 : ℝ) ^ m / 2), ?_, ?_⟩
    · intro i
      have hi := hy i
      simp only [Pi.sub_apply]
      constructor <;> linarith
    · ext i
      simp
  · rintro ⟨x, hx, rfl⟩ i
    have hi := hx i
    simp only [Pi.add_apply]
    constructor <;> linarith

private theorem cutoffOriginCubeAverage_eq_lintegral_div_volume {d : ℕ}
    (M : GMCModel d) (m : ℕ) (omega : PotentialSample d) :
    cutoffOriginCubeAverage M m omega =
      (∫⁻ y in openCubeSet (originCube d (m : ℤ)),
        ENNReal.ofReal (aCutoff M m omega y) ∂volume).toReal /
        (volume (axisCube (0 : Homogenization.Vec d) ((3 : ℝ) ^ m))).toReal := by
  unfold cutoffOriginCubeAverage
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage]
  rw [setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun y ↦ (aCutoff_pos M m omega y).le)
    (continuous_aCutoff M m omega).measurable.aestronglyMeasurable]
  rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.volume_axisCube_toReal _
    (pow_nonneg (by norm_num) m)]
  simp only [cubeVolume, cubeScaleFactor_originCube, zpow_natCast]
  rw [div_eq_mul_inv]
  ring

theorem cutoffTranslatedAxisCubeAverage_eq_origin_translate {d : ℕ}
    (M : GMCModel d) (m : ℕ) (z : Homogenization.Vec d) (omega : PotentialSample d) :
    cutoffTranslatedAxisCubeAverage M m z omega =
      cutoffOriginCubeAverage M m
        (translatePotentialSequence (fun i ↦ z i + (3 : ℝ) ^ m / 2) omega) := by
  let c : Homogenization.Vec d := fun i ↦ z i + (3 : ℝ) ^ m / 2
  rw [cutoffOriginCubeAverage_eq_lintegral_div_volume]
  unfold cutoffTranslatedAxisCubeAverage
  congr 1
  apply congrArg ENNReal.toReal
  have hpres : MeasurePreserving (fun x : Homogenization.Vec d ↦ x + c) volume volume :=
    measurePreserving_add_right volume c
  calc
    ∫⁻ y in axisCube z ((3 : ℝ) ^ m), ENNReal.ofReal (aCutoff M m omega y) ∂volume =
        ∫⁻ y in (fun x : Homogenization.Vec d ↦ x + c) ''
          openCubeSet (originCube d (m : ℤ)),
          ENNReal.ofReal (aCutoff M m omega y) ∂volume := by
      rw [show axisCube z ((3 : ℝ) ^ m) =
        (fun x : Homogenization.Vec d ↦ x + c) ''
          openCubeSet (originCube d (m : ℤ)) by
        simpa only [c] using axisCube_eq_image_add_axisCubeCenter_originCube z m]
    _ = ∫⁻ y in openCubeSet (originCube d (m : ℤ)),
          ENNReal.ofReal (aCutoff M m omega (y + c)) ∂volume := by
      exact (hpres.setLIntegral_comp_emb (Homeomorph.addRight c).measurableEmbedding
        (fun y ↦ ENNReal.ofReal (aCutoff M m omega y))
        (openCubeSet (originCube d (m : ℤ)))).symm
    _ = ∫⁻ y in openCubeSet (originCube d (m : ℤ)),
          ENNReal.ofReal
            (aCutoff M m (translatePotentialSequence c omega) y) ∂volume := by
      apply setLIntegral_congr_fun (measurableSet_openCubeSet _)
      intro y hy
      change ENNReal.ofReal (aCutoff M m omega (y + c)) =
        ENNReal.ofReal (aCutoff M m (translatePotentialSequence c omega) y)
      rw [aCutoff_translatePotentialSequence]

/-- The actual normalized cutoff masses on all real translates obey the same
two-sided logarithmic Gamma-one estimate as the centered cube. -/
theorem exists_cutoffTranslatedAxisCube_logAbs_ogamma (d : ℕ) :
    ∃ C δzero : ℝ, 0 < C ∧ 0 < δzero ∧
      ∀ M : GMCModel d, M.delta ≤ δzero → ∀ (m : ℕ) (z : Homogenization.Vec d),
        SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
          (C * M.delta ^ 2 * |Real.log M.delta| ^ 2)
          (fun omega ↦
            |Real.log
              ((∫⁻ y in axisCube z ((3 : ℝ) ^ m),
                  ENNReal.ofReal (aCutoff M m omega y) ∂volume).toReal /
                (volume (axisCube (0 : Homogenization.Vec d)
                  ((3 : ℝ) ^ m))).toReal)| - Real.log 2) := by
  obtain ⟨C, δzero, hC, hδzero, htail⟩ :=
    exists_cutoffOriginCube_logAbs_ogamma d
  refine ⟨C, δzero, hC, hδzero, ?_⟩
  intro M hM m z
  let c : Homogenization.Vec d := fun i ↦ z i + (3 : ℝ) ^ m / 2
  let X : PotentialSample d → ℝ := fun omega ↦
    |Real.log (cutoffTranslatedAxisCubeAverage M m z omega)| - Real.log 2
  let Y : PotentialSample d → ℝ := fun omega ↦
    |Real.log (cutoffOriginCubeAverage M m omega)| - Real.log 2
  let T := translatePotentialSequence (d := d) c
  have hpoint : X = Y ∘ T := by
    funext omega
    dsimp only [X, Y, T, Function.comp_apply, c]
    rw [cutoffTranslatedAxisCubeAverage_eq_origin_translate]
  have hYm : Measurable Y :=
    (measurable_cutoffOriginCubeAverage M m).log.norm.sub measurable_const
  have hXm : Measurable X := by
    rw [hpoint]
    exact hYm.comp (measurable_translatePotentialSequence c)
  have hident : ProbabilityTheory.IdentDistrib X Y M.P.toMeasure M.P.toMeasure := by
    refine ⟨hXm.aemeasurable, hYm.aemeasurable, ?_⟩
    rw [hpoint]
    calc
      Measure.map (Y ∘ T) M.P.toMeasure =
          Measure.map Y (Measure.map T M.P.toMeasure) := by
        exact (Measure.map_map hYm (measurable_translatePotentialSequence c)).symm
      _ = Measure.map Y M.P.toMeasure := by
        rw [show Measure.map T M.P.toMeasure = M.P.toMeasure by
          exact potentialSequenceLaw_stationary M c]
  simpa only [cutoffTranslatedAxisCubeAverage] using
    ogammaLE_of_identDistrib hident (htail M hM m)

end

end SubdiffusiveProcess.Section9
