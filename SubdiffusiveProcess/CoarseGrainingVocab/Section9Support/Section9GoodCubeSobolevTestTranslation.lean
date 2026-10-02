import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevTranslation
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevNormalization
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeExitTransfer
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceGeometry
/-! Weighted masses and the exact frozen Sobolev display transport with the actual coefficient under every spatial translation. -/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem goodCube_weightedMeasure_translateSet
    {d : ℕ} (z : Vec d) (U : Set (Vec d)) (hU : MeasurableSet U) (a : Vec d → ℝ) :
    weightedMeasure a (translateSet z U) = weightedMeasure (fun x => a (x + z)) U
:= by
  have hT : MeasurableSet (translateSet z U) := by
    rw [← preimage_subRight_eq_translateSet]
    exact hU.preimage (measurable_id.sub measurable_const)
  unfold weightedMeasure
  rw [withDensity_apply _ hT, withDensity_apply _ hU]
  exact ((measurePreserving_addRight_restrict_translateSet z U).lintegral_comp_emb
    (Homeomorph.addRight z).measurableEmbedding (fun x => ENNReal.ofReal (a x))).symm

/-- Literal addition of a cube centre is exact set translation. -/
theorem goodCube_cubeSet_add_eq_translateSet {d : ℕ} (Q : Cube d) (z : Vec d) :
    cubeSet (Q.1 + z, Q.2) = translateSet z (cubeSet Q) := by
  rw [← image_addRight_eq_translateSet]
  simpa only [one_smul, one_mul, add_comm] using
    goodCube_affine_cube_image z Q.1 Q.2 (s := 1) zero_lt_one

theorem goodCube_sobolevDisplay_translate
    {d : ℕ} (z : Vec d) (Q : Cube d) (a : Vec d → ℝ) (ha : Measurable a)
    (p A : ℝ) (hp : 0 < p) (clock : ℝ → ℝ)
    (h : GoodCubeSobolevDisplay (fun x => a (x + z)) p A clock Q) :
    GoodCubeSobolevDisplay a p A clock (Q.1 + z, Q.2)
:= by
  have hQ : MeasurableSet (cubeSet Q) := measurableSet_cubeSet Q
  have hset := goodCube_cubeSet_add_eq_translateSet Q z
  have hT : MeasurableSet (translateSet z (cubeSet Q)) := by
    rw [← hset]
    exact measurableSet_cubeSet _
  have ha0 : Measurable (fun x => a (x + z)) := ha.comp (measurable_id.add measurable_const)
  change ∀ f : H10Function (cubeSet (Q.1 + z, Q.2)),
    lpSq a (cubeSet (Q.1 + z, Q.2)) p f.toH1Function.toFun ≤
      ENNReal.ofReal A * weightedMeasure a (cubeSet (Q.1 + z, Q.2)) ^ (-(1 - 2 / p)) *
        ENNReal.ofReal (clock Q.2 * energy a (cubeSet (Q.1 + z, Q.2)) f.toH1Function)
  rw [hset]
  intro f
  have h0 := h (H10Function.untranslate z f)
  simp only [H10Function.untranslate_toH1Function] at h0
  rw [goodCube_lpSq_eq_weighted_power hQ ha0 _ hp,
    goodCube_weighted_lintegral_untranslate z (cubeSet Q) a p f.toH1Function,
    ← goodCube_weightedMeasure_translateSet z (cubeSet Q) hQ a] at h0
  have henergy : energy (fun x => a (x + z)) (cubeSet Q)
      (H1Function.untranslate z f.toH1Function) =
      energy a (translateSet z (cubeSet Q)) f.toH1Function :=
    setIntegral_comp_addRight_translateSet z (cubeSet Q)
      (fun x => a x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
  rw [henergy] at h0
  rw [goodCube_lpSq_eq_weighted_power hT ha _ hp]
  exact h0

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
