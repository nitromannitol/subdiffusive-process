import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonicCoefficientControl



set_option autoImplicit false
open Homogenization hiding cubeSet
open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
theorem logCoefficientControlOn_const {d : ℕ} (k : ℝ) (hk : 0 < k) (B : Cube d) :
    LogCoefficientControlOn (fun _ => k) 1 B := by
  have hg : ∀ x : Vec d,
      Homogenization.euclideanGradient (fun _ : Vec d => Real.log k) x = 0 := by
    intro x
    funext i
    simp [Homogenization.euclideanGradient, Homogenization.euclideanCoordDeriv]
  refine ⟨fun _ _ => hk, 0, 0, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact differentiableAt_const _
  · intro x _
    simp [hg]
  · intro x _ y _
    simp [hg]
  · simp

theorem familyLogCoefficientControl_const {d : ℕ} (k : ℝ) (hk : 0 < k)
    (Qfam : Set (Cube d)) :
    FamilyLogCoefficientControl (fun _ => k) 1 Qfam := by
  intro B _
  exact logCoefficientControlOn_const k hk B

theorem coefficientContrastOn_const {d : ℕ} (k : ℝ) (hk : 0 < k) (B : Cube d) :
    CoefficientContrastOn (fun _ => k) 1 B := by
  refine ⟨fun _ _ => hk, ?_⟩
  intro x _ y _
  simp only [one_mul]
  exact le_refl k

theorem familyLogCoefficientControl_mono {d : ℕ} {a : Vec d → ℝ} {H : ℝ}
    {Qfam Rfam : Set (Cube d)} (h : FamilyLogCoefficientControl a H Qfam)
    (hsub : Rfam ⊆ Qfam) : FamilyLogCoefficientControl a H Rfam := by
  intro B hB
  exact h B (hsub hB)

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
