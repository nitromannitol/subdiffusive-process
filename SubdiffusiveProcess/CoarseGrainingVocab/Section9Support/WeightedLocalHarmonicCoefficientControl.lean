import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import Homogenization.Sobolev.Foundations.EuclideanL2CZ

/-!
# Scaled coefficient control for the harmonic-family audit

This is the derivative control of the manuscript's below-scale-one lemma,
applied to each member of a family with one dominating constant. Its use on
arbitrarily large cubes is a stronger deterministic specialization, not an
identification with the manuscript's multiscale good-cube event. See C-1.
-/

set_option autoImplicit false
open Homogenization Set
open SubdiffusiveProcess.CoarseGrainingVocab (HolderSeminormBoundOn)
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic

/-- Pointwise, scaled control of the logarithm on the double cube. -/
def LogCoefficientControlOn {d : ℕ} (a : Vec d → ℝ) (H : ℝ) (B : Cube d) : Prop :=
  (∀ x ∈ centeredAxisCube B.1 (2 * B.2), 0 < a x) ∧
    ∃ G K : ℝ, 0 ≤ G ∧ 0 ≤ K ∧
      (∀ x ∈ centeredAxisCube B.1 (2 * B.2),
        DifferentiableAt ℝ (fun w => Real.log (a w)) x) ∧
      (∀ x ∈ centeredAxisCube B.1 (2 * B.2),
        Homogenization.euclideanNorm (Homogenization.euclideanGradient (fun w => Real.log (a w)) x) ≤ G) ∧
      HolderSeminormBoundOn (centeredAxisCube B.1 (2 * B.2)) 1 K
        (Homogenization.euclideanGradient (fun w => Real.log (a w))) ∧
      1 + B.2 ^ 2 * G ^ 2 + B.2 ^ 2 * K ≤ H

/-- One scale-independent bound for every cube of a family. -/
def FamilyLogCoefficientControl {d : ℕ} (a : Vec d → ℝ) (H : ℝ)
    (Qfam : Set (Cube d)) : Prop :=
  ∀ B ∈ Qfam, LogCoefficientControlOn a H B



def CoefficientContrastOn {d : ℕ} (a : Vec d → ℝ) (kappa : ℝ) (B : Cube d) : Prop :=
  (∀ x ∈ cubeSet B, 0 < a x) ∧
    ∀ x ∈ cubeSet B, ∀ y ∈ cubeSet B, a x ≤ kappa * a y

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
