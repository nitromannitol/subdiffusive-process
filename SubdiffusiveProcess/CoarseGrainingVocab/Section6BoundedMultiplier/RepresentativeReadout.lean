module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.ConditionalCoveringAssembly

@[expose] public section

/-!
# Canonical representative readout

Almost-everywhere identification of the canonical ball-average
representative changes the ambient mean and centered normalized `L²` carrier
to the literal representative spelling in the frozen theorem.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

theorem averageOn_eq_of_ae_eq {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volume.restrict W] g) :
    averageOn W f = averageOn W g := by
  unfold averageOn volumeAverage
  rw [MeasureTheory.integral_congr_ae hfg]

theorem normalizedL2On_sub_average_eq_of_ae_eq
    {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hfg : f =ᵐ[volume.restrict W] g) :
    normalizedL2On W (fun x ↦ f x - averageOn W f) =
      normalizedL2On W (fun x ↦ g x - averageOn W g) := by
  have havg := averageOn_eq_of_ae_eq hfg
  unfold normalizedL2On volumeAverage
  apply congrArg Real.sqrt
  apply congrArg (fun t : ℝ ↦ (volume W).toReal⁻¹ * t)
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx, havg]

/-- Replace the Sobolev-carrier mean in the conditional local conclusion by
the literal mean and normalized `L²` carrier of the canonical representative.
-/
theorem boundedMultiplierCanonicalConclusions_to_frozen_shape
    {m : ℤ} {z : Vec d} {j : ℕ} {B' : Set (Vec d)}
    {h : H1Function (translatedCube d m z)} {C c : ℝ}
    (hae : euclideanBallAverageRepresentative h.toFun =ᵐ[
      volume.restrict (translatedCube d m z)] h.toFun)
    (hconcl :
      oscillationOn B' (euclideanBallAverageRepresentative h.toFun) ≤
          C * (3 : ℝ) ^ (-c * j) *
            oscillationOn {x : Vec d | ‖x - z‖ ≤
              3 * (3 : ℝ) ^ m / 8}
              (euclideanBallAverageRepresentative h.toFun) ∧
        sSup {r : ℝ | ∃ x ∈ B',
          r = |euclideanBallAverageRepresentative h.toFun x -
            averageOn (translatedCube d m z) h.toFun|} ≤
          C * normalizedL2On (translatedCube d m z)
            (fun x ↦ h.toFun x -
              averageOn (translatedCube d m z) h.toFun)) :
      oscillationOn B' (euclideanBallAverageRepresentative h.toFun) ≤
          C * (3 : ℝ) ^ (-c * j) *
            oscillationOn {x : Vec d | ‖x - z‖ ≤
              3 * (3 : ℝ) ^ m / 8}
              (euclideanBallAverageRepresentative h.toFun) ∧
        sSup {r : ℝ | ∃ x ∈ B',
          r = |euclideanBallAverageRepresentative h.toFun x -
            averageOn (translatedCube d m z)
              (euclideanBallAverageRepresentative h.toFun)|} ≤
          C * normalizedL2On (translatedCube d m z)
            (fun x ↦ euclideanBallAverageRepresentative h.toFun x -
              averageOn (translatedCube d m z)
                (euclideanBallAverageRepresentative h.toFun)) := by
  have havg := averageOn_eq_of_ae_eq hae
  have hnorm := normalizedL2On_sub_average_eq_of_ae_eq hae
  constructor
  · exact hconcl.1
  · rw [hnorm, havg]
    exact hconcl.2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
