import SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.TailCoefficient
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.EllipticitySpecialization
import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.WindowDomain
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Support

/-!
# Saturation above a finite cutoff

Above the deterministic cutoff `L`, the tail coefficient is the constant
`ahom M L`.  These average-level consequences isolate the easy branch of the
coefficient-ratio calculation in the cutoff Holder proof.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion

noncomputable section

private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

/-- The centered cube average has saturated to `ahom M L` at every scale
above `L`. -/
theorem tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (omega : Sample d) :
    tailCoefficientCubeAverage M L m omega = ahom M L := by
  unfold tailCoefficientCubeAverage
  change volumeAverage (openCubeSet (originCube d (m : ℤ)))
      (tailCoefficient M L m omega) = ahom M L
  rw [show tailCoefficient M L m omega = fun _ => ahom M L by
    funext x
    exact tailCoefficient_of_ge M hLm omega x]
  rw [volumeAverage_const]
  apply ne_of_gt
  rw [volume_openCubeSet_toReal]
  exact cubeVolume_pos _

/-- The same saturation holds for a translated cube average. -/
theorem tailAverage_translatedCube_eq_ahom_of_cutoff_le_scale {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m : ℕ} (hLm : L ≤ m)
    (omega : Sample d) (z : Vec d) :
    tailAverage M L m omega (translatedCube d (m : ℤ) z) = ahom M L := by
  unfold tailAverage
  rw [show tailCoefficient M L m omega = fun _ => ahom M L by
    funext x
    exact tailCoefficient_of_ge M hLm omega x]
  rw [volumeAverage_const]
  apply ne_of_gt
  rw [translatedCube, cube,
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.image_add_eq_translateSet,
    volume_translateSet_eq, volume_openCubeSet_toReal]
  exact cubeVolume_pos _

/-- Changing an observation scale above the cutoff does not change the
centered tail-coefficient average. -/
theorem tailCoefficientCubeAverage_eq_of_cutoff_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m n : ℕ}
    (hLm : L ≤ m) (hLn : L ≤ n) (omega : Sample d) :
    tailCoefficientCubeAverage M L m omega =
      tailCoefficientCubeAverage M L n omega := by
  rw [tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm,
    tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLn]

/-- Both directions of the average ratio are exactly one after saturation. -/
theorem tailCoefficientCubeAverage_ratio_eq_one_of_cutoff_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L m n : ℕ}
    (hLm : L ≤ m) (hLn : L ≤ n) (omega : Sample d) :
    tailCoefficientCubeAverage M L m omega /
          tailCoefficientCubeAverage M L n omega = 1 ∧
      tailCoefficientCubeAverage M L n omega /
          tailCoefficientCubeAverage M L m omega = 1 := by
  rw [tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm,
    tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLn,
    div_self (ahom_pos M L).ne']
  exact ⟨rfl, rfl⟩

/-- The translated local average and centered parent average are both the
same deterministic scalar once their scales are above the cutoff. -/
theorem tailAverage_ratio_eq_one_of_cutoff_le {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) {L q m : ℕ}
    (hLq : L ≤ q) (hLm : L ≤ m) (omega : Sample d) (z : Vec d) :
    tailAverage M L q omega (translatedCube d (q : ℤ) z) /
          tailCoefficientCubeAverage M L m omega = 1 ∧
      tailCoefficientCubeAverage M L m omega /
          tailAverage M L q omega (translatedCube d (q : ℤ) z) = 1 := by
  rw [tailAverage_translatedCube_eq_ahom_of_cutoff_le_scale M hLq,
    tailCoefficientCubeAverage_eq_ahom_of_cutoff_le_scale M hLm,
    div_self (ahom_pos M L).ne']
  exact ⟨rfl, rfl⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Cutoff
