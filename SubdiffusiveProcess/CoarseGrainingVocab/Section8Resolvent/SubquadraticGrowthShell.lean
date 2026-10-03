module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GrowingBallDerivative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GeometricSqrt

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization Homogenization.IndependentSums
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

noncomputable section

variable {d : ℕ}



theorem abs_unscalePotential_apply_le_translatedShellG2
    (k : ℕ) (omega : PotentialSample d) (p : Fin d → ℤ) {w : Vec d}
    (hw : w ∈ translateSet (shellCoverCenter p)
      (openCubeSet (originCube d 0))) :
    |unscalePotential k (omega k) w| ≤
      translatedShellG2 k (shellCoverCenter p) omega := by
  rw [mem_translateSet_iff_sub_mem] at hw
  have h := PotentialField.abs_apply_le_g2Observable
    (PotentialField.translate (shellCoverCenter p)
      (unscalePotential k (omega k))) hw
  have hcancel : w - shellCoverCenter p + shellCoverCenter p = w := by abel
  simpa only [PotentialField.translate_apply, hcancel] using! h



theorem abs_potentialShell_apply_le_of_coverGauge
    (omega : PotentialSample d) {C : ℝ}
    (hC : ∀ n k : ℕ, ∀ p ∈ shellCoverShifts d (coverExp n k),
      translatedShellG2 k (shellCoverCenter p) omega ≤
        C * Real.sqrt ((n : ℝ) + (k : ℝ) + 1))
    (n k : ℕ) {x : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n)) :
    |omega k x| ≤ C * Real.sqrt ((n : ℝ) + (k : ℝ) + 1) := by
  let w : Vec d := (((3 : ℝ) ^ k)⁻¹) • x
  have hwBall : w ∈ Metric.closedBall (0 : Vec d)
      ((((3 : ℝ) ^ k)⁻¹) * growingBallRadius n) :=
    smul_mem_scaledBall n k hx
  have hwCube : w ∈ openCubeSet (originCube d (coverExp n k)) :=
    mem_originCube_of_mem_scaledBall n k hwBall
  obtain ⟨p, hp, hw⟩ := exists_shellCoverShift_mem hwCube
  have hpoint := abs_unscalePotential_apply_le_translatedShellG2 k omega p hw
  have hvalue : unscalePotential k (omega k) w = omega k x := by
    simp only [w, unscalePotential, PotentialField.spatialScale_apply, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ k ≠ 0), one_smul]
  rw [hvalue] at hpoint
  exact hpoint.trans (hC n k p hp)



theorem ae_exists_forall_growingBall_shell_abs_bound
    (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n k : ℕ, ∀ x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
        |omega k x| ≤ C * Real.sqrt ((n : ℝ) + (k : ℝ) + 1) := by
  refine (ae_exists_forall_translatedShellG2_le M).mono ?_
  rintro omega ⟨C, hC0, hC⟩
  exact ⟨C, hC0, fun n k x hx ↦
    abs_potentialShell_apply_le_of_coverGauge omega hC n k hx⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
