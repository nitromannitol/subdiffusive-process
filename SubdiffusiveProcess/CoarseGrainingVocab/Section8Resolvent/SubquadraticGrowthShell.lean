module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GrowingBallDerivative
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GeometricSqrt

@[expose] public section

/-!
# Almost-sure growing-ball bounds for finite-cutoff shell values

The Gaussian Borel--Cantelli cover constructed for the finite-cutoff
coefficient convergence argument also controls the value of every shell on
each dyadic growing ball.  This file records the value readout needed for the
whole-space resolvent uniqueness argument.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization Homogenization.IndependentSums
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

noncomputable section

variable {d : ℕ}

/-- A point of a translated unit cube is controlled by that cube's translated
`(g2)` gauge.  This is the value counterpart of
`norm_deriv_unscalePotential_le_translatedShellG2`.

-/
theorem abs_unscalePotential_apply_le_translatedShellG2
    (k : ℕ) (omega : PotentialSample d) (p : Fin d → ℤ) {w : Vec d}
    (hw : w ∈ translateSet (shellCoverCenter p)
      (openCubeSet (originCube d 0))) :
    |unscalePotential k (omega k) w| ≤
      translatedShellG2 k (shellCoverCenter p) omega := by
  rw [mem_translateSet_iff_sub_mem] at hw
  have h := _root_.SubdiffusiveProcess.Model.PotentialField.abs_apply_le_g2Observable
    (_root_.SubdiffusiveProcess.Model.PotentialField.translate (shellCoverCenter p)
      (unscalePotential k (omega k))) hw
  have hcancel : w - shellCoverCenter p + shellCoverCenter p = w := by abel
  simpa only [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, hcancel] using! h

/-- A translated-shell `(g2)` cover bound gives an absolute bound for the
physical shell on the corresponding dyadic growing ball.

-/
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
    simp only [w, unscalePotential, _root_.SubdiffusiveProcess.Model.PotentialField.spatialScale_apply, smul_smul]
    rw [mul_inv_cancel₀ (by positivity : (3 : ℝ) ^ k ≠ 0), one_smul]
  rw [hvalue] at hpoint
  exact hpoint.trans (hC n k p hp)

/-- Almost surely, one finite nonnegative random constant controls the absolute
value of every shell on every dyadic growing ball with the Gaussian price
`sqrt (n+k+1)`.

-/
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
