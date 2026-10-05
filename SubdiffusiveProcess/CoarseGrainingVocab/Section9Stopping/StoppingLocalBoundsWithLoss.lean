module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.StoppingAnchorVocabulary

@[expose] public section

/-!
# Separate spatial losses in local stopping estimates

The source tests at  give a
spatial-exponent-dependent loss `CA`. The geometric enlargement, Holder
regularity constant and relative-scale exponential retain the separate `C`.
This new predicate does not change the vocabulary of any anchor.
-/

set_option autoImplicit false
open Homogenization _root_.SubdiffusiveProcess.Model MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping

/-- The five local readouts, with spatial loss `CA` separate from `C`. -/
structure StoppingLocalBoundsWithLoss {d : ℕ} (M : GMCModel d) (omega : AnchoredC11Sample d)
    (clock : ℝ → ℝ) (grid : Finset (Vec d)) (p0 A CA C : ℝ) (m : ℕ) (x : Vec d) (K : ℝ) :
    Prop where
  local_scale : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ n →
      LocalScaleQuantitiesLE M omega.val clock n y (K ^ CA)
  minimal_scale : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ n →
      ∃ Lval : ℕ, IsHolderMinimalScaleAt M C n y omega.val Lval ∧
        (Lval : ℝ≥0∞) +
            oscillation (centeredAxisCube y ((3 : ℝ) ^ n)) (stoppingLogRatio M omega n) ≤
          ENNReal.ofReal (CA * Real.log K)
  scale_zero : ∀ y : Vec d, IsGridCube grid y 1 →
    euclideanNorm (y - x) ≤ C * ((m : ℝ) + 2) ^ A * K ^ A →
      StoppingDerivativeBoundAt M omega C y (CA * Real.log K)
  scale_profile : ∀ i j : ℕ, i ≤ j → (j : ℝ) ≤ (m : ℝ) + A * Real.log K →
    K ^ (-CA) * Real.exp (-(C * ((j : ℝ) - (i : ℝ)))) * stoppingProfileAt M omega i x ≤
        stoppingProfileAt M omega j x ∧
      stoppingProfileAt M omega j x ≤
        K ^ CA * Real.exp (C * ((j : ℝ) - (i : ℝ))) * stoppingProfileAt M omega i x
  exit_upper_inputs : ∀ n : ℕ, (n : ℝ) ≤ (m : ℝ) + A * Real.log K → ∀ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) →
    euclideanNorm (y - x) ≤ ((m : ℝ) + 2) ^ A * K ^ A * (3 : ℝ) ^ n →
      SobolevAssumption (aAnchored M omega) (aAnchored M omega)
          (centeredAxisCube y ((3 : ℝ) ^ n)) p0 (K ^ CA) (clock ((3 : ℝ) ^ n)) ∧
        PoincareAssumption (aAnchored M omega) (aAnchored M omega)
          (centeredAxisCube y ((3 : ℝ) ^ n)) (K ^ CA) (clock ((3 : ℝ) ^ n))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
