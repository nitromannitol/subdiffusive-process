import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.StoppingAnchorVocabulary
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.SharedStoppingSchedule




set_option autoImplicit false
open Homogenization SubdiffusiveProcess.Frozen.Assumptions MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping



def stoppingCubeFailure {d : ℕ} (M : GMCModel d) (clock : ℝ → ℝ)
    (grid : Finset (Vec d)) (B C : ℝ) (m h : ℕ) (x : Vec d) (a j : ℕ) :
    Set (AnchoredC11Sample d) :=
  {omega | ∃ n : ℕ, n ≤ stoppingTestScale m h a j ∧ ∃ y : Vec d,
    IsGridCube grid y ((3 : ℝ) ^ n) ∧
    euclideanNorm (y - x) ≤ stoppingTestRadius m h a j n ∧
    (¬ LocalScaleQuantitiesLE M omega.val clock n y
        (Real.exp (B * stoppingTestHeight h a j)) ∨
      ¬ (∃ Lval : ℕ, IsHolderMinimalScaleAt M C n y omega.val Lval ∧
        (Lval : ℝ) ≤ B * stoppingTestHeight h a j) ∨
      ∃ z ∈ centeredAxisCube y ((3 : ℝ) ^ n),
        B * stoppingTestHeight h a j <
          |stoppingLogRatio M omega n z - stoppingLogRatio M omega n y|)}

/-- Failure of the comparison with the common anchor on the ambient ball. -/
def stoppingAmbientFailure {d : ℕ} (M : GMCModel d) (B C : ℝ)
    (m h : ℕ) (x : Vec d) (a j : ℕ) : Set (AnchoredC11Sample d) :=
  {omega | ∃ n : ℕ, n ≤ stoppingTestScale m h a j ∧
    ∃ z ∈ euclideanBall x (C * stoppingTestRadius m h a j n),
      B * stoppingTestHeight h a j <
        |stoppingLogRatio M omega n z - stoppingLogRatio M omega n x|}

/-- The nearby unit-cube derivative tests, also covering descendants below scale zero. -/
def stoppingDerivativeFailure {d : ℕ} (M : GMCModel d) (grid : Finset (Vec d))
    (B C : ℝ) (m h : ℕ) (x : Vec d) (a j : ℕ) : Set (AnchoredC11Sample d) :=
  {omega | ∃ y : Vec d, IsGridCube grid y 1 ∧
    euclideanNorm (y - x) ≤ C * stoppingTestRadius m h a j 0 ∧
    ¬ StoppingDerivativeBoundAt M omega C y (B * stoppingTestHeight h a j)}

/-- The two signed interval-sum tests, expressed as an absolute-value bound. -/
def stoppingIntervalFailure {d : ℕ} (B : ℝ) (m h : ℕ) (x : Vec d) (a j : ℕ) :
    Set (AnchoredC11Sample d) :=
  {omega | ∃ i k : ℕ, i < k ∧ k ≤ stoppingTestScale m h a j ∧
    (k - i : ℕ) + B * stoppingTestHeight h a j <
      |∑ l ∈ Finset.Icc (i + 1) k, omega.val l x|}

/-- The percolation thresholds at the native scales have no testing-exponent loss. -/
def stoppingNativeFailure {Ω : Type*} (crossing component : ℕ → Ω → ℕ)
    (L0 m h : ℕ) : Set Ω :=
  {omega | ∃ n : ℕ, n ≤ m ∧
    (L0 + h < crossing n omega ∨ 1 + h < component n omega)}

/-- At the additional scales the percolation threshold is `H_{a+1,j}`. -/
def stoppingExtraFailure {Ω : Type*} (crossing component : ℕ → Ω → ℕ)
    (L0 m h a j : ℕ) : Set Ω :=
  {omega | ∃ n : ℕ, m < n ∧ n ≤ stoppingTestScale m h a j ∧
    (L0 + stoppingTestHeight h a j < crossing n omega ∨
      1 + stoppingTestHeight h a j < component n omega)}

/-- The union within a single collection of tests. -/
def stoppingPairFailure {d : ℕ} (M : GMCModel d) (clock : ℝ → ℝ)
    (grid : Finset (Vec d)) (B C : ℝ)
    (crossing component : ℕ → AnchoredC11Sample d → ℕ)
    (L0 m h : ℕ) (x : Vec d) (a j : ℕ) : Set (AnchoredC11Sample d) :=
  stoppingCubeFailure M clock grid B C m h x a j ∪
    stoppingAmbientFailure M B C m h x a j ∪
    stoppingDerivativeFailure M grid B C m h x a j ∪
    stoppingIntervalFailure B m h x a j ∪
    stoppingExtraFailure crossing component L0 m h a j

/-- One level failure includes every positive testing exponent and every shell index. -/
def stoppingLevelFailure {d : ℕ} (M : GMCModel d) (clock : ℝ → ℝ)
    (grid : Finset (Vec d)) (B C : ℝ)
    (crossing component : ℕ → AnchoredC11Sample d → ℕ)
    (L0 m h : ℕ) (x : Vec d) : Set (AnchoredC11Sample d) :=
  stoppingNativeFailure crossing component L0 m h ∪
    ⋃ a : ℕ, ⋃ j : ℕ,
      stoppingPairFailure M clock grid B C crossing component L0 m h x a j

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
