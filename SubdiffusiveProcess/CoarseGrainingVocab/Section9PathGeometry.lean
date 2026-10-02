import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.Lattice
import MarkovProcess.Path.ExitTime
set_option autoImplicit false
open Homogenization MeasureTheory MarkovProcess Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry

def gridCube (d : ℕ) (r : ℝ) (k : Fin d → ℤ) : Cube d :=
  ((fun i => (r / 8) * (k i : ℝ)), r)

def gridShift (d : ℕ) (r : ℝ) (a : Fin d → Fin 8) : Vec d :=
  fun i => (r / 8) * ((a i : ℕ) : ℝ)

def closedQuarter {d : ℕ} (U : Cube d) : Set (Vec d) := closure (middleQuarter U)

def hitAfter {d : ℕ} (K : Set (Vec d)) (a : ℝ≥0∞) (p : ContinuousPath (Vec d)) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | ∃ t : NNReal, (t : ℝ≥0∞) = s ∧ a ≤ s ∧ p t ∈ K}

def exitAfter {d : ℕ} (U : Set (Vec d)) (a : ℝ≥0∞) (p : ContinuousPath (Vec d)) : ℝ≥0∞ :=
  hitAfter Uᶜ a p

def selectedIndex {d : ℕ} (order : LinearOrder ℕ) (U : ℕ → Cube d) (active : Set ℕ) (T : ℝ≥0∞) (p : ContinuousPath (Vec d)) : WithTop ℕ :=
  sInf {j : WithTop ℕ | ∃ i : ℕ, j = (i : WithTop ℕ) ∧ i ∈ active ∧ T < ⊤ ∧ p T.toNNReal ∈ closedQuarter (U i) ∧ ∀ k : ℕ, k ∈ active → p T.toNNReal ∈ closedQuarter (U k) → order.le i k}

def greedyStep {d : ℕ} (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ)
    (p : ContinuousPath (Vec d)) (s : Set ℕ × ℝ≥0∞ × ℝ≥0∞ × WithTop ℕ) :
    Set ℕ × ℝ≥0∞ × ℝ≥0∞ × WithTop ℕ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact {j | j ∈ s.1 ∧ ∀ i : ℕ, selectedIndex order U s.1
        (hitAfter (⋃ i ∈ s.1, closedQuarter (U i)) s.2.2.1 p) p = (i : WithTop ℕ) →
        Disjoint (centeredAxisCube (U j).1 (A * (U j).2))
          (centeredAxisCube (U i).1 (A * (U i).2))}
  · exact hitAfter (⋃ i ∈ s.1, closedQuarter (U i)) s.2.2.1 p
  · exact sInf {v : ENNReal | ∃ t : NNReal, v = (t : ENNReal) ∧
      hitAfter (⋃ i ∈ s.1, closedQuarter (U i)) s.2.2.1 p ≤ v ∧
      ∃ i : ℕ, selectedIndex order U s.1
        (hitAfter (⋃ i ∈ s.1, closedQuarter (U i)) s.2.2.1 p) p = (i : WithTop ℕ) ∧
      p t ∉ cubeSet (U i)}
  · exact selectedIndex order U s.1
      (hitAfter (⋃ i ∈ s.1, closedQuarter (U i)) s.2.2.1 p) p

def greedyRun {d : ℕ} (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ)
    (F : Set ℕ) (theta : ℝ≥0∞) (p : ContinuousPath (Vec d)) :
    ℕ → Set ℕ × ℝ≥0∞ × ℝ≥0∞ × WithTop ℕ
  | 0 => (F, theta, theta, ⊤)
  | n + 1 => greedyStep order U A p (greedyRun order U A F theta p n)

def entrance {d : ℕ} (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ) (F : Set ℕ)
    (theta : ℝ≥0∞) (n : ℕ) (p : ContinuousPath (Vec d)) : ℝ≥0∞ :=
  (greedyRun order U A F theta p n).2.1

def departure {d : ℕ} (order : LinearOrder ℕ) (U : ℕ → Cube d) (A : ℝ)
    (F : Set ℕ) (theta : ℝ≥0∞) (n : ℕ) (p : ContinuousPath (Vec d)) : ℝ≥0∞ :=
  (greedyRun order U A F theta p n).2.2.1

end SubdiffusiveProcess.CoarseGrainingVocab.Section9PathGeometry
