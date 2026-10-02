import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import Homogenization.Geometry.OverlapCenters

/-! The exact centre sets and extended norms in the frozen comparison. -/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.BesovComparison

def normalizedLp {d : ℕ} (Q : Set (Vec d)) (p : ℝ≥0∞) (f : Vec d → ℝ) : ℝ≥0∞ :=
  eLpNorm f p ((volume Q)⁻¹ • volume.restrict Q)

def averageLp {ι : Type*} (S : Set ι) (r : ℝ≥0∞) (t : ι → ℝ≥0∞) : ℝ≥0∞ :=
  if r = ∞ then ⨆ z ∈ S, t z
  else ((S.ncard : ℝ≥0∞)⁻¹ * ∑ᶠ z ∈ S, t z ^ r.toReal) ^ (1 / r.toReal)

def aggregate (s : ℝ) (m : ℤ) (q : ℝ≥0∞) (a : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  if q = ∞ then ⨆ n ∈ {n : ℤ | n ≤ m}, a n
  else (ENNReal.ofReal s * ∑' n : ℤ, (if n ≤ m then a n ^ q.toReal else 0)) ^ (1 / q.toReal)

def positiveCenters (d : ℕ) (m n : ℤ) : Set (Vec d) :=
  {z | (∀ a : Fin d, ∃ k : ℤ, z a = (3 : ℝ) ^ (n - 1) * k) ∧ z ∈ cube d m ∧
    translatedCube d n z ⊆ cube d m}

def besov (d : ℕ) (m : ℤ) (s : ℝ) (p q r : ℝ≥0∞) (u : Vec d → ℝ) : ℝ≥0∞ :=
  aggregate s m q (fun n =>
    ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ) * s)) *
      averageLp (positiveCenters d m n) r
        (fun z => normalizedLp (translatedCube d n z) p
          (fun x => u x - ⨍ y in translatedCube d n z, u y)))

def wsp (d : ℕ) (m : ℤ) (s p : ℝ) (u : Vec d → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal s * (volume (cube d m))⁻¹ *
    ∫⁻ x in cube d m, ∫⁻ y in cube d m,
      ENNReal.ofReal (|u x - u y| ^ p) /
        ENNReal.ofReal (Homogenization.euclideanNorm (x - y) ^ ((d : ℝ) + s * p))) ^ (1 / p)

end SubdiffusiveProcess.BesovComparison
