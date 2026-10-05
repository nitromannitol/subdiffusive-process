module

public import SubdiffusiveProcess.Meyers.Defs
public import SubdiffusiveProcess.Meyers.Cover
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeightedLayerCake
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.InteriorOneLevelTail
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaParameters

@[expose] public section

/-! Interior Meyers regularity: Basic. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

/-- The Euclidean ball about the origin, represented on the project's raw Vec carrier. -/
abbrev unitBall (d : ℕ) (r : ℝ) : Set (Vec d) := Meyers.eBall 0 r

/-- Hilbert-valued representative of an H1 weak gradient. -/
def gradientField {d : ℕ} {U : Set (Vec d)} (u : H1Function U) : Vec d → HilbertVec d :=
  hilbertifyVecField u.grad

/-- The scalar weak equation with the manuscript's sign convention. -/
def ScalarEquation {d : ℕ} {U : Set (Vec d)} (a h : Vec d → ℝ)
    (u : H1Function U) : Prop :=
  ∀ phi : H10Function U,
    (∫ x in U, a x * vecDot (u.grad x) (phi.toH1Function.grad x)) =
      -∫ x in U, h x * phi.toH1Function.toFun x

/-- The vector divergence weak equation; no regularity is hidden in this predicate. -/
def VectorEquation {d : ℕ} {U : Set (Vec d)} (a : Vec d → ℝ)
    (F : Vec d → Vec d) (u : H1Function U) : Prop :=
  ∀ phi : H10Function U,
    (∫ x in U, a x * vecDot (u.grad x) (phi.toH1Function.grad x)) =
      -∫ x in U, vecDot (F x) (phi.toH1Function.grad x)

/-- Constant-coefficient equation tested against smooth compactly supported functions. -/
def SmoothEquation {d : ℕ} {U : Set (Vec d)} (H : Vec d → Vec d)
    (u : H1Function U) : Prop :=
  ∀ phi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
    tsupport phi ⊆ U →
    (∫ x in U, vecDot (u.grad x) (euclideanGradient phi x)) =
      -∫ x in U, vecDot (H x) (euclideanGradient phi x)

/-- A finite truncation of the p-moment, with the square density left untruncated. -/
def truncatedMoment {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (f : α → E) (p T : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((min ‖f x‖ T) ^ (p - 2))
    ∂CubeCalderonZygmund.sqWeightedMeasure f μ

/-- The numerical loss caused by the spatial separation in the global L2 cutoff. -/
def spatialPower (d : ℕ) (p : ℝ) : ℝ := (d : ℝ) * (p - 2) / 2

/-- The L2 gradient and Lp vector forcing appearing in the interior estimate. -/
def vectorDataSize {d : ℕ} (p : ℝ) (u : H1Function (unitBall d (3/2)))
    (F : Vec d → Vec d) : ℝ :=
  (eLpNorm (gradientField u) 2 (volume.restrict (unitBall d (3/2)))).toReal +
    (eLpNorm (hilbertifyVecField F) (ENNReal.ofReal p)
      (volume.restrict (unitBall d (3/2)))).toReal

/-- The unit-scale version of the exact frozen conclusion. -/
def UnitMeyersEstimate (d : ℕ) (p epsilon C : ℝ) : Prop :=
  ∀ a h : Vec d → ℝ,
    AEMeasurable a (volume.restrict (unitBall d 3)) →
    (∀ᵐ x ∂volume.restrict (unitBall d 3), |a x - 1| ≤ epsilon) →
    MemLp h (ENNReal.ofReal p) (volume.restrict (unitBall d 3)) →
    ∀ u : H1Function (unitBall d 3), ScalarEquation a h u →
      MemLp (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i)^2))
          (ENNReal.ofReal p) (volume.restrict (unitBall d 1)) ∧
        (eLpNorm (fun x => Real.sqrt (∑ i : Fin d, (u.grad x i)^2))
          (ENNReal.ofReal p) (volume.restrict (unitBall d 1))).toReal ≤
          C * ((eLpNorm u.toFun 2 (volume.restrict (unitBall d 2))).toReal +
            (eLpNorm h (ENNReal.ofReal p) (volume.restrict (unitBall d 2))).toReal)

theorem norm_gradientField {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (x : Vec d) :
    ‖gradientField u x‖ = Real.sqrt (∑ i : Fin d, (u.grad x i)^2) := by
  change ‖HilbertVec.ofVec (u.grad x)‖ = _
  rw [← euclideanNorm_eq_norm_ofVec]
  simp only [euclideanNorm, vecNormSq, vecDot, pow_two]

theorem gradientField_memLp_two {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    MemLp (gradientField u) 2 (volume.restrict U) := by
  exact memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2

end SubdiffusiveProcess.MeyersRegularity
