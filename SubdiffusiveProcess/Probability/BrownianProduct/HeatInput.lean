module

public import Mathlib

@[expose] public section




set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

noncomputable section
namespace SubdiffusiveProcess.Probability.BrownianProduct

local instance pathMeasurableSpace (E : Type*) [TopologicalSpace E] :
    MeasurableSpace C(ℝ≥0, E) := borel _

/-- Standard real Brownian motion, characterized by its Gaussian marginals
and joint Gaussian laws of successive increments on continuous paths. -/
def RealBrownianLaw (ν : Kernel ℝ C(ℝ≥0, ℝ)) : Prop :=
  IsMarkovKernel ν ∧
    (∀ (t : ℝ≥0) (x : ℝ), (ν x).map (fun ω => ω t) = gaussianReal x t) ∧
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ x : ℝ,
      (ν x).map (fun ω (j : Fin n) => ω (t j.succ) - ω (t j.castSucc)) =
        Measure.pi (fun j => gaussianReal 0 (t j.succ - t j.castSucc))

/-- The full-Laplacian normalization of finite-dimensional Brownian motion.
The joint law includes every spatial coordinate and every successive time interval. -/
def LaplacianBrownianLaw (d : ℕ) (ν : Kernel (Fin d → ℝ) C(ℝ≥0, Fin d → ℝ)) : Prop :=
  IsMarkovKernel ν ∧
    (∀ (t : ℝ≥0) (x : Fin d → ℝ), (ν x).map (fun ω => ω t) =
      Measure.pi (fun i => gaussianReal (x i) (2 * t))) ∧
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ x : Fin d → ℝ,
      (ν x).map (fun ω (i : Fin d) (j : Fin n) =>
        ω (t j.succ) i - ω (t j.castSucc) i) =
          Measure.pi (fun _ : Fin d => Measure.pi (fun j : Fin n =>
            gaussianReal 0 (2 * (t j.succ - t j.castSucc))))

/-- The unit-interval sine series, with generator the full Laplacian. -/
def sineHeatSeries (t x y : ℝ) : ℝ :=
  2 * ∑' n : ℕ, Real.exp (-(Real.pi ^ 2 * t) * ((n : ℝ) + 1) ^ 2) *
    (Real.sin (Real.pi * ((n : ℝ) + 1) * x) * Real.sin (Real.pi * ((n : ℝ) + 1) * y))

/-- The candidate killed kernel for standard real Brownian motion on an interval.
The factor two in the time denominator corresponds to generator `½Δ`. -/
def intervalBrownianKernel (c L t x y : ℝ) : ℝ :=
  L⁻¹ * sineHeatSeries (t / (2 * L ^ 2))
    ((x - c) / L + 1 / 2) ((y - c) / L + 1 / 2)

/-- Symmetry of the sine series requires no convergence hypothesis. -/
theorem sineHeatSeries_symm (t x y : ℝ) : sineHeatSeries t x y = sineHeatSeries t y x := by
  unfold sineHeatSeries
  congr 2
  funext n
  rw [mul_comm (Real.sin _) (Real.sin _)]

/-- The sine series vanishes at the left Dirichlet boundary. -/
theorem sineHeatSeries_zero_left (t y : ℝ) : sineHeatSeries t 0 y = 0 := by
  simp [sineHeatSeries]

/-- The sine series vanishes at the right Dirichlet boundary. -/
theorem sineHeatSeries_one_left (t y : ℝ) : sineHeatSeries t 1 y = 0 := by
  have hs (n : ℕ) : Real.sin (Real.pi * ((n : ℝ) + 1)) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using Real.sin_nat_mul_pi (n + 1)
  simp [sineHeatSeries, hs]



def IntervalDirichletHeatInput : Prop :=
  ∀ ν : Kernel ℝ C(ℝ≥0, ℝ), RealBrownianLaw ν →
    ∀ c L : ℝ, 0 < L → ∀ t : ℝ≥0, 0 < t →
      let I := Ioo (c - L / 2) (c - L / 2 + L)
      ∀ x ∈ I,
        (∀ y ∈ I, 0 ≤ intervalBrownianKernel c L t x y) ∧
        ((ν x).restrict {ω | ∀ r : ℝ≥0, r ≤ t → ω r ∈ I}).map (fun ω => ω t) =
          (volume.restrict I).withDensity (fun y => ENNReal.ofReal (intervalBrownianKernel c L t x y))









end SubdiffusiveProcess.Probability.BrownianProduct
