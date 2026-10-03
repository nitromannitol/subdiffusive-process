module

public import SubdiffusiveProcess.Main.DiffusionPath
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import MarkovProcess.Path.ExitTime

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Paper

/-- `Q` is the law of a Brownian motion on `ℝ^d` started at some `x0`, with a (possibly
degenerate) covariance matrix `S`: the start is `x0` almost surely, and for every finite
increasing family of times the increments are independent centred Gaussians with covariance
`(t_{j+1} - t_j) S` (joint characteristic function).  `S = 0` is the constant-path law. -/
def lim_brownian_law {d : ℕ} (Q : Measure (DiffusionPath d)) : Prop :=
  IsProbabilityMeasure Q ∧
  ∃ (x0 : SpatialCoordinates d) (S : Matrix (Fin d) (Fin d) ℝ), S.PosSemidef ∧
    (∀ᵐ w ∂Q, w 0 = x0) ∧
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      ∀ xi : Fin n → SpatialCoordinates d,
        ∫ w, Complex.exp (Complex.I * ∑ j : Fin n, ∑ a : Fin d,
            ((xi j a * (w (t j.succ) a - w (t j.castSucc) a) : ℝ) : ℂ)) ∂Q =
          Complex.exp (-(1 / 2 : ℂ) * ∑ j : Fin n,
            ((((t j.succ : ℝ) - (t j.castSucc : ℝ)) *
              dotProduct (xi j) (S.mulVec (xi j)) : ℝ) : ℂ))

end Paper
