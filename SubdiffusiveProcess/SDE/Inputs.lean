module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# The stochastic differential equation and three cited results

The paper identifies the analytic diffusion of `s.fixed.coefficient` with the solution of the
stochastic differential equation `e.fixed.clock.sde`,
`dX = σ dW + b(X) dt`, with additive noise. That identification rests on three standard results,
which are stated here as explicit hypotheses (cited results, not proved in this repository):

* `StrongSolutionExistsUnique`: strong existence and pathwise uniqueness for a locally Lipschitz
  drift of linear growth (Ikeda–Watanabe, *Stochastic Differential Equations and Diffusion
  Processes*, 2nd ed., Chapter IV, §§2–3; Karatzas–Shreve, *Brownian Motion and Stochastic
  Calculus*, 2nd ed., Theorems 5.2.5 and 5.2.9);
* `ItoFormulaStopped`: Itô's formula for `g(t, X_t)` with `g ∈ C²`, in its martingale form at the
  exit time of a bounded set, where the stochastic integral has a bounded integrand
  (Karatzas–Shreve, Theorem 3.3.6 and Proposition 3.2.10);
* `InteriorEllipticRegularity`: a continuous local weak solution of
  `μ ρ u − ∇·(κ ρ ∇u) = ρ F` with `ρ = e^V`, `V ∈ C^{1,1}_loc` and `F` smooth with compact
  support is `C²` and solves `μ u − κ (Δu + ∇V·∇u) = F` classically (Gilbarg–Trudinger,
  *Elliptic Partial Differential Equations of Second Order*, Theorems 8.8 and 9.19). The paper uses
  it in the same place ("Interior elliptic regularity and Itô's formula").

The objects are on `ℝ^d = Fin d → ℝ` (sup norm), with time `ℝ≥0`.

## Main definitions

* `IsBrownianMotion`: a standard Brownian motion with respect to a filtration;
* `IsStrongSolution`: a continuous adapted solution of `X_t = X_0 + σ W_t + ∫₀ᵗ b(X_s) ds`;
* `exitTime`, `stopAt`: the exit time from the sup-norm ball of radius `R` and the stopped time;
* `spaceTimeGenerator`: `∂ₜ g + (σ²/2) Δₓ g + b·∇ₓ g` for `g : ℝ × ℝ^d → ℝ`;
* `spaceGenerator`: `(σ²/2) Δu + b·∇u` for `u : ℝ^d → ℝ`.
-/

@[expose] public section

noncomputable section

namespace SubdiffusiveProcess.SDE

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

/-- The coordinate space `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

variable {d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `W` is a standard `d`-dimensional Brownian motion with respect to the filtration `ℱ` under
`P`: it starts at `0`, has continuous paths, is adapted, and every increment `W t − W s` with
`s ≤ t` is independent of `ℱ s` and has independent centred Gaussian coordinates of variance
`t − s`. -/
structure IsBrownianMotion (W : ℝ≥0 → Ω → Vec d) (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    Prop where
  zero : ∀ ω, W 0 ω = 0
  continuous : ∀ ω, Continuous fun t => W t ω
  adapted : Adapted ℱ W
  indep : ∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (ℱ s) P
  gaussian : ∀ s t : ℝ≥0, s ≤ t →
    P.map (fun ω => W t ω - W s ω) = Measure.pi fun _ : Fin d => gaussianReal 0 (t - s)

/-- `X` is a continuous `ℱ`-adapted solution of `X_t = X_0 + σ W_t + ∫₀ᵗ b(X_s) ds`. -/
structure IsStrongSolution (σ : ℝ) (b : Vec d → Vec d) (W X : ℝ≥0 → Ω → Vec d)
    (ℱ : Filtration ℝ≥0 mΩ) : Prop where
  adapted : Adapted ℱ X
  continuous : ∀ ω, Continuous fun t => X t ω
  integral_eq : ∀ ω (t : ℝ≥0),
    X t ω = X 0 ω + σ • W t ω + ∫ s in (0 : ℝ)..(t : ℝ), b (X s.toNNReal ω)

/-- The exit time `inf {t : R ≤ ‖X t‖}` of a path from the open sup-norm ball of radius `R`. -/
def exitTime (X : ℝ≥0 → Ω → Vec d) (R : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : R ≤ ‖X t ω‖), (t : ℝ≥0∞)

/-- The time `t ∧ τ` as a nonnegative real. -/
def stopAt (τ : ℝ≥0∞) (t : ℝ≥0) : ℝ≥0 :=
  (min (t : ℝ≥0∞) τ).toNNReal

/-- The time derivative `∂ₜ g` of a function on `ℝ × ℝ^d`. -/
def timeDeriv (g : ℝ × Vec d → ℝ) (p : ℝ × Vec d) : ℝ :=
  fderiv ℝ g p (1, 0)

/-- The space partial derivative `∂ᵢ g` of a function on `ℝ × ℝ^d`. -/
def spacePartial (i : Fin d) (g : ℝ × Vec d → ℝ) (p : ℝ × Vec d) : ℝ :=
  fderiv ℝ g p (0, Pi.single i 1)

/-- The space-time generator `∂ₜ g + (σ²/2) Δₓ g + b·∇ₓ g`. -/
def spaceTimeGenerator (σ : ℝ) (b : Vec d → Vec d) (g : ℝ × Vec d → ℝ) (p : ℝ × Vec d) :
    ℝ :=
  timeDeriv g p + σ ^ 2 / 2 * ∑ i, spacePartial i (spacePartial i g) p +
    ∑ i, b p.2 i * spacePartial i g p

/-- The partial derivative `∂ᵢ u` of a function on `ℝ^d`. -/
def partialDeriv (i : Fin d) (u : Vec d → ℝ) (x : Vec d) : ℝ :=
  fderiv ℝ u x (Pi.single i 1)

/-- The generator `(σ²/2) Δu + b·∇u`. -/
def spaceGenerator (σ : ℝ) (b : Vec d → Vec d) (u : Vec d → ℝ) (x : Vec d) : ℝ :=
  σ ^ 2 / 2 * ∑ i, partialDeriv i (partialDeriv i u) x + ∑ i, b x i * partialDeriv i u x

universe u

/-- **Strong existence and pathwise uniqueness** (cited: Ikeda–Watanabe, Chapter IV, §§2–3;
Karatzas–Shreve, Theorems 5.2.5 and 5.2.9). For a locally Lipschitz drift `b` of linear growth,
`σ ∈ ℝ`, a filtration `ℱ` containing the null sets and an `ℱ`-Brownian motion `W`, from every
`x` there is a continuous `ℱ`-adapted solution of `X_t = x + σ W_t + ∫₀ᵗ b(X_s) ds`, and two such
solutions are indistinguishable. -/
def StrongSolutionExistsUnique (d : ℕ) : Prop :=
  ∀ (σ : ℝ) (b : Vec d → Vec d), LocallyLipschitz b →
    (∃ K : ℝ, ∀ x, ‖b x‖ ≤ K * (1 + ‖x‖)) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›),
      (∀ (t : ℝ≥0) (s : Set Ω), P s = 0 → MeasurableSet[ℱ t] s) →
      ∀ W : ℝ≥0 → Ω → Vec d, IsBrownianMotion W ℱ P → ∀ x : Vec d,
        (∃ X : ℝ≥0 → Ω → Vec d, IsStrongSolution σ b W X ℱ ∧ ∀ ω, X 0 ω = x) ∧
        ∀ X Y : ℝ≥0 → Ω → Vec d, IsStrongSolution σ b W X ℱ → IsStrongSolution σ b W Y ℱ →
          (∀ ω, X 0 ω = x) → (∀ ω, Y 0 ω = x) → ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω

/-- **Itô's formula at the exit time of a ball** (cited: Karatzas–Shreve, Theorem 3.3.6, with the
martingale property of stochastic integrals of bounded integrands, Proposition 3.2.10). Let `X`
solve `dX = σ dW + b(X) dt` with `b` continuous, let `g : ℝ × ℝ^d → ℝ` be `C²` and let `τ` be the
exit time of `X` from the sup-norm ball of radius `R`. Then
`g(t ∧ τ, X_{t∧τ}) − g(0, X_0) − ∫₀^{t∧τ} (∂ₜ g + (σ²/2) Δₓ g + b·∇ₓ g)(r, X_r) dr`
is an `ℱ`-martingale: it is the stochastic integral `∫₀^{t∧τ} σ ∇ₓ g(r, X_r)·dW_r`, whose
integrand is bounded. -/
def ItoFormulaStopped (d : ℕ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (σ : ℝ) (b : Vec d → Vec d), Continuous b →
    ∀ W X : ℝ≥0 → Ω → Vec d, IsBrownianMotion W ℱ P → IsStrongSolution σ b W X ℱ →
      ∀ g : ℝ × Vec d → ℝ, ContDiff ℝ 2 g → ∀ R : ℝ,
        Martingale
          (fun t ω =>
            g ((stopAt (exitTime X R ω) t : ℝ), X (stopAt (exitTime X R ω) t) ω) -
              g (0, X 0 ω) -
              ∫ r in (0 : ℝ)..(stopAt (exitTime X R ω) t : ℝ),
                spaceTimeGenerator σ b g (r, X r.toNNReal ω))
          ℱ P

/-- **Interior elliptic regularity** (cited: Gilbarg–Trudinger, Theorems 8.8 and 9.19). Let
`V : ℝ^d → ℝ` be `C¹` with locally Lipschitz derivative, `κ, μ > 0`, `F` smooth with compact
support, and let `u` be continuous with, on every bounded open convex domain `W`, an `H¹(W)`
representative solving `μ ρ u − ∇·(κ ρ ∇u) = ρ F` weakly, `ρ = e^V`. Then `u` is `C²` and
`μ u − κ (Δu + ∇V·∇u) = F` everywhere. -/
def InteriorEllipticRegularity (d : ℕ) : Prop :=
  ∀ (V : Vec d → ℝ), ContDiff ℝ 1 V → LocallyLipschitz (fderiv ℝ V) →
    ∀ (κ μ : ℝ), 0 < κ → 0 < μ →
    ∀ F : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
    ∀ u : Vec d → ℝ, Continuous u →
      (∀ W : Set (Vec d), Homogenization.IsOpenBoundedConvexDomain W →
        ∃ v : Homogenization.H1Function W, (∀ x ∈ W, v.toFun x = u x) ∧
          CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn
            (fun x => κ * Real.exp (V x)) (fun x => Real.exp (V x)) μ W v F) →
      ContDiff ℝ 2 u ∧
        ∀ x, μ * u x - κ * (∑ i, partialDeriv i (partialDeriv i u) x +
          ∑ i, partialDeriv i V x * partialDeriv i u x) = F x

end SubdiffusiveProcess.SDE
