module

public import MarkovProcess.Main
public import MarkovProcess.Lifetime.Law
public import MarkovProcess.Parameterized.Semigroup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
public import SubdiffusiveProcess.Frozen.Section7.Defs.LifetimeValue
@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
open SubdiffusiveProcess.Frozen.Section7


def SubdiffusiveProcess.Frozen.Section7.IsIntrinsicTimeChange {Theta : Type*} [MeasurableSpace Theta] {d : ℕ}
    (a : Theta → State d → ℝ)
    (PX PY : Kernel (Theta × State d) (MarkovProcess.LifetimePath (State d))) : Prop :=
  ∀ theta x, ∃ timeChange : MarkovProcess.LifetimePath (State d) →
      MarkovProcess.LifetimePath (State d),
    Measurable timeChange ∧ Measure.map timeChange (PX (theta, x)) = PY (theta, x) ∧
    ∀ᵐ path ∂PX (theta, x), ∃ A : ℝ → ℝ,
      Monotone A ∧ A 0 = 0 ∧
      (∀ s : ℝ, 0 ≤ s → ENNReal.ofReal s < path.lifetime →
        A s = ∫ r in (0 : ℝ)..s,
          (a theta (lifetimeValue x (Real.toNNReal r) path))⁻¹) ∧
      (timeChange path).lifetime =
        sSup (ENNReal.ofReal ''
          (A '' {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < path.lifetime})) ∧
      ∀ t : NNReal, ENNReal.ofNNReal t < (timeChange path).lifetime →
        MarkovProcess.LifetimePath.coordinate t (timeChange path) =
          MarkovProcess.LifetimePath.coordinate
            (Real.toNNReal (sInf {s : ℝ | 0 ≤ s ∧ (t : ℝ) < A s})) path


