module

public import MarkovProcess.Main
public import MarkovProcess.Lifetime.Law
public import MarkovProcess.Parameterized.Semigroup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
public import SubdiffusiveProcess.Frozen.Section7.Defs.LifetimeValue
@[expose] public section

/-!
# Intrinsic time change before the lifetime

`IsIntrinsicTimeChange a PX PY` relates two kernels on lifetime paths by a
measurable path transform. Before the input lifetime, the clock is
`A(s) = ∫_0^s a(theta,X_r)^(-1) dr`; before the output lifetime, the transformed
coordinate is read at the generalized inverse `inf {s ≥ 0 : t < A(s)}`.
The lifetime is the extended supremum of attainable clock values. These
coordinate identities have explicit pre-lifetime restrictions. The integrand
and real inverse are total outside that domain; `lifetimeValue` supplies the
cemetery convention, and the clock suppliers provide positivity and divergence
where their conclusions require them.
-/

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


