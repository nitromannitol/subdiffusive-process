module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Order.LiminfLimsup

@[expose] public section




open Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments

/-- The liminf condition of Mosco convergence. -/
def MoscoLiminf {H : Type*} [NormedAddCommGroup H]
    (EN : ℕ → H → ℝ≥0∞) (Elim : H → ℝ≥0∞) : Prop :=
  ∀ (x : H) (y : ℕ → H), Tendsto y atTop (𝓝 x) →
    Elim x ≤ liminf (fun n => EN n (y n)) atTop

/-- The recovery-sequence condition of Mosco convergence. -/
def MoscoRecovery {H : Type*} [NormedAddCommGroup H]
    (EN : ℕ → H → ℝ≥0∞) (Elim : H → ℝ≥0∞) : Prop :=
  ∀ x : H, ∃ y : ℕ → H, Tendsto y atTop (𝓝 x) ∧
    limsup (fun n => EN n (y n)) atTop ≤ Elim x

/-- The killed-form / killed-inverse duality of Proposition
`mfd:prop-killed-inverse`, `mfd:prop-killed-inverse` and `mfd:prop-as-forms`.  Hypothesis structure owned by `SubdiffusiveProcess.VariationalResponses`; stated here so that `SubdiffusiveProcess.ResponseMoments` can prove its side of
`mfd:prop-as-forms`. -/
structure KilledFormDuality (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (EN : ℕ → H → ℝ≥0∞) (Elim : H → ℝ≥0∞)
    (G : ℕ → H →L[ℝ] H) (Glim : H →L[ℝ] H) : Prop where
  /-- Closedness of each finite-cutoff form. -/
  closed : ∀ n : ℕ, LowerSemicontinuous (EN n)
  /-- Closedness of the limiting form. -/
  limit_closed : LowerSemicontinuous Elim
  /-- The forms vanish exactly at `0`; the killed space is the domain. -/
  eq_zero : ∀ n : ℕ, EN n 0 = 0
  limit_eq_zero : Elim 0 = 0
  /-- Orthogonal additivity of the quadratic energy: the algebraic consequence
  used after strong locality identifies disjoint killed subspaces as
  `E`-orthogonal (`mfd:prop-locality`).  It asserts that the limit energy
  splits, `Elim (u+v) = Elim u + Elim v`, precisely when the actual real
  polarization `(Elim (u+v)).toReal - (Elim (u-v)).toReal` of *this same*
  energy vanishes; the finite-energy guards on `u`, `v`, `u+v`, `u-v` are
  mandatory, since they prevent `ENNReal.toReal` at infinity from
  manufacturing a zero polarization.  In particular `v = u` implies zero
  polarization only when this orthogonality premise itself holds, so the field
  is NOT plain subadditivity and is NOT a full definition of strong locality:
  the geometry and the domain membership are supplied at consumers, not a free
  conclusion on all of `H`. -/
  limit_local : ∀ u v : H,
    Elim u ≠ ⊤ → Elim v ≠ ⊤ → Elim (u + v) ≠ ⊤ → Elim (u - v) ≠ ⊤ →
    (1/4:ℝ) * ((Elim (u + v)).toReal - (Elim (u - v)).toReal) = 0 →
    Elim (u + v) = Elim u + Elim v
  /-- The variational duality of `mfd:prop-killed-inverse` at each cutoff. -/
  resolvent_dual : ∀ (n : ℕ) (f : H),
    ENNReal.ofReal (inner ℝ f (G n f)) =
      ⨆ v : H, ENNReal.ofReal (2 * inner ℝ f v) - EN n v
  /-- The same duality for the limit. -/
  limit_resolvent_dual : ∀ f : H,
    ENNReal.ofReal (inner ℝ f (Glim f)) =
      ⨆ v : H, ENNReal.ofReal (2 * inner ℝ f v) - Elim v
  /-- The consequence actually consumed: operator-norm convergence of the
  killed inverses gives Mosco convergence of the forms. -/
  mosco_of_operatorNorm : Tendsto G atTop (𝓝 Glim) →
    MoscoLiminf EN Elim ∧ MoscoRecovery EN Elim

end ResponseMoments
end SubdiffusiveProcess
