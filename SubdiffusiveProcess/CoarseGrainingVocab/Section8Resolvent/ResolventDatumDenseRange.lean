module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumC0Data

@[expose] public section

/-!
# The second obligation is exactly dense range of one resolvent

`ResolventDatumInterface.lean` records the second remaining obligation of the
Section 8 datum as `HasStrongMassiveResolventLimit`, the strong convergence
`μ R_μ f → f` in `C₀`.  The classical elliptic proof needs a local barrier which does not exist for a
merely continuous coefficient.

This module replaces it by an equivalent statement of a different shape:

  **the range of one resolvent `R_ν` is dense in `C₀`.**

Both directions are already available inside the proved package and need no new
analysis:

* dense range ⇒ strong convergence is `C0ResolventDatum.tendsto_smul_solution`,
  i.e. the Hille–Yosida layer of `MarkovProcess`
  (`ContractiveResolvent.tendsto_scaledOperator_apply`);
* strong convergence ⇒ dense range is the proved
  `MassiveC0Resolvent.denseRange_operator`.

The point of the change is that dense range is *literally a clause of the
frozen conclusion* of the GMC resolvent datum, so nothing is lost, and the debt is
now a single statement about one operator instead of a limit along the shift.
`MassiveC0Resolvent.sol_eq` makes it independent of which solution operator is
used.

## Main declarations

* `HasDenseMassiveResolventRange` — the replacement obligation.
* `hasStrongMassiveResolventLimit_of_hasDenseMassiveResolventRange` and its
  converse — the equivalence.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter Topology
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- **The replacement for the strong-limit obligation.**  The range of the
whole-space resolvent is dense in `C₀`.  By `MassiveC0Resolvent.sol_eq` this
does not depend on which solution operator is used, and by
`C0ResolventDatum.denseRange_operator_of_denseRange` it does not depend on the
shift either. -/
def HasDenseMassiveResolventRange (c rho : Vec d → ℝ) : Prop :=
  ∀ (R : MassiveC0Resolvent c rho) (nu : PositiveShift),
    DenseRange (fun f : C₀(Vec d, ℝ) ↦ R.sol nu f)

/-- The coerced resolvent operator of the packaged datum is the solution map. -/
theorem MassiveC0Resolvent.coe_operator_toC0ResolventDatum
    {c rho : Vec d → ℝ} (R : MassiveC0Resolvent c rho)
    (B : MassiveCubeBounds c rho) (mu : PositiveShift) :
    ⇑((R.toC0ResolventDatum B).operator mu) = fun f : C₀(Vec d, ℝ) ↦ R.sol mu f :=
  rfl

/-- **Dense range gives the strong limit.**  This is the Hille–Yosida layer of
`MarkovProcess`, applied to the packaged datum. -/
theorem hasStrongMassiveResolventLimit_of_hasDenseMassiveResolventRange
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    (h : HasDenseMassiveResolventRange c rho) :
    HasStrongMassiveResolventLimit c rho := by
  intro R f
  have hd : ∀ mu : PositiveShift,
      DenseRange ((R.toC0ResolventDatum B).operator mu) := by
    intro mu
    rw [DenseRange, R.coe_operator_toC0ResolventDatum B mu]
    exact h R mu
  exact (R.toC0ResolventDatum B).tendsto_smul_solution hd f

/-- **The strong limit gives dense range.**  The converse direction, so the two
obligations are equivalent. -/
theorem hasDenseMassiveResolventRange_of_hasStrongMassiveResolventLimit
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    (h : HasStrongMassiveResolventLimit c rho) :
    HasDenseMassiveResolventRange c rho := by
  intro R nu
  have hd := R.denseRange_operator B (h R) nu
  rw [DenseRange, R.coe_operator_toC0ResolventDatum B nu] at hd
  exact hd

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
