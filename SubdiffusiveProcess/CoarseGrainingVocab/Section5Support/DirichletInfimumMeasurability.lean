module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteDirichletConvergence

@[expose] public section

/-!
# Measurability of the continuum Dirichlet minimum in the sample

`q_*` of `p.homogenized.coefficient.strict.decay` is an *expectation* of the continuum
minimum, so building that minimum (P-80's `dirichletInfOn`) creates a
probabilistic obligation that the source never has to state:

```text
omega |-> dirichletInfOn (shellFactor M 0 omega) spx_0^pi p   is measurable.
```

`dirichletInfOn` is an infimum over the *uncountable* class `H_0^1(U)`, so
nothing is automatic.  P-80 named two possible routes -- the countable dense
subclass of the `H10Function` carrier, or the limit of the discrete infima.
This file takes the **second**, because (S2c) makes it available:
`dirichletInfOn_eq_iInf_kuhnDirichletInf` already expresses the continuum
minimum as a *countable* infimum of discrete ones, and the discrete infimum

```text
kuhnDirichletInf B S U p = sInf { sum_T |U cap T| (sup_{closure T} B) |p + q_T|^2 :
                                    q in kuhnSlopeSet U S }
```

depends on the sample only through the finitely many numbers `cellSup B T`,
because `kuhnSlopeSet U S` was deliberately defined without reference to `B`.

What this file lands is the whole reduction:

* `measurable_dirichletInfOn_of_measurable_kuhnDirichletInf` -- from the
  discrete infima to the continuum one, by `Measurable.iInf` over the scales;
* `kuhnDirichletInf_eq_iInf` -- the criterion under which the discrete infimum is
  a countable infimum: a countable family of admissible slope assignments that
  is `eps`-optimal at every sample;
* `measurable_kuhnDirichletInf_of_iInf` -- the corresponding measurability step;
* `measurable_kuhnDiscreteEnergy` -- the last reduction: for a *fixed* slope
  assignment the discrete energy is measurable as soon as each
  `omega |-> cellSup (B omega) T` is.

## What is left to the two downstream files

Two obligations remain *at this point*, and both are finite-dimensional or
compactness statements, not Sobolev ones.  They are discharged in
`DiscreteSlopeSeparability.lean` (M2) and `CellSupMeasurability.lean` (M1),
where `measurable_dirichletInfOn_of_measurable_apply` closes the obligation
outright.

* **(M1)** `omega |-> cellSup (B omega) T` is measurable.  Route: a closed Kuhn
  cell is compact (`isCompact_closedCarrier`) and `B omega` is continuous, so
  `cellSup` is the supremum over any countable dense subset of the cell, and a
  countable supremum of measurable functions is measurable.
* **(M2)** a countable family `D : Nat -> KuhnCell d -> Vec d` inside
  `kuhnSlopeSet U S` that is `eps`-optimal at *every* sample.  Route: the
  discrete energy factors through the restriction `q |-> q|_S` to a *finite*
  index set, so it is a continuous function on a finite-dimensional space; a
  subset of such a space is separable, and a countable dense subset of
  `kuhnSlopeSet U S` restricted to `S` is `eps`-optimal for every `B`
  simultaneously, uniformly in the sample, because the modulus of continuity of
  the energy is controlled by `sup_T cellSup B T` at that sample only.

Neither uses any Sobolev input; that is the point of routing the measurability
through the discrete infima rather than through the `H10Function` carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The discrete infimum over a countable family -/

/-- The defining bound, stated on the slope set rather than on a competitor. -/
theorem kuhnDirichletInf_le_of_mem_kuhnSlopeSet {B : Vec d → ℝ}
    {S : Finset (KuhnCell d)} {U : Set (Vec d)} (hB : Continuous B)
    (hB0 : ∀ x, 0 ≤ B x) (p : Vec d) {q : KuhnCell d → Vec d}
    (hq : q ∈ kuhnSlopeSet U S) :
    kuhnDirichletInf B S U p ≤ kuhnDiscreteEnergy B S U p q :=
  csInf_le (bddBelow_kuhnDiscreteEnergy_image hB hB0 p) ⟨q, hq, rfl⟩

/-- **The discrete infimum as a countable infimum.**  A countable family of
admissible slope assignments which is `eps`-optimal realizes `Q_{R,pi}(p)`. -/
theorem kuhnDirichletInf_eq_iInf {B : Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec d)
    (D : ℕ → KuhnCell d → Vec d) (hD : ∀ m, D m ∈ kuhnSlopeSet U S)
    (hopt : ∀ eps > 0, ∃ m,
      kuhnDiscreteEnergy B S U p (D m) < kuhnDirichletInf B S U p + eps) :
    kuhnDirichletInf B S U p = ⨅ m, kuhnDiscreteEnergy B S U p (D m) := by
  have hbdd : BddBelow (Set.range fun m => kuhnDiscreteEnergy B S U p (D m)) := by
    refine ⟨0, ?_⟩
    rintro E ⟨m, rfl⟩
    exact kuhnDiscreteEnergy_nonneg hB hB0 p (D m)
  refine le_antisymm
    (le_ciInf fun m => kuhnDirichletInf_le_of_mem_kuhnSlopeSet hB hB0 p (hD m)) ?_
  refine le_of_forall_pos_le_add fun eps heps => ?_
  obtain ⟨m, hm⟩ := hopt eps heps
  exact le_trans (ciInf_le hbdd m) hm.le

/-! ## The measurability chain -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The last reduction.**  For a *fixed* slope assignment the discrete energy is
measurable in the sample as soon as each cellwise supremum is: the slope set and
the cell volumes carry no sample dependence. -/
theorem measurable_kuhnDiscreteEnergy {B : Ω → Vec d → ℝ} {S : Finset (KuhnCell d)}
    {U : Set (Vec d)} {p : Vec d} {q : KuhnCell d → Vec d}
    (h : ∀ T ∈ S, Measurable fun ω => cellSup (B ω) T) :
    Measurable fun ω => kuhnDiscreteEnergy (B ω) S U p q := by
  refine Finset.measurable_sum S fun T hT => ?_
  exact ((h T hT).mul_const (vecNormSq (p + q T))).const_mul
    (volume.real (U ∩ T.openCarrier))

/-- **Measurability of `Q_{R,pi}(p)`** from a sample-independent countable family
of `eps`-optimal slope assignments. -/
theorem measurable_kuhnDirichletInf_of_iInf {B : Ω → Vec d → ℝ}
    {S : Finset (KuhnCell d)} {U : Set (Vec d)} {p : Vec d}
    (D : ℕ → KuhnCell d → Vec d)
    (hmeas : ∀ m, Measurable fun ω => kuhnDiscreteEnergy (B ω) S U p (D m))
    (heq : ∀ ω, kuhnDirichletInf (B ω) S U p =
      ⨅ m, kuhnDiscreteEnergy (B ω) S U p (D m)) :
    Measurable fun ω => kuhnDirichletInf (B ω) S U p := by
  have hfun : (fun ω => kuhnDirichletInf (B ω) S U p) =
      fun ω => ⨅ m, kuhnDiscreteEnergy (B ω) S U p (D m) := funext heq
  rw [hfun]
  exact Measurable.iInf hmeas

/-- **The measurability obligation of the bundle report, reduced.**  The
continuum Dirichlet minimum is measurable in the sample as soon as each
*discrete* minimum is, because (S2c) writes it as a countable infimum of them.

Applied with `B omega = shellFactor M 0 omega` (continuous and nonnegative sample
by sample, by P-78's `contDiff_one_shellFactor` and `shellFactor_pos`) and
`U = spx_0^pi`, this is the statement `q_*` needs. -/
theorem measurable_dirichletInfOn_of_measurable_kuhnDirichletInf {n : ℕ}
    {Q : TriadicCube (n + 1)} {U : Set (Vec (n + 1))} {B : Ω → Vec (n + 1) → ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hUQ : U ⊆ openCubeSet Q)
    (hB : ∀ ω, Continuous (B ω)) (hB0 : ∀ ω x, 0 ≤ B ω x) (p : Vec (n + 1))
    (hmeas : ∀ j : ℤ, Measurable fun ω =>
      kuhnDirichletInf (B ω) (triadicSimplexPartition Q (min j Q.scale)) U p) :
    Measurable fun ω => dirichletInfOn (B ω) U p := by
  have hfun : (fun ω => dirichletInfOn (B ω) U p) =
      fun ω => ⨅ j : ℤ,
        kuhnDirichletInf (B ω) (triadicSimplexPartition Q (min j Q.scale)) U p :=
    funext fun ω =>
      dirichletInfOn_eq_iInf_kuhnDirichletInf hU hUQ (hB ω) (hB0 ω) p
  rw [hfun]
  exact Measurable.iInf hmeas

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
