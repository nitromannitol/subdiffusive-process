module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteSlopeSeparability

@[expose] public section

/-!
# A measurable selection of the discrete slopes

Step 3 of the strict-decay proof (`p.homogenized.coefficient.strict.decay`) conditions on
the outer layer `B_{NR}` and then says

> The slopes `p_T` and the displayed cell weights are then fixed, whereas
> `A_{N-1}^{(R)}` is independent of `B_{NR}`.

For that sentence to be a Lean statement the slopes `p_T` must be a
`B_{NR}`-measurable function of the sample.  P-89 and P-91 both recorded "a
measurable selection of the Dirichlet minimizer" as the bundle's honest
obstruction.  This file discharges it, and records precisely *which* minimizer
has to be selected:

* **not** the continuum minimizer `u_T` of `p.homogenized.coefficient.strict.decay`.  Gluing
  those (`MeshGluing.lean`) proves an inequality between two *infima*, in which
  the `u_T` occur only as witnesses inside the proof, so no measurable choice of
  them is ever required;
* only the **discrete** minimizer `v` of `p.homogenized.coefficient.strict.decay`, and of it
  only the finitely many slopes `p_T`.

The discrete selection is elementary, because P-91's
`exists_countable_eps_optimal_kuhnSlopes` already produces a **countable,
sample-free** family `D : Nat -> KuhnCell d -> Vec d` of admissible slope
assignments which is `eps`-optimal at every coefficient simultaneously.  Taking
the least index that works,

```text
n omega := Nat.find (the eps-optimality of D at the sample omega),
```

is measurable by mathlib's `measurable_find`, since each defining event compares two
functions already known to be measurable (P-91's `measurable_kuhnDiscreteEnergy`
and `measurable_kuhnDirichletInf`).

The output is stronger than a measurable selection: the selected assignment is
**countably valued**, so the sample space is partitioned into countably many
measurable pieces on each of which the slope assignment is one *deterministic*
element of the slope set.  That is what the conditioning of Step 3 consumes -- on
each piece the "frozen" slopes are constants, and the independence of
`A_{N-1}^{(R)}` from `B_{NR}` can be used with no conditional-expectation
apparatus at all.

## Scope

* The measurability hypothesis is exactly (M1) of
  `DirichletInfimumMeasurability.lean`, the cellwise suprema, which
  `CellSupMeasurability.lean` discharges for the GMC layers.
* No probability measure is used: the statements are about a bare measurable
  space, so they apply verbatim to a sub-sigma-algebra such as the one generated
  by one layer.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Set

noncomputable section

variable {d : ℕ}

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The measurable `eps`-optimal discrete selection.**  There is a countable
sample-free family `D` of admissible slope assignments and a *measurable* index
`n` such that `D (n omega)` is `eps`-optimal for the discrete Dirichlet problem
at every sample.

This is the measurable selection that `p.homogenized.coefficient.strict.decay` needs: the
per-cell slopes `p_T = p + D (n omega) T` are measurable in the sample, and
depend on it only through the cellwise suprema of the coefficient. -/
theorem exists_measurable_eps_optimal_kuhnSlopes {B : Ω → Vec d → ℝ}
    {S : Finset (KuhnCell d)} {U : Set (Vec d)} (p : Vec d)
    (hB : ∀ ω, Continuous (B ω)) (hB0 : ∀ ω x, 0 ≤ B ω x)
    (hcell : ∀ T ∈ S, Measurable fun ω => cellSup (B ω) T) {eps : ℝ} (heps : 0 < eps) :
    ∃ (D : ℕ → KuhnCell d → Vec d) (n : Ω → ℕ),
      (∀ m, D m ∈ kuhnSlopeSet U S) ∧ Measurable n ∧
        ∀ ω, kuhnDiscreteEnergy (B ω) S U p (D (n ω)) <
          kuhnDirichletInf (B ω) S U p + eps := by
  classical
  obtain ⟨D, hD, hopt⟩ := exists_countable_eps_optimal_kuhnSlopes U S
  set P : Ω → ℕ → Prop := fun ω m =>
    kuhnDiscreteEnergy (B ω) S U p (D m) < kuhnDirichletInf (B ω) S U p + eps with hP
  have hex : ∀ ω, ∃ m, P ω m := fun ω => hopt (B ω) p eps heps
  have hmeas : ∀ m, MeasurableSet {ω | P ω m} := by
    intro m
    exact measurableSet_lt (measurable_kuhnDiscreteEnergy hcell)
      ((measurable_kuhnDirichletInf hB hB0 hcell).add_const eps)
  exact ⟨D, fun ω => Nat.find (hex ω), hD, measurable_find hex hmeas,
    fun ω => Nat.find_spec (hex ω)⟩

/-- The selected slope field is measurable, cell by cell: it is a countably
valued function of the sample. -/
theorem measurable_selected_slope {D : ℕ → KuhnCell d → Vec d} {n : Ω → ℕ}
    (hn : Measurable n) (T : KuhnCell d) :
    Measurable fun ω => D (n ω) T :=
  (measurable_from_top (f := fun m => D m T)).comp hn

/-- The pieces of the induced countable partition of the sample space are
measurable, and on each of them the selected slope assignment is one
*deterministic* member of the slope set.  This is the exact form in which Step 3
freezes the slopes before using the independence of `A_{N-1}^{(R)}` from
`B_{NR}`. -/
theorem measurableSet_selection_fiber {n : Ω → ℕ} (hn : Measurable n) (m : ℕ) :
    MeasurableSet {ω | n ω = m} :=
  hn (measurableSet_singleton m)

omit [MeasurableSpace Ω] in
theorem selected_slope_eq_on_fiber {D : ℕ → KuhnCell d → Vec d} {n : Ω → ℕ} {m : ℕ}
    {ω : Ω} (hω : ω ∈ {ω | n ω = m}) : D (n ω) = D m := by
  rw [show n ω = m from hω]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
