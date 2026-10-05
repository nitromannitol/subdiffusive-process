module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Sobolev.WeakGradient

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Documented published input** (Fukushima–Oshima–Takeda, *Dirichlet Forms and
Symmetric Markov Processes*, 2nd edition, Theorem 2.1.3 together with Theorem 3.2.2
and Lemma 3.2.4); specified route (ii) for `obl_BH`.

A regular Dirichlet form admits a **quasi-continuous representative family**: a choice
`rep v hv` of a Borel representative of each `v ∈ D(E)` at which the energy-measure
calculus is valid.  The two calculus clauses are exactly the conclusions of the children
`obl_BH_compact_preimage_nullity` and `obl_BH_energy_measure_convergence`, which the
project proves for a **globally continuous** representative; a general domain element has
none, and neither conclusion survives modification of the representative on a
Lebesgue-null set, because energy measures charge Lebesgue-null sets.  Constructing `rep`
needs capacity theory (the fundamental inequality, equilibrium potentials, quasi-uniform
convergence), which is present in no pinned library of this project.

This is a `Prop`-valued carrier, passed as a hypothesis wherever it is used.  It is not an
axiom and it asserts nothing about an arbitrary measurable representative: the family is
existentially bound, so the clauses are claimed only for the one `rep` that the capacity
construction produces.

Tick list:
- `rep` is a *choice*, existentially bound; no clause is asserted for every measurable
  representative (that would be false).
- Clause 3 is the compact case only; the passage to arbitrary Lebesgue-null sets, and
  the absolute continuity of the image measure, are proved in `obl_BH` by inner regularity
  and are not assumed here.
- Clause 4 is verbatim the conclusion of `obl_BH_energy_measure_convergence` with its
  `(vc, hvc : Continuous vc, hrep)` triple replaced by `rep v hv`.
- No continuity of `rep v hv` is asserted; only `Measurable`. -/
def obl_BH_quasi_continuous_representative {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm) : Prop :=
  ∃ rep :
      ∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))),
        v ∈ E.toClosedForm.domain → SpatialCoordinates d → ℝ,
    (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
        (hv : v ∈ E.toClosedForm.domain), Measurable (rep v hv)) ∧
    (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
        (hv : v ∈ E.toClosedForm.domain),
      (⇑v =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] rep v hv)) ∧
    (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
        (hv : v ∈ E.toClosedForm.domain),
      ∀ K : Set ℝ, IsCompact K → volume K = 0 →
        Gamma.measure v ((rep v hv) ⁻¹' K) = 0) ∧
    (∀ (v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
        (hv : v ∈ E.toClosedForm.domain),
      ∀ T : ℝ → ℝ, (∃ K : ℝ≥0, LipschitzWith K T) → T 0 = 0 →
      ∀ Tderiv : ℝ → ℝ, Measurable Tderiv →
        (∀ᵐ s : ℝ, HasDerivAt T (Tderiv s) s) →
        ∀ (w : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
          (_hw : w ∈ E.toClosedForm.domain),
          (⇑w =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
            (fun x => T (rep v hv x))) →
          ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
            ((Gamma.measure w B).toReal =
              ∫ x in B, (Tderiv (rep v hv x)) ^ 2 ∂(Gamma.measure v)))

/-- **Non-vacuity of the carrier.**  The zero Dirichlet form with its zero energy measure
satisfies it.  This establishes NON-VACUITY only: inhabitation at the paper's form is the
published input itself, exactly as for `SubdiffusiveProcess.DirichletForm.HasEnergyMeasure`.  Without this
check a consumer that carries the `Prop` could be vacuously true. -/
theorem aux_obl_BH_quasi_continuous_representative_nonvacuous
    {d : ℕ} (Q : Opens (SpatialCoordinates d)) :
    obl_BH_quasi_continuous_representative
      (_root_.SubdiffusiveProcess.DirichletForm.zeroDirichletForm
        (volume.restrict (Q : Set (SpatialCoordinates d))))
      (_root_.SubdiffusiveProcess.DirichletForm.zeroEnergyMeasure
        (volume.restrict (Q : Set (SpatialCoordinates d)))) := by
  classical
  refine ⟨fun v _ => (Lp.aestronglyMeasurable v).mk ⇑v, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact (Lp.aestronglyMeasurable v).stronglyMeasurable_mk.measurable
  · intro v hv
    exact (Lp.aestronglyMeasurable v).ae_eq_mk
  · intro v hv K hK hKnull
    simp [_root_.SubdiffusiveProcess.DirichletForm.zeroEnergyMeasure]
  · intro v hv T hT hT0 Tderiv hTm hTd w hw hwrep B hB
    simp [_root_.SubdiffusiveProcess.DirichletForm.zeroEnergyMeasure]

end SubdiffusiveProcess.Paper
