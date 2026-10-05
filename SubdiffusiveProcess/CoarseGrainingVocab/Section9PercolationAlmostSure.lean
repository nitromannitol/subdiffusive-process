module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolationGeometry
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
# The almost-sure form of the multiscale percolation geometry

`SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolationGeometry` states the
three geometric clauses of the manuscript's multiscale percolation lemma at **every**
sample.  This is the wrong quantifier: the lemma's hypotheses
are law-level (a probability bound, two independence statements and translation invariance
of the joint law), all invariant under modifying the event field on a null set, while the
three clauses are sample-wise; the conjunction is therefore false (machine-checked in
`Section9ChemicalRefutation`).  The manuscript's minimal scales `L_cross(z)`, `H_perc(z)`
are random variables that are finite almost surely, and the three clauses are asserted
where they are finite — that is, almost surely.

This file splits the sample-wise part off as `FiniteRangePercolationGeometryAt` and records
the almost-sure carrier `AEFiniteRangePercolationGeometry`, which is what the proposed
version 2 of the anchor uses.  The positivity `0 < c` of the crossing density is a
constant, not a sample-wise assertion, and stays outside the almost-sure quantifier.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

open MeasureTheory Set

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-- The sample-wise part of `FiniteRangePercolationGeometry`: the three geometric clauses
at the single sample `ω`.
-/
def FiniteRangePercolationGeometryAt (E : ℕ → Lattice d → Set Ω)
    (Cbox J : ℕ) (c C q : ℝ)
    (crossing component : Lattice d → Ω → ℕ) (ω : Ω) : Prop :=
  ∀ z,
    (∀ l : ℕ, crossing z ω ≤ l →
      ∀ path : List (Lattice d), IsJStepListPath J path →
      (∃ v ∈ path, InLatticeBallReal z v (l / 3 : ℝ)) →
      (∃ v ∈ path, ¬InLatticeBallReal z v (2 * l / 3 : ℝ)) →
      ∃ chosen : List (Lattice d),
        chosen.Sublist path ∧ c * l ≤ chosen.length ∧
          (∀ v ∈ chosen,
            IsPercolationGoodSite E Cbox ω v ∧
              latticeBallSet v Cbox ⊆
                latticeBallSet z (3 * l / 4 : ℝ) \ latticeBallSet z (l / 4 : ℝ)) ∧
          chosen.Pairwise fun v w ↦
            Disjoint (latticeBallSet v Cbox) (latticeBallSet w Cbox)) ∧
    (∀ s : ℝ, 0 ≤ s → ∀ v : Lattice d,
      InLatticeBallReal z v s → ¬IsPercolationGoodSite E Cbox ω v →
      HasLatticeDiameterAtMost
        (jStepComponent J {u | ¬IsPercolationGoodSite E Cbox ω u} v)
        (C * (1 + component z ω + q⁻¹ * Real.log (2 + s)) ^ 2)) ∧
    (∀ l : ℕ, Real.exp (C * component z ω) ≤ l →
      ∀ v w : Lattice d,
      InLatticeBallReal z v l → InLatticeBallReal z w l →
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω (l / 10 : ℝ) v →
      InGoodComponentOfDiameterAtLeast E Cbox 1 ω (l / 10 : ℝ) w →
      ∃ path : List (Lattice d),
        path.head? = some v ∧ path.getLast? = some w ∧
          path.length ≤ C * l ∧ IsJStepListPath 1 path ∧
            ∀ u ∈ path, IsPercolationGoodSite E Cbox ω u)

/-- The sample-wise split of `FiniteRangePercolationGeometry` is definitional. -/
theorem finiteRangePercolationGeometry_iff (E : ℕ → Lattice d → Set Ω)
    (Cbox J : ℕ) (c C q : ℝ) (crossing component : Lattice d → Ω → ℕ) :
    FiniteRangePercolationGeometry E Cbox J c C q crossing component ↔
      0 < c ∧ ∀ ω, FiniteRangePercolationGeometryAt E Cbox J c C q crossing component ω :=
  Iff.rfl

/-- **The almost-sure multiscale percolation geometry.**  The crossing density `c` is
positive, and the three geometric clauses hold at almost every sample.

This is the carrier of version 2 of `SubdiffusiveProcess.Section9.weighted_multiscale_percolation`. -/
def AEFiniteRangePercolationGeometry [MeasurableSpace Ω] (mu : Measure Ω)
    (E : ℕ → Lattice d → Set Ω) (Cbox J : ℕ) (c C q : ℝ)
    (crossing component : Lattice d → Ω → ℕ) : Prop :=
  0 < c ∧
    ∀ᵐ ω ∂mu, FiniteRangePercolationGeometryAt E Cbox J c C q crossing component ω

/-- The sample-wise geometry implies the almost-sure geometry. -/
theorem aeFiniteRangePercolationGeometry_of_finiteRangePercolationGeometry
    [MeasurableSpace Ω] {mu : Measure Ω} {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ}
    {c C q : ℝ} {crossing component : Lattice d → Ω → ℕ}
    (h : FiniteRangePercolationGeometry E Cbox J c C q crossing component) :
    AEFiniteRangePercolationGeometry mu E Cbox J c C q crossing component :=
  ⟨h.1, Filter.Eventually.of_forall h.2⟩

/-- The almost-sure geometry is stable under modifying the witnesses on a null set. -/
theorem AEFiniteRangePercolationGeometry.congr_ae
    [MeasurableSpace Ω] {mu : Measure Ω} {E : ℕ → Lattice d → Set Ω} {Cbox J : ℕ}
    {c C q : ℝ} {crossing component crossing' component' : Lattice d → Ω → ℕ}
    (h : AEFiniteRangePercolationGeometry mu E Cbox J c C q crossing component)
    (hcr : ∀ᵐ ω ∂mu, ∀ z, crossing' z ω = crossing z ω)
    (hco : ∀ᵐ ω ∂mu, ∀ z, component' z ω = component z ω) :
    AEFiniteRangePercolationGeometry mu E Cbox J c C q crossing' component' := by
  refine ⟨h.1, ?_⟩
  filter_upwards [h.2, hcr, hco] with ω hω hcrω hcoω
  intro z
  rw [hcrω z, hcoω z]
  exact hω z

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
