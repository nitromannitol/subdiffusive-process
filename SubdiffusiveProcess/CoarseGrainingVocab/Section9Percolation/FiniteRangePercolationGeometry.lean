module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolation

@[expose] public section

/-!
# Source-shaped multiscale percolation geometry

The `PercolationGeometry` proposed for Section 9 omits the connectedness
and meeting hypotheses for bad components and the large-component hypotheses for good
endpoints. This file records those notions explicitly and assembles the literal three-part
geometric conclusion. It does not assert the probabilistic renormalization theorem.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

open Set

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-- A finite list whose consecutive vertices are at lattice distance at most `J`.

-/
def IsJStepListPath (J : ℕ) (path : List (Lattice d)) : Prop :=
  ∀ k : ℕ, k + 1 < path.length → latticeDist path[k]! path[k + 1]! ≤ J

/-- Two sites are connected inside `S` by a finite `J`-step path.

-/
def JStepReachableIn (J : ℕ) (S : Set (Lattice d)) (v w : Lattice d) : Prop :=
  ∃ path : List (Lattice d),
    path.head? = some v ∧ path.getLast? = some w ∧
      IsJStepListPath J path ∧ ∀ u ∈ path, u ∈ S

/-- The `J`-step component of `v` in `S`, expressed through finite paths.

-/
def jStepComponent (J : ℕ) (S : Set (Lattice d)) (v : Lattice d) :
    Set (Lattice d) :=
  {w | JStepReachableIn J S v w}

/-- Membership in a real-radius closed lattice ball for the `ℓ∞` convention.

-/
def InLatticeBallReal (z v : Lattice d) (R : ℝ) : Prop :=
  ∀ i : Fin d, |(v i - z i : ℤ)| ≤ R

/-- The real-radius closed lattice ball as a set.

-/
def latticeBallSet (z : Lattice d) (R : ℝ) : Set (Lattice d) :=
  {v | InLatticeBallReal z v R}

/-- A set has `ℓ∞` diameter at most `R`.

-/
def HasLatticeDiameterAtMost (S : Set (Lattice d)) (R : ℝ) : Prop :=
  ∀ v ∈ S, ∀ w ∈ S, ∀ i : Fin d, |(v i - w i : ℤ)| ≤ R

/-- The good component containing `v` has `ℓ∞` diameter at least `R`.

-/
def InGoodComponentOfDiameterAtLeast (E : ℕ → Lattice d → Set Ω)
    (C J : ℕ) (ω : Ω) (R : ℝ) (v : Lattice d) : Prop :=
  IsPercolationGoodSite E C ω v ∧
    ∃ u w : Lattice d,
      JStepReachableIn J {z | IsPercolationGoodSite E C ω z} v u ∧
        JStepReachableIn J {z | IsPercolationGoodSite E C ω z} v w ∧
          R ≤ latticeDist u w

/-- The three geometric conclusions in the source multiscale-percolation lemma.

Unlike the earlier proposed carrier, the bad-component clause refers to the actual
`J`-step component meeting the prescribed ball, the good-path clause requires both endpoints
to lie in large nearest-neighbor good components, and the crossing coefficient is positive.

-/
def FiniteRangePercolationGeometry (E : ℕ → Lattice d → Set Ω)
    (Cbox J : ℕ) (c C q : ℝ)
    (crossing component : Lattice d → Ω → ℕ) : Prop :=
  0 < c ∧ ∀ ω z,
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

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
