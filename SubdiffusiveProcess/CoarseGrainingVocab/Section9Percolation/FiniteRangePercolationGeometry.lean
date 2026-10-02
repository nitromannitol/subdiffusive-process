import SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation.FiniteRangePercolation

/-!
# Source-shaped multiscale percolation geometry

The proposed `PercolationGeometry` in the Section 9 freeze dossier omits the connectedness
and meeting hypotheses for bad components and the large-component hypotheses for good
endpoints. This file records those notions explicitly and assembles the literal three-part
geometric conclusion. It does not assert the probabilistic renormalization theorem.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation

open Set

noncomputable section

variable {d : ℕ} {Ω : Type*}



def IsJStepListPath (J : ℕ) (path : List (Lattice d)) : Prop :=
  ∀ k : ℕ, k + 1 < path.length → latticeDist path[k]! path[k + 1]! ≤ J



def JStepReachableIn (J : ℕ) (S : Set (Lattice d)) (v w : Lattice d) : Prop :=
  ∃ path : List (Lattice d),
    path.head? = some v ∧ path.getLast? = some w ∧
      IsJStepListPath J path ∧ ∀ u ∈ path, u ∈ S



def jStepComponent (J : ℕ) (S : Set (Lattice d)) (v : Lattice d) :
    Set (Lattice d) :=
  {w | JStepReachableIn J S v w}



def InLatticeBallReal (z v : Lattice d) (R : ℝ) : Prop :=
  ∀ i : Fin d, |(v i - z i : ℤ)| ≤ R



def latticeBallSet (z : Lattice d) (R : ℝ) : Set (Lattice d) :=
  {v | InLatticeBallReal z v R}



def HasLatticeDiameterAtMost (S : Set (Lattice d)) (R : ℝ) : Prop :=
  ∀ v ∈ S, ∀ w ∈ S, ∀ i : Fin d, |(v i - w i : ℤ)| ≤ R



def InGoodComponentOfDiameterAtLeast (E : ℕ → Lattice d → Set Ω)
    (C J : ℕ) (ω : Ω) (R : ℝ) (v : Lattice d) : Prop :=
  IsPercolationGoodSite E C ω v ∧
    ∃ u w : Lattice d,
      JStepReachableIn J {z | IsPercolationGoodSite E C ω z} v u ∧
        JStepReachableIn J {z | IsPercolationGoodSite E C ω z} v w ∧
          R ≤ latticeDist u w



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
