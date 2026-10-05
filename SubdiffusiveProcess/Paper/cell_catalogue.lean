module

public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments Set TopologicalSpace

namespace SubdiffusiveProcess.Paper
noncomputable section



def cell_catalogue (d : ℕ) (Enl Cmp : Type) [Fintype Enl] [Fintype Cmp]
    (cellOf : ℕ → (Fin d → ℝ) → Set (SpatialCoordinates d))
    (enlOf : ℕ → (Fin d → ℝ) → Enl → Set (SpatialCoordinates d))
    (cmpOf : ℕ → (Fin d → ℝ) → Cmp → Set (SpatialCoordinates d))
    (self : Enl) (chosen : ℕ → (Fin d → ℝ) → Cmp) : Prop :=
  ∃ (eps lam : ℝ) (_k0 : ℕ)
    (factor : Enl → ℕ)
    (shifts : Finset (SpatialCoordinates d))
    (roots : ℕ → SpatialCoordinates d → Enl → Finset (SpatialCoordinates d))
    (Cd : ℝ)
    (centres : ℕ → SpatialCoordinates d → Enl → ℕ → Finset (SpatialCoordinates d))
    (catalogue : ℕ → SpatialCoordinates d → Set (Set (SpatialCoordinates d))),
    let side : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(k : ℝ))
    let bigSide : ℕ → Enl → ℝ := fun k e => side k * (3 : ℝ) ^ (factor e)
    let shiftedCentre : ℕ → SpatialCoordinates d → Enl → SpatialCoordinates d →
        SpatialCoordinates d := fun k z e t => z + bigSide k e • t
    (0 < eps ∧ eps < 1) ∧
    (0 < lam ∧ lam < 1) ∧
    factor self = 0 ∧
    (0 : SpatialCoordinates d) ∈ shifts ∧
    0 < Cd ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d) (e : Enl),
      ((roots k z e).card : ℝ) ≤ Cd) ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d),
      cellOf k z = Metric.ball z (side k / 2)) ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d) (e : Enl),
      enlOf k z e = Metric.ball z (bigSide k e / 2)) ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d) (c : Cmp),
      cmpOf k z c ∈ catalogue k z ∧ ∃ e : Enl, cmpOf k z c ⊆ enlOf k z e) ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d),
      cmpOf k z (chosen k z) ∈ catalogue k z ∧
        ∃ e : Enl, cmpOf k z (chosen k z) ⊆ enlOf k z e) ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d) (V : Set (SpatialCoordinates d)),
      V ∈ catalogue k z ↔
        ∃ (e : Enl) (t : SpatialCoordinates d), t ∈ shifts ∧
          ∃ (D : ℕ) (word : Fin D → OddGridIndex d 1),
            V = Metric.ball
              (descendantCenter 1 (shiftedCentre k z e t) (bigSide k e) D word)
              (descendantSide 1 D (bigSide k e) / 2)) ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d) (e : Enl) (D : ℕ)
        (w : SpatialCoordinates d),
      w ∈ centres k z e D ↔
        w ∈ roots k z e ∨ ∃ word : Fin D → OddGridIndex d 1,
          w = descendantCenter 1 z (bigSide k e) D word) ∧
    (∀ (k : ℕ) (z : SpatialCoordinates d) (e : Enl) (D : ℕ),
      ((centres k z e D).card : ℝ) ≤ (Cd + 1) * (3 : ℝ) ^ ((d : ℝ) * (D : ℝ))) ∧
    (∀ (k : ℕ) (z : Fin d → ℝ), enlOf k z self = cellOf k z) ∧
    (∀ (k : ℕ) (z : Fin d → ℝ) (e : Enl), cellOf k z ⊆ enlOf k z e) ∧
    (∀ (k : ℕ) (z : Fin d → ℝ), cellOf (k + 1) z ⊆ cellOf k z)

end
end SubdiffusiveProcess.Paper
