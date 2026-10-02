import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceDecayExterior




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- An `L²` function has exponential exterior `L²` decay once its cell
energies satisfy the source bound, local graph contraction, bounded sphere
growth, and the graph-distance cover.

This is the carrier-independent deterministic conclusion of the proof of
`l.whole.space.resolvent.estimates`, source lines 11683--11727. -/
theorem integral_sq_exterior_le_of_graph_cells
    (u : Vec d → ℝ) (hu : MemLp u 2 volume)
    (count : ℕ → ℕ)
    (cell : (j : ℕ) → Fin (count j) → Set (Vec d))
    (exterior : Set (Vec d)) {A theta : ℝ} (N D : ℕ) {rate : ℝ}
    (hA : 0 ≤ A) (htheta : 0 < theta) (hD : 0 < D)
    (heffective : (D : ℝ) * theta < 1)
    (hsource : ∀ i : Fin (count 0),
      ∫ x in cell 0 i, u x ^ 2 ∂volume ≤ A)
    (hstep : ∀ (j : ℕ) (i : Fin (count j)), 0 < j →
      ∃ p : Σ k : ℕ, Fin (count k),
        j ≤ p.1 + 1 ∧
        ∫ x in cell j i, u x ^ 2 ∂volume ≤
          theta * ∫ x in cell p.1 p.2, u x ^ 2 ∂volume)
    (hcard : ∀ j, count j ≤ N * D ^ j)
    (hcover : exterior ⊆
      ⋃ p : Σ k : ℕ, Fin (count (⌈rate⌉₊ + k)),
        cell (⌈rate⌉₊ + p.1) p.2) :
    ∫ x in exterior, u x ^ 2 ∂volume ≤
      (N : ℝ) * A * (1 - (D : ℝ) * theta)⁻¹ *
        Real.exp (Real.log ((D : ℝ) * theta) * rate) := by
  let Cell := Σ j : ℕ, Fin (count j)
  let mass : Cell → ℝ := fun p ↦
    ∫ x in cell p.1 p.2, u x ^ 2 ∂volume
  let level : Cell → ℕ := fun p ↦ p.1
  let B : ℝ := ∫ x, u x ^ 2 ∂volume
  have hB : 0 ≤ B := integral_nonneg fun x ↦ sq_nonneg (u x)
  have hmassB : ∀ Q, mass Q ≤ B := by
    intro Q
    exact setIntegral_le_integral hu.integrable_sq
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg (u x))
  have hsource' : ∀ Q, level Q = 0 → mass Q ≤ A := by
    rintro ⟨j, i⟩ hj
    change j = 0 at hj
    subst j
    exact hsource i
  have hstep' : ∀ Q, 0 < level Q →
      ∃ Q', level Q ≤ level Q' + 1 ∧ mass Q ≤ theta * mass Q' := by
    rintro ⟨j, i⟩ hj
    exact hstep j i hj
  have hDone : (1 : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hD))
  have hthetaOne : theta < 1 := by
    calc
      theta = 1 * theta := by rw [one_mul]
      _ ≤ (D : ℝ) * theta := mul_le_mul_of_nonneg_right hDone htheta.le
      _ < 1 := heffective
  have hpoint : ∀ Q, mass Q ≤ theta ^ level Q * A :=
    cell_mass_le_geometric_of_step mass level hA hB htheta.le hthetaOne
      hmassB hsource' hstep'
  have hshell : ∀ j,
      ∑ i : Fin (count j), ∫ x in cell j i, u x ^ 2 ∂volume ≤
        (N : ℝ) * A * ((D : ℝ) * theta) ^ j := by
    intro j
    apply sum_cell_mass_le_geometric_of_card
      (Finset.univ : Finset (Fin (count j)))
      (fun i ↦ mass ⟨j, i⟩) (fun _i ↦ j) j N D hA htheta.le
    · intro i
      exact hpoint ⟨j, i⟩
    · intro _i _hi
      rfl
    · simpa only [Finset.card_univ, Fintype.card_fin] using hcard j
  have heffectivePos : 0 < (D : ℝ) * theta := by
    exact mul_pos (by exact_mod_cast hD) htheta
  exact integral_sq_exterior_le_exp_of_real_shell hu count cell exterior
    (mul_nonneg (Nat.cast_nonneg N) hA) heffectivePos heffective hcover hshell

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
