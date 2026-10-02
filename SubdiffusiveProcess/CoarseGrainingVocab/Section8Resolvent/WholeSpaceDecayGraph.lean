import SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.FiniteRangeGreedySelection
import Mathlib.Analysis.SpecificLimits.Basic




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Values used to take the supremum beyond graph distance `n`.  Zero is
included so that the set is nonempty even when there are no cells at that
distance. -/
def wholeSpaceDecayTailSet {Cell : Type*} (mass : Cell → ℝ)
    (level : Cell → ℕ) (n : ℕ) : Set ℝ :=
  {x | x = 0 ∨ ∃ Q, n ≤ level Q ∧ x = mass Q}

/-- Supremum of the nonnegative cell masses at graph distance at least `n`. -/
def wholeSpaceDecayTailSup {Cell : Type*} (mass : Cell → ℝ)
    (level : Cell → ℕ) (n : ℕ) : ℝ :=
  sSup (wholeSpaceDecayTailSet mass level n)

private theorem wholeSpaceDecayTailSet_bddAbove {Cell : Type*}
    {mass : Cell → ℝ} {level : Cell → ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hmassB : ∀ Q, mass Q ≤ B) (n : ℕ) :
    BddAbove (wholeSpaceDecayTailSet mass level n) := by
  refine ⟨B, ?_⟩
  rintro x (rfl | ⟨Q, _hlevel, rfl⟩)
  · exact hB
  · exact hmassB Q

private theorem wholeSpaceDecayTailSup_nonneg {Cell : Type*}
    {mass : Cell → ℝ} {level : Cell → ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hmassB : ∀ Q, mass Q ≤ B) (n : ℕ) :
    0 ≤ wholeSpaceDecayTailSup mass level n := by
  apply le_csSup (wholeSpaceDecayTailSet_bddAbove hB hmassB n)
  exact Or.inl rfl

private theorem mass_le_wholeSpaceDecayTailSup {Cell : Type*}
    {mass : Cell → ℝ} {level : Cell → ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hmassB : ∀ Q, mass Q ≤ B)
    {n : ℕ} {Q : Cell} (hQ : n ≤ level Q) :
    mass Q ≤ wholeSpaceDecayTailSup mass level n := by
  apply le_csSup (wholeSpaceDecayTailSet_bddAbove hB hmassB n)
  exact Or.inr ⟨Q, hQ, rfl⟩

/-- Infinite-graph discrete maximum principle.

If every nonsource cell is controlled by `theta` times a cell whose graph
level can drop by at most one, then its mass is bounded by
`theta ^ level * A`.  The comparison cell may lie at the same or a larger
level; global boundedness and `theta < 1` rule out an escaping chain. -/
theorem cell_mass_le_geometric_of_step {Cell : Type*}
    (mass : Cell → ℝ) (level : Cell → ℕ) {A B theta : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (htheta : 0 ≤ theta)
    (hthetaOne : theta < 1)
    (hmassB : ∀ Q, mass Q ≤ B)
    (hsource : ∀ Q, level Q = 0 → mass Q ≤ A)
    (hstep : ∀ Q, 0 < level Q →
      ∃ Q', level Q ≤ level Q' + 1 ∧ mass Q ≤ theta * mass Q') :
    ∀ Q, mass Q ≤ theta ^ level Q * A := by
  have htailZero : wholeSpaceDecayTailSup mass level 0 ≤ A := by
    let S := wholeSpaceDecayTailSup mass level 0
    have hSnonneg : 0 ≤ S :=
      wholeSpaceDecayTailSup_nonneg hB hmassB 0
    have hSmax : S ≤ max A (theta * S) := by
      apply Real.sSup_le
      · intro x hx
        rcases hx with rfl | ⟨Q, _hlevel, rfl⟩
        · exact le_max_of_le_left hA
        · by_cases hQzero : level Q = 0
          · exact (hsource Q hQzero).trans (le_max_left _ _)
          · obtain ⟨Q', _hlevelStep, hmassStep⟩ :=
              hstep Q (Nat.pos_of_ne_zero hQzero)
            have hQ'tail : mass Q' ≤ S := by
              exact mass_le_wholeSpaceDecayTailSup hB hmassB (Nat.zero_le _)
            exact hmassStep.trans <|
              (mul_le_mul_of_nonneg_left hQ'tail htheta).trans (le_max_right _ _)
      · exact hA.trans (le_max_left _ _)
    by_cases hthetaS : theta * S ≤ A
    · simpa only [max_eq_left hthetaS] using hSmax
    · have hAThetaS : A ≤ theta * S := le_of_not_ge hthetaS
      have hSStep : S ≤ theta * S := by
        simpa only [max_eq_right hAThetaS] using hSmax
      nlinarith
  have htailStep : ∀ n,
      wholeSpaceDecayTailSup mass level (n + 1) ≤
        theta * wholeSpaceDecayTailSup mass level n := by
    intro n
    have htailNonneg :
        0 ≤ theta * wholeSpaceDecayTailSup mass level n :=
      mul_nonneg htheta (wholeSpaceDecayTailSup_nonneg hB hmassB n)
    apply Real.sSup_le
    · intro x hx
      rcases hx with rfl | ⟨Q, hQlevel, rfl⟩
      · exact htailNonneg
      · have hQpos : 0 < level Q := by omega
        obtain ⟨Q', hlevelStep, hmassStep⟩ := hstep Q hQpos
        have hnQ' : n ≤ level Q' := by omega
        exact hmassStep.trans <| mul_le_mul_of_nonneg_left
          (mass_le_wholeSpaceDecayTailSup hB hmassB hnQ') htheta
    · exact htailNonneg
  have htailPow : ∀ n,
      wholeSpaceDecayTailSup mass level n ≤ theta ^ n * A := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, one_mul] using htailZero
    | succ n ih =>
        calc
          wholeSpaceDecayTailSup mass level (n + 1) ≤
              theta * wholeSpaceDecayTailSup mass level n := htailStep n
          _ ≤ theta * (theta ^ n * A) :=
            mul_le_mul_of_nonneg_left ih htheta
          _ = theta ^ (n + 1) * A := by ring
  intro Q
  exact (mass_le_wholeSpaceDecayTailSup hB hmassB (le_refl (level Q))).trans
    (htailPow (level Q))

/-- Summing the pointwise graph decay over one finite graph sphere costs only
the cardinality of that sphere. -/
theorem sum_cell_mass_le_card_mul_geometric {Cell : Type*}
    (cells : Finset Cell) (mass : Cell → ℝ) (level : Cell → ℕ)
    (j : ℕ) {A theta : ℝ}
    (hmass : ∀ Q, mass Q ≤ theta ^ level Q * A)
    (hlevel : ∀ Q ∈ cells, level Q = j) :
    ∑ Q ∈ cells, mass Q ≤
      (cells.card : ℝ) * (theta ^ j * A) := by
  calc
    ∑ Q ∈ cells, mass Q ≤ ∑ _Q ∈ cells, theta ^ j * A := by
      apply Finset.sum_le_sum
      intro Q hQ
      simpa only [hlevel Q hQ] using hmass Q
    _ = (cells.card : ℝ) * (theta ^ j * A) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Bounded graph-sphere growth turns pointwise contraction into a shell
contraction.  The effective shell ratio is `D * theta`. -/
theorem sum_cell_mass_le_geometric_of_card {Cell : Type*}
    (cells : Finset Cell) (mass : Cell → ℝ) (level : Cell → ℕ)
    (j N D : ℕ) {A theta : ℝ}
    (hA : 0 ≤ A) (htheta : 0 ≤ theta)
    (hmass : ∀ Q, mass Q ≤ theta ^ level Q * A)
    (hlevel : ∀ Q ∈ cells, level Q = j)
    (hcard : cells.card ≤ N * D ^ j) :
    ∑ Q ∈ cells, mass Q ≤
      (N : ℝ) * A * ((D : ℝ) * theta) ^ j := by
  have hterm : 0 ≤ theta ^ j * A := mul_nonneg (pow_nonneg htheta _) hA
  calc
    ∑ Q ∈ cells, mass Q ≤
        (cells.card : ℝ) * (theta ^ j * A) :=
      sum_cell_mass_le_card_mul_geometric cells mass level j hmass hlevel
    _ ≤ ((N * D ^ j : ℕ) : ℝ) * (theta ^ j * A) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hterm
    _ = (N : ℝ) * A * ((D : ℝ) * theta) ^ j := by
      push_cast
      rw [mul_pow]
      ring



theorem sum_cell_mass_le_selected_card_mul_of_finiteRange_cover
    {Cell : Type*} [DecidableEq Cell]
    (candidates selected : Finset Cell) (Blocks : Cell → Cell → Prop)
    (D : ℕ) (mass : Cell → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hmass : ∀ Q ∈ candidates, mass Q ≤ M)
    (hcover : ∀ Q ∈ candidates, ∃ P ∈ selected, Blocks P Q)
    (hbounded : ∀ P ∈ selected,
      (candidates.filter (Blocks P)).card ≤ D) :
    ∑ Q ∈ candidates, mass Q ≤
      ((selected.card : ℝ) * (D : ℝ)) * M := by
  have hcard : candidates.card ≤ selected.card * D :=
    card_le_card_mul_of_covered_by_bounded_fibers
      candidates selected Blocks D hcover hbounded
  calc
    ∑ Q ∈ candidates, mass Q ≤ ∑ _Q ∈ candidates, M := by
      exact Finset.sum_le_sum fun Q hQ ↦ hmass Q hQ
    _ = (candidates.card : ℝ) * M := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((selected.card * D : ℕ) : ℝ) * M := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
    _ = ((selected.card : ℝ) * (D : ℝ)) * M := by
      rw [Nat.cast_mul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
