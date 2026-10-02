import SubdiffusiveProcess.Geometry.BoundaryStep
open Set
namespace SubdiffusiveProcess
/-- Construct a finite trace of nearest-face activations and half-triadic radii. Every transition has its actual projected-ball containment, and termination occurs after at most the number of inactive coordinates. -/
theorem exists_finite_boundary_chain
    {d : ℕ} (x : SpatialCoordinates d)
    (hx : ∀ j : Fin d, |x j| < (1 / 2 : ℝ))
    (I P : Finset (Fin d)) (hP : ∀ j : Fin d, j ∈ P ↔ 0 ≤ x j)
    (m q : ℤ) (L : ℝ) (hL : 10 ≤ L) :
    let δ : Fin d → ℝ := fun j => (1 / 2 : ℝ) - |x j|
    let z : Finset (Fin d) → SpatialCoordinates d := fun J j =>
      if j ∈ J then (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j
    let Rstar : ℝ := (3 : ℝ) ^ m / 2
    ∃ n : ℕ, n ≤ d - I.card ∧
      ∃ J : ℕ → Finset (Fin d), ∃ k : ℕ → ℤ,
        J 0 = I ∧ k 0 = q ∧
        let s : ℕ → ℝ := fun j => (3 : ℝ) ^ (k j) / 2
        (Rstar / 24 ≤ s n ∨
          (8 * s n < Rstar ∧ ∀ i : Fin d, i ∉ J n → 4 * L * Rstar ≤ δ i)) ∧
        ∀ j : ℕ, j < n → s j < Rstar / 24 ∧
          ∃ i : Fin d, i ∉ J j ∧ J (j + 1) = insert i (J j) ∧
            (∀ i' : Fin d, i' ∉ J j → δ i ≤ δ i') ∧
            ((δ i ≤ 100 * L * s j ∧ s j + δ i ≤ s (j + 1) ∧
              s (j + 1) < 3 * (1 + 100 * L) * s j ∧
              Metric.ball (z (J j)) (s j) ⊆ Metric.ball (z (J (j + 1))) (s (j + 1))) ∨
            (∃ a : ℤ, let R : ℝ := (3 : ℝ) ^ a / 2
              8 * s j < R ∧ R < Rstar ∧
              (∀ i' : Fin d, i' ∉ J j → 4 * L * R ≤ δ i') ∧
              L * R + δ i ≤ s (j + 1) ∧ s (j + 1) < 39 * L * R ∧
              Metric.ball (z (J j)) (L * R) ⊆ Metric.ball (z (J (j + 1))) (s (j + 1)))) := by
  classical
  dsimp only
  let δ : Fin d → ℝ := fun j => (1 / 2 : ℝ) - |x j|
  let z : Finset (Fin d) → SpatialCoordinates d := fun J j =>
    if j ∈ J then (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j
  let Rstar : ℝ := (3 : ℝ) ^ m / 2
  have hspos : ∀ a : ℤ, 0 < (3 : ℝ) ^ a / 2 := fun a =>
    div_pos (zpow_pos (by norm_num) a) (by norm_num)
  have aux : ∀ r : ℕ, ∀ (I : Finset (Fin d)) (q : ℤ), d - I.card = r →
      ∃ n : ℕ, n ≤ r ∧
        ∃ J : ℕ → Finset (Fin d), ∃ k : ℕ → ℤ,
          J 0 = I ∧ k 0 = q ∧
          let s : ℕ → ℝ := fun j => (3 : ℝ) ^ (k j) / 2
          (Rstar / 24 ≤ s n ∨
            (8 * s n < Rstar ∧ ∀ i : Fin d, i ∉ J n → 4 * L * Rstar ≤ δ i)) ∧
          ∀ j : ℕ, j < n → s j < Rstar / 24 ∧
            ∃ i : Fin d, i ∉ J j ∧ J (j + 1) = insert i (J j) ∧
              (∀ i' : Fin d, i' ∉ J j → δ i ≤ δ i') ∧
              ((δ i ≤ 100 * L * s j ∧ s j + δ i ≤ s (j + 1) ∧
                s (j + 1) < 3 * (1 + 100 * L) * s j ∧
                Metric.ball (z (J j)) (s j) ⊆ Metric.ball (z (J (j + 1))) (s (j + 1))) ∨
              (∃ a : ℤ, let R : ℝ := (3 : ℝ) ^ a / 2
                8 * s j < R ∧ R < Rstar ∧
                (∀ i' : Fin d, i' ∉ J j → 4 * L * R ≤ δ i') ∧
                L * R + δ i ≤ s (j + 1) ∧ s (j + 1) < 39 * L * R ∧
                Metric.ball (z (J j)) (L * R) ⊆ Metric.ball (z (J (j + 1))) (s (j + 1)))) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ihr =>
      intro I q hr
      let s0 : ℝ := (3 : ℝ) ^ q / 2
      by_cases hlarge : Rstar / 24 ≤ s0
      · refine ⟨0, Nat.zero_le _, fun _ => I, fun _ => q, rfl, rfl, ?_, ?_⟩
        · exact Or.inl hlarge
        · intro j hj
          omega
      · have hsmall : s0 < Rstar / 24 := lt_of_not_ge hlarge
        have hstep := boundary_step_or_terminal x hx I P hP m L s0 hL (hspos q)
        dsimp only at hstep
        rcases hstep with hlarge' | hterminal | hactivate
        · exact (False.elim (hlarge hlarge'))
        · refine ⟨0, Nat.zero_le _, fun _ => I, fun _ => q, rfl, rfl, ?_, ?_⟩
          · exact Or.inr hterminal
          · intro j hj
            omega
        · obtain ⟨i, hi, hnearest, q', htransition⟩ := hactivate
          have hcardI : I.card ≤ d := by
            simpa using Finset.card_le_univ I
          have hcard : (insert i I).card = I.card + 1 :=
            Finset.card_insert_of_notMem hi
          have hcardInsert : (insert i I).card ≤ d := by
            simpa using Finset.card_le_univ (insert i I)
          have hrpos : 0 < r := by
            rw [← hr, Nat.sub_pos_iff_lt]
            omega
          have hrem : d - (insert i I).card = r - 1 := by
            omega
          obtain ⟨n, hn, J, k, hJ0, hk0, hterm, hsteps⟩ :=
            ihr (r - 1) (by omega) (insert i I) q' hrem
          let J' : ℕ → Finset (Fin d)
            | 0 => I
            | t + 1 => J t
          let k' : ℕ → ℤ
            | 0 => q
            | t + 1 => k t
          refine ⟨n + 1, ?_, J', k', rfl, rfl, ?_, ?_⟩
          · omega
          · simpa [J', k'] using hterm
          · intro j hj
            cases j with
            | zero =>
                refine ⟨hsmall, i, ?_, ?_, ?_, ?_⟩
                · simpa [J'] using hi
                · simpa [J'] using hJ0
                · change ∀ i' : Fin d, i' ∉ I → δ i ≤ δ i'
                  exact hnearest
                · simpa only [J', k', Nat.zero_add, hJ0, hk0, δ, z, Rstar, s0]
                    using htransition
            | succ j =>
                have hjn : j < n := by omega
                simpa [J', k', Nat.succ_eq_add_one] using hsteps j hjn
  simpa [δ, z, Rstar] using aux (d - I.card) I q rfl

end SubdiffusiveProcess
