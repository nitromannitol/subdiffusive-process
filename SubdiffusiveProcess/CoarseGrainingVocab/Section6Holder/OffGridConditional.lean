module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder.OffGridTransfer

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

/-- The dimension-only outer-window loss in the Step-7 off-grid sandwich. -/
noncomputable def holderOffGridOuterFactor (d : ℕ) : ℝ :=
  3 * Real.sqrt (27 ^ d)

/-- The dimension-only normalized-oscillation loss in the Step-7 sandwich. -/
noncomputable def holderOffGridOscillationFactor (d : ℕ) : ℝ :=
  Real.sqrt (27 ^ d)

theorem holderOffGridOuterFactor_pos (d : ℕ) :
    0 < holderOffGridOuterFactor d := by
  unfold holderOffGridOuterFactor
  positivity

theorem holderOffGridOscillationFactor_pos (d : ℕ) :
    0 < holderOffGridOscillationFactor d := by
  unfold holderOffGridOscillationFactor
  positivity

/-- Complete long-gap off-grid transfer with the geometric factors prepaid.

If the grid-centred estimate uses coefficients `a/K²`, `b/(K Kosc)`, and
`c/K`, where `K` and `Kosc` are the two dimension-only window losses, then
the arbitrary-centre conclusion has the literal coefficients `a`, `b`, and
`c`.  This is the exact downstream interface used by the final Step-7
assembly. -/
theorem exists_holderOffGridExcessTransfer_scaled
    {d m n ell : ℕ} {x : Vec d} {u : Vec d → ℝ} {a b c : ℝ}
    (hx : x ∈ cube d m) (hnell : n + 2 < ell) (hellm : ell ≤ m)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m ell x)))
    (hgrid : ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
      truncatedCube d m n x ⊆ truncatedCube d m (n + 1) z →
      truncatedCube d m ((ell : ℤ) - 1) z ⊆ truncatedCube d m ell x →
      excess (n + 1) (truncatedCube d m (n + 1) z) u ≤
        (a / holderOffGridOuterFactor d ^ 2) *
            excess ((ell : ℤ) - 1)
              (truncatedCube d m ((ell : ℤ) - 1) z) u +
          (b / (holderOffGridOuterFactor d *
              holderOffGridOscillationFactor d)) *
            normalizedL2On (truncatedCube d m ((ell : ℤ) - 1) z)
              (fun y ↦ u y -
                averageOn (truncatedCube d m ((ell : ℤ) - 1) z) u) +
          c / holderOffGridOuterFactor d) :
    ∃ z : Vec d, OnTriadicGrid n z ∧ z ∈ cube d m ∧
      excess n (truncatedCube d m n x) u ≤
        a * excess ell (truncatedCube d m ell x) u +
          b * normalizedL2On (truncatedCube d m ell x)
            (fun y ↦ u y - averageOn (truncatedCube d m ell x) u) + c := by
  let K := holderOffGridOuterFactor d
  let Kosc := holderOffGridOscillationFactor d
  have hK : 0 < K := holderOffGridOuterFactor_pos d
  have hKosc : 0 < Kosc := holderOffGridOscillationFactor_pos d
  have hA : 0 ≤ a / K ^ 2 := div_nonneg ha (sq_nonneg K)
  have hB : 0 ≤ b / (K * Kosc) := div_nonneg hb (mul_nonneg hK.le hKosc.le)
  obtain ⟨z, hzgrid, hz, hraw⟩ := exists_holderOffGridExcessTransfer
    hx hnell hellm hA hB hu (by
      intro z hzgrid hz hsubN hsubEll
      simpa only [K, Kosc] using hgrid z hzgrid hz hsubN hsubEll)
  dsimp only [K, Kosc] at hraw
  refine ⟨z, hzgrid, hz, hraw.trans_eq ?_⟩
  dsimp only [holderOffGridOuterFactor, holderOffGridOscillationFactor] at hraw ⊢
  have hKne : 3 * Real.sqrt (27 ^ d) ≠ 0 := by positivity
  have hKoscne : Real.sqrt (27 ^ d) ≠ 0 := by positivity
  field_simp [hKne, hKoscne]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
