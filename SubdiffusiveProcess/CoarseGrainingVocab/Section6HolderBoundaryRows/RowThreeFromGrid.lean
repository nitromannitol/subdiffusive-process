import SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows.RowThreeShort

/-!
# Boundary Holder row three from its long grid estimate

This isolates the only analytic residue of the datum-bearing third row.  The
short branch and the off-grid transfer are discharged here; the input is the
normalized long grid estimate produced by the stopped excess recurrence.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The complete datum-bearing third row, conditional only on the normalized
long grid estimate. -/
theorem boundaryRowThree_of_grid {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (C alpha : ℝ) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (m X : ℕ)
    (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
    (hC : Real.sqrt 3 * (9 : ℝ) ^ (d + 1) ≤ C)
    (halpha : alpha ≤ 1) (hX : 0 < X)
    (hg : MemHolder (cube d m) (1 / 2) g)
    (hh : MemHolder (cube d m) (1 / 2) h.grad)
    (hgrid :
      ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
        (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
        ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → n + 2 < ell →
        ∀ x ∈ cube d m, ∀ z : Vec d, OnTriadicGrid n z → z ∈ cube d m →
        truncatedCube d m n x ⊆ truncatedCube d m (n + 1) z →
        truncatedCube d m ((ell : ℤ) - 1) z ⊆ truncatedCube d m ell x →
          excess (n + 1) (truncatedCube d m (n + 1) z) u.toFun ≤
            (C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) /
                holderOffGridOuterFactor d ^ 2) *
              excess ((ell : ℤ) - 1)
                (truncatedCube d m ((ell : ℤ) - 1) z) u.toFun +
            (C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) /
                (holderOffGridOuterFactor d * holderOffGridOscillationFactor d)) *
              normalizedL2On (truncatedCube d m ((ell : ℤ) - 1) z)
                (fun y ↦ u.toFun y -
                  averageOn (truncatedCube d m ((ell : ℤ) - 1) z) u.toFun) +
            (C * (tailAverage M L m omega (cube d m))⁻¹ *
                (3 : ℝ) ^ ((ell : ℝ) / 2) *
                holderSeminormOn (cube d m) (1 / 2) g +
              (if x ∈ cube d (m - 1) then 0 else
                C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
                    vectorSupNormOn (cube d m) h.grad +
                  (3 : ℝ) ^ ((ell : ℝ) / 2) *
                    fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                      (1 / 2) h.grad))) /
                holderOffGridOuterFactor d) :
    ∀ n : ℕ, (X : ℤ) ≤ (m : ℤ) - (n : ℤ) →
      (m : ℝ) - (n : ℝ) ≤ (1 - alpha)⁻¹ →
      ∀ ell : ℕ, n ≤ ell → ell + 5 ≤ m → ∀ x ∈ cube d m,
        excess n (truncatedCube d m n x) u.toFun ≤
          C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) *
              excess ell (truncatedCube d m ell x) u.toFun +
            C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) *
              normalizedL2On (truncatedCube d m ell x)
                (fun z ↦ u.toFun z - averageOn (truncatedCube d m ell x) u.toFun) +
            C * (tailAverage M L m omega (cube d m))⁻¹ *
              (3 : ℝ) ^ ((ell : ℝ) / 2) *
              holderSeminormOn (cube d m) (1 / 2) g +
            (if x ∈ cube d (m - 1) then 0 else
              C * ((1 - alpha) * ((m : ℝ) - (n : ℝ)) *
                  vectorSupNormOn (cube d m) h.grad +
                (3 : ℝ) ^ ((ell : ℝ) / 2) *
                  fractionalInfinityNormOnReal (cube d m) ((3 : ℝ) ^ m)
                    (1 / 2) h.grad)) := by
  have hC0 : 0 ≤ C := le_trans (by positivity) hC
  intro n hn hwindow ell hnell hellm x hx
  by_cases hlong : n + 2 < ell
  · have ha : 0 ≤ C * (3 : ℝ) ^ (-((ell : ℝ) - (n : ℝ)) / 4) := by
      positivity
    have hb : 0 ≤ C * Real.sqrt (1 - alpha) * (3 : ℝ) ^ (-(ell : ℝ)) := by
      exact mul_nonneg (mul_nonneg hC0 (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (by norm_num) _)
    have huWindow : MemLp u.toFun 2
        (volume.restrict (truncatedCube d m ell x)) :=
      u.memL2.mono_measure
        (Measure.restrict_mono (truncatedCube_subset_cube d m ell x) le_rfl)
    obtain ⟨_z, _hzgrid, _hz, hbound⟩ :=
      exists_holderOffGridExcessTransfer_scaled hx hlong (by omega) ha hb huWindow
        (by
          intro z hzgrid hz hsubN hsubEll
          exact hgrid n hn hwindow ell hnell hellm hlong x hx z hzgrid hz
            hsubN hsubEll)
    simpa only [add_assoc] using hbound
  · exact boundaryRowThree_short M C alpha L omega m X u h g hC halpha hX hg hh
      n hn hwindow ell hnell hellm (by omega) x hx

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBoundaryRows
