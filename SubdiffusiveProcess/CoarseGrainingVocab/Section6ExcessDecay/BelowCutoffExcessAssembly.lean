module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffBoundaryExcess
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.BelowCutoffInteriorExcess
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodScaleIteration

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The complete source-shaped cutoff boundary excess-decay package follows
from its matching cutoff harmonic package. -/
theorem belowCutoffHolderExcessDecay_of_harmonic (d : ℕ)
    (hharm : BoundaryCutoffHarmonicApproximationInputV6 d) :
    BoundaryCutoffHolderExcessDecayInputV4 d := by
  unfold BoundaryCutoffHolderExcessDecayInputV4
  have hcap : BelowCutoffMathcalECapInput d :=
    belowCutoffMathcalECapInput_holds d
  obtain ⟨C₁, hC₁, hinterior⟩ :=
    belowCutoffInteriorExcessDecay_of_harmonic_and_cap d hharm hcap
  obtain ⟨C₂, hC₂, hboundary⟩ :=
    belowCutoffBoundaryExcessDecay_of_harmonic_and_cap d hharm hcap
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left C₁ C₂), ?_⟩
  intro M s hs epsilon hepsilon k hk L m n hkn hnm x hx z hz hxz omega
    u h g hsolution hg hholder ell hell
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hs0 : 0 < s :=
    (mul_pos (by norm_num : (0 : ℝ) < 512) (pow_pos hdelta 2)).trans_le hs.1
  have hepsilon0 : 0 ≤ epsilon :=
    le_trans
      (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr hs0.le))
        (sq_nonneg M.delta))
      hepsilon.1
  have hholderWindow : MemHolder (truncatedCube d m n x) (1 / 2) h.grad :=
    memHolder_mono hholder (truncatedCube_subset_cube d m n x)
  have hE : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u.toFun :=
    excess_nonneg _ _ _
  have ha : 0 ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hb : 0 ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
    Real.rpow_nonneg (by norm_num) _
  have hss : 0 ≤ s ^ (-2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hErr : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) omega z :=
    ENNReal.toReal_nonneg
  have hSl : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
  have hJ : 0 ≤
      (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
        s ^ (-3 / 2 : ℝ) *
          Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
      else 0) := by
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.sqrt_nonneg _)
    · exact le_rfl
  have hsourceWeight : 0 ≤ s ^ (-8 : ℝ) := Real.rpow_nonneg hs0.le _
  have hTinv : 0 ≤
      (tailAverage M L (n + 2) omega (translatedCube d (n + 2) z))⁻¹ :=
    inv_nonneg.mpr (tailAverage_nonneg M L (n + 2) omega _)
  have hscaleWeight : 0 ≤ (3 : ℝ) ^ (s * n) :=
    Real.rpow_nonneg (by norm_num) _
  have hFg : 0 ≤
      (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
    ENNReal.toReal_nonneg
  have hholderWeight : 0 ≤ s ^ (-7 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
  have hholderScale : 0 ≤ (3 : ℝ) ^ ((n : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hHh : 0 ≤ holderSeminormOn
      (truncatedCube d m n x) (1 / 2) h.grad :=
    holderSeminormOn_nonneg hholderWindow
  by_cases hgate : translatedCube d ((n : ℤ) - 4) x ⊆ cube d m
  · exact excess_decay_rhs_mono (le_max_left C₁ C₂) hE ha hb hss hepsilon0
      hErr hSl hJ hsourceWeight hTinv hscaleWeight hFg hholderWeight
      hholderScale hHh
      (hinterior M s hs epsilon hepsilon k hk L m n hkn hnm x hx z hz hxz
        hgate omega u h g hsolution hg hholder ell hell)
  · exact excess_decay_rhs_mono (le_max_right C₁ C₂) hE ha hb hss hepsilon0
      hErr hSl hJ hsourceWeight hTinv hscaleWeight hFg hholderWeight
      hholderScale hHh
      (hboundary M s hs epsilon hepsilon k hk L m n hkn hnm x hx z hz hxz
        hgate omega u h g hsolution hg hholder ell hell)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
