import SubdiffusiveProcess.BesovComparison.Representatives

/-! The zero-dimensional endpoint present in the frozen declaration. -/
open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.BesovComparison

theorem overlap_const_zero {d : ℕ} (P : ExactOverlapFiniteParameters) (Q : TriadicCube d)
    (u : Vec d → ℝ) (c : ℝ) (hconst : ∀ x, u x = c) (hu : ExactOverlapIntegrable Q u) :
    exactOverlapFiniteSeminorm P Q u hu = 0 := by
  have hloc : ∀ (S : TriadicCube d) (p : ℝ≥0∞)
      (hS : Integrable u (ScalarOverlap.normalizedCubeMeasure S)),
      exactOverlapLocalOscillation S p u hS = 0 := by
    intro S p hS
    unfold exactOverlapLocalOscillation exactOverlapLocalMean
    have hmean : (∫ x : Vec d, u x ∂ScalarOverlap.normalizedCubeMeasure S) = c := by
      simp_rw [hconst]
      simp [integral_const, measureReal_def]
    rw [hmean]
    simp [hconst]
  have hp : 0 < P.p := zero_lt_one.trans_le P.p_one_le
  have hq : 0 < P.q := zero_lt_one.trans_le P.q_one_le
  unfold exactOverlapFiniteSeminorm exactOverlapDepthTerm exactOverlapDepthAverage
  simp [hloc, ENNReal.zero_rpow_of_pos hp, ENNReal.zero_rpow_of_pos (inv_pos.mpr hp),
    ENNReal.zero_rpow_of_pos hq, ENNReal.zero_rpow_of_pos (inv_pos.mpr hq)]

theorem besov_zero_dimension (m : ℤ) (s p : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hp : 1 ≤ p) (u : Vec 0 → ℝ)
    (hu : MemLp u (ENNReal.ofReal p) (volume.restrict (cube 0 m))) :
    besov 0 m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u = 0 := by
  let P : ExactOverlapFiniteParameters := ⟨s,p,p,hs,hs1,hp,hp⟩
  have hp' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  let hi := overlapIntegrableOfMemLp _ _ hp' u (memLp_normalized_root m _ u hu)
  rw [besov_eq_overlap m s p (zero_le_one.trans hp) P rfl rfl rfl u hi]
  have hconst : ∀ x : Vec 0, u x = u 0 := by
    intro x; exact congrArg u (Subsingleton.elim x 0)
  rw [overlap_const_zero P _ u (u 0) hconst hi, mul_zero]

theorem wsp_zero_dimension (m : ℤ) (s p : ℝ) (hp : 0 < p) (u : Vec 0 → ℝ) :
    wsp 0 m s p u = 0 := by
  have hdiff : ∀ x y : Vec 0, u x - u y = 0 := by
    intro x y; rw [Subsingleton.elim x y, sub_self]
  simp [wsp, hdiff, Real.zero_rpow hp.ne', hp]

end SubdiffusiveProcess.BesovComparison
