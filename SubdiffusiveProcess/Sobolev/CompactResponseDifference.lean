module

public import SubdiffusiveProcess.Sobolev.CompactResponses
@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The change in either actual compact-potential response is bounded by exp(distance)-1 times its original value; an arbitrary common potential cancels. -/
theorem compact_response_difference_le_original
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)]
    (L : S.space →L[ℝ] ℝ) (b : weakSobolevGraph Ω)
    (f g h : C(K, ℝ)) :
    |inverseResponse S (expPotentialCoefficient (compactPotentialToLp K (f + h))) L -
      inverseResponse S (expPotentialCoefficient (compactPotentialToLp K (g + h))) L| ≤
        (Real.exp (dist f g) - 1) *
          inverseResponse S (expPotentialCoefficient (compactPotentialToLp K (g + h))) L ∧
    |dirichletResponse S (expPotentialCoefficient (compactPotentialToLp K (f + h))) b -
      dirichletResponse S (expPotentialCoefficient (compactPotentialToLp K (g + h))) b| ≤
        (Real.exp (dist f g) - 1) *
          dirichletResponse S (expPotentialCoefficient (compactPotentialToLp K (g + h))) b := by
  have sharp_difference {a b E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hE : 1 ≤ E) (hab : a ≤ E * b) (hba : b ≤ E * a) :
      |a - b| ≤ (E - 1) * b := by
    by_cases hab_order : a ≤ b
    · rw [abs_of_nonpos (sub_nonpos.mpr hab_order)]
      rw [neg_sub]
      have hfactor : 0 ≤ E - 1 := sub_nonneg.mpr hE
      calc
        b - a ≤ E * a - a := sub_le_sub_right hba a
        _ = (E - 1) * a := by ring
        _ ≤ (E - 1) * b := mul_le_mul_of_nonneg_left hab_order hfactor
    · have hba_order : b ≤ a := le_of_lt (lt_of_not_ge hab_order)
      rw [abs_of_nonneg (sub_nonneg.mpr hba_order)]
      calc
        a - b ≤ E * b - b := sub_le_sub_right hab b
        _ = (E - 1) * b := by ring
  constructor
  · apply sharp_difference
      (inverseResponse_nonneg S _ L)
      (inverseResponse_nonneg S _ L)
      (Real.one_le_exp dist_nonneg)
      (inverseResponse_compact_add_comparison S K L f g h)
    simpa only [dist_comm] using inverseResponse_compact_add_comparison S K L g f h
  · apply sharp_difference
      (dirichletResponse_nonneg S _ b)
      (dirichletResponse_nonneg S _ b)
      (Real.one_le_exp dist_nonneg)
      (dirichletResponse_compact_add_comparison S K b f g h)
    simpa only [dist_comm] using dirichletResponse_compact_add_comparison S K b g f h

end SubdiffusiveProcess
