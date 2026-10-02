import SubdiffusiveProcess.Sobolev.CompactPotential

/-! # Actual responses to continuous compact-root potentials

Restriction and coefficient exponentiation are concrete maps. These
comparison estimates keep an arbitrary common discarded potential, with
constant one in the retained compact-root norm.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- The actual inverse response is continuous in the compact-root potential. -/
theorem continuous_inverseResponse_compact (S : ResponseSpace Ω) (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)]
    (L : S.space →L[ℝ] ℝ) :
    Continuous (fun f : C(K, ℝ) => inverseResponse S (expPotentialCoefficient (compactPotentialToLp K f)) L) :=
  (continuous_inverseResponse_potential S L).comp (compactPotentialToLp K).continuous

/-- The actual boundary minimum is continuous in the compact-root potential. -/
theorem continuous_dirichletResponse_compact (S : ResponseSpace Ω) (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)]
    (b : weakSobolevGraph Ω) :
    Continuous (fun f : C(K, ℝ) => dirichletResponse S (expPotentialCoefficient (compactPotentialToLp K f)) b) :=
  (continuous_dirichletResponse_potential S b).comp (compactPotentialToLp K).continuous

/-- A common discarded potential cancels from the retained-potential difference. -/
theorem compactPotential_common_add_norm_le (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)] (f g h : C(K, ℝ)) :
    ‖compactPotentialToLp (Ω := Ω) K (f + h) - compactPotentialToLp K (g + h)‖ ≤ dist f g := by
  simpa only [add_sub_add_right_eq_sub, dist_eq_norm] using
    compactPotentialToLp_sub_norm_le (Ω := Ω) K (f + h) (g + h)

/-- Uniform inverse-response comparison with any common discarded compact potential. -/
theorem inverseResponse_compact_add_comparison (S : ResponseSpace Ω) (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)]
    (L : S.space →L[ℝ] ℝ) (f g h : C(K, ℝ)) :
    inverseResponse S (expPotentialCoefficient (compactPotentialToLp K (f + h))) L ≤
      Real.exp (dist f g) * inverseResponse S (expPotentialCoefficient (compactPotentialToLp K (g + h))) L := by
  apply (inverseResponse_potential_comparison S L
    (compactPotentialToLp K (g + h)) (compactPotentialToLp K (f + h))).2.trans
  apply mul_le_mul_of_nonneg_right _ (inverseResponse_nonneg S _ L)
  apply Real.exp_monotone
  rw [dist_comm]
  exact compactPotential_common_add_norm_le K g f h

/-- Uniform boundary-response comparison with the same discarded compact potential. -/
theorem dirichletResponse_compact_add_comparison (S : ResponseSpace Ω) (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)]
    (b : weakSobolevGraph Ω) (f g h : C(K, ℝ)) :
    dirichletResponse S (expPotentialCoefficient (compactPotentialToLp K (f + h))) b ≤
      Real.exp (dist f g) * dirichletResponse S (expPotentialCoefficient (compactPotentialToLp K (g + h))) b := by
  apply (dirichletResponse_potential_comparison S b
    (compactPotentialToLp K (g + h)) (compactPotentialToLp K (f + h))).2.trans
  apply mul_le_mul_of_nonneg_right _ (dirichletResponse_nonneg S _ b)
  apply Real.exp_monotone
  rw [dist_comm]
  exact compactPotential_common_add_norm_le K g f h

end SubdiffusiveProcess
