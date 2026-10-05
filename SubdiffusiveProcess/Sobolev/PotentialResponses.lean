module

public import SubdiffusiveProcess.Sobolev.DirichletComparison
public import SubdiffusiveProcess.Sobolev.PotentialCoefficient
public import SubdiffusiveProcess.Probability.ResponseContinuity

@[expose] public section

/-! # Continuous responses to actual bounded potentials

The potential-to-coefficient map is the actual exponential L∞ class. The
canonical scalar source and boundary responses satisfy the uniform
multiplicative comparison, hence are continuous and Borel measurable.
This does not supply the model's quantitative resampling or moment bounds.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- Uniform potential comparison for the actual inverse variational response. -/
theorem inverseResponse_potential_comparison (S : ResponseSpace Ω) (L : S.space →L[ℝ] ℝ)
    (g h : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    Real.exp (-‖g - h‖) * inverseResponse S (expPotentialCoefficient g) L ≤
        inverseResponse S (expPotentialCoefficient h) L ∧
      inverseResponse S (expPotentialCoefficient h) L ≤
        Real.exp ‖g - h‖ * inverseResponse S (expPotentialCoefficient g) L :=
  inverseResponse_exp_comparison S _ _ L _
    (expPotentialCoefficient_comparison g h).1 (expPotentialCoefficient_comparison g h).2

/-- Uniform potential comparison for the actual boundary variational response. -/
theorem dirichletResponse_potential_comparison (S : ResponseSpace Ω) (b : weakSobolevGraph Ω)
    (g h : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    Real.exp (-‖g - h‖) * dirichletResponse S (expPotentialCoefficient g) b ≤
        dirichletResponse S (expPotentialCoefficient h) b ∧
      dirichletResponse S (expPotentialCoefficient h) b ≤
        Real.exp ‖g - h‖ * dirichletResponse S (expPotentialCoefficient g) b :=
  dirichletResponse_exp_comparison S _ _ b _
    (expPotentialCoefficient_comparison g h).1 (expPotentialCoefficient_comparison g h).2

/-- The canonical inverse response is continuous in the L∞ potential. -/
theorem continuous_inverseResponse_potential (S : ResponseSpace Ω) (L : S.space →L[ℝ] ℝ) :
    Continuous (fun g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) =>
      inverseResponse S (expPotentialCoefficient g) L) := by
  have he := equicontinuous_of_exp_comparison
    (f := fun _ : Unit => fun g => inverseResponse S (expPotentialCoefficient g) L)
    (C := 1) (by norm_num)
    (fun _ g => inverseResponse_nonneg S _ L) (fun _ g h => ?_)
    (fun g => ⟨inverseResponse S (expPotentialCoefficient g) L, fun _ => le_rfl⟩)
  · exact he.continuous ()
  · rw [one_mul, dist_comm g h, dist_eq_norm]
    exact (inverseResponse_potential_comparison S L h g).2

/-- The canonical boundary response is continuous in the L∞ potential. -/
theorem continuous_dirichletResponse_potential (S : ResponseSpace Ω) (b : weakSobolevGraph Ω) :
    Continuous (fun g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) =>
      dirichletResponse S (expPotentialCoefficient g) b) := by
  have he := equicontinuous_of_exp_comparison
    (f := fun _ : Unit => fun g => dirichletResponse S (expPotentialCoefficient g) b)
    (C := 1) (by norm_num)
    (fun _ g => dirichletResponse_nonneg S _ b) (fun _ g h => ?_)
    (fun g => ⟨dirichletResponse S (expPotentialCoefficient g) b, fun _ => le_rfl⟩)
  · exact he.continuous ()
  · rw [one_mul, dist_comm g h, dist_eq_norm]
    exact (dirichletResponse_potential_comparison S b h g).2

/-- Borel measurability uses the actual potential norm topology. -/
theorem measurable_inverseResponse_potential (S : ResponseSpace Ω) (L : S.space →L[ℝ] ℝ) :
    @Measurable (Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) ℝ (borel _) (borel ℝ)
      (fun g => inverseResponse S (expPotentialCoefficient g) L) :=
  (continuous_inverseResponse_potential S L).borel_measurable

/-- The boundary response is also Borel measurable on the actual potential space. -/
theorem measurable_dirichletResponse_potential (S : ResponseSpace Ω) (b : weakSobolevGraph Ω) :
    @Measurable (Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) ℝ (borel _) (borel ℝ)
      (fun g => dirichletResponse S (expPotentialCoefficient g) b) :=
  (continuous_dirichletResponse_potential S b).borel_measurable

end SubdiffusiveProcess
