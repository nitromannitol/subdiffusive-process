import SubdiffusiveProcess.Sobolev.FiniteResponses
import SubdiffusiveProcess.Variational.SourceObjectives

/-!
# Concrete spaces and coefficients for finite responses

The space is a closed subspace of the actual distributional H1 graph,
with ordinary Poincare stated explicitly. The coefficient is an actual L∞
class bounded away from zero. No response or limiting theorem is a field.
-/

open MeasureTheory InnerProductSpace Filter Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- A concrete Sobolev variation space on which ordinary Poincare holds. -/
structure ResponseSpace (Ω : Opens (SpatialCoordinates d)) where
  space : Submodule ℝ (SobolevData Ω)
  le_weak : space ≤ weakSobolevGraph Ω
  closed : IsClosed (space : Set (SobolevData Ω))
  poincare : ∃ K : ℝ≥0, ∀ z : space,
    ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient space z‖

/-- Killed variations use the previously constructed H1_0 completion. -/
def killedResponseSpace (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
    ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖) :
    ResponseSpace Ω :=
  ⟨killedSobolevGraph Ω, killedSobolevGraph_le_weakSobolevGraph,
    isClosed_killedSobolevGraph, hP⟩

/-- Neumann variations use the actual mean-zero weak-gradient graph. -/
def meanZeroResponseSpace [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖) :
    ResponseSpace Ω :=
  ⟨meanZeroSobolevGraph Ω, inf_le_left, isClosed_meanZeroSobolevGraph, hP⟩

/-- Actual bounded scalar coefficients with a uniform positive lower bound. -/
def PositiveCoefficient (Ω : Opens (SpatialCoordinates d)) :=
  {a : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) //
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), c ≤ a x}

/-- The bilinear energy on the concrete Sobolev variation space. -/
def responseForm (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) :
    S.space →L[ℝ] S.space →L[ℝ] ℝ :=
  (weightedGradientForm a.val).bilinearComp (subspaceGradient S.space) (subspaceGradient S.space)

/-- The space-level form retains the exact unnormalized coefficient integral. -/
theorem responseForm_apply (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (u v : S.space) :
    responseForm S a u v = ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
      a.val x * ((u : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x) := by
  exact weightedGradientForm_apply a.val _ _

/-- The actual coefficient form is symmetric. -/
theorem responseForm_symm (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (u v : S.space) :
    responseForm S a u v = responseForm S a v u :=
  weightedGradientForm_symm a.val _ _

/-- Its quadratic energy is nonnegative. -/
theorem responseForm_nonneg (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (u : S.space) :
    0 ≤ responseForm S a u u := by
  obtain ⟨c, hc, ha⟩ := a.property
  obtain ⟨c', hc', hb⟩ := weightedGradientForm_coercive a.val hc ha
  exact (mul_nonneg (mul_nonneg hc'.le (norm_nonneg _)) (norm_nonneg _)).trans (hb _)

/-- The already proved gradient-space construction gives the unique source solution. -/
theorem existsUnique_responseForm_solution (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) : ∃! u : S.space, ∀ v, responseForm S a u v = L v := by
  obtain ⟨K, hP⟩ := S.poincare
  obtain ⟨c, hc, ha⟩ := a.property
  exact existsUnique_gradient_subspace_solution S.space S.closed K hP a.val hc ha L

/-- The unique weak source solution; no fallback value is used. -/
def responseSolution (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) :
    S.space := Classical.choose (existsUnique_responseForm_solution S a L)

/-- Defining equation of the selected unique source solution. -/
theorem responseSolution_spec (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) (v : S.space) :
    responseForm S a (responseSolution S a L) v = L v :=
  (Classical.choose_spec (existsUnique_responseForm_solution S a L)).1 v

/-- Every weak solution is the same selected solution. -/
theorem responseSolution_eq (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) (u : S.space) (hu : ∀ v, responseForm S a u v = L v) :
    u = responseSolution S a L :=
  (Classical.choose_spec (existsUnique_responseForm_solution S a L)).2 u hu

/-- The scalar inverse response is the actual energy of the unique weak solution. -/
def inverseResponse (S : ResponseSpace Ω) (a : PositiveCoefficient Ω) (L : S.space →L[ℝ] ℝ) : ℝ :=
  responseForm S a (responseSolution S a L) (responseSolution S a L)

/-- The inverse response also equals the load evaluated at its solution. -/
theorem inverseResponse_eq_load (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) : inverseResponse S a L = L (responseSolution S a L) :=
  responseSolution_spec S a L _

/-- Inverse responses are nonnegative, including the zero-load case. -/
theorem inverseResponse_nonneg (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) : 0 ≤ inverseResponse S a L := responseForm_nonneg S a _

/-- The objective loses exactly the energy of the difference from its unique maximizer. -/
theorem inverseResponse_objective_gap (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) (v : S.space) :
    inverseResponse S a L - (2 * L v - responseForm S a v v) =
      responseForm S a (v - responseSolution S a L) (v - responseSolution S a L) :=
  bilinear_source_objective_gap (responseForm S a) (responseForm_symm S a) L
    (responseSolution S a L) (responseSolution_spec S a L) v

/-- The source variational formula is an attained greatest value, not a formal supremum. -/
theorem inverseResponse_isGreatest (S : ResponseSpace Ω) (a : PositiveCoefficient Ω)
    (L : S.space →L[ℝ] ℝ) :
    IsGreatest (Set.range fun v : S.space => 2 * L v - responseForm S a v v)
      (inverseResponse S a L) := by
  constructor
  · refine ⟨responseSolution S a L, ?_⟩
    change 2 * L (responseSolution S a L) - inverseResponse S a L = _
    rw [inverseResponse_eq_load]
    ring
  · rintro x ⟨v, rfl⟩
    have hg := inverseResponse_objective_gap S a L v
    have hn := responseForm_nonneg S a (v - responseSolution S a L)
    linarith

end SubdiffusiveProcess
