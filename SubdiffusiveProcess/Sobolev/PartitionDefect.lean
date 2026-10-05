module

public import SubdiffusiveProcess.Sobolev.DiagonalDefect
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction

@[expose] public section

/-! # Normalizing the finite-partition response inequalities

The two unnormalized inequalities below are precisely the scalar primal
and inverse-Neumann subadditivity inputs. All cell coefficients are actual
restrictions of one root coefficient. The proved volume identity preserves
the constant term of the normalized diagonal defect.
-/
open MeasureTheory Set TopologicalSpace
open scoped NNReal
noncomputable section
namespace SubdiffusiveProcess

private theorem weighted_defect_sum {ι : Type*} (S : Finset ι)
    {V : ℝ} (hV : V ≠ 0) (v D N : ι → ℝ) (c : ℝ)
    (hv : ∀ i ∈ S, v i ≠ 0) (hvol : ∑ i ∈ S, v i = V) :
    (∑ i ∈ S, (v i / V) * ((D i + N i) / (2 * v i) - c)) =
      ((∑ i ∈ S, D i) + ∑ i ∈ S, N i) / (2 * V) - c := by
  calc
    _ = ∑ i ∈ S, ((D i + N i) / (2 * V) - (v i / V) * c) := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [hV, hv i hi]
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.sum_div, hvol, div_self hV, one_mul]

variable {d : ℕ} {ι : Type*} {Ω : Opens (SpatialCoordinates d)}
variable [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- Actual finite-volume primal and dual subadditivity imply the weighted diagonal-defect bound. -/
theorem affineDiagonalDefect_le_partition
    (q : ι → Opens (SpatialCoordinates d))
    [∀ i, IsFiniteMeasure (volume.restrict (q i : Set (SpatialCoordinates d)))]
    (S : Finset ι) (hq : ∀ i, q i ≤ Ω)
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Ω : Set (SpatialCoordinates d)))
    (hqvol : ∀ i, 0 < volume.real (q i : Set (SpatialCoordinates d)))
    (hvolsum : (∑ i ∈ S, volume.real (q i : Set (SpatialCoordinates d))) =
      volume.real (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
    (hN : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) u‖)
    (hDq : ∀ i, ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (q i),
      ‖(u : SobolevData (q i)).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph (q i)) u‖)
    (hNq : ∀ i, ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (q i),
      ‖(u : SobolevData (q i)).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph (q i)) u‖)
    (a : PositiveCoefficient Ω) (p : Fin d → ℝ)
    (hDir : affineDirichletResponse hΩ hD a p ≤
      ∑ i ∈ S, affineDirichletResponse (hΩ.subset (hq i)) (hDq i)
        (positiveCoefficientRestrict (hq i) a) p)
    (hNeu : affineInverseNeumannResponse hN a p ≤
      ∑ i ∈ S, affineInverseNeumannResponse (hNq i)
        (positiveCoefficientRestrict (hq i) a) p) :
    affineDiagonalDefect hΩ hvol hD hN a p ≤
      ∑ i ∈ S, (volume.real (q i : Set (SpatialCoordinates d)) /
        volume.real (Ω : Set (SpatialCoordinates d))) *
        affineDiagonalDefect (hΩ.subset (hq i)) (hqvol i) (hDq i) (hNq i)
          (positiveCoefficientRestrict (hq i) a) p := by
  unfold affineDiagonalDefect
  rw [weighted_defect_sum S hvol.ne' _ _ _ _ (fun i _ => (hqvol i).ne') hvolsum]
  exact sub_le_sub_right (div_le_div_of_nonneg_right (add_le_add hDir hNeu)
    (mul_pos (by norm_num) hvol).le) _

end SubdiffusiveProcess
