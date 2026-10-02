import SubdiffusiveProcess.Sobolev.CompactResponseDifference
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The actual boundary-response difference has its Lp norm bounded by the product of the exponential-increment and original-response L(2p) norms. Both moment premises remain explicit, and no moment of the copied response is required. -/
theorem dirichletResponse_compact_difference_memLp
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)]
    (b : weakSobolevGraph Ω)
    (F G J : α → C(K, ℝ))
    (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ)
    (hJ : AEStronglyMeasurable J μ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hE : MemLp (fun x => Real.exp (dist (F x) (G x)) - 1) (2 * p) μ)
    (hR : MemLp (fun x => dirichletResponse S
      (expPotentialCoefficient (compactPotentialToLp K (G x + J x))) b) (2 * p) μ) :
    let D := fun x => dirichletResponse S
        (expPotentialCoefficient (compactPotentialToLp K (F x + J x))) b -
      dirichletResponse S
        (expPotentialCoefficient (compactPotentialToLp K (G x + J x))) b
    MemLp D p μ ∧ eLpNorm D p μ ≤
      eLpNorm (fun x => Real.exp (dist (F x) (G x)) - 1) (2 * p) μ *
      eLpNorm (fun x => dirichletResponse S
        (expPotentialCoefficient (compactPotentialToLp K (G x + J x))) b) (2 * p) μ := by
  intro D
  letI : ENNReal.HolderTriple (2 * p) (2 * p) p := by
    constructor
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← add_mul]
    rw [ENNReal.inv_two_add_inv_two, one_mul]
  have hD : AEStronglyMeasurable D μ :=
    ((continuous_dirichletResponse_compact S K b).comp_aestronglyMeasurable
      (hF.add hJ)).sub
      ((continuous_dirichletResponse_compact S K b).comp_aestronglyMeasurable (hG.add hJ))
  have hdom : ∀ᵐ x ∂μ, ‖D x‖ ≤
      (Real.exp (dist (F x) (G x)) - 1) *
        dirichletResponse S (expPotentialCoefficient (compactPotentialToLp K (G x + J x))) b :=
    Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using
        (compact_response_difference_le_original S K (0 : S.space →L[ℝ] ℝ) b
          (F x) (G x) (J x)).2
  refine ⟨(hR.mul' hE).mono' hD hdom, (eLpNorm_mono_ae_real hdom).trans ?_⟩
  simpa only [smul_eq_mul] using
    eLpNorm_smul_le_mul_eLpNorm hR.aestronglyMeasurable hE.aestronglyMeasurable

end SubdiffusiveProcess
