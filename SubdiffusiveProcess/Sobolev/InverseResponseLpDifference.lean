module

public import SubdiffusiveProcess.Sobolev.CompactResponseDifference
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess

/-- The actual inverse-response difference has its Lp norm bounded by the product of the exponential-increment and original-response L(2p) norms. Both moment premises remain explicit; no changed-response moment or independence is required. -/
theorem inverseResponse_compact_difference_memLp
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (K : Compacts (SpatialCoordinates d))
    [Fact ((Ω : Set (SpatialCoordinates d)) ⊆ K)]
    (L : S.space →L[ℝ] ℝ)
    (F G J : α → C(K, ℝ))
    (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ)
    (hJ : AEStronglyMeasurable J μ)
    (p : ℝ≥0∞) (_hp : 1 ≤ p) (_hpt : p ≠ ∞)
    (hE : MemLp (fun x => Real.exp (dist (F x) (G x)) - 1) (2 * p) μ)
    (hR : MemLp (fun x => inverseResponse S
      (expPotentialCoefficient (compactPotentialToLp K (G x + J x))) L) (2 * p) μ) :
    let D := fun x => inverseResponse S
        (expPotentialCoefficient (compactPotentialToLp K (F x + J x))) L -
      inverseResponse S
        (expPotentialCoefficient (compactPotentialToLp K (G x + J x))) L
    MemLp D p μ ∧ eLpNorm D p μ ≤
      eLpNorm (fun x => Real.exp (dist (F x) (G x)) - 1) (2 * p) μ *
      eLpNorm (fun x => inverseResponse S
        (expPotentialCoefficient (compactPotentialToLp K (G x + J x))) L) (2 * p) μ := by
  intro D
  let : ENNReal.HolderTriple (2 * p) (2 * p) p := by
    constructor
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← add_mul]
    rw [ENNReal.inv_two_add_inv_two, one_mul]
  have hD : AEStronglyMeasurable D μ :=
    ((continuous_inverseResponse_compact S K L).comp_aestronglyMeasurable
      (hF.add hJ)).sub
      ((continuous_inverseResponse_compact S K L).comp_aestronglyMeasurable (hG.add hJ))
  have hdom : ∀ᵐ x ∂μ, ‖D x‖ ≤
      (Real.exp (dist (F x) (G x)) - 1) *
        inverseResponse S (expPotentialCoefficient (compactPotentialToLp K (G x + J x))) L :=
    Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using
        (compact_response_difference_le_original S K L (0 : weakSobolevGraph Ω)
          (F x) (G x) (J x)).1
  refine ⟨(hE.fun_mul hR).mono' hD hdom, (eLpNorm_mono_ae_real hD hdom).trans ?_⟩
  simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def] using
    eLpNorm_smul_le_mul_eLpNorm hE.aestronglyMeasurable hR.aestronglyMeasurable

end SubdiffusiveProcess
