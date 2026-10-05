module

public import SubdiffusiveProcess.EllipticRegularity.Scaling
public import SubdiffusiveProcess.EllipticRegularity.Bridge

@[expose] public section




open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess



theorem responseJ_eq_affineDiagonalDefect {d : ℕ}
    (U : Homogenization.Book.Ch02.Domain d) (Om : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Om : Set (SpatialCoordinates d)))]
    (hset : (Om : Set (SpatialCoordinates d)) = (U : Set (Homogenization.Vec d)))
    {a : Homogenization.Vec d → ℝ} {alpha : ℝ} (halpha : 0 < alpha)
    (data : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U a)
    (hOm : Bornology.IsBounded (Om : Set (SpatialCoordinates d)))
    (hvol : 0 < volume.real (Om : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Om) w‖)
    (hN : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph Om,
      ‖(w : SobolevData Om).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Om) w‖)
    (aQ : PositiveCoefficient Om)
    (haQ : ((aQ.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] fun x => a x / alpha))
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    Homogenization.Book.Ch02.responseJ U data.toCoeffOn
        ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e) =
      affineDiagonalDefect hOm hvol hD hN aQ e := by
  obtain ⟨Uc, hUdom, hUne⟩ := U
  simp only at hset data ⊢
  subst hset
  set aP : PositiveCoefficient Om := smulPositiveCoefficient halpha aQ with haPdef
  have haP : ((aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Om : Set (SpatialCoordinates d))] a) := by
    filter_upwards [smulPositiveCoefficient_coeFn halpha aQ, haQ] with x hx hq
    rw [haPdef, hx, hq]
    field_simp
  have htheory := Homogenization.Book.Ch02.responseSymmetricDirichletNeumannTheory
      (⟨(Om : Set (SpatialCoordinates d)), hUdom, hUne⟩ :
        Homogenization.Book.Ch02.Domain d) data.toCoeffOn data.isSymmetric
  have hsplit := htheory.response_dirichlet_neumann_split
      ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e)
  rw [hsplit,
    _root_.SubdiffusiveProcess.EllipticRegularity.symmetricDirichletNu_eq_affineDirichletResponse hUdom hUne data hOm hD aP haP hvol,
    _root_.SubdiffusiveProcess.EllipticRegularity.symmetricNeumannNu_eq_affineInverseNeumannResponse hUdom hUne data hN aP haP hvol]
  have hdot : Homogenization.vecDot ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e) = 1 := by
    have hs : Real.sqrt alpha ≠ 0 := ne_of_gt (Real.sqrt_pos.2 halpha)
    rw [Homogenization.vecDot]
    rw [← he, Homogenization.vecNormSq, Homogenization.vecDot]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [hdot, affineDiagonalDefect,
    ← affineDirichletResponse_normalizedSlope hOm hD halpha aQ e,
    ← affineInverseNeumannResponse_normalizedSlope hN halpha aQ e, ← haPdef]
  have hesq : (∑ i : Fin d, (e i) ^ 2) = 1 := by
    rw [← he, Homogenization.vecNormSq, Homogenization.vecDot]
    exact Finset.sum_congr rfl fun i _ => sq (e i)
  rw [hesq]
  ring

end SubdiffusiveProcess
