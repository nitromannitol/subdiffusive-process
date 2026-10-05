module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalDirichletCarrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PositiveFractionalDatum
public import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS
public import SubdiffusiveProcess.Frozen.Section6.Defs.H2DatumNorm
public import Homogenization.Book.Ch03.Theorems.SobolevPublic
public import Homogenization.Sobolev.FiniteLpCoordinate
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeakHessianRowL2Energy

@[expose] public section

/-!
# Positive fractional pricing of the frozen `H²` boundary datum

The frozen boundary datum stores an `H¹` representative and a weak Hessian.
Its gradient is therefore a coordinatewise `H¹` vector field.  This file
places that field in the interpolation carrier used by the Dirichlet energy
row and bounds the retained unit-cube budget by the literal frozen `h.norm`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

/-- Every term in the frozen coordinate-sum `H²` norm is a genuine finite
`L²` norm. -/
theorem h2Datum_norm_lt_top {d : ℕ} {Q : TriadicCube d} (h : H2Datum Q) :
    h.norm < ∞ := by
  unfold H2Datum.norm l2Size
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr
      ⟨h.toH1.memL2.eLpNorm_lt_top,
        (ENNReal.sum_lt_top).2 fun i _ ↦
          (h.toH1.grad_memL2 i).eLpNorm_lt_top⟩,
      (ENNReal.sum_lt_top).2 fun i _ ↦ (ENNReal.sum_lt_top).2 fun j _ ↦
          (h.weakHessian.hess_memL2 i j).eLpNorm_lt_top⟩

/-- The gradient of a frozen `H²` datum as a coordinatewise `H¹` vector
field. -/
noncomputable def h2DatumGradientH1 {d : ℕ}
    (h : H2Datum (originCube d 0)) :
    CubeVectorH1Function (originCube d 0) where
  coord := fun i ↦ h.weakHessian.gradCoordH1Function i

@[simp] theorem h2DatumGradientH1_toField {d : ℕ}
    (h : H2Datum (originCube d 0)) :
    (h2DatumGradientH1 h).toField = h.toH1.grad := by
  funext x i
  rfl

theorem h2DatumGradientH1_gradientCoordL2NormSum {d : ℕ}
    (h : H2Datum (originCube d 0)) :
    (h2DatumGradientH1 h).gradientCoordL2NormSum =
      h.weakHessian.hessianCoordL2NormSum := by
  unfold h2DatumGradientH1 CubeVectorH1Function.gradientCoordL2NormSum
  exact Finset.sum_congr rfl fun i _ ↦
    h.weakHessian.gradCoordH1Function_gradientCoordL2NormSum_eq i

/-- Dimension-only loss in converting the direct Euclidean gradient `L²`
carrier to the coordinate-sum norm frozen in `H2Datum.norm`. -/
noncomputable def h2DatumGradientBudgetConstant (d : ℕ) : ℝ≥0∞ :=
  max ‖(d : ℝ)‖ₑ 1

theorem h2DatumGradientBudgetConstant_lt_top (d : ℕ) :
    h2DatumGradientBudgetConstant d < ∞ := by
  rw [h2DatumGradientBudgetConstant, max_lt_iff]
  exact ⟨enorm_lt_top, ENNReal.one_lt_top⟩

/-- The direct Euclidean `L²` size of the boundary gradient is bounded by
the coordinate sum appearing literally in the frozen datum norm. -/
theorem unitEuclideanL2_h2DatumGradient_le
    {d : ℕ} (h : H2Datum (originCube d 0)) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (unitEuclideanL2FieldOfCubeVectorH1 (h2DatumGradientH1 h)) ≤
      ‖(d : ℝ)‖ₑ *
        ∑ i : Fin d, l2Size (originCube d 0) (fun x ↦ h.toH1.grad x i) := by
  have hcoord : ∀ i : Fin d,
      AEStronglyMeasurable (fun x ↦ h.toH1.grad x i)
        (normalizedCubeMeasure (originCube d 0)) := by
    intro i
    rw [normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet]
    exact (h.toH1.gradMemL2 i).aestronglyMeasurable
  have hmain := euclidean_eLpNorm_le_dimension_mul_sum_coordinates
    (normalizedCubeMeasure (originCube d 0)) FiniteLpExponent.two
    h.toH1.grad hcoord
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
    BoundedMeasurableDomain.normalizedLpENorm
  rw [← normalizedCubeMeasure_originCube_zero_eq_unitCenteredCubeDomain_normalizedVolume]
  simp only [unitEuclideanL2FieldOfCubeVectorH1_apply,
    h2DatumGradientH1_toField]
  simp only [euclideanNorm_eq_norm_ofVec]
  rw [eLpNorm_norm _ (by
    simpa only [Function.comp_def, HilbertVec.ofVecL_apply] using!
      (HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable
        (aemeasurable_pi_iff.mpr (fun i => (hcoord i).aemeasurable)).aestronglyMeasurable)]
  simpa only [FiniteLpExponent.two_exponent, euclideanNorm_eq_norm_ofVec,
    l2Size, volumeMeasureOn,
    normalizedCubeMeasure_originCube_zero_eq_volumeMeasureOn_openCubeSet] using! hmain

/-- Extended-real spelling of the weak-Hessian coordinate sum retained by
the interpolation budget. -/
theorem ofReal_h2DatumGradientCoordL2NormSum_eq
    {d : ℕ} (h : H2Datum (originCube d 0)) :
    ENNReal.ofReal (h2DatumGradientH1 h).gradientCoordL2NormSum =
      ∑ i : Fin d, ∑ j : Fin d,
        l2Size (originCube d 0) (h.weakHessian.hess i j) := by
  rw [h2DatumGradientH1_gradientCoordL2NormSum]
  unfold HasWeakHessianOn.hessianCoordL2NormSum
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro j _
      rw [l2Size]
      exact
        (h.weakHessian.eLpNorm_hess_eq_ofReal_norm_hessCoordToScalarL2 i j).symm
    · intro j _
      exact norm_nonneg _
  · intro i _
    exact Finset.sum_nonneg fun j _ ↦ norm_nonneg _

/-- The whole unit interpolation budget of the boundary gradient is bounded
by the literal frozen `H²` norm with a dimension-only loss. -/
theorem unitCubeVectorH1ENormBudget_h2DatumGradient_le
    {d : ℕ} (h : H2Datum (originCube d 0)) :
    unitCubeVectorH1ENormBudget (h2DatumGradientH1 h) ≤
      h2DatumGradientBudgetConstant d * h.norm := by
  let G : ℝ≥0∞ :=
    ∑ i : Fin d, l2Size (originCube d 0) (fun x ↦ h.toH1.grad x i)
  let H : ℝ≥0∞ :=
    ∑ i : Fin d, ∑ j : Fin d,
      l2Size (originCube d 0) (h.weakHessian.hess i j)
  let K : ℝ≥0∞ := h2DatumGradientBudgetConstant d
  have hL := unitEuclideanL2_h2DatumGradient_le h
  have hKdim : ‖(d : ℝ)‖ₑ ≤ K := le_max_left _ _
  have hKone : 1 ≤ K := le_max_right _ _
  unfold unitCubeVectorH1ENormBudget
  rw [ofReal_h2DatumGradientCoordL2NormSum_eq]
  change _ + H ≤ K * h.norm
  calc
    _ ≤ ‖(d : ℝ)‖ₑ * G + H := add_le_add hL le_rfl
    _ ≤ K * G + K * H := by
      exact add_le_add
        (by simpa only [mul_comm] using! mul_le_mul_right hKdim G)
        (by simpa only [one_mul, mul_comm] using! mul_le_mul_right hKone H)
    _ = K * (G + H) := by ring
    _ ≤ K * h.norm := by
      have hGH : G + H ≤ h.norm := by
        unfold H2Datum.norm
        change G + H ≤ l2Size (originCube d 0) h.toH1.toFun + G + H
        calc
        G + H ≤ l2Size (originCube d 0) h.toH1.toFun + (G + H) :=
          le_add_of_nonneg_left (zero_le)
        _ = l2Size (originCube d 0) h.toH1.toFun + G + H := by ring
      simpa only [mul_comm] using! mul_le_mul_right hGH K

/-- The physical positive fractional seminorm of the boundary gradient is
priced directly by the frozen `H²` datum norm. -/
theorem paperFractionalSeminorm_h2DatumGradientDilation_le
    {d : ℕ} (alpha : ℝ) (m : ℤ) (s : FractionalOrder)
    (h : H2Datum (originCube d 0)) :
    paperFractionalSeminorm (originCube d m) s FiniteLpExponent.two
        (centeredCubeScaledVectorDilation alpha m
          (h2DatumGradientH1 h)).toField ≤
      scaledVectorDatumFractionalConstant s d *
        (ENNReal.ofReal (centeredCubeScale m)) ^ (-s.1) *
          ‖alpha * (centeredCubeScale m)⁻¹‖ₑ *
            (h2DatumGradientBudgetConstant d * h.norm) := by
  exact
    (paperFractionalSeminorm_centeredCubeScaledVectorDilation_le_h1Budget
      alpha m s (h2DatumGradientH1 h)).trans (by
        unfold scaledVectorDatumFractionalENormBound
        exact mul_le_mul_right
          (unitCubeVectorH1ENormBudget_h2DatumGradient_le h) _)

/-- The dilated boundary gradient has the exact positive-Besov regularity
required by the Chapter 3 energy consequence. -/
theorem forceBesovRegularity_h2DatumGradientDilation
    {d : ℕ} [NeZero d] (m : ℤ) (s : FractionalOrder)
    (h : H2Datum (originCube d 0)) :
    ForceBesovRegularity (originCube d m) s.1
      (centeredCubeScaledVectorDilation 1 m
        (h2DatumGradientH1 h)).toField := by
  let F : CubeEuclideanWspField (originCube d m) s FiniteLpExponent.two :=
    centeredCubeScaledVectorDilationWspField 1 m s (h2DatumGradientH1 h)
  have hsob := cubeEuclideanWspField_forceSobolevRegularity s F
  simpa only [F, centeredCubeScaledVectorDilationWspField_toField] using!
    hsob.toForceBesovRegularity s.2.1 s.2.2.le

/-- The stored boundary gradient of the concrete physical cutoff solution is
literally the dilation of the frozen `H²` datum's gradient. -/
theorem cutoffPhysicalDirichlet_boundaryGradient_eq_h2DatumDilation
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {u : H1Function (openCubeSet (originCube d 0))}
    (h : H2Datum (originCube d 0)) {f : Vec d → ℝ}
    (F : CubeVectorH1Function (originCube d 0))
    (hu : IsScalarDirichletSolutionOn
      (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
      (originCube d 0) u h.toH1 f)
    (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
      ∫ x in openCubeSet (originCube d 0),
          f x * psi.toH1Function.toFun x ∂volume =
        -∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume) :
    dirichletBoundaryGradientField
        (cutoffPhysicalDirichletForcedCubeSolution M L N omega F hu hF) =
      (centeredCubeScaledVectorDilation 1 (N : ℤ)
        (h2DatumGradientH1 h)).toField := by
  funext y
  unfold dirichletBoundaryGradientField
  change (centeredCubeRawDilation (N : ℤ) h.toH1).grad y = _
  rw [centeredCubeRawDilation_grad,
    centeredCubeScaledVectorDilation_toField]
  rw [h2DatumGradientH1_toField]
  simp only [one_mul]

/-- The concrete physical cutoff solution therefore discharges the boundary
regularity premise of `EnergyConsequence` without an extra hypothesis. -/
theorem forceBesovRegularity_cutoffPhysicalDirichlet_boundaryGradient
    {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {u : H1Function (openCubeSet (originCube d 0))}
    (h : H2Datum (originCube d 0)) {f : Vec d → ℝ}
    (F : CubeVectorH1Function (originCube d 0))
    (hu : IsScalarDirichletSolutionOn
      (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
      (originCube d 0) u h.toH1 f)
    (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
      ∫ x in openCubeSet (originCube d 0),
          f x * psi.toH1Function.toFun x ∂volume =
        -∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume)
    (s : FractionalOrder) :
    ForceBesovRegularity (originCube d (N : ℤ)) s.1
      (dirichletBoundaryGradientField
        (cutoffPhysicalDirichletForcedCubeSolution M L N omega F hu hF)) := by
  rw [cutoffPhysicalDirichlet_boundaryGradient_eq_h2DatumDilation]
  exact forceBesovRegularity_h2DatumGradientDilation (N : ℤ) s h

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
