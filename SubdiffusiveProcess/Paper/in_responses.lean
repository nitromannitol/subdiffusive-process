module

public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper



structure in_responses (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) where
  /-- The coefficient field `a_m` of the remark, at scale `m` and sample `om`. -/
  coeffAt : ℕ → BilateralField d → Homogenization.CoeffField d
  /-- `a_m` is the scalar field `x ↦ coeffScalar m om x` times the identity. -/
  coeffScalar : ℕ → BilateralField d → SpatialCoordinates d → ℝ
  coeffScalar_pos : ∀ m om x, 0 < coeffScalar m om x
  /-- The scalar coefficient is pinned to the stationary ORIGINAL nonnegative layers at
  scale `m`: `coeffScalar m om x = exp(finePotential m - (m+1)τ²)`. -/
  coeffScalar_eq : ∀ (m : ℕ) (om : BilateralField d) (x : SpatialCoordinates d),
    coeffScalar m om x =
      Real.exp ((∑ j ∈ Finset.range (m + 1), (om (j : ℤ)) x) -
        ((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
  coeffAt_eq : ∀ m om x, coeffAt m om x =
    Homogenization.scalarMatrix (coeffScalar m om x)
  /-- The working cube `y + 𝕔_m`, as an upstream domain. -/
  cubeAt : ℕ → SpatialCoordinates d → Homogenization.Book.Ch02.Domain d
  cubeAt_eq : ∀ (m : ℕ) (y : SpatialCoordinates d) (hr : (0 : ℝ) < 3 ^ m),
    (cubeAt m y : Set (Homogenization.Vec d)) =
      (centeredCube y ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d))
  defect : ℕ → SpatialCoordinates d → BilateralField d → ℝ
  defect_nonneg : ∀ m y om, 0 ≤ defect m y om
  /-- `defect` is the paper's `max_{|e|=1} J(y+𝕔_m, â_m^{-1/2}e, â_m^{1/2}e; a_m)`, not an
  arbitrary nonnegative function: without this the moment bound is vacuous. -/
  defect_isGreatest : ∀ (m : ℕ) (y : SpatialCoordinates d) (om : BilateralField d),
    IsGreatest {t : ℝ | ∃ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 ∧
        t = Homogenization.ResponseJ (cubeAt m y : Set (Homogenization.Vec d))
              ((Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m))⁻¹ • e)
              (Real.sqrt (SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) • e)
              (coeffAt m om)}
      (defect m y om)
  C : ℝ
  C_pos : 0 < C
  /-- The paper's actual finite moment assertion: the raw real integral moment bound alone
  admits a nonintegrable junk integral, so the defect is a genuine `L^xi` function before
  the numerical bound is applied. -/
  defect_memLp : ∀ xi : ℝ, 1 ≤ xi →
    xi ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
    ∀ (m : ℕ) (y : SpatialCoordinates d),
      MemLp (defect m y) (ENNReal.ofReal xi) (chaosSampleLaw M).toMeasure
  /-- Proposition `p.coarse.grained.bound`, uniform in the deterministic centre `y`. -/
  moment : ∀ xi : ℝ, 1 ≤ xi → xi ≤ C⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
    ∀ (m : ℕ) (y : SpatialCoordinates d),
      (∫ om, defect m y om ^ xi ∂(chaosSampleLaw M).toMeasure) ^ (1 / xi) ≤
        C * xi * Real.log (2 + xi) * M.delta ^ 2
  /-- `e.annealed.ordering`. -/
  ahom_ordering : ∀ n m : ℕ, n < m →
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M m ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom M n ∧
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M n ≤
        Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m : ℝ) - n)) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m
  /-- Mean one and `e.ord.bounds.truncated`. -/
  ahom_le_one : ∀ m : ℕ, SubdiffusiveProcess.CoarseGrainingVocab.ahom M m ≤ 1
  /-- Proposition `p.homogenized.coefficient.reciprocal.lower`. -/
  ahom_lower : ∀ m : ℕ,
    Real.exp (-((m : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≤
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M m
  /-- Definition `d.bLm`: the reference coefficients `b_{L,m} = â_{m∧L} a_L / a_{m∧L}`. -/
  bRef : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ
  bRef_eq : ∀ (L m : ℕ) (om : BilateralField d) (x : SpatialCoordinates d),
    bRef L m om x =
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M (min m L) * coeffScalar L om x /
        coeffScalar (min m L) om x
  /-- The reference scalar of the working cube `z + 𝕔_{j+2}` is the spatial average
  `(b_{L,j+2})_{z+𝕔_{j+2}}`, which is what `in_iteration` and `prop_folded_iteration`
  consume as `a₀`. -/
  refScalar : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ
  refScalar_eq : ∀ (L j : ℕ) (z : SpatialCoordinates d) (om : BilateralField d)
      (hr : (0 : ℝ) < 3 ^ (j + 2)),
    refScalar L j z om =
      (volume.real
          (centeredCube z ((3 : ℝ) ^ (j + 2)) hr : Set (SpatialCoordinates d)))⁻¹ *
        ∫ x in (centeredCube z ((3 : ℝ) ^ (j + 2)) hr : Set (SpatialCoordinates d)),
          bRef L (j + 2) om x

end SubdiffusiveProcess.Paper
