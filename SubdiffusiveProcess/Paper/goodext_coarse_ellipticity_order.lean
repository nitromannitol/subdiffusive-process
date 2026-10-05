module

public import SubdiffusiveProcess.Paper.in_J
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Localization

@[expose] public section

open Filter MeasureTheory Set SubdiffusiveProcess
open scoped Topology ENNReal
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The actual normalized lower coefficient is no larger than the upper coefficient. -/
theorem goodext_coarse_ellipticity_order
    {d : ℕ} [NeZero d] (I : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) :
    I.lam z r hr a w r' sigma 2 ≤ I.Lam z r hr a w r' sigma 2 := by
  rw [I.lam_eq z r hr a w r' hr' hsub sigma hsigma 2 (by norm_num)]
  rw [I.Lam_eq z r hr a w r' hr' hsub sigma hsigma 2 (by norm_num)]
  have htwo_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have htwo_real : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hq : (Homogenization.Book.Ch02.MultiscaleExponent.finite 2).IsAdmissible := by
    norm_num [Homogenization.Book.Ch02.MultiscaleExponent.IsAdmissible]
  let Q := Homogenization.originCube d 0
  let A := I.chart z r hr a w r'
  simpa only [ite_eq_right htwo_top, htwo_real] using
    (calc
      Homogenization.Book.Ch02.lambdaSq Q sigma
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) A ≤
          (Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm Q A)⁻¹ :=
        Homogenization.Book.Ch02.lambdaSq_le_oneCube Q A hsigma.1 hq
      _ ≤ Homogenization.Book.Ch02.coarseBMatrixNorm Q A :=
        Homogenization.Book.Ch02.oneCube_sigmaStarInv_le_b Q A
      _ ≤ Homogenization.Book.Ch02.LambdaSq Q sigma
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2) A :=
        Homogenization.Book.Ch02.oneCube_b_le_LambdaSq Q A hsigma.1 hq)

end SubdiffusiveProcess.Paper
