module

public import SubdiffusiveProcess.Paper.in_extension

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem inputs_extension_ellipticity (d : ℕ) (Jc : Paper.in_J d) :
    (∀ (z : SpatialCoordinates d) (m : ℕ) (hr : (0 : ℝ) < (3 : ℝ) ^ m)
      (a : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hr)) (t : ℝ),
      t ∈ Set.Ioc (0 : ℝ) 1 →
      let Q := Homogenization.originCube d (m : ℤ);
      let A := Homogenization.Book.Ch02.TriadicCoeffFamily.dilate (m : ℤ)
        (Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m));
      (Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) t 2 =
        Homogenization.Book.Ch02.lambdaSq Q t (.finite 2) A) ∧
      (Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) t 2 =
        Homogenization.Book.Ch02.LambdaSq Q t (.finite 2) A)) := by
  intro z m hr a t ht
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let A : Homogenization.Book.Ch02.TriadicCoeffFamily d :=
    Homogenization.Book.Ch02.TriadicCoeffFamily.dilate (m : ℤ)
      (Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m))
  have hAdil := Homogenization.Book.Ch02.TriadicCoeffFamily.isDilation_dilate (m : ℤ)
    (Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m))
  constructor
  · calc
      _ = Homogenization.Book.Ch02.lambdaSq (Homogenization.originCube d 0) t (.finite 2)
          (Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m)) :=
        Jc.lam_eq z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) hr Set.Subset.rfl t ht 2 (by norm_num)
      _ = Homogenization.Book.Ch02.lambdaSq Q t (.finite 2) A := by
        rw [← Homogenization.Book.Ch02.lambdaSq_dilate hAdil
          (Homogenization.originCube d 0) t (.finite 2)]
        simp [Q, A, Homogenization.Book.Ch02.dilateCube, Homogenization.originCube]
  · calc
      _ = Homogenization.Book.Ch02.LambdaSq (Homogenization.originCube d 0) t (.finite 2)
          (Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m)) :=
        Jc.Lam_eq z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) hr Set.Subset.rfl t ht 2 (by norm_num)
      _ = Homogenization.Book.Ch02.LambdaSq Q t (.finite 2) A := by
        rw [← Homogenization.Book.Ch02.LambdaSq_dilate hAdil
          (Homogenization.originCube d 0) t (.finite 2)]
        simp [Q, A, Homogenization.Book.Ch02.dilateCube, Homogenization.originCube]


end Paper

