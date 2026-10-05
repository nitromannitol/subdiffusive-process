module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.DilationWeakEquation
public import Homogenization.Book.Ch03.Definitions

@[expose] public section

/-!
# Physical Dirichlet carriers after centered-cube dilation

The Dirichlet proof first transports the two unit-cube scalar solutions to
the physical cube.  This file records the corresponding transport of their
common zero-trace boundary datum and converts the sign convention of the
ABK26 forced equation into the public Chapter 3 Dirichlet-solution carrier.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open MeasureTheory Homogenization Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped Pointwise

noncomputable section

theorem unitCenteredOpenCube_eq_inv_smul_centeredOpenCube
    {d : ℕ} (m : ℤ) :
    openCubeSet (originCube d 0) =
      (centeredCubeScale m)⁻¹ • openCubeSet (originCube d m) := by
  rw [openCubeSet_originCube_eq_smul_originCube_zero (d := d) m]
  rw [show cubeScaleFactor (originCube d m) = centeredCubeScale m by rfl]
  rw [smul_smul, inv_mul_cancel₀ (centeredCubeScale_ne_zero m), one_smul]

private theorem castH10Function_toFun {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (w : H10Function U) (x : Vec d) :
    (hUV ▸ w).toH1Function.toFun x = w.toH1Function.toFun x := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.aux_dedup_d209_castH10Function_toFun (d := d) (U := U) (V := V) (hUV := hUV) (phi := w) (x := x)

private theorem castH10Function_grad {d : ℕ} {U V : Set (Vec d)}
    (hUV : U = V) (w : H10Function U) (x : Vec d) :
    (hUV ▸ w).toH1Function.grad x = w.toH1Function.grad x := by exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.aux_dedup_d213_castH10Function_grad (d := d) (U := U) (V := V) (hUV := hUV) (phi := w) (x := x)

/-- Raw pushforward `w_m(y) = w((3^m)⁻¹ y)` of a unit-cube zero-trace
witness.  Unlike the normalized test-function transport, its value carries
no extra amplitude. -/
noncomputable def centeredCubeH10RawDilation {d : ℕ} (m : ℤ)
    (w : H10Function (openCubeSet (originCube d 0))) :
    H10Function (openCubeSet (originCube d m)) :=
  H10Function.unscale (inv_pos.mpr (centeredCubeScale_pos m))
    (unitCenteredOpenCube_eq_inv_smul_centeredOpenCube m ▸ w)

@[simp] theorem centeredCubeH10RawDilation_toFun {d : ℕ} (m : ℤ)
    (w : H10Function (openCubeSet (originCube d 0))) (y : Vec d) :
    (centeredCubeH10RawDilation m w).toH1Function.toFun y =
      w.toH1Function.toFun ((centeredCubeScale m)⁻¹ • y) := by
  unfold centeredCubeH10RawDilation
  rw [H10Function.unscale_toH1Function, H1Function.unscale_toFun]
  exact castH10Function_toFun
    (unitCenteredOpenCube_eq_inv_smul_centeredOpenCube m) w _

@[simp] theorem centeredCubeH10RawDilation_grad {d : ℕ} (m : ℤ)
    (w : H10Function (openCubeSet (originCube d 0))) (y : Vec d) :
    (centeredCubeH10RawDilation m w).toH1Function.grad y =
      (centeredCubeScale m)⁻¹ •
        w.toH1Function.grad ((centeredCubeScale m)⁻¹ • y) := by
  unfold centeredCubeH10RawDilation
  rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
  rw [castH10Function_grad]

/-- The full pointwise zero-trace carrier is stable under raw centered-cube
dilation. -/
theorem hasZeroTraceDifferenceOn_centeredCubeRawDilation
    {d : ℕ} (m : ℤ)
    {u h : H1Function (openCubeSet (originCube d 0))}
    (hzero : HasZeroTraceDifferenceOn
      (openCubeSet (originCube d 0)) u h) :
    HasZeroTraceDifferenceOn (openCubeSet (originCube d m))
      (centeredCubeRawDilation m u) (centeredCubeRawDilation m h) := by
  obtain ⟨w, hwValue, hwGrad⟩ := hzero
  refine ⟨centeredCubeH10RawDilation m w, ?_, ?_⟩
  · intro y
    rw [centeredCubeRawDilation_toFun, centeredCubeRawDilation_toFun,
      centeredCubeH10RawDilation_toFun,
      hwValue ((centeredCubeScale m)⁻¹ • y)]
  · intro y
    rw [centeredCubeRawDilation_grad, centeredCubeRawDilation_grad,
      centeredCubeH10RawDilation_grad,
      hwGrad ((centeredCubeScale m)⁻¹ • y)]
    module

/-- A common unit-cube boundary datum remains a common zero-trace datum after
raw dilation to the physical centered cube. -/
theorem hasH10Difference_centeredCubeRawDilation
    {d : ℕ} (m : ℤ)
    {u h : H1Function (openCubeSet (originCube d 0))}
    (hzero : HasZeroTraceDifferenceOn
      (openCubeSet (originCube d 0)) u h) :
    Book.Ch03.ABK26.HasH10Difference (originCube d m)
      (centeredCubeRawDilation m u) (centeredCubeRawDilation m h) := by
  obtain ⟨w, hwValue, _hwGrad⟩ := hzero
  refine ⟨centeredCubeH10RawDilation m w,
    Filter.Eventually.of_forall fun y ↦ ?_⟩
  rw [centeredCubeH10RawDilation_toFun]
  change w.toH1Function.toFun ((centeredCubeScale m)⁻¹ • y) =
    (centeredCubeRawDilation m u).toFun y -
      (centeredCubeRawDilation m h).toFun y
  rw [
    centeredCubeRawDilation_toFun, centeredCubeRawDilation_toFun]
  rw [hwValue ((centeredCubeScale m)⁻¹ • y)]
  ring

/-- Two unit-cube solutions with the same boundary datum retain the common
`H¹₀` difference required by the physical coarse-graining theorem. -/
theorem hasH10Difference_centeredCubeRawDilation_of_commonBoundary
    {d : ℕ} (m : ℤ)
    {u v h : H1Function (openCubeSet (originCube d 0))}
    (hu : HasZeroTraceDifferenceOn
      (openCubeSet (originCube d 0)) u h)
    (hv : HasZeroTraceDifferenceOn
      (openCubeSet (originCube d 0)) v h) :
    Book.Ch03.ABK26.HasH10Difference (originCube d m)
      (centeredCubeRawDilation m u) (centeredCubeRawDilation m v) :=
  hasH10Difference_of_hasZeroTraceDifferenceOn
    (hasZeroTraceDifferenceOn_centeredCubeRawDilation m hu)
    (hasZeroTraceDifferenceOn_centeredCubeRawDilation m hv)

/-- The public Chapter 3 convention has the opposite forcing sign from the
ABK26 coarse-graining convention. -/
theorem publicIsForcedEquation_neg_of_ABK26
    {d : ℕ} {Q : TriadicCube d} {a : Book.Ch03.CoeffFamily d}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : Book.Ch03.ABK26.IsForcedEquation Q (a.coeffOn Q) u g) :
    Book.Ch03.IsForcedEquation Q a u (fun x ↦ -g x) := by
  intro phi
  have h := hu phi
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet Q,
          vecDot (g x) (phi.toH1Function.grad x) ∂volume := h
    _ = ∫ x in openCubeSet Q,
          vecDot (-g x) (phi.toH1Function.grad x) ∂volume := by
      simp_rw [vecDot_neg_left]
      rw [integral_neg]

/-- Package an ABK26 physical solution and its boundary datum as the public
Dirichlet forced solution consumed by the energy consequence. -/
noncomputable def dirichletForcedCubeSolutionOfABK26
    {d : ℕ} {Q : TriadicCube d} (a : Book.Ch03.CoeffFamily d)
    (u h : H1Function (openCubeSet Q)) (g : Vec d → Vec d)
    (hu : Book.Ch03.ABK26.IsForcedEquation Q (a.coeffOn Q) u g)
    (hzero : Book.Ch03.ABK26.HasH10Difference Q u h) :
    Book.Ch03.DirichletForcedCubeSolution Q a (fun x ↦ -g x) where
  toH1 := u
  boundaryData := h
  weakSolution := publicIsForcedEquation_neg_of_ABK26 hu
  zeroTraceDifference := hzero

/-- Concrete physical Dirichlet carrier for the cutoff equation obtained by
dilating the literal rescaled-coefficient unit solution. -/
noncomputable def cutoffPhysicalDirichletForcedCubeSolution
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {u h : H1Function (openCubeSet (originCube d 0))}
    {f : Vec d → ℝ} (F : CubeVectorH1Function (originCube d 0))
    (hu : IsScalarDirichletSolutionOn
      (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
      (originCube d 0) u h f)
    (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
      ∫ x in openCubeSet (originCube d 0),
          f x * psi.toH1Function.toFun x ∂volume =
        -∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume) :
    Book.Ch03.DirichletForcedCubeSolution (originCube d (N : ℤ))
      (aCutoffFamily M L omega)
      (fun x ↦ -(centeredCubeScaledVectorDilation
        (ahom M L) (N : ℤ) F).toField x) :=
  dirichletForcedCubeSolutionOfABK26
    (aCutoffFamily M L omega)
    (centeredCubeRawDilation (N : ℤ) u)
    (centeredCubeRawDilation (N : ℤ) h)
    (centeredCubeScaledVectorDilation (ahom M L) (N : ℤ) F).toField
    (isForcedEquation_aCutoff_centeredCubeRawDilation M L N omega F hu hF)
    (hasH10Difference_centeredCubeRawDilation (N : ℤ) hu.1)

@[simp] theorem cutoffPhysicalDirichletForcedCubeSolution_toH1
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {u h : H1Function (openCubeSet (originCube d 0))}
    {f : Vec d → ℝ} (F : CubeVectorH1Function (originCube d 0))
    (hu : IsScalarDirichletSolutionOn
      (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
      (originCube d 0) u h f)
    (hF : ∀ psi : H10Function (openCubeSet (originCube d 0)),
      ∫ x in openCubeSet (originCube d 0),
          f x * psi.toH1Function.toFun x ∂volume =
        -∫ x in openCubeSet (originCube d 0),
          vecDot (F.toField x) (psi.toH1Function.grad x) ∂volume) :
    (cutoffPhysicalDirichletForcedCubeSolution M L N omega F hu hF).toH1 =
      centeredCubeRawDilation (N : ℤ) u :=
  rfl

/-- The cutoff and homogenized physical solutions inherit their common
unit-cube boundary datum, supplying the third analytic premise of the
prebalance theorem. -/
theorem hasH10Difference_cutoff_ahom_centeredCubeRawDilation
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L N : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {u v h : H1Function (openCubeSet (originCube d 0))}
    {f : Vec d → ℝ}
    (hu : IsScalarDirichletSolutionOn
      (scalarCoeffField (rescaledCutoffCoefficient M L N omega))
      (originCube d 0) u h f)
    (hv : IsScalarDirichletSolutionOn (fun _ ↦ (1 : Mat d))
      (originCube d 0) v h f) :
    Book.Ch03.ABK26.HasH10Difference (originCube d (N : ℤ))
      (centeredCubeRawDilation (N : ℤ) u)
      (centeredCubeRawDilation (N : ℤ) v) :=
  hasH10Difference_centeredCubeRawDilation_of_commonBoundary
    (N : ℤ) hu.1 hv.1

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
