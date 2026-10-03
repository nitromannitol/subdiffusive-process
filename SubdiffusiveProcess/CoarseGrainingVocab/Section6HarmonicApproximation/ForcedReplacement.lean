/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.WeakSolutionConstructors
public import Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingDefinitions

@[expose] public section

/-!
# Constant-coefficient forced replacement

The construction is the affine-shift realization of the auxiliary `v_g` in
the harmonic-approximation proof.  It mirrors
`Algsuperdiff/Section4/Provider/ExcessDecay/HarmonicReplacement.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

section Window

variable [NeZero d] (Q : TriadicCube d)

theorem hasPotentialZeroTraceClosureRealization_openCubeSet :
    PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization (openCubeSet Q) :=
  PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)

instance instIsFiniteMeasureVolumeMeasureOnOpenCubeSet :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (Ch02.cubeDomain Q).instIsFiniteMeasureVolumeMeasureOn

omit [NeZero d] in
theorem isEllipticFieldOn_openCubeSet (a0 : Ch03.ConstantCoeffMatrix d) :
    IsEllipticFieldOn a0.lam a0.Lam (openCubeSet Q) (constantCoeffField a0.matrix) :=
  Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0
    (measurableSet_openCubeSet Q)

end Window

section Pairing

variable {U : Set (Vec d)}

private theorem integral_vecDot_sub_left_split {F G H : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G)
    (hH : ∀ x, H x = F x - G x) (φ : H10Function U) :
    ∫ x in U, vecDot (H x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      (∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂MeasureTheory.volume) -
        ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
  have hFint : MeasureTheory.IntegrableOn
      (fun x => vecDot (F x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2
  have hGint : MeasureTheory.IntegrableOn
      (fun x => vecDot (G x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG φ.toH1Function.grad_memVectorL2
  have hfun : (fun x => vecDot (H x) (φ.toH1Function.grad x)) =
      fun x => vecDot (F x) (φ.toH1Function.grad x) -
        vecDot (G x) (φ.toH1Function.grad x) := by
    funext x
    rw [hH x, sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
  rw [hfun, MeasureTheory.integral_sub hFint hGint]

end Pairing

variable [NeZero d] {Q : TriadicCube d}

/-- A positive scalar coefficient packaged as Chapter 3's constant matrix. -/
def scalarConstantCoeffMatrix {sigma : ℝ} (hsigma : 0 < sigma) :
    Ch03.ConstantCoeffMatrix d where
  matrix := scalarMatrix (d := d) sigma
  isSymm := scalarMatrix_isSymm sigma
  lam := sigma
  Lam := sigma
  lam_pos := hsigma
  lam_le_Lam := le_rfl
  elliptic := isEllipticMatrix_scalarMatrix hsigma

/-- The zero-trace correction force `a₀∇u - g`. -/
def replacementCorrectorForce (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) (g : Vec d → Vec d) : Vec d → Vec d :=
  fun x => matVecMul a0.matrix (u.grad x) - g x

omit [NeZero d] in
private theorem memVectorL2_constantFlux (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q) fun x => matVecMul a0.matrix (u.grad x) :=
  memVectorL2_matVecMul_of_isEllipticFieldOn (isEllipticFieldOn_openCubeSet Q a0)
    u.grad_memVectorL2

omit [NeZero d] in
private theorem memVectorL2_replacementCorrectorForce (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    MemVectorL2 (openCubeSet Q) (replacementCorrectorForce a0 u g) :=
  (memVectorL2_constantFlux a0 u).sub hg

private theorem exists_replacementCorrector (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    ∃ rho : H10Function (openCubeSet Q),
      IsZeroTraceDirichletRhsWeakSolution (constantCoeffField a0.matrix)
        (openCubeSet Q) rho (replacementCorrectorForce a0 u g) :=
  exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
    (a := constantCoeffField a0.matrix) (U := openCubeSet Q)
    (g := replacementCorrectorForce a0 u g) (lam := a0.lam) (Lam := a0.Lam)
    (memVectorL2_replacementCorrectorForce a0 u hg)
    (hasPotentialZeroTraceClosureRealization_openCubeSet Q)
    (Ch02.openCubeSet_nonempty Q) (isEllipticFieldOn_openCubeSet Q a0)

/-- The chosen zero-trace correction. -/
def replacementCorrector (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) : H10Function (openCubeSet Q) :=
  Classical.choose (show ∃ rho : H10Function (openCubeSet Q),
    IsZeroTraceDirichletRhsWeakSolution (constantCoeffField a0.matrix)
      (openCubeSet Q) rho (replacementCorrectorForce a0 u g) from by
    exact exists_replacementCorrector a0 u hg)

theorem replacementCorrector_weakSolution (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    IsZeroTraceDirichletRhsWeakSolution (constantCoeffField a0.matrix)
      (openCubeSet Q) (replacementCorrector a0 u hg)
        (replacementCorrectorForce a0 u g) :=
  Classical.choose_spec (exists_replacementCorrector a0 u hg)

/-- The auxiliary solution `v_g` with the boundary values of `u`. -/
def forcedReplacement (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) : H1Function (openCubeSet Q) :=
  u - (replacementCorrector a0 u hg).toH1Function

@[simp] theorem forcedReplacement_toFun (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (forcedReplacement a0 u hg).toFun x =
      u.toFun x - (replacementCorrector a0 u hg).toH1Function.toFun x := by
  rw [forcedReplacement, H1Function.sub_toFun]

@[simp] theorem forcedReplacement_grad (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (forcedReplacement a0 u hg).grad x =
      u.grad x - (replacementCorrector a0 u hg).toH1Function.grad x := by
  rw [forcedReplacement, H1Function.sub_grad]

theorem replacementCorrector_toFun_eq_sub (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (replacementCorrector a0 u hg).toH1Function.toFun x =
      u.toFun x - (forcedReplacement a0 u hg).toFun x := by
  rw [forcedReplacement_toFun]
  ring

theorem replacementCorrector_grad_eq_sub (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (replacementCorrector a0 u hg).toH1Function.grad x =
      u.grad x - (forcedReplacement a0 u hg).grad x := by
  rw [forcedReplacement_grad]
  funext i
  simp

/-- `v_g` solves the constant-coefficient forced equation. -/
theorem isConstantCoeffForcedEquation_forcedReplacement
    (a0 : Ch03.ConstantCoeffMatrix d) (u : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g) :
    Ch03.IsConstantCoeffForcedEquation Q a0 (forcedReplacement a0 u hg) g := by
  intro φ
  simp only [Ch02.cubeDomain_coe]
  have hflux : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul a0.matrix (u.grad x)) := memVectorL2_constantFlux a0 u
  have hrhoflux : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul a0.matrix
        ((replacementCorrector a0 u hg).toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn (isEllipticFieldOn_openCubeSet Q a0)
      (replacementCorrector a0 u hg).toH1Function.grad_memVectorL2
  have hsplit := integral_vecDot_sub_left_split (U := openCubeSet Q) hflux hrhoflux
    (H := fun x => matVecMul a0.matrix ((forcedReplacement a0 u hg).grad x))
    (fun x => by
      show matVecMul a0.matrix ((forcedReplacement a0 u hg).grad x) = _
      rw [forcedReplacement_grad, sub_eq_add_neg, matVecMul_add, matVecMul_neg,
        ← sub_eq_add_neg]) φ
  have hcorr := replacementCorrector_weakSolution a0 u hg φ
  have hforce := integral_vecDot_sub_left_split (U := openCubeSet Q) hflux hg
    (H := replacementCorrectorForce a0 u g) (fun _ => rfl) φ
  rw [hsplit, hcorr, hforce]
  ring

/-- The forced replacement has the boundary values of the original function,
in the exact Chapter 3 zero-trace-difference carrier. -/
theorem hasH10Difference_forcedReplacement
    (a0 : Ch03.ConstantCoeffMatrix d) (u : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g) :
    Ch03.ABK26.HasH10Difference Q u (forcedReplacement a0 u hg) := by
  refine ⟨replacementCorrector a0 u hg, ?_⟩
  exact Filter.Eventually.of_forall fun x => replacementCorrector_toFun_eq_sub a0 u hg x

/-- The source-sign forced replacement.  Chapter 3's older constant-coefficient
constructor uses the positive weak pairing, whereas ABK26 writes
`-div(a ∇v) = div g`, whose weak right-hand side is `-∫ g · ∇φ`. -/
def sourceForcedReplacement (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) : H1Function (openCubeSet Q) :=
  forcedReplacement a0 u hg.neg

/-- The source-sign replacement satisfies the exact scalar-comparator equation
used by the finite-`p` coarse-graining endpoint. -/
theorem isScalarForcedEquation_sourceForcedReplacement {sigma : ℝ} (hsigma : 0 < sigma)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) :
    Ch03.ABK26.IsScalarForcedEquation Q sigma
      (sourceForcedReplacement (scalarConstantCoeffMatrix (d := d) hsigma) u hg) g := by
  intro phi
  have hbase := isConstantCoeffForcedEquation_forcedReplacement
    (scalarConstantCoeffMatrix (d := d) hsigma) u hg.neg phi
  have hfun : (fun x => vecDot (-g x) (phi.toH1Function.grad x)) =
      fun x => -vecDot (g x) (phi.toH1Function.grad x) := by
    funext x
    rw [vecDot_neg_left]
  simp only [Pi.neg_apply] at hbase
  rw [hfun, MeasureTheory.integral_neg] at hbase
  simpa [sourceForcedReplacement, scalarConstantCoeffMatrix,
    Ch03.IsConstantCoeffForcedEquation, constantCoeffField] using hbase

theorem hasH10Difference_sourceForcedReplacement
    (a0 : Ch03.ConstantCoeffMatrix d) (u : H1Function (openCubeSet Q))
    {g : Vec d → Vec d} (hg : MemVectorL2 (openCubeSet Q) g) :
    Ch03.ABK26.HasH10Difference Q u (sourceForcedReplacement a0 u hg) :=
  hasH10Difference_forcedReplacement a0 u hg.neg

/-- The corresponding homogeneous replacement. -/
def harmonicReplacement (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) : H1Function (openCubeSet Q) :=
  forcedReplacement a0 u
    (g := (0 : Vec d → Vec d))
    (MeasureTheory.memLp_const (μ := volumeMeasureOn (openCubeSet Q))
      (p := (2 : ENNReal)) (0 : Vec d))

theorem isConstantCoeffForcedEquation_harmonicReplacement
    (a0 : Ch03.ConstantCoeffMatrix d) (u : H1Function (openCubeSet Q)) :
    Ch03.IsConstantCoeffForcedEquation Q a0 (harmonicReplacement a0 u)
      (0 : Vec d → Vec d) :=
  isConstantCoeffForcedEquation_forcedReplacement a0 u _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
