module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeConstantTorsionTransport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubePositiveScaleTailDirichlet
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
@[expose] public section

/-!
An actual translated response test controls the physical unit-forcing torsion
discrepancy at the raw cutoff. The tolerances are chosen before the model; the
comparison derives both unit-cube equations and pays the exact physical scale.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Filter SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Section9
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open scoped ENNReal BigOperators Pointwise
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Small actual response gives the physical torsion comparison on positive scales. -/
theorem exists_goodCube_positiveScale_torsion_comparison
    (d J : ℕ) [NeZero d] (hd : 2 ≤ d) (eps : ℝ) (heps : 0 < eps) :
    ∃ c e : ℝ, 0 < c ∧ 0 < e ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ c →
      ∀ n m : ℕ, m ≤ n → n - m ≤ J → ∀ z : Vec d,
        ∀ᵐ omega ∂M.P.toMeasure,
          ellipticityMomentObservable M n (m : ℤ) (1 / 8)
              (translatePotentialSample z omega) ≤ ENNReal.ofReal e →
          ∀ u w : H10Function (openCubeSet (originCube d (m : ℤ))),
            IsMassiveWeakSolutionOn
              (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega))
              (fun _ => 1) 0 (openCubeSet (originCube d (m : ℤ)))
              u.toH1Function (fun _ => 1) →
            IsMassiveWeakSolutionOn (fun _ => ahom M n) (fun _ => 1) 0
              (openCubeSet (originCube d (m : ℤ))) w.toH1Function (fun _ => 1) →
            cubeLpNorm (originCube d (m : ℤ)) 2
                (fun x => u.toH1Function.toFun x - w.toH1Function.toFun x) ≤
              eps * (cubeScaleFactor (originCube d (m : ℤ))) ^ 2 / ahom M n := by
  obtain ⟨c, e, hc, he, hcomp⟩ :=
    exists_goodCube_positiveScale_dirichlet_comparison d J hd eps heps
  refine ⟨c, e, hc, he, ?_⟩
  intro M hM n m hmn hmJ z
  filter_upwards [hcomp M hM n m hmn hmJ z] with omega homega
  intro hobs u w hu hw
  have hapos : 0 < ahom M n := ahom_pos M n
  have hane : ahom M n ≠ 0 := ne_of_gt hapos
  haveI : MeasureTheory.IsFiniteMeasure
      (volume.restrict (openCubeSet (originCube d 0))) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d 0)).isFiniteMeasure_restrict_volume
  have hf : MemLp (fun _ : Vec d => (1 : ℝ)) 2
      (volume.restrict (openCubeSet (originCube d 0))) := memLp_const _
  have hunit : l2Size (originCube d 0) (fun _ : Vec d => (1 : ℝ)) = 1 := by
    have h1 : l2Size (originCube d 0) (fun _ : Vec d => (1 : ℝ))
        = eLpNorm (fun _ : Vec d => (1 : ℝ)) 2
            (volume.restrict (openCubeSet (originCube d 0))) := rfl
    rw [h1, MeasureTheory.eLpNorm_const' (1 : ℝ) (by simp) (by simp),
      MeasureTheory.Measure.restrict_apply_univ, volume_openCubeSet_originCube_zero]
    simp
  have huU : IsScalarDirichletSolutionOn
      (scalarCoeffField (rescaledCutoffCoefficient M n m (translatePotentialSample z omega)))
      (originCube d 0)
      (goodCubeTorsionPullback (ahom M n) u).toH1Function
      (goodCubeZeroH2Datum (originCube d 0)).toH1 (fun _ => 1) := by
    have h := goodCube_isScalarDirichlet_torsionPullback (m := (m : ℤ))
      (alpha := ahom M n) hapos
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample z omega)) u hu
    simpa only [rescaledCutoffCoefficient, centeredCubeScale, zpow_natCast] using! h
  have hwW : IsScalarDirichletSolutionOn (fun _ => (1 : Mat d))
      (originCube d 0)
      (goodCubeTorsionPullback (ahom M n) w).toH1Function
      (goodCubeZeroH2Datum (originCube d 0)).toH1 (fun _ => 1) := by
    have h := goodCube_isScalarDirichlet_torsionPullback (m := (m : ℤ))
      (alpha := ahom M n) hapos (fun _ : Vec d => ahom M n) w hw
    simpa only [inv_mul_cancel₀ hane, scalarCoeffField_one] using h
  have key : l2Size (originCube d 0) (fun x =>
      (goodCubeTorsionPullback (ahom M n) u).toH1Function.toFun x -
        (goodCubeTorsionPullback (ahom M n) w).toH1Function.toFun x) ≤
      ENNReal.ofReal eps := by
    have h := homega hobs (fun _ : Vec d => (1 : ℝ)) hf
      (goodCubeZeroH2Datum (originCube d 0))
      (goodCubeTorsionPullback (ahom M n) u).toH1Function
      (goodCubeTorsionPullback (ahom M n) w).toH1Function huU hwW
    rw [goodCubeZeroH2Datum_norm, add_zero, hunit, mul_one] at h
    exact h
  have hfinal := goodCube_cubeLpNorm_le_of_torsionPullback_l2Size_le
    (m := (m : ℤ)) (alpha := ahom M n) (eps := eps) hapos heps.le u w key
  simp only [centeredCubeScale] at hfinal
  rw [cubeScaleFactor_originCube]
  exact hfinal.trans (le_of_eq (by ring))

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
