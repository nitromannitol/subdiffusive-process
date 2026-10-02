import SubdiffusiveProcess.Section10.RetainedPrefixComparison
import SubdiffusiveProcess.Section10.RetainedPrefixReadoutCube
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerConclusion

/-!
# Finite-cube ahom readout at arbitrary cutoffs

The sole mathematical input is the lawful retained-prefix induction bound.
The comparison reinserts all omitted layers up to any later cutoff m, even
between retained scales. One finite cube at scale ell+NR suffices for ahom.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (ahom abarScalarReadout abarScalarReadout_nonneg
  randomAMatrix aCutoffCoeffOnData)
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

/-- An actual retained-prefix induction bound and index inclusion imply the
ahom bound at every later full cutoff; no positivity premise for kap is added. -/
theorem ahom_le_of_retainedPrefixSparseBound {d : ℕ} (M : GMCModel d)
    {ell R N m : ℕ} (hm : ell + N * R ≤ m) {kap : ℝ}
    (hIH : RetainedPrefixSparseBound M ell R N kap) : ahom M m ≤ kap := by
  obtain ⟨n0, rfl⟩ : ∃ n0 : ℕ, d = n0 + 1 :=
    ⟨d - 1, by have := M.shellPrefix.dimension; omega⟩
  let k := ell + N * R
  let Q : TriadicCube (n0 + 1) := originCube (n0 + 1) (k : ℤ)
  let U := Ch02.cubeDomain Q
  let e : Vec (n0 + 1) := Pi.single (0 : Fin (n0 + 1)) (1 : ℝ)
  have hle : ahom M m ≤ abarScalarReadout M m k := by
    rw [ahom]
    refine csInf_le ⟨0, ?_⟩ ⟨k, rfl⟩
    rintro x ⟨j, rfl⟩
    exact abarScalarReadout_nonneg M m j
  refine hle.trans ?_
  rw [abarScalarReadout_eq_integral_vecDot M m k (0 : Fin (n0 + 1))]
  have hfull (omega : PotentialSample (n0 + 1)) :
      vecDot e (matVecMul (randomAMatrix M m U omega) e) =
        (volume (openCubeSet Q)).toReal⁻¹ *
          dirichletInfOn (aCutoff M m omega) (openCubeSet Q) e := by
    rw [randomAMatrix, vecDot_aMatrix_eq_dirichletInfOn
      (aCutoffCoeffOnData M m omega U) (fun _ => (Real.exp_pos _).le) e]
    rfl
  have hcomp : ∫ omega, vecDot e (matVecMul (randomAMatrix M m U omega) e)
      ∂M.P.toMeasure ≤
      ∫ omega, retainedPrefixCubeEnergy M ell R N Q omega e ∂M.P.toMeasure := by
    simp_rw [hfull]
    unfold retainedPrefixCubeEnergy
    rw [integral_const_mul, integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_aCutoff_dirichletInfOn_le_retainedPrefix M hm
        (isOpenBoundedConvexDomain_openCubeSet Q) (subset_refl _) e) (by positivity)
  refine hcomp.trans ?_
  have hcube := integral_retainedPrefixCubeEnergy_le M ell R N hIH Q rfl e
  simpa only [e, vecNormSq_single, mul_one] using hcube

end

end SubdiffusiveProcess.Section10
