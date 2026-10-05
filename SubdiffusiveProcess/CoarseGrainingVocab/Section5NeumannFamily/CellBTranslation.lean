module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.OverlapFamilyBudgets

@[expose] public section

/-!
# Translation covariance of the literal cell observable `B_z`

The Calderon--Zygmund package
(`exists_oneStepShell_scalarDivergence_cz`) and hence the whole
descendant-average Dirichlet machinery is stated **only on origin cubes**
`originCube d m`.  The retained parents of the two-radius family are
concentric cubes centred at `cubeCenter S`, which are translates of origin
cubes but not themselves triadic.  Transporting the Dirichlet budget therefore
requires knowing that `oneStepCellB` is translation covariant.

The statement below is deliberately cast-free: it relates two cells and two
weak Hessians through a *pointwise* relation between their `hess` fields, so
no `Eq.rec` on Sobolev carriers ever appears.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- The scalar `L²` norm of one Hessian coordinate is its `eLpNorm`. -/
theorem norm_hessCoordToScalarL2_eq_eLpNorm {U : Set (Vec d)}
    {u : H1Function U} (H : HasWeakHessianOn U u) (i j : Fin d) :
    ‖H.hessCoordToScalarL2 i j‖ =
      (eLpNorm (H.hess i j) 2 (volumeMeasureOn U)).toReal := by
  unfold HasWeakHessianOn.hessCoordToScalarL2 Homogenization.toScalarL2
  rw [Lp.norm_toLp]

/-- Literal `eLpNorm` form of the cell observable. -/
theorem oneStepCellB_eq_sum_eLpNorm (R : TriadicCube d)
    {u : H1Function (openCubeSet R)}
    (H : HasWeakHessianOn (openCubeSet R) u) :
    oneStepCellB R H =
      cubeScaleFactor R * ((cubeVolume R)⁻¹) ^ (1 / 2 : ℝ) *
        ∑ i : Fin d, ∑ j : Fin d,
          (eLpNorm (H.hess i j) 2
            (volumeMeasureOn (openCubeSet R))).toReal := by
  unfold oneStepCellB oneStepCellNormalizedHessianSize
  rw [← mul_assoc]
  congr 1
  unfold HasWeakHessianOn.hessianCoordL2NormSum
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ =>
      norm_hessCoordToScalarL2_eq_eLpNorm H i j

/-- Translation covariance of the literal cell observable.  Only a pointwise
relation between the two `hess` fields and equality of the two scales is
used. -/
theorem oneStepCellB_translate_eq {R R' : TriadicCube d} (z : Vec d)
    (hset : openCubeSet R' = translateSet z (openCubeSet R))
    (hscale : R'.scale = R.scale)
    {u : H1Function (openCubeSet R)} (H : HasWeakHessianOn (openCubeSet R) u)
    {u' : H1Function (openCubeSet R')}
    (H' : HasWeakHessianOn (openCubeSet R') u')
    (hhess : ∀ i j x, H'.hess i j x = H.hess i j (x - z)) :
    oneStepCellB R' H' = oneStepCellB R H := by
  rw [oneStepCellB_eq_sum_eLpNorm, oneStepCellB_eq_sum_eLpNorm]
  have hsf : cubeScaleFactor R' = cubeScaleFactor R := by
    simp only [cubeScaleFactor, hscale]
  have hvol : cubeVolume R' = cubeVolume R := by
    simp only [cubeVolume, hsf]
  rw [hsf, hvol]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hfun : H'.hess i j = fun x => H.hess i j (x - z) := funext (hhess i j)
  rw [hfun]
  congr 1
  rw [hset]
  exact eLpNorm_comp_measurePreserving
    (H.hess_memL2 i j).aestronglyMeasurable
    (measurePreserving_subRight_restrict_translateSet z (openCubeSet R))

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
