
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsMesoscopicSummation

@[expose] public section

/-!
# The price summation over the mesoscopic triadic partition

`mesoscopicCrossPriceEnergyOn_of_cells`  transports the mesoscopic cross
price from a finite family of cells to an enclosing pair `(W, V)` provided the
cells are **pairwise disjoint and contained** in `W` resp. `V` and the cross term
splits exactly.  The cheapest family with those properties — and, by the splitting argument,
the family the *price* leg must use, since it needs no Caccioppoli core and
hence no half-grid translation — is the set of triadic descendants of the
contraction cube at a fixed depth: they are an exact partition of the
(half-open) cube, so all three hypotheses are equalities.

This module supplies that specialization:

* `setIntegral_openCubeSet_eq_sum_descendantsAtDepth` — a set integral over a
  triadic cube is the sum of the set integrals over its depth-`n` descendants
  (the half-open realization partitions exactly, and open and half-open cubes
  carry the same integrals);
* `mesoscopicCrossPriceEnergyOn_openCubeSet_of_descendantsAtDepth` — the price
  at the contraction cube from the per-cell price of
  `WholeSpaceRowsCellPrice.lean` on every depth-`n` descendant.

The only inputs beyond the per-cell prices are the integrability of the three
integrands on the contraction cube and the nonnegativity of the coefficient.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Set integrals over the triadic partition -/

/-- **A set integral over a triadic cube splits over the depth-`n`
descendants.**

The half-open realization `cubeSet` partitions exactly
(`cubeSet_eq_iUnion_descendantsAtDepth`, `pairwiseDisjoint_descendantsAtDepth`),
and open and half-open cubes carry the same set integrals
(`setIntegral_cubeSet_eq_setIntegral_openCubeSet`). -/
theorem setIntegral_openCubeSet_eq_sum_descendantsAtDepth
    (Q : TriadicCube d) (n : ℕ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (cubeSet Q) volume) :
    (∫ x in openCubeSet Q, f x ∂volume) =
      ∑ S ∈ descendantsAtDepth Q n, ∫ x in openCubeSet S, f x ∂volume := by
  classical
  have hmeas : ∀ S ∈ descendantsAtDepth Q n, MeasurableSet (cubeSet S) :=
    fun S _ => measurableSet_cubeSet S
  have hdisj : Set.Pairwise (↑(descendantsAtDepth Q n) : Set (TriadicCube d))
      (Function.onFun Disjoint (cubeSet : TriadicCube d → Set (Vec d))) :=
    pairwiseDisjoint_descendantsAtDepth Q n
  have hint : ∀ S ∈ descendantsAtDepth Q n, IntegrableOn f (cubeSet S) volume :=
    fun S hS => hf.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hS)
  have h1 : (∫ x in cubeSet Q, f x ∂volume) =
      ∑ S ∈ descendantsAtDepth Q n, ∫ x in cubeSet S, f x ∂volume := by
    conv_lhs => rw [cubeSet_eq_iUnion_descendantsAtDepth Q n]
    exact integral_biUnion_finset _ hmeas hdisj hint
  rw [← setIntegral_cubeSet_eq_setIntegral_openCubeSet, h1]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact setIntegral_cubeSet_eq_setIntegral_openCubeSet

/-! ## The price at the contraction cube -/

/-- **The mesoscopic cross price at the contraction cube, from the per-cell
prices on an exact mesoscopic triadic partition.**

`mesoscopicCrossPriceEnergyOn_of_cells` with `I = descendantsAtDepth Q n` and
`Ws i = Vs i = openCubeSet i`: the cross term splits exactly, and the energy and
mass hypotheses hold with equality, so no overlap multiplicity is paid. -/
theorem mesoscopicCrossPriceEnergyOn_openCubeSet_of_descendantsAtDepth
    {a : Vec d → ℝ} {w : Vec d → ℝ} {G : Vec d → Vec d} {chi : Vec d → ℝ}
    {t P R Sc : ℝ} (Q : TriadicCube d) (n : ℕ)
    (ht : 0 < t) (hP : 0 ≤ P) (hR : 0 ≤ R) (hSc : 0 ≤ Sc)
    (haNonneg : ∀ x, 0 ≤ a x)
    (hcross : IntegrableOn (fun x => a x * chi x * w x *
      vecDot (G x) (fun i ↦ (fderiv ℝ chi x) (basisVec i))) (cubeSet Q) volume)
    (henergyInt : IntegrableOn (fun x => a x * vecNormSq (G x))
      (cubeSet Q) volume)
    (hmassInt : IntegrableOn (fun x => w x ^ 2) (cubeSet Q) volume)
    (hcell : ∀ S ∈ descendantsAtDepth Q n,
      MesoscopicCrossPriceEnergyOn a (openCubeSet S) (openCubeSet S) w G chi
        t P R Sc) :
    MesoscopicCrossPriceEnergyOn a (openCubeSet Q) (openCubeSet Q) w G chi
      t P R Sc := by
  classical
  have hsplitE := setIntegral_openCubeSet_eq_sum_descendantsAtDepth Q n henergyInt
  have hsplitM := setIntegral_openCubeSet_eq_sum_descendantsAtDepth Q n hmassInt
  have hsplitC := setIntegral_openCubeSet_eq_sum_descendantsAtDepth Q n hcross
  refine mesoscopicCrossPriceEnergyOn_of_cells (descendantsAtDepth Q n)
    (Ws := fun S : TriadicCube d => openCubeSet S)
    (Vs := fun S : TriadicCube d => openCubeSet S)
    ht hP hR hSc ?_ ?_ hcell ?_ ?_ ?_
  · intro S
    exact setIntegral_nonneg (measurableSet_openCubeSet S) fun x _ ↦
      mul_nonneg (haNonneg x) (vecNormSq_nonneg _)
  · intro S
    exact setIntegral_nonneg (measurableSet_openCubeSet S) fun x _ ↦ sq_nonneg _
  · rw [hsplitC, Finset.mul_sum]
  · exact le_of_eq hsplitE.symm
  · exact le_of_eq hsplitM.symm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
