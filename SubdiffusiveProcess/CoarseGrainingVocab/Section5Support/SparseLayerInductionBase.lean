module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StrictDecayConstants

@[expose] public section

/-!
# The base case `N = 0` of the sparse induction

`e.strict.decay.qR.def` and `e.strict.decay.sparse.induction` opens Step 3 with

> For `N = 0`, this follows because the continuum minimum is bounded above by
> `Q_{R,pi}(p)` in `e.strict.decay.qR.def`.

The only
gap between `qStarCell_le_qRCell` and the printed statement is the identity
`A_0^{(R)} = B_0`, i.e. `Finset.prod_range_one`.  This file closes it.

* `sparseLayerCoefficient_zero` -- the empty-spacing identity
  `A_0^{(R)} = B_0` for every spacing `R`;
* `integral_vecDot_randomSparseMatrix_zero` -- consequently
  `E[p . A_0^{(R)}(spx) p] = qStarSlope M spx p`, the quantity `q_*` is the
  supremum of;
* **`integral_vecDot_randomSparseMatrix_zero_le`** -- the base case in the shape
  of `e.strict.decay.sparse.induction` at `N = 0`:

  ```text
  E[p . A_0^{(R)}(spx_0^pi) p] <= q_R |p|^2      (|p| = 1),
  ```

  with `q_R = qRCell M (unitMesh d (-R)) spx` the constant selected below
  one.

## Scope

The statement is at the *unit-scale* simplex `spx_0^pi`, which is where the
induction starts.  Transporting it to the simplices `spx_{NR}^pi` that the
inductive step consumes needs the scaling and stationarity covariance of
`dirichletInfOn`, which is not proved anywhere in the tree; see the bundle
report for the exact remaining statement.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Homogenization.Book Kuhn MeasureTheory
open _root_.SubdiffusiveProcess.Model

noncomputable section

variable {d : ℕ}

/-- **`A_0^{(R)} = B_0`** (`p.homogenized.coefficient.strict.decay` at `N = 0`): the sparse
product over the single layer `0` is the shell factor itself, for every
spacing. -/
@[simp] theorem sparseLayerCoefficient_zero (M : GMCModel d) (R : ℕ)
    (omega : PotentialSample d) :
    sparseLayerCoefficient M R 0 omega = shellFactor M 0 omega := by
  funext x
  simp [sparseLayerCoefficient]

/-- The sparse matrix at `N = 0` is the one-cell shell matrix `B_0(spx)`. -/
theorem vecDot_randomSparseMatrix_zero (M : GMCModel d) (R : ℕ)
    (T : KuhnCell d) (omega : PotentialSample d) (p : Vec d) :
    vecDot p (matVecMul (randomSparseMatrix M R 0 (kuhnCellDomain T) omega) p) =
      vecDot p (matVecMul (randomShellMatrix M 0 T omega) p) := by
  rw [vecDot_randomSparseMatrix_eq, sparseLayerCoefficient_zero,
    kuhnCellDomain_coe]
  exact (vecDot_aMatrix_eq_dirichletInfOn
    (shellFactorCoeffOnData M 0 omega (kuhnCellDomain T))
    (fun x => (shellFactor_pos M 0 omega x).le) p).symm

/-- `E[p . A_0^{(R)}(spx) p]` is the quantity `q_*` is the supremum of. -/
theorem integral_vecDot_randomSparseMatrix_zero (M : GMCModel d) (R : ℕ)
    (T : KuhnCell d) (p : Vec d) :
    ∫ omega, vecDot p
        (matVecMul (randomSparseMatrix M R 0 (kuhnCellDomain T) omega) p)
      ∂M.P.toMeasure = qStarSlope M T p := by
  simp only [vecDot_randomSparseMatrix_zero]
  rfl

/-- **The base case of `e.strict.decay.sparse.induction`.**  At `N = 0` the
sparse coefficient is `B_0`, and the continuum minimum is dominated by the
piecewise-affine one, so the expected quadratic form is at most `q_R`. -/
theorem integral_vecDot_randomSparseMatrix_zero_le (M : GMCModel d) (R : ℕ)
    {T : KuhnCell d} (hT : T.supportCube = originCube d 0) {j : ℤ} (hj : j ≤ 0)
    {p : Vec d} (hp : p ∈ vecUnitSphere d) :
    ∫ omega, vecDot p
        (matVecMul (randomSparseMatrix M R 0 (kuhnCellDomain T) omega) p)
      ∂M.P.toMeasure ≤ qRCell M (unitMesh d j) T := by
  rw [integral_vecDot_randomSparseMatrix_zero]
  exact le_trans (qStarSlope_le_qRSlope M hT hj p)
    (qRSlope_le_qRCell M (fun V hV => closedCarrier_subset_of_mem_unitMesh hj hV) T hp)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
