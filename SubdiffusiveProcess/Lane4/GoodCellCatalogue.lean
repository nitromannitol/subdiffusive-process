import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Frozen.Assumptions.GMCModel
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import Mathlib.Tactic

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess.Lane3 SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators Topology

/-!
# Concrete good-cell catalogue (definitions only)

Definitions of the concrete root catalogue used to instantiate the K4 good-cell event
(`candidate_good_event`, `lem_affine`, `lem_goodext`): enlargement factors `0, 1, gH`
(self, pad, comparison root), root shifts `{-1/2, 0, 1/2}^d`, observation centres, the reference
scalar `s_N`, the finite score prefixes, and the per-cell good event built from limit arrays.
This file proves nothing and asserts no estimate.
-/

noncomputable section
namespace SubdiffusiveProcess

variable {d : ℕ}

/-- Enlargement factors of the good-cell catalogue: self `0`, pad `1`, comparison root `gH`. -/
def gcat_factor (gH : ℕ) : Fin 3 → ℕ := ![0, 1, gH]

/-- Root shift labels `t i ∈ Fin 3` ↦ `(t i - 1)/2 ∈ {-1/2, 0, 1/2}`. -/
def gcat_shift (t : Fin d → Fin 3) : SpatialCoordinates d := fun i => (((t i : ℕ) : ℝ) - 1) / 2

/-- Integer level of the root `U` of the cell of level `k`. -/
def gcat_rootLevel (gH k : ℕ) (U : Fin 3 × (Fin d → Fin 3)) : ℤ := (k : ℤ) - (gcat_factor gH U.1 : ℤ)

/-- Side of the root `U`. -/
def gcat_rootSide (gH k : ℕ) (U : Fin 3 × (Fin d → Fin 3)) : ℝ := (3 : ℝ) ^ (-(gcat_rootLevel gH k U))

/-- Centre of the root `U` of the cell of level `k` and centre `z`. -/
def gcat_rootCentre (gH k : ℕ) (z : SpatialCoordinates d) (U : Fin 3 × (Fin d → Fin 3)) :
    SpatialCoordinates d := z + gcat_rootSide gH k U • gcat_shift U.2

/-- Observation centres: descendant centres of `U` at depth `D`, or root centres. -/
def gcat_obsCentre (gH k : ℕ) (z : SpatialCoordinates d) (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ)
    (code : (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) : SpatialCoordinates d :=
  Sum.elim (fun w => descendantCenter 1 (gcat_rootCentre gH k z U) (gcat_rootSide gH k U) D w)
    (fun V => gcat_rootCentre gH k z V) code

/-- The reference scalar `s_N(l, w)` (one for invalid `N < l`). -/
def gcat_sN [MeasurableSpace C(SpatialCoordinates d, ℝ)] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (l : ℤ)
    (w : SpatialCoordinates d) (omega : BilateralField d) : ℝ :=
  if l ≤ (N : ℤ) then
    (let kappa : ℕ → ℝ := fun J =>
      Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
     let retained : ℤ → SpatialCoordinates d → BilateralField d → ℝ :=
       fun ell v beta => if 0 ≤ ell then ∑ j ∈ Finset.Ico (0 : ℤ) ell, beta (-j) v
         else -∑ j ∈ Finset.Ico ell (0 : ℤ), beta (-j) v
     kappa ((N : ℤ) - l).toNat / kappa N * Real.exp (H omega w + retained l w omega))
  else 1

/-- Finite prefix sums of a real score array `X` (used for `Z` and `D.toReal`). -/
def gcat_prefix (gH cbuf k : ℕ) (z : SpatialCoordinates d)
    (X : ℕ → ℕ → Vec d → BilateralField d → ℝ) (N : ℕ) (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ)
    (code : (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) (omega : BilateralField d) : ℝ :=
  if gcat_rootLevel gH k U + (D : ℤ) ≤ (N : ℤ) then
    ∑ j ∈ Finset.Icc (gcat_rootLevel gH k U - (cbuf : ℤ)) (gcat_rootLevel gH k U + (D : ℤ)),
      if 0 ≤ (N : ℤ) - j then
        X N ((N : ℤ) - j).toNat (((3 : ℝ) ^ N) • gcat_obsCentre gH k z U D code) omega
      else 0
  else 0

/-- The per-cell good event, from limit arrays of the concrete catalogue (the body of
`candidate_good_event` with `Enl × Shift = Fin 3 × (Fin d → Fin 3)` and `Cmp = Unit`). -/
def gcat_good (k0 : ℕ) (lambdaLim cell epshom cdet : ℝ)
    (ZLim DLim : (Fin 3 × (Fin d → Fin 3)) → ∀ D : ℕ,
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loLim hiLim : (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (errLim ratioLim : Unit → BilateralField d → ℝ) : Set (BilateralField d) :=
  {omega |
    (∀ (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ), k0 ≤ D →
      ∀ code : (Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3)),
        ZLim U D code omega < lambdaLim * (D : ℝ) ∧
        DLim U D code omega < lambdaLim * (D : ℝ)) ∧
    (∀ U : Fin 3 × (Fin d → Fin 3), cell ≤ loLim U omega ∧ hiLim U omega ≤ cell⁻¹) ∧
    errLim () omega ≤ epshom * cdet ∧
    (∀ c : Unit, ratioLim c omega ∈ Set.Ioo (1 / 2 : ℝ) 2)}

end SubdiffusiveProcess
