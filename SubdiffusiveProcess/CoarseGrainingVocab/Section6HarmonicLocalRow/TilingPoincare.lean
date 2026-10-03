module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryZeroSetPoincare

@[expose] public section

/-!
# Summing a local estimate over a disjoint tile family

The slab Poincare of `ledger/reports/provider-37-harmonic-local-row.md` §13 is
obtained by tiling the doubled slab by small cubes straddling the boundary
face, applying the landed zero-set Poincare
(`BoundaryZeroSetPoincare.eLpNorm_le_of_zeroSet_of_volume_le`) on each tile —
where the mirror half is a zero set of exactly half the tile's volume, so
`K = 2` — and summing.  The point of tiling rather than using one big cube is
that the zero-set Poincare constant is proportional to the *side of the cube it
is applied to*: tiles of side `delta` give a constant `C(d) * delta`, which is
the free smallness the radius recurrence needs.

This module contains the summation step, stated for plain set integrals of
squares so that no `eLpNorm`/`ENNReal` algebra is needed at the point of use.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow

open MeasureTheory Homogenization

noncomputable section

variable {d : ℕ}

/-- A strict inclusion gives the a.e. cover hypothesis.  Note that for *open*
tiles (such as `axisCube`) a strict inclusion is never available: the union of
open tiles misses the grid faces.  That null set is exactly why the covering
hypothesis below is stated a.e. -/
theorem ae_cover_of_subset {S T : Set (Vec d)} (h : S ⊆ T) :
    volume (S \ T) = 0 := by
  simp [Set.diff_eq_empty.mpr h]

/-- **Tile summation.**  A local square estimate valid on each member of a
finite pairwise-disjoint measurable family transfers, with the same constant,
to any subset of their union. -/
theorem setIntegral_sq_le_of_tiling
    {S : Set (Vec d)} {f g : Vec d → ℝ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → Set (Vec d))
    (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : volume (S \ ⋃ i, A i) = 0)
    (hfint : ∀ i, IntegrableOn (fun x ↦ f x ^ 2) (A i))
    (hgint : ∀ i, IntegrableOn (fun x ↦ g x ^ 2) (A i))
    {c : ℝ}
    (htile : ∀ i, ∫ x in A i, f x ^ 2 ≤ c * ∫ x in A i, g x ^ 2) :
    ∫ x in S, f x ^ 2 ≤ c * ∫ x in ⋃ i, A i, g x ^ 2 := by
  have hUmeas : MeasurableSet (⋃ i, A i) := MeasurableSet.iUnion hmeas
  have hfU : IntegrableOn (fun x ↦ f x ^ 2) (⋃ i, A i) :=
    (integrableOn_finset_iUnion (s := (Finset.univ : Finset ι))).mpr (fun i _ ↦ hfint i)
      |>.mono_set (by simp)
  have hgU : IntegrableOn (fun x ↦ g x ^ 2) (⋃ i, A i) :=
    (integrableOn_finset_iUnion (s := (Finset.univ : Finset ι))).mpr (fun i _ ↦ hgint i)
      |>.mono_set (by simp)
  -- restrict to `S`
  have hmono : ∫ x in S, f x ^ 2 ≤ ∫ x in ⋃ i, A i, f x ^ 2 :=
    setIntegral_mono_set hfU (Filter.Eventually.of_forall fun x ↦ sq_nonneg (f x))
      (MeasureTheory.ae_le_set.mpr hcover)
  -- split both sides over the family
  have hsplitf : ∫ x in ⋃ i, A i, f x ^ 2 = ∑ i, ∫ x in A i, f x ^ 2 := by
    rw [show (⋃ i, A i) = ⋃ i ∈ (Finset.univ : Finset ι), A i by simp]
    exact integral_biUnion_finset Finset.univ (fun i _ ↦ hmeas i)
      (fun i _ j _ hij ↦ hdisj hij) (fun i _ ↦ hfint i)
  have hsplitg : ∫ x in ⋃ i, A i, g x ^ 2 = ∑ i, ∫ x in A i, g x ^ 2 := by
    rw [show (⋃ i, A i) = ⋃ i ∈ (Finset.univ : Finset ι), A i by simp]
    exact integral_biUnion_finset Finset.univ (fun i _ ↦ hmeas i)
      (fun i _ j _ hij ↦ hdisj hij) (fun i _ ↦ hgint i)
  have hsum : ∑ i, ∫ x in A i, f x ^ 2 ≤ ∑ i, c * ∫ x in A i, g x ^ 2 :=
    Finset.sum_le_sum fun i _ ↦ htile i
  rw [hsplitg, Finset.mul_sum]
  calc ∫ x in S, f x ^ 2 ≤ ∫ x in ⋃ i, A i, f x ^ 2 := hmono
    _ = ∑ i, ∫ x in A i, f x ^ 2 := hsplitf
    _ ≤ ∑ i, c * ∫ x in A i, g x ^ 2 := hsum

/-- Cauchy-Schwarz over the `d` gradient components: the zero-set Poincare is
stated with a *sum of component norms*, and the tiling needs a sum of squares. -/
theorem sq_sum_le_card_smul {n : ℕ} (b : Fin n → ℝ) :
    (∑ i, b i) ^ 2 ≤ (n : ℝ) * ∑ i, b i ^ 2 := by
  simpa using
    sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := b)

/-- **Slab Poincare from a tile family.**  Given the per-tile estimate with a
constant proportional to the tile side `L`, the same constant controls the
whole slab.  The right-hand side is enlarged to any ambient set `W` containing
the tiles — in the application `W` is the doubled slab, on which the zero
extension has gradient supported in the interior slab. -/
theorem setIntegral_sq_le_of_tiling_ambient
    {S W : Set (Vec d)} {f g : Vec d → ℝ} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : ι → Set (Vec d))
    (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : volume (S \ ⋃ i, A i) = 0) (hinside : (⋃ i, A i) ⊆ W)
    (hfint : ∀ i, IntegrableOn (fun x ↦ f x ^ 2) (A i))
    (hgint : ∀ i, IntegrableOn (fun x ↦ g x ^ 2) (A i))
    (hgW : IntegrableOn (fun x ↦ g x ^ 2) W)
    {c : ℝ} (hc : 0 ≤ c)
    (htile : ∀ i, ∫ x in A i, f x ^ 2 ≤ c * ∫ x in A i, g x ^ 2) :
    ∫ x in S, f x ^ 2 ≤ c * ∫ x in W, g x ^ 2 := by
  have hmain := setIntegral_sq_le_of_tiling A hmeas hdisj hcover hfint hgint htile
  have hmono : ∫ x in ⋃ i, A i, g x ^ 2 ≤ ∫ x in W, g x ^ 2 :=
    setIntegral_mono_set hgW
      (Filter.Eventually.of_forall fun x ↦ sq_nonneg (g x))
      (HasSubset.Subset.eventuallyLE hinside)
  exact hmain.trans (mul_le_mul_of_nonneg_left hmono hc)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicLocalRow
