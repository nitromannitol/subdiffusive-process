module

public import SubdiffusiveProcess.Geometry.OddGridFold
public import SubdiffusiveProcess.Sobolev.ReflectionEnergy
public import SubdiffusiveProcess.Sobolev.CompactPotential

@[expose] public section

/-! # One actual continuous potential before and after folding

Composition on the compact root defines the folded potential everywhere.
On a retained cell it is exactly the pullback from the reflected original
cell. Only this bijective cell reflection transports Lp equivalence classes;
no measure-preserving property is assigned to the whole fold.
-/
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess
variable {d m : ℕ} {U Ω : Opens (SpatialCoordinates d)}

/-- Exponentiation commutes with the actual measure-preserving coefficient reflection. -/
theorem reflectionCoefficient_exp (z : SpatialCoordinates d) (I : Finset (Fin d))
    (hU : coordinateReflection z I ⁻¹' (Ω : Set (SpatialCoordinates d)) = U)
    (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    reflectionCoefficient z I hU (expPotentialCoefficient g) =
      expPotentialCoefficient (reflectionLp z I hU g) := by
  apply Subtype.ext
  apply Lp.ext
  have hm := coordinateReflection_domain_measurePreserving z I hU
  filter_upwards [reflectionCoefficient_coeFn z I hU (expPotentialCoefficient g),
    hm.quasiMeasurePreserving.ae_eq_comp (expPotentialCoefficient_coeFn g),
    expPotentialCoefficient_coeFn (reflectionLp z I hU g), reflectionLp_coeFn z I hU g]
    with x ha hg he hr
  exact ha.trans (hg.trans (by rw [he, hr]; rfl))

/-- Compact-root composition has exactly the folded point values throughout the root. -/
theorem compactPotentialExtension_comp_coordinateFoldOnCube (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (I P : Finset (Fin d)) (g : C(closedCube z r hr, ℝ))
    {x : SpatialCoordinates d} (hx : x ∈ closedCube z r hr) :
    compactPotentialExtension (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P)) x =
      compactPotentialExtension (closedCube z r hr) g (coordinateFold z I P x) := by
  calc
    _ = g (coordinateFoldOnCube z hr I P ⟨x, hx⟩) :=
      compactPotentialExtension_apply _ _ ⟨x, hx⟩
    _ = _ := (compactPotentialExtension_apply _ g (coordinateFoldOnCube z hr I P ⟨x, hx⟩)).symm

/-- The actual folded potential on a retained cell equals the L-infinity reflection of the original cell. -/
theorem reflectionLp_compactPotential_fold_cell (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (I P : Finset (Fin d))
    (k : OddGridIndex d m) (hk : k ∉ oddGridUnresolved m I) (g : C(closedCube z r hr, ℝ)) :
    reflectionLp
      (U := oddGridCell z r hr m k)
      (Ω := oddGridCell z r hr m (oddGridReflect (oddGridFoldReflections I P k) k))
      z (oddGridFoldReflections I P k)
      (coordinateReflection_preimage_oddGridCell z hr (oddGridFoldReflections I P k) k)
      (compactPotentialLp (Ω := oddGridCell z r hr m
        (oddGridReflect (oddGridFoldReflections I P k) k)) (closedCube z r hr) g) =
      compactPotentialLp (Ω := oddGridCell z r hr m k) (closedCube z r hr)
        (g.comp (coordinateFoldOnCube z hr I P)) := by
  let J := oddGridFoldReflections I P k
  let hU := coordinateReflection_preimage_oddGridCell z hr J k
  let a := compactPotentialLp (Ω := oddGridCell z r hr m (oddGridReflect J k))
    (closedCube z r hr) g
  have hm := coordinateReflection_domain_measurePreserving
    (U := oddGridCell z r hr m k) (Ω := oddGridCell z r hr m (oddGridReflect J k)) z J hU
  apply Lp.ext
  filter_upwards [reflectionLp_coeFn z J hU a,
    hm.quasiMeasurePreserving.ae_eq_comp
      (compactPotentialLp_coeFn (Ω := oddGridCell z r hr m (oddGridReflect J k))
        (closedCube z r hr) g),
    compactPotentialLp_coeFn (Ω := oddGridCell z r hr m k) (closedCube z r hr)
      (g.comp (coordinateFoldOnCube z hr I P)),
    ae_restrict_mem (oddGridCell z r hr m k).isOpen.measurableSet] with x ha hg he hx
  change reflectionLp z J hU a x = _
  rw [ha, hg, he]
  change compactPotentialExtension (closedCube z r hr) g (coordinateReflection z J x) = _
  rw [compactPotentialExtension_comp_coordinateFoldOnCube z hr I P g
    (centeredCube_subset_closedCube z hr (oddGridCell_subset z hr m k hx)),
    coordinateFold_eqOn_oddGridCell z hr I P k hk hx]

/-- The folded exponential coefficient is the same original-cell coefficient pulled back by reflection. -/
theorem reflectionCoefficient_compactPotential_fold_cell (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (I P : Finset (Fin d))
    (k : OddGridIndex d m) (hk : k ∉ oddGridUnresolved m I) (g : C(closedCube z r hr, ℝ)) :
    reflectionCoefficient
      (U := oddGridCell z r hr m k)
      (Ω := oddGridCell z r hr m (oddGridReflect (oddGridFoldReflections I P k) k))
      z (oddGridFoldReflections I P k)
      (coordinateReflection_preimage_oddGridCell z hr (oddGridFoldReflections I P k) k)
      (expPotentialCoefficient (compactPotentialLp (Ω := oddGridCell z r hr m
        (oddGridReflect (oddGridFoldReflections I P k) k)) (closedCube z r hr) g)) =
      expPotentialCoefficient (compactPotentialLp (Ω := oddGridCell z r hr m k)
        (closedCube z r hr) (g.comp (coordinateFoldOnCube z hr I P))) := by
  rw [reflectionCoefficient_exp, reflectionLp_compactPotential_fold_cell z hr I P k hk g]

end SubdiffusiveProcess
