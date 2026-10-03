/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsLocalL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsHodge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszPerCellClosure

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The origin cube is the translate of itself by `0` -/

/-- The paper cube at the origin is the `0`-translate of itself: this is what
lets the centred contraction of `WholeSpaceRowsLocalL2.lean` be read on
`openCubeSet (originCube d m)`. -/
theorem translatedCube_zero (d : ℕ) (m : ℤ) :
    translatedCube d m (0 : Vec d) = openCubeSet (originCube d m) := by
  simp [translatedCube, SubdiffusiveProcess.CoarseGrainingVocab.cube]

/-! ## 2. The normalized symmetric energy of a scalar coefficient -/

/-- **Exact readout of the normalized symmetric energy.**

For a scalar coefficient field the normalized symmetric local energy squared is
the cube average of `a |∇u|²`, so multiplying by the cube volume returns the
plain Dirichlet energy on the cube. -/
theorem cubeVolume_mul_localSymmetricEnergy_sq_eq {m : ℤ}
    (acoeff : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    {a : Vec d → ℝ} (ha : ∀ y, acoeff.toCoeffField y = scalarCoeffField a y)
    (haNonneg : ∀ x, 0 ≤ a x)
    (u0 : H1Function (openCubeSet (originCube d m))) :
    cubeVolume (originCube d m) *
        (localSymmetricEnergyENorm (originCube d m) acoeff u0).toReal ^ 2 =
      ∫ x in openCubeSet (originCube d m),
        a x * vecNormSq (u0.grad x) ∂volume := by
  classical
  have hdensity : coefficientEnergyDensity acoeff.toCoeffField u0.grad =
      fun x ↦ a x * vecNormSq (u0.grad x) :=
    funext fun x ↦ coefficientEnergyDensity_scalar ha u0.grad x
  set I : ℝ := ∫ x in openCubeSet (originCube d m),
    a x * vecNormSq (u0.grad x) ∂volume with hI
  have hIcube : (∫ x in cubeSet (originCube d m),
      a x * vecNormSq (u0.grad x) ∂volume) = I := by
    rw [hI, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have hInonneg : 0 ≤ I := by
    rw [hI]
    exact setIntegral_nonneg (measurableSet_openCubeSet _)
      fun x _ ↦ mul_nonneg (haNonneg x) (vecNormSq_nonneg _)
  have havg : cubeAverage (originCube d m)
      (coefficientEnergyDensity acoeff.toCoeffField u0.grad) =
      (cubeVolume (originCube d m))⁻¹ * I := by
    rw [cubeAverage, hdensity, hIcube]
  have hvol : 0 < cubeVolume (originCube d m) := cubeVolume_pos _
  have havgNonneg : 0 ≤ cubeAverage (originCube d m)
      (coefficientEnergyDensity acoeff.toCoeffField u0.grad) := by
    rw [havg]
    positivity
  have hnorm := localSymmetricEnergyENorm_eq_ofReal_cubeAverage_coefficientEnergyDensity
    (originCube d m) acoeff u0
  rw [hnorm, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal havgNonneg, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt havgNonneg, havg]
  field_simp

/-! ## 3. The zero-forcing Caccioppoli on the origin-cube pair -/

/-- **The Caccioppoli inequality on the origin-cube pair.**

`localL2_resolvent_translatedCube_contraction` at centre `0`: for a solution of
the homogeneous massive equation `t⁻¹ w - ∇·(a ∇w) = 0` on `□_{m+1}`,

```
∫_{□_m} w² + t ∫_{□_m} a |∇w|² ≤ 4096 d Λ t 3^{-2m} ∫_{□_{m+1}} w² .
```
-/
theorem originCube_energy_le_of_massive
    {a : Vec d → ℝ} {lam Lam t : ℝ} {m : ℤ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d (m + 1)))
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (hLam : 0 ≤ Lam)
    (haLe : ∀ x ∈ openCubeSet (originCube d (m + 1)), a x ≤ Lam) (ht : 0 < t)
    (w : H1Function (openCubeSet (originCube d (m + 1))))
    (hw : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (openCubeSet (originCube d (m + 1))) w (fun _ ↦ (0 : ℝ))) :
    (∫ x in openCubeSet (originCube d m), w.toFun x ^ 2 ∂volume) +
        t * ∫ x in openCubeSet (originCube d m),
          a x * vecNormSq (w.grad x) ∂volume ≤
      4096 * (d : ℝ) * Lam * t * ((3 : ℝ) ^ m)⁻¹ ^ 2 *
        ∫ x in openCubeSet (originCube d (m + 1)), w.toFun x ^ 2 ∂volume := by
  have hset : openCubeSet (originCube d (m + 1)) =
      translatedCube d (m + 1) (0 : Vec d) := (translatedCube_zero d (m + 1)).symm
  have hsetm : translatedCube d m (0 : Vec d) =
      openCubeSet (originCube d m) := translatedCube_zero d m
  revert hEll haLe w hw
  rw [hset]
  intro hEll haLe w hw
  have hbase := localL2_resolvent_translatedCube_contraction hEll haNonneg hLam
    haLe ht w hw
  rw [hsetm] at hbase
  exact hbase

/-! ## 4. The composite consumed by the energy slot -/

/-- **The energy slot's Caccioppoli input.**

The cube-volume-weighted square of the normalized symmetric energy on the cell
is bounded by `4096 d Λ 3^{-2m}` times the `L²` mass of the solution on the
parent cell.  This is the missing ingredient (B-1) of the local flux price,
after the recentring of `isMassiveWeakSolutionOn_untranslate`. -/
theorem cubeVolume_mul_localSymmetricEnergy_sq_le_of_massive
    {a : Vec d → ℝ} {lam Lam t : ℝ} {m : ℤ}
    (acoeff : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    (ha : ∀ y, acoeff.toCoeffField y = scalarCoeffField a y)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d (m + 1)))
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (hLam : 0 ≤ Lam)
    (haLe : ∀ x ∈ openCubeSet (originCube d (m + 1)), a x ≤ Lam) (ht : 0 < t)
    (w : H1Function (openCubeSet (originCube d (m + 1))))
    (hw : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (openCubeSet (originCube d (m + 1))) w (fun _ ↦ (0 : ℝ)))
    (u0 : H1Function (openCubeSet (originCube d m)))
    (hu0 : u0.grad =ᵐ[volume.restrict (openCubeSet (originCube d m))] w.grad) :
    cubeVolume (originCube d m) *
        (localSymmetricEnergyENorm (originCube d m) acoeff u0).toReal ^ 2 ≤
      4096 * (d : ℝ) * Lam * ((3 : ℝ) ^ m)⁻¹ ^ 2 *
        ∫ x in openCubeSet (originCube d (m + 1)), w.toFun x ^ 2 ∂volume := by
  have hreadout := cubeVolume_mul_localSymmetricEnergy_sq_eq acoeff ha haNonneg u0
  have hcongr : (∫ x in openCubeSet (originCube d m),
        a x * vecNormSq (u0.grad x) ∂volume) =
      ∫ x in openCubeSet (originCube d m),
        a x * vecNormSq (w.grad x) ∂volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hu0] with x hx
    rw [hx]
  have hcacc := originCube_energy_le_of_massive hEll haNonneg hLam haLe ht w hw
  have hmass : 0 ≤ ∫ x in openCubeSet (originCube d m), w.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg (measurableSet_openCubeSet _) fun x _ ↦ sq_nonneg _
  have hkey : t * ∫ x in openCubeSet (originCube d m),
      a x * vecNormSq (w.grad x) ∂volume ≤
      4096 * (d : ℝ) * Lam * t * ((3 : ℝ) ^ m)⁻¹ ^ 2 *
        ∫ x in openCubeSet (originCube d (m + 1)), w.toFun x ^ 2 ∂volume := by
    linarith
  rw [hreadout, hcongr]
  have ht' : (0 : ℝ) < t := ht
  nlinarith [hkey, ht']

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
