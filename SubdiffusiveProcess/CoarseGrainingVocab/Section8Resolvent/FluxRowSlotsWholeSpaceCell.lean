
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowRieszTranslatedCell
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables

@[expose] public section

/-!
# The Caccioppoli slot for the whole-space carrier, on a translated cell

`FluxRowSlotsCaccioppoli.lean` proved the Caccioppoli inequality for a *local*
zero-forcing massive solution on the origin-cube pair.  This file composes it
with the whole-space carrier and with the recentring, producing the
statement the energy slot  actually consumes:

```
|Q| ‖u‖²_{E(Q)} ≤ 4096 d Λ 3^{-2m} ∫_{Q̂} u²      (Q = z + □_m, Q̂ = z + □_{m+1})
```

for a `WholeSpaceDivergenceResolventSolution` and for the *recentred* energy
`localSymmetricEnergyENorm (originCube d m) a(·+z) u0` that the Section 2
coarse-graining anchor uses.

The two halves are

* `wholeSpaceSolution_translatedCell_energy_le_of_zero_source` — the carrier
  version of `localL2_resolvent_translatedCube_contraction`, valid on a cell
  whose parent misses the source (`hf0`), which is exactly the manuscript's
  "the terms containing `f` occur only for `Q ∈ 𝒞`"; and
* `cubeVolume_mul_recentred_localSymmetricEnergy_sq_eq` — the change of
  variables identifying the recentred normalized symmetric energy with the
  plain Dirichlet energy on the translated cell.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Section8
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The carrier version of the translated-cell Caccioppoli -/

/-- **The Caccioppoli inequality for the whole-space carrier on a translated
cell.**

The carrier only promises a local `H¹` solution on each open bounded
convex domain; the datum vanishing on the enlargement makes that local equation
homogeneous, and `localL2_resolvent_translatedCube_contraction` then applies.
Both the mass and the energy of the local solution are transported back to the
carrier's own fields (the gradient only almost everywhere, which is all the
integral needs). -/
theorem wholeSpaceSolution_translatedCell_energy_le_of_zero_source
    {a f : Vec d → ℝ} {lam Lam t : ℝ} {m : ℤ} {z : Vec d}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (m + 1) z, f x = 0)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (m + 1) z)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (hLam : 0 ≤ Lam)
    (haLe : ∀ x ∈ translatedCube d (m + 1) z, a x ≤ Lam) (ht : 0 < t) :
    (∫ x in translatedCube d m z, a x * vecNormSq (u.grad x) ∂volume) ≤
      4096 * (d : ℝ) * Lam * ((3 : ℝ) ^ m)⁻¹ ^ 2 *
        ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume := by
  classical
  have hWdom : IsOpenBoundedConvexDomain (translatedCube d (m + 1) z) :=
    isOpenBoundedConvexDomain_translatedCube (m + 1) z
  have hWmeas : MeasurableSet (translatedCube d (m + 1) z) :=
    hWdom.isOpen.measurableSet
  have hQmeas : MeasurableSet (translatedCube d m z) :=
    (isOpenBoundedConvexDomain_translatedCube m z).isOpen.measurableSet
  have hQW : translatedCube d m z ⊆ translatedCube d (m + 1) z :=
    translatedCube_subset_succ d m z
  obtain ⟨v, hval, hgrad, hsol⟩ :=
    u.locally_weak_solution (translatedCube d (m + 1) z) hWdom
  have hsol0 : IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹
      (translatedCube d (m + 1) z) v (fun _ ↦ (0 : ℝ)) := by
    intro phi
    refine (hsol phi).trans ?_
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    simp [hf0 x hx]
  have hbase := localL2_resolvent_translatedCube_contraction hEll haNonneg hLam
    haLe ht v hsol0
  have hgradQ : v.grad =ᵐ[volume.restrict (translatedCube d m z)] u.grad :=
    ae_restrict_of_ae_restrict_of_subset hQW hgrad
  have hEnergy : (∫ x in translatedCube d m z,
      a x * vecNormSq (v.grad x) ∂volume) =
      ∫ x in translatedCube d m z, a x * vecNormSq (u.grad x) ∂volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hgradQ] with x hx
    rw [hx]
  have hWval : (∫ x in translatedCube d (m + 1) z, v.toFun x ^ 2 ∂volume) =
      ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume := by
    refine setIntegral_congr_fun hWmeas fun x hx ↦ ?_
    rw [hval x hx]
  have hmassQ : 0 ≤ ∫ x in translatedCube d m z, v.toFun x ^ 2 ∂volume :=
    setIntegral_nonneg hQmeas fun x _ ↦ sq_nonneg _
  rw [hEnergy, hWval] at hbase
  nlinarith [hbase, hmassQ, ht]

/-! ## 2. The recentred normalized energy is the translated-cell energy -/

/-- **Change of variables for the recentred normalized symmetric energy.**

If `u0` is the recentring of a field `G` (`u0.grad x = G (x + z)` a.e. on the
origin cube) and the recentred coefficient is `a (· + z)`, then the cube-volume
weighted square of `localSymmetricEnergyENorm` on the origin cube is the plain
Dirichlet energy of `G` on the translated cell. -/
theorem cubeVolume_mul_recentred_localSymmetricEnergy_sq_eq {m : ℤ} (z : Vec d)
    (acoeff : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    {a : Vec d → ℝ}
    (ha : ∀ y, acoeff.toCoeffField y = scalarCoeffField (fun x ↦ a (x + z)) y)
    (haNonneg : ∀ x, 0 ≤ a x)
    (u0 : H1Function (openCubeSet (originCube d m))) (G : Vec d → Vec d)
    (hu0 : u0.grad =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      fun x ↦ G (x + z)) :
    cubeVolume (originCube d m) *
        (localSymmetricEnergyENorm (originCube d m) acoeff u0).toReal ^ 2 =
      ∫ x in translatedCube d m z, a x * vecNormSq (G x) ∂volume := by
  have hreadout := cubeVolume_mul_localSymmetricEnergy_sq_eq acoeff ha
    (fun x ↦ haNonneg (x + z)) u0
  have hcongr : (∫ x in openCubeSet (originCube d m),
        a (x + z) * vecNormSq (u0.grad x) ∂volume) =
      ∫ x in openCubeSet (originCube d m),
        a (x + z) * vecNormSq (G (x + z)) ∂volume := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hu0] with x hx
    rw [hx]
  have htrans := setIntegral_comp_addRight_translateSet (d := d) z
    (openCubeSet (originCube d m)) (fun y ↦ a y * vecNormSq (G y))
  rw [hreadout, hcongr, htrans, ← fluxRowRiesz_translatedCube_eq_translateSet]

/-! ## 2b. The recentred cutoff family is the translated coefficient -/

/-- The coefficient representative of the recentred cutoff family on any triadic
cube is the translate `a_L(· + z)` of the global cutoff coefficient.  This is the
`ha` hypothesis of §3 for the family the local flux price is stated
with. -/
theorem aCutoffFamily_translatePotentialSample_coeffOn_toCoeffField
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (z : Vec d)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) (Q : TriadicCube d) :
    ∀ y, ((aCutoffFamily M L
        (translatePotentialSample z omega)).coeffOn
          Q).toCoeffField y =
      scalarCoeffField
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega (x + z)) y := by
  intro y
  simp only [scalarCoeffField]
  rw [show ((aCutoffFamily M L
      (translatePotentialSample z omega)).coeffOn
        Q).toCoeffField y =
      scalarMatrix (_root_.SubdiffusiveProcess.Model.aCutoff M L
        (translatePotentialSample z omega) y) from rfl,
    Section6Covariance.aCutoff_translatePotentialSample]

/-! ## 3. The composite: the exact Caccioppoli input of the energy slot -/

/-- **The energy slot's Caccioppoli input, for the whole-space carrier
on a recentred stopping cell.**

This is the missing ingredient named in the director's `(B-1)` table. -/
theorem wholeSpaceSolution_recentredCell_localSymmetricEnergy_sq_le
    {a f : Vec d → ℝ} {lam Lam t : ℝ} {m : ℤ} {z : Vec d}
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (hf0 : ∀ x ∈ translatedCube d (m + 1) z, f x = 0)
    (hEll : IsEllipticFieldOn lam Lam (translatedCube d (m + 1) z)
      (scalarCoeffField a))
    (haNonneg : ∀ x, 0 ≤ a x) (hLam : 0 ≤ Lam)
    (haLe : ∀ x ∈ translatedCube d (m + 1) z, a x ≤ Lam) (ht : 0 < t)
    (acoeff : Ch02.CoeffOn (Ch02.cubeDomain (originCube d m)))
    (ha : ∀ y, acoeff.toCoeffField y = scalarCoeffField (fun x ↦ a (x + z)) y)
    (u0 : H1Function (openCubeSet (originCube d m)))
    (hu0 : u0.grad =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      fun x ↦ u.grad (x + z)) :
    cubeVolume (originCube d m) *
        (localSymmetricEnergyENorm (originCube d m) acoeff u0).toReal ^ 2 ≤
      4096 * (d : ℝ) * Lam * ((3 : ℝ) ^ m)⁻¹ ^ 2 *
        ∫ x in translatedCube d (m + 1) z, u.toFun x ^ 2 ∂volume := by
  rw [cubeVolume_mul_recentred_localSymmetricEnergy_sq_eq z acoeff ha haNonneg
    u0 u.grad hu0]
  exact wholeSpaceSolution_translatedCell_energy_le_of_zero_source u hf0 hEll
    haNonneg hLam haLe ht

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
