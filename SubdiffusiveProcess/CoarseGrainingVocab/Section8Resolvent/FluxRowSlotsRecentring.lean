
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowSlotsWholeSpaceCell

@[expose] public section

/-!
# The recentring identification of the flux row's cell gradient

The local flux price
`exists_fluxRowRiesz_repairedStoppingCell_localFluxPrice` produces the
recentred solution `u0 = fluxRowRieszUntranslatedH1 z u`, where `u` is the
*cell* representative of the whole-space carrier, while the Caccioppoli input
`wholeSpaceSolution_recentredCell_localSymmetricEnergy_sq_le` consumes

```
u0.grad =ᵐ[volume.restrict (openCubeSet (originCube d m))] fun x ↦ U.grad (x + z)
```

with `U` the carrier's own gradient field.  §9 item 4 listed this as the
one place where the recentring is not already discharged.  It is closed here.

The chain has exactly three links:

* `fluxRowRieszUntranslatedH1_grad` — the *pointwise* identity
  `u0.grad x = u.grad (x + z)`, a `castH1Domain`/`untranslate` computation;
* `fluxRowSlots_ae_eq_comp_addRight` — transport of an almost-everywhere
  identity along the measure-preserving map `x ↦ x + z` from
  `volume.restrict (openCubeSet (originCube d m))` to
  `volume.restrict (translatedCube d m z)`;
* `wholeSpaceSolution_untranslatedCell_grad_ae_eq` — the composite, applied to
  the carrier's own `u.grad =ᵐ grad` promise.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open _root_.SubdiffusiveProcess.Section8

noncomputable section

variable {d : ℕ}

/-! ## 1. The pointwise recentring identity -/

/-- The recentred cell solution has the translated gradient, pointwise. -/
@[simp] theorem fluxRowRieszUntranslatedH1_grad {m : ℤ} (z : Vec d)
    (u : H1Function (translatedCube d m z)) (x : Vec d) :
    (fluxRowRieszUntranslatedH1 z u).grad x = u.grad (x + z) := by
  rw [fluxRowRieszUntranslatedH1, H1Function.untranslate_grad,
    fluxRowRieszTranslatedH1, Ch03.castH1Domain_grad]

/-! ## 2. Transport of an almost-everywhere identity along `x ↦ x + z` -/

/-- An almost-everywhere identity on a translated cell pulls back to the
origin cube along `x ↦ x + z`. -/
theorem fluxRowSlots_ae_eq_comp_addRight {m : ℤ} (z : Vec d)
    {G H : Vec d → Vec d}
    (h : G =ᵐ[volume.restrict (translatedCube d m z)] H) :
    (fun x ↦ G (x + z)) =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      fun x ↦ H (x + z) := by
  have hset : translatedCube d m z = translateSet z (openCubeSet (originCube d m)) :=
    fluxRowRiesz_translatedCube_eq_translateSet m z
  have h' : G =ᵐ[volume.restrict (translateSet z (openCubeSet (originCube d m)))] H := by
    rwa [hset] at h
  have hmp := measurePreserving_addRight_restrict_translateSet (d := d) z
    (openCubeSet (originCube d m))
  exact hmp.quasiMeasurePreserving.ae_eq_comp h'

/-! ## 3. The composite consumed by the energy slot -/

/-- **The gradient identification of the flux row's recentred cell solution.**

If the cell representative `u` agrees almost everywhere with the whole-space
carrier's gradient field on the cell — which is exactly what the carrier
promises through `locally_weak_solution` — then the recentred solution
`fluxRowRieszUntranslatedH1 z u` produced by the local flux price has
the translated carrier gradient almost everywhere on the origin cube.  This is
the hypothesis `hu0` of
`wholeSpaceSolution_recentredCell_localSymmetricEnergy_sq_le`. -/
theorem fluxRowRieszUntranslatedH1_grad_ae_eq {m : ℤ} (z : Vec d)
    (u : H1Function (translatedCube d m z)) {G : Vec d → Vec d}
    (hgrad : u.grad =ᵐ[volume.restrict (translatedCube d m z)] G) :
    (fluxRowRieszUntranslatedH1 z u).grad =ᵐ[volume.restrict
        (openCubeSet (originCube d m))] fun x ↦ G (x + z) := by
  have hpt : (fluxRowRieszUntranslatedH1 z u).grad = fun x ↦ u.grad (x + z) := by
    funext x
    exact fluxRowRieszUntranslatedH1_grad z u x
  rw [hpt]
  exact fluxRowSlots_ae_eq_comp_addRight z hgrad

/-- **The whole-space carrier version.**

The carrier's cell representative recentres to a field whose gradient is
the translated carrier gradient. -/
theorem wholeSpaceSolution_untranslatedCell_grad_ae_eq
    {a f : Vec d → ℝ} {t : ℝ} {m : ℤ} {z : Vec d}
    (U : WholeSpaceDivergenceResolventSolution a t f)
    (u : H1Function (translatedCube d m z))
    (hgrad : u.grad =ᵐ[volume.restrict (translatedCube d m z)] U.grad) :
    (fluxRowRieszUntranslatedH1 z u).grad =ᵐ[volume.restrict
        (openCubeSet (originCube d m))] fun x ↦ U.grad (x + z) :=
  fluxRowRieszUntranslatedH1_grad_ae_eq z u hgrad

/-- **A cell representative always exists, with the identification.**

Applying `locally_weak_solution` on the cell itself produces a cell
representative whose recentring satisfies the energy slot's `hu0`.  The
massive equation it satisfies is carried along, so This is the constructor a
consumer may use when the theorem's `u` is not already fixed. -/
theorem exists_wholeSpaceSolution_cell_representative_grad_ae_eq
    {a f : Vec d → ℝ} {t : ℝ} (m : ℤ) (z : Vec d)
    (U : WholeSpaceDivergenceResolventSolution a t f) :
    ∃ u : H1Function (translatedCube d m z),
      (∀ x ∈ translatedCube d m z, u.toFun x = U.toFun x) ∧
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹ (translatedCube d m z) u
        (fun x ↦ t⁻¹ * f x) ∧
      (fluxRowRieszUntranslatedH1 z u).grad =ᵐ[volume.restrict
        (openCubeSet (originCube d m))] fun x ↦ U.grad (x + z) := by
  obtain ⟨u, hval, hgrad, hsol⟩ :=
    U.locally_weak_solution (translatedCube d m z)
      (isOpenBoundedConvexDomain_translatedCube m z)
  exact ⟨u, hval, hsol, wholeSpaceSolution_untranslatedCell_grad_ae_eq U u hgrad⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
