/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Observables
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationRestriction
public import SubdiffusiveProcess.CoarseGrainingVocab.Model
public import Homogenization.Sobolev.H1.Translation

@[expose] public section

/-!
# Translation of the local Section 6 equation

PROVENANCE: this is the scalar GMC specialization of
`Algsuperdiff/Section4/Provider/ExcessDecay/TranslationTransport.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- A divergence-form equation on a translated set becomes the corresponding
equation on the origin set after precomposing every datum by the translation. -/
theorem isDivFormWeakSolutionOn_untranslate {U : Set (Vec d)} (z : Vec d)
    {a : Vec d → ℝ} {u : H1Function (translateSet z U)} {g : Vec d → Vec d}
    (h : IsDivFormWeakSolutionOn a (translateSet z U) u g) :
    IsDivFormWeakSolutionOn (fun x => a (x + z)) U
      (H1Function.untranslate z u) (fun x => g (x + z)) := by
  intro phi
  have hkey := h (H10Function.translate phi z)
  have hL := setIntegral_comp_addRight_translateSet z U
    (fun y => vecDot (a y • u.grad y) (phi.toH1Function.grad (y - z)))
  have hR := setIntegral_comp_addRight_translateSet z U
    (fun y => vecDot (g y) (phi.toH1Function.grad (y - z)))
  have hLform : (fun y : Vec d =>
        vecDot (a (y + z) • u.grad (y + z))
          (phi.toH1Function.grad (y + z - z))) =
      fun y : Vec d =>
        vecDot ((fun x => a (x + z)) y •
          (H1Function.untranslate z u).grad y) (phi.toH1Function.grad y) := by
    funext y
    rw [add_sub_cancel_right]
    rfl
  have hRform : (fun y : Vec d =>
        vecDot (g (y + z)) (phi.toH1Function.grad (y + z - z))) =
      fun y : Vec d =>
        vecDot ((fun x => g (x + z)) y) (phi.toH1Function.grad y) := by
    funext y
    rw [add_sub_cancel_right]
  rw [hLform] at hL
  rw [hRform] at hR
  rw [hL, hR]
  exact hkey

/-- Unit weak harmonicity is preserved when a translated window is recentered.
This is the flat-comparator transport used after the physical equation has
been recentered on an origin cube. -/
theorem isUnitWeaklyHarmonicOn_untranslate {U : Set (Vec d)} (z : Vec d)
    {u : H1Function (translateSet z U)}
    (h : Section6Schauder.IsUnitWeaklyHarmonicOn (translateSet z U) u) :
    Section6Schauder.IsUnitWeaklyHarmonicOn U (H1Function.untranslate z u) := by
  have hdiv : IsDivFormWeakSolutionOn (fun _ : Vec d => 1)
      (translateSet z U) u (0 : Vec d → Vec d) := by
    intro phi
    simp only [one_smul]
    rw [h phi]
    simp [vecDot]
  have htr := isDivFormWeakSolutionOn_untranslate z hdiv
  intro phi
  have hphi := htr phi
  simpa [vecDot] using hphi

/-- The translated scalar cutoff equation in Chapter 3's matrix-family
spelling. -/
theorem isForcedEquation_aCutoff_untranslate
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (omega : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Q : TriadicCube d) (z : Vec d)
    {u : H1Function (translateSet z (openCubeSet Q))} {g : Vec d → Vec d}
    (h : IsDivFormWeakSolutionOn (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega)
      (translateSet z (openCubeSet Q)) u g) :
    Ch03.ABK26.IsForcedEquation Q
      ((aCutoffFamily M L (translatePotentialSample z omega)).coeffOn Q)
      (H1Function.untranslate z u) (fun x => g (x + z)) := by
  have htr := isDivFormWeakSolutionOn_untranslate z h
  intro phi
  have hphi := htr phi
  simpa [aCutoffFamily, aCutoffTriadicData,
    ScalarTriadicCoeffData.toTriadicCoeffFamily,
    aCutoffCoeffOnData, ScalarCoeffOnData.toCoeffOn, scalarCoeffField,
    Section6Covariance.aCutoff_translatePotentialSample,
    matVecMul_scalarMatrix] using hphi

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
