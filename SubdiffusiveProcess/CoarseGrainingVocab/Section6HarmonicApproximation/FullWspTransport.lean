/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.WindowDomain
public import Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingDefinitions
public import Homogenization.Geometry.Translation
public import Homogenization.Sobolev.Fractional.DefinitionsAPI

@[expose] public section

/-!
# Restriction and real-translation transport for the Section 6 force

The v5 harmonic-approximation anchor supplies the inhomogeneous Euclidean
`W^{s,2}` carrier on the ambient centered cube, whereas the deterministic
coarse-graining theorem is applied after translating an arbitrary local cube
back to the origin.  This file supplies that transport.

PROVENANCE: the decomposition and measure argument mirror
`Algsuperdiff/Section4/Provider/ExcessDecay/ForceTransport.lean` and
`InteriorGlueWindow.lean`.  The present version uses CoarseGraining's
Euclidean kernel (`cubeEuclideanWspKernel`) rather than the additive model's
generic Gagliardo kernel.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private noncomputable def normalizedVolumeMeasureOn (A : Set (Vec d)) :
    Measure (Vec d) :=
  (volume A)⁻¹ • volume.restrict A

private noncomputable def normalizedGagliardoMeasureOn (A : Set (Vec d)) :
    Measure (Vec d × Vec d) :=
  (normalizedVolumeMeasureOn A).prod (volume.restrict A)

private theorem normalizedVolumeMeasureOn_openCubeSet (Q : TriadicCube d) :
    normalizedVolumeMeasureOn (openCubeSet Q) = normalizedCubeMeasure Q := by
  have h : normalizedVolumeMeasureOn (openCubeSet Q) =
      normalizedVolumeMeasureOn (cubeSet Q) := by
    rw [normalizedVolumeMeasureOn, normalizedVolumeMeasureOn,
      volume_openCubeSet_eq_volume_cubeSet,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [h, normalizedVolumeMeasureOn, normalizedCubeMeasure, cubeMeasure]
  have hvol : volume (cubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    rw [← cubeMeasure_apply_univ Q]
    exact cubeMeasure_apply_univ_eq Q
  rw [hvol, ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]

private theorem normalizedGagliardoMeasureOn_openCubeSet (Q : TriadicCube d) :
    normalizedGagliardoMeasureOn (openCubeSet Q) =
      Gagliardo.gagliardoCubeMeasure Q := by
  rw [normalizedGagliardoMeasureOn, normalizedVolumeMeasureOn_openCubeSet,
    Gagliardo.gagliardoCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

private theorem volume_openCubeSet_ne_zero (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ 0 := by
  intro hzero
  have htoReal : (volume (cubeSet Q)).toReal = 0 := by
    rw [← volume_openCubeSet_eq_volume_cubeSet, hzero]
    simp
  rw [volume_cubeSet_toReal] at htoReal
  exact (cubeVolume_pos Q).ne' htoReal

private theorem volume_openCubeSet_ne_top (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ ∞ :=
  (volume_openCubeSet_lt_top Q).ne

private theorem volume_translate_openCubeSet_ne_zero (z : Vec d) (Q : TriadicCube d) :
    volume (translateSet z (openCubeSet Q)) ≠ 0 := by
  rw [volume_translateSet_eq]
  exact volume_openCubeSet_ne_zero Q

private theorem memLp_normalizedVolumeMeasureOn_subset
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {A B : Set (Vec d)}
    (hAB : B ⊆ A) (hA0 : volume A ≠ 0) (hAtop : volume A ≠ ∞)
    (hB0 : volume B ≠ 0) {f : Vec d → E}
    (h : MemLp f p (normalizedVolumeMeasureOn A)) :
    MemLp f p (normalizedVolumeMeasureOn B) := by
  rw [normalizedVolumeMeasureOn] at h
  have hres : MemLp f p (volume.restrict A) := by
    have hsm := h.smul_measure (c := volume A) hAtop
    rwa [smul_smul, ENNReal.mul_inv_cancel hA0 hAtop, one_smul] at hsm
  have hresB : MemLp f p (volume.restrict B) :=
    hres.mono_measure (Measure.restrict_mono hAB le_rfl)
  rw [normalizedVolumeMeasureOn]
  exact hresB.smul_measure (ENNReal.inv_ne_top.mpr hB0)

private theorem normalizedGagliardoMeasureOn_eq_smul_restrict (A : Set (Vec d)) :
    normalizedGagliardoMeasureOn A =
      (volume A)⁻¹ • ((volume.prod volume).restrict (A ×ˢ A)) := by
  rw [normalizedGagliardoMeasureOn, normalizedVolumeMeasureOn,
    Measure.prod_smul_left, Measure.prod_restrict]

private theorem memLp_normalizedGagliardoMeasureOn_subset
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {A B : Set (Vec d)}
    (hAB : B ⊆ A) (hA0 : volume A ≠ 0) (hAtop : volume A ≠ ∞)
    (hB0 : volume B ≠ 0) {f : Vec d × Vec d → E}
    (h : MemLp f p (normalizedGagliardoMeasureOn A)) :
    MemLp f p (normalizedGagliardoMeasureOn B) := by
  rw [normalizedGagliardoMeasureOn_eq_smul_restrict] at h
  have hres : MemLp f p ((volume.prod volume).restrict (A ×ˢ A)) := by
    have hsm := h.smul_measure (c := volume A) hAtop
    rwa [smul_smul, ENNReal.mul_inv_cancel hA0 hAtop, one_smul] at hsm
  have hsq : (B ×ˢ B : Set (Vec d × Vec d)) ⊆ A ×ˢ A := Set.prod_mono hAB hAB
  have hresB : MemLp f p ((volume.prod volume).restrict (B ×ˢ B)) :=
    hres.mono_measure (Measure.restrict_mono hsq le_rfl)
  rw [normalizedGagliardoMeasureOn_eq_smul_restrict]
  exact hresB.smul_measure (ENNReal.inv_ne_top.mpr hB0)

private theorem normalizedVolumeMeasureOn_translateSet (z : Vec d) (A : Set (Vec d)) :
    normalizedVolumeMeasureOn (translateSet z A) =
      Measure.map (fun x : Vec d => x + z) (normalizedVolumeMeasureOn A) := by
  have hmeas : Measurable (fun x : Vec d => x + z) := measurable_id.add_const z
  rw [normalizedVolumeMeasureOn, normalizedVolumeMeasureOn, Measure.map_smul _ hmeas.aemeasurable,
    (measurePreserving_addRight_restrict_translateSet z A).map_eq,
    volume_translateSet_eq]

private theorem measurePreserving_addRight_normalizedVolumeMeasureOn
    (z : Vec d) (A : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x + z)
      (normalizedVolumeMeasureOn A) (normalizedVolumeMeasureOn (translateSet z A)) :=
  ⟨(MeasurableEquiv.addRight z).measurable,
    (normalizedVolumeMeasureOn_translateSet z A).symm⟩

private theorem normalizedGagliardoMeasureOn_translateSet
    (z : Vec d) (A : Set (Vec d)) :
    normalizedGagliardoMeasureOn (translateSet z A) =
      Measure.map (Prod.map (fun x : Vec d => x + z) (fun x : Vec d => x + z))
        (normalizedGagliardoMeasureOn A) := by
  haveI : SFinite (volume.restrict A) := inferInstance
  haveI : SFinite (volume.restrict (translateSet z A)) := inferInstance
  have hmeas : Measurable (fun x : Vec d => x + z) := measurable_id.add_const z
  rw [normalizedGagliardoMeasureOn, normalizedGagliardoMeasureOn,
    normalizedVolumeMeasureOn, normalizedVolumeMeasureOn,
    Measure.prod_smul_left, Measure.prod_smul_left, Measure.map_smul _ (hmeas.prodMap hmeas).aemeasurable,
    ← Measure.map_prod_map _ _ hmeas hmeas,
    (measurePreserving_addRight_restrict_translateSet z A).map_eq,
    volume_translateSet_eq]

private theorem measurePreserving_prodMap_addRight_normalizedGagliardoMeasureOn
    (z : Vec d) (A : Set (Vec d)) :
    MeasurePreserving
      (fun w => (((MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d).prodCongr
        (MeasurableEquiv.addRight z : Vec d ≃ᵐ Vec d))) w)
      (normalizedGagliardoMeasureOn A)
      (normalizedGagliardoMeasureOn (translateSet z A)) := by
  refine ⟨(MeasurableEquiv.prodCongr _ _).measurable, ?_⟩
  rw [normalizedGagliardoMeasureOn_translateSet z A]
  rfl

private theorem memLp_comp_measurePreservingEquiv
    {alpha beta E : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    [NormedAddCommGroup E] {mu : Measure alpha} {nu : Measure beta}
    (e : alpha ≃ᵐ beta) (he : MeasurePreserving (fun x => e x) mu nu)
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {f : beta → E} (hf : MemLp f p nu) :
    MemLp (fun x => f (e x)) p mu := by
  simpa only [Function.comp_def] using! hf.comp_measurePreserving he

/-- A full Euclidean fractional-Sobolev datum restricts to an arbitrary real
translate of a subcube and, after recentering, has exactly the origin-cube
carrier required by the deterministic coarse-graining theorem. -/
theorem memCubeEuclideanFullWsp_translate_of_subset
    (Q P : TriadicCube d) (z : Vec d) (s : FractionalOrder)
    (p : FiniteLpExponent) (g : Vec d → Vec d)
    (hsub : translateSet z (openCubeSet Q) ⊆ openCubeSet P)
    (hg : Ch03.ABK26.MemCubeEuclideanFullWsp P s p g) :
    Ch03.ABK26.MemCubeEuclideanFullWsp Q s p (fun x => g (x + z)) := by
  have hgLpOpen : MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedVolumeMeasureOn (openCubeSet P)) := by
    rw [normalizedVolumeMeasureOn_openCubeSet]
    exact hg.1
  have hgLpLocal := memLp_normalizedVolumeMeasureOn_subset hsub
    (volume_openCubeSet_ne_zero P) (volume_openCubeSet_ne_top P)
    (volume_translate_openCubeSet_ne_zero z Q) hgLpOpen
  have hgWOpen : MemLp (cubeEuclideanWspKernel s p g) p.exponent
      (normalizedGagliardoMeasureOn (openCubeSet P)) := by
    rw [normalizedGagliardoMeasureOn_openCubeSet]
    exact hg.2
  have hgWLocal := memLp_normalizedGagliardoMeasureOn_subset hsub
    (volume_openCubeSet_ne_zero P) (volume_openCubeSet_ne_top P)
    (volume_translate_openCubeSet_ne_zero z Q) hgWOpen
  constructor
  · rw [← normalizedVolumeMeasureOn_openCubeSet Q]
    have htr := memLp_comp_measurePreservingEquiv
      (MeasurableEquiv.addRight z)
      (measurePreserving_addRight_normalizedVolumeMeasureOn z (openCubeSet Q))
      (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne hgLpLocal
    simpa only using! htr
  · unfold MemCubeEuclideanWsp
    rw [← normalizedGagliardoMeasureOn_openCubeSet Q]
    let T : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight z
    let TP : Vec d × Vec d ≃ᵐ Vec d × Vec d := T.prodCongr T
    have htr := memLp_comp_measurePreservingEquiv TP
      (measurePreserving_prodMap_addRight_normalizedGagliardoMeasureOn
        z (openCubeSet Q))
      (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne hgWLocal
    have hker : (fun w => cubeEuclideanWspKernel s p g (TP w)) =
        cubeEuclideanWspKernel s p (fun x => g (x + z)) := by
      funext w
      change cubeEuclideanWspKernel s p g (w.1 + z, w.2 + z) = _
      rw [cubeEuclideanWspKernel_apply, cubeEuclideanWspKernel_apply,
        euclideanDist_add_right]
    rwa [hker] at htr

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
