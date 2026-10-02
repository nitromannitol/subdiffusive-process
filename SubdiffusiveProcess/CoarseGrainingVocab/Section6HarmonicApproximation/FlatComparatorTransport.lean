/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.EquationTranslation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorForcing
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryMeanControlComparator




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-- Normalized scalar `L²` is invariant under a spatial translation. -/
theorem normalizedL2On_translateSet (z : Vec d) (U : Set (Vec d))
    (f : Vec d → ℝ) :
    normalizedL2On (translateSet z U) f =
      normalizedL2On U (fun x ↦ f (x + z)) := by
  unfold normalizedL2On volumeAverage
  rw [volume_translateSet_eq]
  have hint :
      ∫ x in translateSet z U, f x ^ 2 ∂volume =
        ∫ x in U, f (x + z) ^ 2 ∂volume := by
    exact (setIntegral_comp_addRight_translateSet z U (fun x ↦ f x ^ 2)).symm
  rw [hint]

/-- Zero-trace membership transported across a definitional domain
identification. -/
theorem memH10_castDomain {U V : Set (Vec d)} (hUV : U = V)
    {f : Vec d → ℝ} (hf : MemH10 U f) : MemH10 V f := by
  subst V
  exact hf

/-- Unit weak harmonicity transported across a domain identification. -/
theorem isUnitWeaklyHarmonicOn_castDomain {U V : Set (Vec d)}
    (hUV : U = V) {u : H1Function U}
    (hu : IsUnitWeaklyHarmonicOn U u) :
    IsUnitWeaklyHarmonicOn V (Ch03.castH1Domain hUV u) := by
  subst V
  exact hu

/-- The Chapter 3 zero-trace-difference carrier is transitive. -/
theorem hasH10Difference_trans
    {Q : TriadicCube d} {u v w : H1Function (openCubeSet Q)}
    (huv : Homogenization.Book.Ch03.ABK26.HasH10Difference Q u v)
    (hvw : Homogenization.Book.Ch03.ABK26.HasH10Difference Q v w) :
    Homogenization.Book.Ch03.ABK26.HasH10Difference Q u w := by
  obtain ⟨rho, hrho⟩ := huv
  obtain ⟨eta, heta⟩ := hvw
  refine ⟨rho + eta, ?_⟩
  filter_upwards [hrho, heta] with x hx hy
  change rho.toH1Function.toFun x + eta.toH1Function.toFun x =
    u.toFun x - w.toFun x
  rw [hx, hy]
  ring

/-- The Chapter 3 zero-trace-difference carrier is symmetric. -/
theorem hasH10Difference_symm
    {Q : TriadicCube d} {u v : H1Function (openCubeSet Q)}
    (huv : Homogenization.Book.Ch03.ABK26.HasH10Difference Q u v) :
    Homogenization.Book.Ch03.ABK26.HasH10Difference Q v u := by
  obtain ⟨rho, hrho⟩ := huv
  refine ⟨-rho, ?_⟩
  filter_upwards [hrho] with x hx
  change (-rho.toH1Function).toFun x = v.toFun x - u.toFun x
  rw [H1Function.neg_toFun]
  change -rho.toFun x = v.toFun x - u.toFun x
  rw [hx]
  ring

/-- Triangle composition of the coefficient-to-scalar homogenization error
and the scalar-to-flat forcing error. -/
theorem cubeLpNorm_sub_unitHarmonic_le_add
    (Q : TriadicCube d)
    (u v h : H1Function (openCubeSet Q)) {E F : ℝ}
    (huv : cubeLpNorm Q 2 (fun x ↦ u.toFun x - v.toFun x) ≤ E)
    (hvh : cubeLpNorm Q 2 (fun x ↦ v.toFun x - h.toFun x) ≤ F) :
    cubeLpNorm Q 2 (fun x ↦ u.toFun x - h.toFun x) ≤ E + F := by
  have hu : MemLp (fun x ↦ u.toFun x - v.toFun x) 2
      (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure.sub v.memL2_normalizedCubeMeasure
  have hv : MemLp (fun x ↦ v.toFun x - h.toFun x) 2
      (normalizedCubeMeasure Q) :=
    v.memL2_normalizedCubeMeasure.sub h.memL2_normalizedCubeMeasure
  have htriangle := cubeLpNorm_add_le Q (2 : ENNReal)
    (fun x ↦ u.toFun x - v.toFun x) (fun x ↦ v.toFun x - h.toFun x)
    hu hv (by norm_num)
  have hfun : (fun x ↦ (u.toFun x - v.toFun x) +
      (v.toFun x - h.toFun x)) = fun x ↦ u.toFun x - h.toFun x := by
    funext x
    ring
  rw [hfun] at htriangle
  exact htriangle.trans (add_le_add huv hvh)

/-- Recenter a physical flat comparator, retaining harmonicity, its trace
relation to the supplied origin representative, and the exact normalized
value norm. -/
theorem exists_recenteredFlatComparator
    (Q : TriadicCube d) (c : Vec d)
    (u0 : H1Function (openCubeSet Q)) (uPhysical : Vec d → ℝ)
    (ubar : H1Function (translateSet c (openCubeSet Q)))
    (hharm : IsUnitWeaklyHarmonicOn
      (translateSet c (openCubeSet Q)) ubar)
    (htrace : MemH10 (translateSet c (openCubeSet Q))
      (fun y ↦ ubar.toFun y - uPhysical y))
    (hu0 : ∀ x, u0.toFun x = uPhysical (x + c)) :
    ∃ ubar0 : H1Function (openCubeSet Q),
      IsUnitWeaklyHarmonicOn (openCubeSet Q) ubar0 ∧
      Homogenization.Book.Ch03.ABK26.HasH10Difference Q u0 ubar0 ∧
      normalizedL2On (translateSet c (openCubeSet Q))
          (fun y ↦ uPhysical y - ubar.toFun y) =
        cubeLpNorm Q 2 (fun x ↦ u0.toFun x - ubar0.toFun x) := by
  let ubar0 : H1Function (openCubeSet Q) := H1Function.untranslate c ubar
  obtain ⟨rho, hrho⟩ := htrace
  let rho0 : H10Function (openCubeSet Q) := H10Function.untranslate c rho
  have hharm0 : IsUnitWeaklyHarmonicOn (openCubeSet Q) ubar0 :=
    isUnitWeaklyHarmonicOn_untranslate c hharm
  have hzero : Homogenization.Book.Ch03.ABK26.HasH10Difference Q u0 ubar0 := by
    refine ⟨-rho0, Filter.Eventually.of_forall fun x ↦ ?_⟩
    have hrhoAt := congrFun hrho (x + c)
    dsimp only [rho0, ubar0]
    change (-(H1Function.untranslate c rho.toH1Function)).toFun x =
      u0.toFun x - ubar.toFun (x + c)
    rw [H1Function.neg_toFun]
    change -(H1Function.untranslate c rho.toH1Function).toFun x =
      u0.toFun x - ubar.toFun (x + c)
    rw [H1Function.untranslate_toFun]
    rw [hrhoAt, hu0 x]
    ring
  refine ⟨ubar0, hharm0, hzero, ?_⟩
  rw [normalizedL2On_translateSet]
  have hmem : MemLp (fun x ↦ u0.toFun x - ubar0.toFun x) 2
      (volume.restrict (openCubeSet Q)) := u0.memL2.sub ubar0.memL2
  have hfun : (fun x ↦ uPhysical (x + c) - ubar.toFun (x + c)) =
      fun x ↦ u0.toFun x - ubar0.toFun x := by
    funext x
    dsimp only [ubar0]
    rw [H1Function.untranslate_toFun, hu0]
  rw [hfun]
  rw [normalizedL2On_openCubeSet_eq_cubeLpNorm Q hmem]



theorem exists_recenteredFlatComparator_wellPlaced
    {m k : ℤ} (hkm : k ≤ m) (q : Vec d)
    (u0 : H1Function (openCubeSet (originCube d k)))
    (uPhysical : Vec d → ℝ)
    (ubar : H1Function
      (truncatedWindow (Section6ExcessDecay.wellPlacedCentre q m k) m k))
    (hharm : IsUnitWeaklyHarmonicOn
      (truncatedWindow (Section6ExcessDecay.wellPlacedCentre q m k) m k) ubar)
    (htrace : MemH10
      (truncatedWindow (Section6ExcessDecay.wellPlacedCentre q m k) m k)
      (fun y ↦ ubar.toFun y - uPhysical y))
    (hu0 : ∀ x, u0.toFun x =
      uPhysical (x + Section6ExcessDecay.wellPlacedCentre q m k)) :
    ∃ ubar0 : H1Function (openCubeSet (originCube d k)),
      IsUnitWeaklyHarmonicOn (openCubeSet (originCube d k)) ubar0 ∧
      Ch03.ABK26.HasH10Difference (originCube d k) u0 ubar0 ∧
      normalizedL2On
          (translatedCube d k (Section6ExcessDecay.wellPlacedCentre q m k))
          (fun y ↦ uPhysical y - ubar.toFun y) =
        cubeLpNorm (originCube d k) 2
          (fun x ↦ u0.toFun x - ubar0.toFun x) := by
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  have hW : truncatedWindow c m k = translateSet c (openCubeSet (originCube d k)) := by
    calc
      truncatedWindow c m k = translatedCube d k c :=
        truncatedWindow_wellPlacedCentre_eq_translatedCube hkm q
      _ = translateSet c (openCubeSet (originCube d k)) := by
        rw [translatedCube, cube,
          Section6SchauderDatum.image_add_eq_translateSet]
  let ubarT : H1Function (translateSet c (openCubeSet (originCube d k))) :=
    Ch03.castH1Domain hW ubar
  have hharmT : IsUnitWeaklyHarmonicOn
      (translateSet c (openCubeSet (originCube d k))) ubarT :=
    isUnitWeaklyHarmonicOn_castDomain hW hharm
  have htraceT : MemH10 (translateSet c (openCubeSet (originCube d k)))
      (fun y ↦ ubarT.toFun y - uPhysical y) := by
    have ht := memH10_castDomain hW htrace
    simpa only [ubarT, Ch03.castH1Domain_toFun] using ht
  obtain ⟨ubar0, hh0, hz0, hnorm⟩ :=
    exists_recenteredFlatComparator (originCube d k) c u0 uPhysical ubarT
      hharmT htraceT hu0
  refine ⟨ubar0, hh0, hz0, ?_⟩
  simpa only [c, ubarT, Ch03.castH1Domain_toFun,
    translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet] using hnorm

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
