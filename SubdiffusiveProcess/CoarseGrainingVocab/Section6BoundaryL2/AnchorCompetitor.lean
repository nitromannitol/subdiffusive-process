module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.Restriction
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.SeamCore
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.CornerProducer

@[expose] public section

/-!
# The boundary competitor at the excess-decay anchor

`Section6SchauderDatum.CornerProducer.exists_classicalCompetitor_datumSplit_corner`
builds the classical, face-odd competitor `V` on the doubled window from a
harmonic replacement `v` whose trace matches the solution **on the window
itself**: its `hvu` slot is `MemH10 (U_{m,k}(x)) (v − u)`.

The anchor of `l.excess.decay.good.scales.GMC` does not supply that.  Its
harmonic replacement lives on the *enveloping* cube `Y ⊇ U_{m,k}(x)` produced by
`exists_windowChoice`, and the trace match it supplies is
`MemH10 Y (v − u)` — an `H¹₀` statement on the larger set, which does **not**
restrict to the window.

This module closes that mismatch.  The chain
`ZeroTrace.localizedZeroTraceFunctionOn_datumSplit` consumes `hvu` only through
`localizedZeroTraceFunctionOn_of_memH10`, and the localized zero trace on the
window against the doubled window is available from `MemH10 Y` alone, because

```text
  reflectedWindow x m k ∩ Y = U_{m,k}(x)
```

(`Restriction.reflectedWindow_inter_eq_truncatedWindow`, from
`reflectedWindow ∩ □_m = U_{m,k}(x)` and `U_{m,k}(x) ⊆ Y ⊆ □_m`).  So the whole
producer goes through with the anchor's weaker trace datum.

The output also carries the **pointwise met-face oddness of `V` on the doubled
window**, which is what `Section6OddClass.Interface` consumes: the `H¹` odd
reflection `w` is odd *globally*, `V` agrees with it a.e., and
`Section6OddClass.SeamCore.eqOn_faceOdd_{upper,lower}_of_ae_eq` upgrades the a.e.
identity to a pointwise one on the open doubled window using the continuity of
the harmonic representative.

Finally `exists_meetsFace_of_not_translatedCube_subset` records the elementary
geometric fact that the interior gate of `AnchorInterior` failing is exactly a
met face: it is the entitlement hypothesis of `Section6OddClass.Interface`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2

open MeasureTheory InnerProductSpace
open Homogenization (Vec H1Function H10Function MemH10 LocalizedZeroTraceFunctionOn
  openCubeSet originCube coordFaceReflection)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay (affineLift)

noncomputable section

variable {d : ℕ}

/-! ### The interior gate fails exactly at a met face -/

/-- **Failure of the interior gate is a met face.**

If the translate `x + □_k` is not contained in `□_m`, then some coordinate
window of `U_{m,k}(x)` reaches a face of `∂□_m`.  This is the hypothesis
`MeetsUpperFace x m k i ∨ MeetsLowerFace x m k i` of
`Section6OddClass.Interface.exists_gradientHolder_boundary_metSet_truncatedCube`,
and its negation is the interior gate of
`Section6ExcessDecay.excess_decay_good_scales_interior`. -/
theorem exists_meetsFace_of_not_translatedCube_subset {m k : ℤ} {x : Vec d}
    (hnot : ¬ translatedCube d k x ⊆ cube d m) :
    ∃ i : Fin d, MeetsUpperFace x m k i ∨ MeetsLowerFace x m k i := by
  classical
  rw [Set.not_subset] at hnot
  obtain ⟨p, hp, hpc⟩ := hnot
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    Homogenization.mem_openCubeSet_originCube_iff] at hp
  rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hpc
  push Not at hpc
  obtain ⟨i, hi⟩ := hpc
  obtain ⟨hp1, hp2⟩ := hp i
  simp only [Pi.sub_apply] at hp1 hp2
  refine ⟨i, ?_⟩
  by_cases hcase : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < p i
  · left
    show (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ x i + (1 / 2 : ℝ) * (3 : ℝ) ^ k
    have hup := hi hcase
    linarith only [hup, hp2]
  · right
    show x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ m
    push Not at hcase
    linarith only [hcase, hp1]

/-! ### The localized zero trace from the anchor's enveloping cube -/

/-- **The `hzt` supplier for the datum-split competitor, from an `H¹₀` trace on
an enveloping set.**

`ZeroTrace.localizedZeroTraceFunctionOn_datumSplit` with its first leg replaced:
`hvu` is now `MemH10 Y (v − u)` for any open `Y` with
`U_{m,k}(x) ⊆ Y ⊆ □_m`, which is what the excess-decay anchor supplies. -/
theorem localizedZeroTraceFunctionOn_datumSplit_of_memH10_superset {m k : ℤ} {x : Vec d}
    {Y : Set (Vec d)} (hYopen : IsOpen Y) (hWY : truncatedWindow x m k ⊆ Y)
    (hYm : Y ⊆ openCubeSet (originCube d m))
    {u h ell : Vec d → ℝ}
    (hdat : MemH10 (openCubeSet (originCube d m)) (fun y => u y - h y))
    {v : H1Function (truncatedWindow x m k)}
    (hvu : MemH10 Y (fun y => v.toFun y - u y))
    {v₁ Ψ : H1Function (truncatedWindow x m k)}
    (hΨ : ∀ y ∈ truncatedWindow x m k, Ψ.toFun y = h y - ell y)
    (hv₁Ψ : MemH10 (truncatedWindow x m k) (fun y => v₁.toFun y - Ψ.toFun y)) :
    LocalizedZeroTraceFunctionOn (truncatedWindow x m k) (reflectedWindow x m k)
      (fun y => v.toFun y - ell y - v₁.toFun y) := by
  have h1 : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) (fun y => v.toFun y - u y) :=
    localizedZeroTraceFunctionOn_of_memH10_inter hYopen (isOpen_reflectedWindow x m k)
      (reflectedWindow_inter_eq_truncatedWindow hWY hYm) hvu
  have h2 : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) (fun y => u y - h y) :=
    localizedZeroTraceFunctionOn_truncatedWindow_of_memH10_cube x hdat
  have h3 : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) (fun y => h y - ell y - Ψ.toFun y) :=
    localizedZeroTraceFunctionOn_of_forall_eq_zero
      (isOpen_truncatedWindow x m k).measurableSet
      (fun y hy => by rw [hΨ y hy]; ring)
  have h4 : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) (fun y => Ψ.toFun y - v₁.toFun y) := by
    have hneg := Homogenization.memH10_neg hv₁Ψ
    refine localizedZeroTraceFunctionOn_of_memH10 ?_
    have hfun : (fun y => -(v₁.toFun y - Ψ.toFun y))
        = fun y => Ψ.toFun y - v₁.toFun y := by
      funext y
      ring
    rwa [hfun] at hneg
  have h12 := Homogenization.localizedZeroTraceFunctionOn_add h1 h2
  have h34 := Homogenization.localizedZeroTraceFunctionOn_add h3 h4
  have h := Homogenization.localizedZeroTraceFunctionOn_add h12 h34
  exact localizedZeroTraceFunctionOn_congr (fun y => by ring) h

/-! ### The classical competitor, with pointwise met-face oddness -/

/-- **The boundary competitor at the excess-decay anchor.**

The twin of `CornerProducer.exists_classicalCompetitor_datumSplit_corner` whose
trace hypothesis is the anchor's `MemH10 Y (v − u)` on the enveloping cube, and
whose conclusion additionally carries the **pointwise** met-face oddness of `V`
on the doubled window — the four hypotheses
`Section6OddClass.Interface.exists_gradientHolder_boundary_metSet_truncatedCube`
consumes, plus the `hVae` slot of
`OneStepL2.excess_oneStep_boundary_datumSplit_l2`. -/
theorem exists_classicalCompetitor_datumSplit_anchor [NeZero d] {x : Vec d} {m k : ℤ}
    (hkm : k < m) {Y : Set (Vec d)} (hYopen : IsOpen Y)
    (hWY : truncatedWindow x m k ⊆ Y) (hYm : Y ⊆ openCubeSet (originCube d m))
    {u h : Vec d → ℝ} {c : ℝ} {A : Vec d}
    (hdat : MemH10 (openCubeSet (originCube d m)) (fun y => u y - h y))
    {v : H1Function (truncatedWindow x m k)}
    (hvharm : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v)
    (hvu : MemH10 Y (fun y => v.toFun y - u y))
    {v₁ Ψ : H1Function (truncatedWindow x m k)}
    (hv₁harm : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v₁)
    (hΨ : ∀ y ∈ truncatedWindow x m k, Ψ.toFun y = h y - affineLift x c A y)
    (hv₁Ψ : MemH10 (truncatedWindow x m k) (fun y => v₁.toFun y - Ψ.toFun y)) :
    ∃ V : Vec d → ℝ,
      (∀ l : Fin d, MeetsUpperFace x m k l → ∀ y ∈ reflectedWindow x m k,
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
      (∀ l : Fin d, MeetsLowerFace x m k l → ∀ y ∈ reflectedWindow x m k,
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m k) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (truncatedWindow x m k)]
        (fun y => v.toFun y - affineLift x c A y - v₁.toFun y) := by
  have hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x m k) (reflectedWindow x m k)
      (datumSplitH1 v v₁ c A).toFun := by
    rw [datumSplitH1_toFun]
    exact localizedZeroTraceFunctionOn_datumSplit_of_memH10_superset hYopen hWY hYm
      hdat hvu hΨ hv₁Ψ
  obtain ⟨w, hwharm, hwpin, hwodd⟩ :=
    exists_h1_oddReflection_reflectedWindow hkm (datumSplitH1 v v₁ c A)
      (isUnitWeaklyHarmonicOn_datumSplitH1 hvharm hv₁harm c A) hzt
  obtain ⟨V, hVR, hVmem, hVae⟩ := exists_classicalCompetitor_reflectedWindow x m k hwharm
  have hVcont : ContinuousOn V (reflectedWindow x m k) :=
    Section6OddClass.continuousOn_of_harmonicOnNhd hVR
  refine ⟨V, ?_, ?_, hVR, hVmem, ?_⟩
  · intro l hl
    exact Section6OddClass.eqOn_faceOdd_upper_of_ae_eq hkm hl hVcont hVae ((hwodd l).1 hl)
  · intro l hl
    exact Section6OddClass.eqOn_faceOdd_lower_of_ae_eq hkm hl hVcont hVae ((hwodd l).2 hl)
  · have hVaeW : V =ᵐ[volume.restrict (truncatedWindow x m k)] w.toFun :=
      hVae.filter_mono (MeasureTheory.ae_mono (Measure.restrict_mono
        (truncatedWindow_subset_reflectedWindow x m k) le_rfl))
    filter_upwards [hVaeW, MeasureTheory.self_mem_ae_restrict
      (measurableSet_truncatedWindow x m k)] with y hy hymem
    rw [hy, hwpin y hymem, datumSplitH1_toFun]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2
