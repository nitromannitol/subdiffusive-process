module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.PartialReflection
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Producer

@[expose] public section

/-!
# The classical boundary competitor at every window position, corners included

`Producer` produces the classical competitor on the doubled window only in the
**one-met-face** regime: its `hother` binder asks that no coordinate other than
the reflected one meets a face of `∂□_m`.  This module lifts that restriction.

## What changes, and what does not

Nothing in the *consumer* changes.  `Section6Schauder`'s flat-face Schauder
estimate `exists_gradientHolder_boundary_truncatedCube` asks only for classical
harmonicity of `V` on `reflectedWindow x m (n-4)` — it carries no met-face
hypothesis of its own — and neither does the generic Weyl step
`Section6Schauder.exists_classicalCompetitor_reflectedWindow`.  The one-met-face
scope was located entirely in the *producer* of that harmonicity, i.e. in the
odd-reflection apparatus.  `PartialReflection.exists_h1_oddReflection_reflectedWindow`
replaces it, and `exists_classicalCompetitor_datumSplit_corner` below is the
same three-step composition as `Producer`'s two theorems with the multi-face
endpoint in place of the one-face one:

```text
  AffineHarmonic + ZeroTrace     (the shifted competitor is weakly harmonic
                                  with face-only zero trace)
  → PartialReflection            (the H¹ odd extension to the doubled window,
                                  any met configuration)
  → BoundaryComposition          (Weyl: classical harmonicity there)
```

## The `hVae` slot, discharged

`Producer` states its a.e. link on the **reflected** window, against
`oddFaceExtend … (zeroExtend … (v − ℓ_h − v₁))`, which then has to be collapsed
to `v − ℓ_h − v₁` before `OneStepDatum.excess_oneStep_boundary_datumSplit` can
consume it.  Here the
link is stated directly **on the window**, as

```text
  V =ᵐ[volume.restrict (truncatedWindow x m k)]
    fun y => v.toFun y - affineLift x c A y - v₁.toFun y ,
```

because the multi-face endpoint carries the *pointwise* restriction pinning
`w = v` on the window (`hwpin`) as one of its chain invariants.  Since
`truncatedWindow x m k = truncatedCube d m k x` definitionally, that is verbatim
`excess_oneStep_boundary_datumSplit`'s `hVae` at `k = n - 4`; no unwinding of
`oddFaceExtend ∘ zeroExtend` is left for the caller.

## Scope

None on the met configuration: interior, one face, edge and corner windows are
all served by the single statement below.  The remaining hypotheses are the ones
`Producer` already had — the anchor's Dirichlet datum, the weak harmonicity of
`v` and of the corrector `v₁`, and the corrector's trace structure.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

open MeasureTheory InnerProductSpace
open Homogenization (Vec H1Function MemH10 LocalizedZeroTraceFunctionOn openCubeSet originCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay (affineLift)

noncomputable section

variable {d : ℕ}

/-! ### The odd extension of the shifted competitor, any met configuration -/

/-- **The datum-split competitor extends oddly across *every* met face.**  The
instantiation of `PartialReflection.exists_h1_oddReflection_reflectedWindow` at
`V_odd = v − ℓ_h − v₁`: the two inputs are `AffineHarmonic`'s weak harmonicity
of the shift and `ZeroTrace`'s face-only zero trace, both already proved and
both free of any met-face hypothesis. -/
theorem exists_h1_oddReflection_datumSplit {x : Vec d} {m k : ℤ} (hkm : k < m)
    {u h : Vec d → ℝ} {c : ℝ} {A : Vec d}
    (hdat : MemH10 (openCubeSet (originCube d m)) (fun y => u y - h y))
    {v : H1Function (truncatedWindow x m k)}
    (hvharm : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v)
    (hvu : MemH10 (truncatedWindow x m k) (fun y => v.toFun y - u y))
    {v₁ Ψ : H1Function (truncatedWindow x m k)}
    (hv₁harm : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v₁)
    (hΨ : ∀ y ∈ truncatedWindow x m k, Ψ.toFun y = h y - affineLift x c A y)
    (hv₁Ψ : MemH10 (truncatedWindow x m k) (fun y => v₁.toFun y - Ψ.toFun y)) :
    ∃ w : H1Function (reflectedWindow x m k),
      IsUnitWeaklyHarmonicOn (reflectedWindow x m k) w ∧
      (∀ y ∈ truncatedWindow x m k,
        w.toFun y = v.toFun y - affineLift x c A y - v₁.toFun y) := by
  obtain ⟨w, hwharm, hwpin, -⟩ :=
    exists_h1_oddReflection_reflectedWindow hkm (datumSplitH1 v v₁ c A)
      (isUnitWeaklyHarmonicOn_datumSplitH1 hvharm hv₁harm c A)
      (localizedZeroTraceFunctionOn_datumSplitH1 hdat hvu hΨ hv₁Ψ)
  refine ⟨w, hwharm, fun y hy => ?_⟩
  rw [hwpin y hy, datumSplitH1_toFun]

/-! ### The classical competitor on the doubled window, any met configuration -/

/-- **The classical boundary competitor at the datum-split competitor, at every
window position.**

From the anchor's Dirichlet datum `u − h ∈ H¹₀(□_m)`, the weak harmonicity of
`v` and of the corrector `v₁`, and the corrector's trace structure, the odd
extension of `V_odd = v − ℓ_h − v₁` across **all** the met faces is *classically*
harmonic on the doubled window `reflectedWindow x m k`, and agrees a.e. with
`V_odd` on the window itself.

The first two conjuncts are the `hharm` and `hintsq`-carrying slots of
`Section6Schauder.exists_gradientHolder_boundary_truncatedCube`; the last is the
`hVae` slot of `OneStepDatum.excess_oneStep_boundary_datumSplit`.  Unlike
`Producer.exists_classicalCompetitor_datumSplit_of_meets{Upper,Lower}Face`, there
is **no** met-face hypothesis: interior, one-face, edge and corner windows are
served alike. -/
theorem exists_classicalCompetitor_datumSplit_corner [NeZero d] {x : Vec d} {m k : ℤ}
    (hkm : k < m) {u h : Vec d → ℝ} {c : ℝ} {A : Vec d}
    (hdat : MemH10 (openCubeSet (originCube d m)) (fun y => u y - h y))
    {v : H1Function (truncatedWindow x m k)}
    (hvharm : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v)
    (hvu : MemH10 (truncatedWindow x m k) (fun y => v.toFun y - u y))
    {v₁ Ψ : H1Function (truncatedWindow x m k)}
    (hv₁harm : IsUnitWeaklyHarmonicOn (truncatedWindow x m k) v₁)
    (hΨ : ∀ y ∈ truncatedWindow x m k, Ψ.toFun y = h y - affineLift x c A y)
    (hv₁Ψ : MemH10 (truncatedWindow x m k) (fun y => v₁.toFun y - Ψ.toFun y)) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m k) ∧
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedWindow x m k) ∧
      MemLp V 2 (volume : Measure (Vec d)) ∧
      V =ᵐ[volume.restrict (truncatedWindow x m k)]
        (fun y => v.toFun y - affineLift x c A y - v₁.toFun y) := by
  obtain ⟨w, hwharm, hwpin⟩ :=
    exists_h1_oddReflection_datumSplit hkm hdat hvharm hvu hv₁harm hΨ hv₁Ψ
  obtain ⟨V, hVR, hVmem, hVae⟩ := exists_classicalCompetitor_reflectedWindow x m k hwharm
  refine ⟨V, hVR, harmonicOnNhd_truncatedWindow_of_classicalCompetitor hVR, hVmem, ?_⟩
  have hVaeW : V =ᵐ[volume.restrict (truncatedWindow x m k)] w.toFun :=
    hVae.filter_mono (MeasureTheory.ae_mono (Measure.restrict_mono
      (truncatedWindow_subset_reflectedWindow x m k) le_rfl))
  filter_upwards [hVaeW, MeasureTheory.self_mem_ae_restrict
    (measurableSet_truncatedWindow x m k)] with y hy hymem
  rw [hy, hwpin y hymem]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
