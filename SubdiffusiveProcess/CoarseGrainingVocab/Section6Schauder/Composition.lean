import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Interface
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.WeylRepresentative

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/OneStepSchauderComposeInterior.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepSchauderComposeInterior.lean

/-!
# Composing Weyl's lemma with the interior Schauder estimate

`Interface.exists_gradientHolder_truncatedCube` assumes the competitor is
**classically** harmonic (`HarmonicOnNhd`).  What section 6's
harmonic-approximation input delivers is the **variational**
`IsWeaklyHarmonicOn (fun _ => 1)` on the replacement cube `y + □_{n-2}`.
Weyl's lemma (`WeylRepresentative.exists_harmonicRepresentative_memLp`) bridges
the two, and this module performs the composition.

The competitor produced here is a *representative*: it agrees with the given
`H¹` function almost everywhere on the replacement cube, which is all that the
`L̲²` comparison error `‖u-v‖_{L̲²}` of the one-step contraction can see.

## Scope

Interior branch only (`hcube`): the enveloping window `U_{m,n-4}(x)` is a full
translated cube, so no face of `∂□_m` is met and the boundary-datum leg is
`K_h = 0`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

open MeasureTheory InnerProductSpace
open Homogenization (Vec H1Function)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ### The replacement cube as a domain -/

theorem isOpen_translatedCube (d : ℕ) (j : ℤ) (y : Vec d) :
    IsOpen (translatedCube d j y) :=
  (isOpenBoundedConvexDomain_translatedCube d j y).isOpen

theorem measurableSet_translatedCube (d : ℕ) (j : ℤ) (y : Vec d) :
    MeasurableSet (translatedCube d j y) :=
  (isOpen_translatedCube d j y).measurableSet

/-! ### The classical competitor -/

/-- **The classical competitor.**  From a variationally harmonic `H¹` function
on a replacement cube `y + □_j`, Weyl's lemma produces a globally square
integrable representative which is classically harmonic on the whole cube and
agrees with it almost everywhere there. -/
theorem exists_classicalCompetitor_translatedCube [NeZero d] (j : ℤ) (y : Vec d)
    {w : H1Function (translatedCube d j y)}
    (hw : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (translatedCube d j y) w) :
    ∃ v : Vec d → ℝ,
      HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' translatedCube d j y) ∧
      MemLp v 2 (volume : Measure (Vec d)) ∧
      v =ᵐ[volume.restrict (translatedCube d j y)] w.toFun := by
  obtain ⟨v, hharm, hmem, hae⟩ :=
    exists_harmonicRepresentative_memLp (isOpen_translatedCube d j y)
      (isUnitWeaklyHarmonicOn_iff.2 hw)
  refine ⟨v, hharm, hmem, ?_⟩
  have h1 : v =ᵐ[volume.restrict (translatedCube d j y)]
      Set.indicator (translatedCube d j y) w.toFun :=
    MeasureTheory.ae_restrict_of_ae hae
  filter_upwards [h1,
    MeasureTheory.self_mem_ae_restrict (measurableSet_translatedCube d j y)] with p hp hpR
  rw [hp, Set.indicator_of_mem hpR]

/-! ### The composed interior endpoint -/

/-- **The Schauder gradient-Hölder package from variational harmonicity alone.**

Given a competitor `w` that is only *weakly* harmonic on the replacement cube
`y + □_{n-2}` — which is what section 6's harmonic-approximation input produces
— there is a representative `v`, equal to `w` almost everywhere there, whose
gradient field realizes the four slots
`hint / hgrad / hhol / hschauder` of
`SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.excess_oneStep_of_schauder`, with
`Csch = schauderInteriorConst d` and `K_h = 0`. -/
theorem exists_gradientHolder_of_weaklyHarmonic [NeZero d] (hd : d ≠ 0) {m n : ℤ} {x y : Vec d}
    (hx : x ∈ cube d m) (hnm : n - 5 ≤ m)
    (hcube : translatedCube d (n - 4) x ⊆ cube d m)
    (hsub : truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y)
    {w : H1Function (translatedCube d (n - 2) y)}
    (hw : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) (translatedCube d (n - 2) y) w) :
    ∃ (v : Vec d → ℝ) (K : ℝ),
      v =ᵐ[volume.restrict (translatedCube d (n - 2) y)] w.toFun ∧
      MemLp v 2 (volume : Measure (Vec d)) ∧
      0 ≤ K ∧
      (∀ i, IntegrableOn (fun p => gradField v p i) (truncatedCube d m (n - 5) x) volume) ∧
      HasGradientOn (truncatedCube d m (n - 5) x) v (gradField v) ∧
      HolderSeminormBoundOn (truncatedCube d m (n - 5) x) (1 / 2 : ℝ) K (gradField v) ∧
      K ≤ schauderInteriorConst d * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
            excess (n - 4) (truncatedCube d m (n - 4) x) v + 0 := by
  obtain ⟨v, hvharm, hvmem, hvae⟩ := exists_classicalCompetitor_translatedCube (n - 2) y hw
  have hharm : HarmonicOnNhd (v ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' truncatedCube d m (n - 4) x) :=
    hvharm.mono (Set.image_mono hsub)
  obtain ⟨K, hK0, hint, hgrad, hhol, hbound⟩ :=
    exists_gradientHolder_truncatedCube hd hx hnm hcube hharm (hvmem.restrict _)
  exact ⟨v, K, hvae, hvmem, hK0, hint, hgrad, hhol, hbound⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
