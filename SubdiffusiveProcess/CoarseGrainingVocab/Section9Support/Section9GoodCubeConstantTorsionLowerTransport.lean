import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionTest
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.MassiveTranslation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.FlatComparatorTransport
import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySplit
/-!

Transport an actual constant torsion carrier, its weak equation and its interior profile to a physical translated cube. The coefficient-local comparison test then bounds the physical normalized L2 discrepancy.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Filter Set SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Construct the translated zero-trace profile and derive its actual physical comparison. -/
theorem goodCube_translated_constantTorsion_data
    {d : ℕ} (Q : TriadicCube d) (z : Vec d) (a : Vec d → ℝ)
    (sigma eps theta c : ℝ)
    (htest : GoodCubeTorsionComparisonTest Q (fun x => a (x + z)) sigma eps)
    (w : H10Function (openCubeSet Q))
    (hw : IsMassiveWeakSolutionOn (fun _ => sigma) (fun _ => 1) 0
      (openCubeSet Q) w.toH1Function (fun _ => 1))
    (hwlower : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      x ∈ scaledClosedCubeSet Q theta → c ≤ w.toH1Function.toFun x) :
    ∃ g : H10Function (translateSet z (openCubeSet Q)),
      g.toH1Function.toFun = (fun x => w.toH1Function.toFun (x - z)) ∧
      IsMassiveWeakSolutionOn (fun _ => sigma) (fun _ => 1) 0
        (translateSet z (openCubeSet Q)) g.toH1Function (fun _ => 1) ∧
      (∀ᵐ x ∂volume.restrict (translateSet z (openCubeSet Q)),
        x ∈ translateSet z (scaledClosedCubeSet Q theta) → c ≤ g.toH1Function.toFun x) ∧
      ∀ u : H10Function (translateSet z (openCubeSet Q)),
        IsMassiveWeakSolutionOn a a 0 (translateSet z (openCubeSet Q))
          u.toH1Function (fun _ => 1) →
        normalizedL2On (translateSet z (openCubeSet Q))
            (fun x => u.toH1Function.toFun x - g.toH1Function.toFun x) ≤
          eps * (cubeScaleFactor Q)^2 / sigma := by
  refine ⟨w.translate z, ?_, ?_, ?_, ?_⟩
  · funext x
    simp only [H10Function.translate_toH1Function, H1Function.translate_toFun]
  · simp only [H10Function.translate_toH1Function]
    exact isMassiveWeakSolutionOn_translate z hw
  · have hae : ∀ᵐ x ∂volume.restrict (translateSet z (openCubeSet Q)),
      x - z ∈ scaledClosedCubeSet Q theta → c ≤ w.toH1Function.toFun (x - z) :=
      (measurePreserving_subRight_restrict_translateSet z
        (openCubeSet Q)).quasiMeasurePreserving.ae hwlower
    filter_upwards [hae] with x hx hmem
    change c ≤ w.toH1Function.toFun (x - z)
    exact hx (mem_translateSet_iff_sub_mem.mp hmem)
  · intro u hu
    have hu0 : IsMassiveWeakSolutionOn (fun x => a (x + z)) (fun x => a (x + z)) 0
        (openCubeSet Q) (H10Function.untranslate z u).toH1Function (fun _ => 1) := by
      simpa only [H10Function.untranslate_toH1Function] using
        isMassiveWeakSolutionOn_untranslate z u.toH1Function hu
    have hbound := htest (H10Function.untranslate z u) w hu0 hw
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.normalizedL2On_translateSet z
      (openCubeSet Q)
      (fun x => u.toH1Function.toFun x - (w.translate z).toH1Function.toFun x)]
    have hfun : (fun x => u.toH1Function.toFun (x + z) -
          (w.translate z).toH1Function.toFun (x + z)) =
        (fun x => (H10Function.untranslate z u).toH1Function.toFun x -
          w.toH1Function.toFun x) := by
      funext x
      simp [H10Function.translate_toH1Function, H10Function.untranslate_toH1Function,
        ← H1Function.untranslate_toFun]
    simp only [hfun]
    have hmem : MemLp (fun x => (H10Function.untranslate z u).toH1Function.toFun x -
        w.toH1Function.toFun x) 2 (volume.restrict (openCubeSet Q)) :=
      MemLp.sub (H10Function.untranslate z u).toH1Function.memL2 w.toH1Function.memL2
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.normalizedL2On_openCubeSet_eq_cubeLpNorm
      Q hmem]
    exact hbound

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
