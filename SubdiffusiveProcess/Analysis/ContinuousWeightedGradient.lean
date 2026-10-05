module

public import SubdiffusiveProcess.Analysis.NativeEnergyWindow
public import Homogenization.Sobolev.H1.BasicLemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

/-! A continuous scalar weight preserves local square integrability of a
Sobolev gradient on a bounded cube. Only finiteness, not a uniform coefficient
bound, is used in the resulting energy monotonicity estimate.
-/
open MeasureTheory Set SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
namespace SubdiffusiveProcess

/-- A continuous scalar function is essentially bounded on each bounded cube. -/
theorem continuous_memLp_top_cube {d : ℕ} (Q : Homogenization.TriadicCube d)
    (a : Vec d → ℝ) (ha : Continuous a) :
    MemLp a ⊤ (volume.restrict (openCubeSet Q)) := by
  obtain ⟨C, hC⟩ := (((isBounded_openCubeSet Q).isCompact_closure).image ha).isBounded.exists_norm_le
  refine memLp_top_of_bound ha.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx
  exact hC (a x) (mem_image_of_mem a (subset_closure hx))

/-- A continuous square-root coefficient times a Sobolev gradient is square integrable. -/
theorem continuousWeightedGradient_memLp {d : ℕ} (Q : Homogenization.TriadicCube d)
    (a : Vec d → ℝ) (ha : Continuous a) (u : H1Function (openCubeSet Q)) :
    MemLp (fun x => HilbertVec.ofVec (Real.sqrt (a x) • u.grad x)) 2
      (volume.restrict (openCubeSet Q)) := by
  have hG : MemLp (fun x => HilbertVec.ofVec (u.grad x)) 2 (volume.restrict (openCubeSet Q)) :=
    (HilbertVec.ofVecL d).comp_memLp' u.grad_memVectorL2
  have hS := continuous_memLp_top_cube Q (fun x => Real.sqrt (a x)) (Real.continuous_sqrt.comp ha)
  simpa only [Pi.smul_apply, ← HilbertVec.ofVecL_apply, map_smul] using! hS.smul hG

/-- All nested native gradient energies obey the deterministic volume comparison. -/
theorem continuousWeightedGradient_window {d : ℕ} (m : ℕ)
    (a : Vec d → ℝ) (ha : Continuous a) (u : H1Function (openCubeSet (originCube d (m : ℤ))))
    (i j : ℕ) (hij : i ≤ j) (hjm : j ≤ m) :
    vectorNormalizedL2On (openCubeSet (originCube d (i : ℤ))) (fun x => Real.sqrt (a x) • u.grad x) ≤
      Real.sqrt (((3 : ℝ) ^ j) ^ d / ((3 : ℝ) ^ i) ^ d) *
        vectorNormalizedL2On (openCubeSet (originCube d (j : ℤ))) (fun x => Real.sqrt (a x) • u.grad x) := by
  apply nativeEnergyWindow_le i j hij
  exact (continuousWeightedGradient_memLp (originCube d (m : ℤ)) a ha u).mono_measure
    (Measure.restrict_mono (openCubeSet_originCube_subset_of_scale_le
      (show (j : ℤ) ≤ m by exact_mod_cast hjm)) le_rfl)

end SubdiffusiveProcess
