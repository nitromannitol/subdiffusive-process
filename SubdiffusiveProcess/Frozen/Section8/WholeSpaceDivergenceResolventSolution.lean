module

public import SubdiffusiveProcess.Frozen.Section8.MassiveWeakSolution
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FrozenNamespace

@[expose] public section

open MeasureTheory
open Homogenization

noncomputable section
open SubdiffusiveProcess.Frozen.Section8


structure SubdiffusiveProcess.Frozen.Section8.WholeSpaceDivergenceResolventSolution {d : ℕ}
    (a : Vec d → ℝ) (t : ℝ) (f : Vec d → ℝ) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memL2_toFun : MemLp toFun 2 volume
  integrable_energy : Integrable (fun x ↦ a x * vecNormSq (grad x)) volume
  locally_weak_solution : ∀ (W : Set (Vec d)), IsOpenBoundedConvexDomain W →
    ∃ u : H1Function W,
      (∀ x ∈ W, u.toFun x = toFun x) ∧
      u.grad =ᵐ[volume.restrict W] grad ∧
      IsMassiveWeakSolutionOn a (fun _ ↦ (1 : ℝ)) t⁻¹ W u
        (fun x ↦ t⁻¹ * f x)


