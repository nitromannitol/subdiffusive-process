module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WeightedMassiveSolution
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FrozenNamespace

@[expose] public section

open MeasureTheory
open Homogenization

noncomputable section
open SubdiffusiveProcess.Frozen.Section8


def SubdiffusiveProcess.Frozen.Section8.IsMassiveWeakSolutionOn {d : ℕ} (c rho : Vec d → ℝ) (mu : ℝ)
    (W : Set (Vec d)) (u : H1Function W) (f : Vec d → ℝ) : Prop :=
  ∀ phi : H10Function W,
    mu * ∫ x in W, rho x * u.toFun x * phi.toH1Function.toFun x ∂volume +
        ∫ x in W, vecDot (c x • u.grad x) (phi.toH1Function.grad x) ∂volume =
      ∫ x in W, rho x * f x * phi.toH1Function.toFun x ∂volume


