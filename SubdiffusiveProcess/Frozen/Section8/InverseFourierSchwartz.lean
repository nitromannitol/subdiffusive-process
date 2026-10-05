module

public import SubdiffusiveProcess.Frozen.Section8.VecDotLinear
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FrozenNamespace

@[expose] public section

open MeasureTheory
open Homogenization

noncomputable section
open SubdiffusiveProcess.Frozen.Section8


def SubdiffusiveProcess.Frozen.Section8.inverseFourierSchwartz {d : ℕ} (phi : SchwartzMap (Vec d) ℂ)
    (x : Vec d) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume (vecDotLinear d)
    (fun xi : Vec d ↦ phi xi) (-x)


