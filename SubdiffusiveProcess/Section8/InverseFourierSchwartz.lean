module

public import SubdiffusiveProcess.Section8.VecDotLinear
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.NamespaceAnchor

@[expose] public section

open MeasureTheory
open Homogenization

noncomputable section
open _root_.SubdiffusiveProcess.Section8

def SubdiffusiveProcess.Section8.inverseFourierSchwartz {d : ℕ} (phi : SchwartzMap (Vec d) ℂ)
    (x : Vec d) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume (vecDotLinear d)
    (fun xi : Vec d ↦ phi xi) (-x)
