module

public import SubdiffusiveProcess.Section8.InverseFourierSchwartz
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.NamespaceAnchor

@[expose] public section

open MeasureTheory
open Homogenization

noncomputable section
open _root_.SubdiffusiveProcess.Section8

def SubdiffusiveProcess.Section8.IsFourierRepresentative {d : ℕ} (F : Vec d → Vec d)
    (Fhat : Vec d → Fin d → ℂ) : Prop :=
  ∀ i (phi : SchwartzMap (Vec d) ℂ),
    Integrable
        (fun x ↦ Complex.ofReal (F x i) * inverseFourierSchwartz phi x)
        volume ∧
    Integrable (fun xi ↦ Fhat xi i * phi xi) volume ∧
    ∫ x, Complex.ofReal (F x i) * inverseFourierSchwartz phi x ∂volume =
      ∫ xi, Fhat xi i * phi xi ∂volume
