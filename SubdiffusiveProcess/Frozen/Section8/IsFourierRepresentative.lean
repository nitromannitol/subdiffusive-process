import SubdiffusiveProcess.Frozen.Section8.InverseFourierSchwartz
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FrozenNamespace

open MeasureTheory
open Homogenization

noncomputable section
open SubdiffusiveProcess.Frozen.Section8


def SubdiffusiveProcess.Frozen.Section8.IsFourierRepresentative {d : ℕ} (F : Vec d → Vec d)
    (Fhat : Vec d → Fin d → ℂ) : Prop :=
  ∀ i (phi : SchwartzMap (Vec d) ℂ),
    Integrable
        (fun x ↦ Complex.ofReal (F x i) * inverseFourierSchwartz phi x)
        volume ∧
    Integrable (fun xi ↦ Fhat xi i * phi xi) volume ∧
    ∫ x, Complex.ofReal (F x i) * inverseFourierSchwartz phi x ∂volume =
      ∫ xi, Fhat xi i * phi xi ∂volume


