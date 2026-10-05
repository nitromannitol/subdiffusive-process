module

public import SubdiffusiveProcess.Probability.LayerProductBlocks

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace SubdiffusiveProcess

/-- Replacing any entire block of an original product field by the same block of an independent copy preserves the original field law, including infinite blocks. The product is formed before completion. -/
theorem measurePreserving_copy_infinitePi_block
    {I : Type*} {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Set I) [DecidablePred (fun i => i ∈ S)] :
    MeasurePreserving
      (fun z : ((i : I) → X i) × ((i : I) → X i) =>
        fun i : I => if i ∈ S then z.2 i else z.1 i)
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ))
      (Measure.infinitePi μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd X (fun i => i ∈ S)
  let νS := Measure.infinitePi (fun i : S => μ i)
  let νC := Measure.infinitePi (fun i : {i // i ∉ S} => μ i)
  have hsplit : MeasurePreserving e (Measure.infinitePi μ) (νS.prod νC) :=
    measurePreserving_infinitePi_split μ (fun i => i ∈ S)
  have hproject : MeasurePreserving (Prod.map Prod.fst Prod.snd)
      ((νS.prod νC).prod (νS.prod νC)) (νS.prod νC) :=
    measurePreserving_fst.prod measurePreserving_snd
  have hswap : MeasurePreserving Prod.swap
      ((νS.prod νC).prod (νS.prod νC))
      ((νS.prod νC).prod (νS.prod νC)) :=
    Measure.measurePreserving_swap
  have h := (MeasurePreserving.symm e hsplit).comp
    (hproject.comp (hswap.comp (hsplit.prod hsplit)))
  convert h using 1
  funext z i
  change (if i ∈ S then z.2 i else z.1 i) =
    (if _h : i ∈ S then z.2 i else z.1 i)
  split_ifs <;> rfl

end SubdiffusiveProcess
