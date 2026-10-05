module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.NamespaceAnchor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierGrowth

@[expose] public section

open MeasureTheory
open Homogenization
open MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section
open _root_.SubdiffusiveProcess.Section8

/-- Provider for the frozen datum anchor v3 : the bare application of
`exists_delta0_gmc_resolvent_data`. -/
theorem SubdiffusiveProcess.Providers.Section8.exists_gmc_resolvent_data {d : ℕ} [NeZero d] :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 → ∀ L : WithTop ℕ,
    ∃ hmeas : MeasurableSet (_root_.SubdiffusiveProcess.Model.anchoredC11GoodSet d),
    ∃ hfull : M.P.toMeasure (_root_.SubdiffusiveProcess.Model.anchoredC11GoodSet d) = 1,
    ∃ full : Set (_root_.SubdiffusiveProcess.Model.AnchoredC11Sample d),
      MeasurableSet full ∧
      (_root_.SubdiffusiveProcess.Model.anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
    ∃ DX DY : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d →
        SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (Vec d),
      ∀ omega ∈ full,
        (∀ mu, DenseRange ((DX omega).operator mu)) ∧
        SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
          (SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt M L omega)
          (SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt M L omega) (DX omega) ∧
        (∀ mu, DenseRange ((DY omega).operator mu)) ∧
        SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
          (SubdiffusiveProcess.CoarseGrainingVocab.coefficientAt M L omega)
          (fun _ ↦ (1 : ℝ)) (DY omega)
:= SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.exists_delta0_gmc_resolvent_data d
