import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FrozenNamespace
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumBarrierGrowth

open MeasureTheory
open Homogenization
open MarkovProcess.Semigroup
open scoped ZeroAtInfty

noncomputable section
open SubdiffusiveProcess.Frozen.Section8

/-- Provider for the frozen datum anchor v3 (D-109): the bare application of
`exists_delta0_gmc_resolvent_data` (P-203). -/
theorem SubdiffusiveProcess.Providers.Section8.exists_gmc_resolvent_data {d : ℕ} [NeZero d] :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 → ∀ L : WithTop ℕ,
    ∃ hmeas : MeasurableSet (SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet d),
    ∃ hfull : M.P.toMeasure (SubdiffusiveProcess.Frozen.Assumptions.anchoredC11GoodSet d) = 1,
    ∃ full : Set (SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d),
      MeasurableSet full ∧
      (SubdiffusiveProcess.Frozen.Assumptions.anchoredC11SampleLaw M hmeas hfull).toMeasure full = 1 ∧
    ∃ DX DY : SubdiffusiveProcess.Frozen.Assumptions.AnchoredC11Sample d →
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
