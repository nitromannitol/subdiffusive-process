module

public import MarkovProcess.Main
public import MarkovProcess.Lifetime.Law
public import MarkovProcess.Parameterized.Semigroup
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
public import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
public import SubdiffusiveProcess.Frozen.Section7.Defs.GeneratedDiffusionFamily
public import SubdiffusiveProcess.Frozen.Section7.Defs.PerStartKolmogorovRegular
@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
open SubdiffusiveProcess.Frozen.Section7


structure SubdiffusiveProcess.Frozen.Section7.CemeteryDiffusion {Theta : Type*} [MeasurableSpace Theta] (d : ℕ)
    {coefficient weight : Theta → State d → ℝ}
    {datum : Theta → SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (State d)}
    (D : GeneratedDiffusionFamily Theta d coefficient weight datum) where
  law : Kernel (Theta × State d) (MarkovProcess.ContinuousPath (State d))
  isMarkov : IsMarkovKernel law
  finiteDimensionalLaw : ∀ theta x (I : Finset NNReal),
    (law (theta, x)).map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
      MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
        (D.semigroup.toSubMarkovKernelSemigroup theta) I x
  kolmogorovRegularAt : PerStartKolmogorovRegular
    (MarkovProcess.Kernel.toLifetimePathKernel law)

