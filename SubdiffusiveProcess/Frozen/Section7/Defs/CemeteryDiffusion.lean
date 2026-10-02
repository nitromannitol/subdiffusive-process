import MarkovProcess.Main
import MarkovProcess.Lifetime.Law
import MarkovProcess.Parameterized.Semigroup
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.IntrinsicClock
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Process.State
import SubdiffusiveProcess.Frozen.Section7.Defs.GeneratedDiffusionFamily
import SubdiffusiveProcess.Frozen.Section7.Defs.PerStartKolmogorovRegular
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

