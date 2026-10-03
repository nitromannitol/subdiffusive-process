module

public import SubdiffusiveProcess.Processes.E7.KilledGenerator
public import SubdiffusiveProcess.Processes.E7.ZeroDim
public import SubdiffusiveProcess.Probability.Diffusion.AnalyticInput

@[expose] public section

/-!
# `inputs_classical_e7` from the two frozen classical leaves

The lifetime restart law comes from the Feller ⇒ strong Markov leaf, after the semigroup is shown to
be Feller (`isFeller_of_realization_and_datum`); the killed generator comes from the part-process leaf
after the association `D = G` (`association_of_datum`) and the analytic assembly (`part_analytic`),
in dimension `d ≥ 1`; dimension `0` is degenerate.
-/
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.E7
open SubdiffusiveProcess.Probability.Diffusion.Input
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

theorem continuous_of_locallyC11 {d : ℕ} {a : State d → ℝ} (h : LocallyC11 a) : Continuous a := by
  obtain ⟨Da, hDa, _⟩ := h
  exact continuous_iff_continuousAt.2 fun x => (hDa x).continuousAt

/-- **`inputs_classical_e7`, discharged from the two frozen leaves.** -/
theorem e7_of_leaves (hSM : FellerStrongMarkov) (hFOT : FOTPartProcess)
    (d : ℕ) (c rho : (Fin d → ℝ) → ℝ)
    (hcpos : ∀ x, 0 < c x) (hrhopos : ∀ x, 0 < rho x)
    (hc : LocallyC11 c) (hrho : LocallyC11 rho)
    (P : SubMarkovKernelSemigroup (Fin d → ℝ))
    (hP : P.IsConservative)
    (D : C0ResolventDatum (Fin d → ℝ))
    (hdense : ∀ mu, DenseRange (D.operator mu))
    (hweak : IsWeakEllipticResolvent c rho D)
    (hlaplace : ∀ (mu : Semigroup.PositiveShift)
      (f : ZeroAtInftyContinuousMap (Fin d → ℝ) ℝ) (x : Fin d → ℝ),
      D.solution mu f x = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) f x)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ)))
    (hK : IsMarkovKernel K)
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) :
    Restart (K.map LifetimePath.ofContinuousPath) ∧
      KilledGenerator c rho (K.map LifetimePath.ofContinuousPath) := by
  haveI := hK
  have hFeller := (isFeller_of_realization_and_datum P D hdense hlaplace K hfdd).2
  refine ⟨hSM d P hP hFeller K hK hfdd, ?_⟩
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact killedGenerator_zero_dim c rho K
  · haveI : NeZero d := ⟨hd.ne'⟩
    exact killedGenerator_of_leaf (continuous_of_locallyC11 hc) (continuous_of_locallyC11 hrho)
      hcpos hrhopos P hP hFeller D hweak hlaplace K hfdd hFOT

end SubdiffusiveProcess.E7
