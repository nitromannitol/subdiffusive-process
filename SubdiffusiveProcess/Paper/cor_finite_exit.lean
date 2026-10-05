module

public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Paper.mfd_convergence

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal LevyProkhorov
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The native limiting diffusion has uniformly finite mean exit times from
all bounded open sets, simultaneously on one event of full environment measure.
Every analytic/process supplier is applied internally. The convergence
conjunct identifies the actual limiting law, rather than an arbitrary kernel. -/
theorem cor_finite_exit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∃ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N)),
        in_crossing M H PN KN ∧
        ∃ (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (_hP : ∀ omega, (P omega).IsConservative)
          (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
          (hK : IsMarkovKernel K),
          ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ B : Set (SpatialCoordinates d), IsCompact B →
              ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
                ∀ x ∈ B,
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x) < epsilon) ∧
            HasFiniteMeanExits K omega :=
 by
  classical
  obtain ⟨Jc, Pc, Xc, Sf, W, Cp, D, hES, Step, Dbase, Interp, BD, BDQ,
    hcontract, hlife, _EM, deltaR, Cresp, hdeltaR, _hCresp, hsup⟩ :=
    inputs_simultaneous d hd
  obtain ⟨deltaC, hdeltaC, hconv⟩ := mfd_convergence d hd Jc Pc Xc Sf W Cp D
    hES Step Dbase Interp BD BDQ hcontract hlife
  refine ⟨min deltaR deltaC, lt_min hdeltaR hdeltaC, ?_⟩
  intro M hM
  have hMR : M.delta ≤ deltaR := hM.trans (min_le_left _ _)
  have hMC : M.delta ≤ deltaC := hM.trans (min_le_right _ _)
  obtain ⟨Rm, Sreg, _hRm, ⟨It⟩⟩ := hsup M M.shellPrefix.delta_pos hMR
  obtain ⟨H, hHmeas, PN, hPN, P, hP, KN, hKN, K, hK, hae, _hann⟩ :=
    hconv M Rm Sreg It M.shellPrefix.delta_pos hMC
  have hH : InfraredCharacterization M H :=
    ⟨hHmeas, hae.mono fun omega h => h.1⟩
  have hin : in_crossing M H PN KN :=
    ⟨hae.mono fun omega h => h.2.1, hPN,
      hae.mono fun omega h => h.2.2.1⟩
  refine ⟨H, hH, PN, KN, hKN, hin, P, hP, K, hK, ?_⟩
  filter_upwards [hae] with omega h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2⟩

end SubdiffusiveProcess.Paper
