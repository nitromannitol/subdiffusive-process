module

public import SubdiffusiveProcess.Paper.mfd_prop_uniform_resolvent
public import SubdiffusiveProcess.Paper.Support.KillingNativeAssembly

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem mfd_lem_killing
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
        aux_cutoff_lifetime_package_LocalInput M H KN ∧
        ∃ (P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
          (K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
          (hK : IsMarkovKernel K)
          (mu : BilateralField d → Measure (SpatialCoordinates d)),
          Measurable mu ∧
          (∀ B : Set (SpatialCoordinates d), IsCompact B →
            ∀ eps : ℝ, 0 < eps →
              Tendsto (fun N ↦ (chaosSampleLaw M).toMeasure
                {omega : BilateralField d | ∃ x ∈ B, eps ≤
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x)}) atTop (nhds 0)) ∧
          (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            MeasuresConvergeLocally
              (fun N ↦ cutoffSpeedMeasure M H omega N) (mu omega) ∧
            IsLocallyFiniteMeasure (mu omega) ∧
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
              Continuous (kernelIntegral (P omega t) f)) ∧
            (P omega).IsConservative ∧
            HasStrongMarkovRestart K omega ∧
            SemigroupSymmetric (P omega) (mu omega) ∧
            (∀ nu : Measure (SpatialCoordinates d),
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) nu →
              IsLocallyFiniteMeasure nu → SemigroupSymmetric (P omega) nu)) ∧
          SubdiffusiveProcess.Section9.KilledFormResolventIdentification d hd M H KN K mu :=
by
  classical
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  let epsilon : ℝ := 1 / (16 * ((d : ℝ) + 2))
  have hden : 0 < (d : ℝ) + 2 := by positivity
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hepsilon' : epsilon < 1 / (8 * ((d : ℝ) + 2)) := by
    dsimp only [epsilon]
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  obtain ⟨deltaR, hdeltaR, hmain⟩ := mfd_prop_uniform_resolvent d hd
    epsilon hepsilon hepsilon' {2} (by simp) (by simp)
  apply aux_mfd_lem_killing_of_produced_bank hd deltaR hdeltaR
  intro M hM H hH PN KN hKN hin
  obtain ⟨G, muFull, hGmeas, hmumeas, hGconv, hmu, T, Ktrace, Ctrace,
    lift, J, ustar, R, KQ, htrace, hRmeas, hprob, hKm, hregular⟩ :=
    hmain M M.shellPrefix.delta_pos hM H hH PN KN hKN hin
  refine ⟨muFull, hmumeas, G, hGmeas, hGconv, hmu, T, Ktrace, Ctrace,
    lift, J, ustar, R, KQ, htrace, hRmeas, hprob, ?_, hregular⟩
  intro i
  exact ⟨(hKm i).1, by simpa using (hKm i).2 2 (by simp)⟩

end SubdiffusiveProcess.Paper
