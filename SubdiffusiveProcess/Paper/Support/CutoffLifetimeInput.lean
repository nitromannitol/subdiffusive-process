import SubdiffusiveProcess.Examples.NormalizedDensity
import SubdiffusiveProcess.Paper.lim_thm_measure





/-! # The exact normalized-cutoff continuous-density carried input -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

namespace SubdiffusiveProcess.Examples
noncomputable section

/-- Attach continuous densities to the supplied crossing kernel, with no kernel replacement. -/
theorem cutoff_continuousKilledDensities_of_regular {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : Paper.in_crossing M H PN KN)
    (hregular : ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SubdiffusiveProcess.Probability.Diffusion.Input.LocallyC11 (cutoffSpeedDensity M H w N)) :
    ∀ᵐ w ∂(chaosSampleLaw M).toMeasure, ∀ N,
      SubdiffusiveProcess.Probability.Diffusion.Input.ContinuousKilledDensities (cutoffSpeedDensity M H w N)
        (Paper.aux_cutoff_lifetime_package_kernel KN N w) := by
  filter_upwards [hin.1, hin.2.2, hregular] with w hres hfdd hreg
  intro N
  obtain ⟨D, hdense, hweak, hlap⟩ := hres N
  let L := (KN N).comap (Prod.mk w) measurable_prodMk_left
  letI : IsMarkovKernel (KN N) := hKN N
  letI : IsMarkovKernel L := by dsimp [L]; infer_instance
  have hLfdd : ∀ I, L.map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel (PN N w) I := by
    intro I
    ext x B hB
    rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _),
      Kernel.comap_apply, ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation _)]
    exact congrArg (fun mu => mu B) (hfdd N I x)
  exact normalized_continuousKilledDensities hd Paper.aux_limit_measure_fotPartProcess
    (cutoffSpeedDensity M H w N) (fun _ => Real.exp_pos _) (hreg N)
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹
    (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
    (PN N w) (hin.2.1 N w) D hdense hweak hlap L hLfdd

/-- Exact inhabitant of the paper's full lifetime input for the actual infrared model.
There is no density premise and no small-disorder premise. All KN rows are retained. -/
theorem cutoff_lifetime_input {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d) (M : GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N)) (hin : Paper.in_crossing M H PN KN) :
    Paper.aux_cutoff_lifetime_package_Input M H KN := by
  have hreg := Paper.inputs_local_coefficients_c11 M H hd hH
  have hdens := cutoff_continuousKilledDensities_of_regular hd M H PN KN hKN hin
    (hreg.mono fun _ h N => (h N).2)
  have hlocal := Paper.aux_lim_thm_measure_actual_cutoff_localDiffusion_supplier hd
    M H hH PN KN hKN hin
  refine ⟨?_⟩
  filter_upwards [hlocal, hdens] with w hl hd
  intro N
  refine ⟨hl N, ?_⟩
  intro U hU hUb
  obtain ⟨p, hm, hp, heq, hc⟩ := hd N U hU hUb
  exact ⟨p, ⟨hm, hp, heq⟩, hc⟩

end
end SubdiffusiveProcess.Examples
