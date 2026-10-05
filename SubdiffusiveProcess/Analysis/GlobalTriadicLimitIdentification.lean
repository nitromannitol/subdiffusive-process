module

public import SubdiffusiveProcess.Analysis.GlobalTriadicPointwise
public import Mathlib

@[expose] public section

open MeasureTheory Set TopologicalSpace Filter
open SubdiffusiveProcess.CoarseGrainingVocab
noncomputable section
namespace SubdiffusiveProcess

local notation:50 f " =ᵃᵉ[" μ "] " g:50 => f =ᵐ[μ] g

theorem globalTriadicAverages_L2_limit_eq_ae_indicator_of_continuousOn
    {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (ν : Measure (SpatialCoordinates d))
    (hplanes : ∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0)
    (f : SpatialCoordinates d → ℝ)
    (hf : ContinuousOn f (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (g : SpatialCoordinates d → ℝ) :
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  (∀ n : ℕ, MemLp (E n) 2 ν) →
  MemLp g 2 ν →
  Filter.Tendsto (fun n => eLpNorm (fun x => E n x - g x) 2 ν) Filter.atTop (nhds 0) →
  g =ᵃᵉ[ν] (centeredCube z r hr : Set (SpatialCoordinates d)).indicator f := by
  dsimp only
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  change (∀ n : ℕ, MemLp (E n) 2 ν) →
    MemLp g 2 ν →
    Filter.Tendsto (fun n => eLpNorm (fun x => E n x - g x) 2 ν) Filter.atTop (nhds 0) →
    g =ᵐ[ν] (centeredCube z r hr : Set (SpatialCoordinates d)).indicator f
  intro hE hg hnorm
  have hmeasure : TendstoInMeasure ν E Filter.atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hnorm
  obtain ⟨ns, hns, hsub⟩ := hmeasure.exists_seq_tendsto_ae
  have hpoint : ∀ᵐ x ∂ν, Tendsto (fun n => E n x) Filter.atTop
      (nhds ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator f x)) := by
    simpa only [E] using!
      (globalTriadicAverages_tendsto_ae_of_continuousOn hd z hr ν hplanes f hf)
  have hpoint_sub : ∀ᵐ x ∂ν, Tendsto (fun i => E (ns i) x) Filter.atTop
      (nhds ((centeredCube z r hr : Set (SpatialCoordinates d)).indicator f x)) := by
    filter_upwards [hpoint] with x hx
    exact hx.comp hns.tendsto_atTop
  exact AEEqFun.tendsto_ae_unique hsub hpoint_sub


end SubdiffusiveProcess
