module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.WeightedField

@[expose] public section

/-!
# The two displays pass to the limit, from convergence on the outer window only

`Section6TheoremC.EstimateLimits` closes both limit passages once convergence
is known **on each of the two windows separately**.  In the infinite-cutoff
argument the convergence is produced only on the outer window `𝔠_m`, by the
energy comparison; on the inner window `z + 𝔠_n ⊆ 𝔠_m` it follows by
monotonicity of the integral.

This file performs that reduction once for each display, so that the assembly
supplies a single hypothesis per display: an outer-window `L²` limit.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- **The oscillation display passes to the limit.**  Only outer-window `L²`
convergence is assumed. -/
theorem centeredNormalizedL2On_le_mul_of_outer_tendsto {V W : Set (Vec d)}
    {f : ℕ → Vec d → ℝ} {flim : Vec d → ℝ} {K : ℝ}
    (hVm : MeasurableSet V) (hVpos : 0 < (volume V).toReal)
    (hVfin : volume V ≠ ⊤)
    (hWm : MeasurableSet W) (hWpos : 0 < (volume W).toReal)
    (hWfin : volume W ≠ ⊤) (hVW : V ⊆ W)
    (hfW : ∀ j, MemLp (f j) 2 (volume.restrict W))
    (hflimW : MemLp flim 2 (volume.restrict W))
    (hconv : Tendsto (fun j ↦ ∫ x in W, (f j x - flim x) ^ 2 ∂volume)
      atTop (nhds 0))
    (hle : ∀ j, normalizedL2On V (fun x ↦ f j x - averageOn V (f j)) ≤
      K * normalizedL2On W (fun x ↦ f j x - averageOn W (f j))) :
    normalizedL2On V (fun x ↦ flim x - averageOn V flim) ≤
      K * normalizedL2On W (fun x ↦ flim x - averageOn W flim) := by
  have hrestrict : volume.restrict V ≤ volume.restrict W :=
    Measure.restrict_mono hVW le_rfl
  have hfV : ∀ j, MemLp (f j) 2 (volume.restrict V) := fun j ↦
    (hfW j).mono_measure hrestrict
  have hflimV : MemLp flim 2 (volume.restrict V) :=
    hflimW.mono_measure hrestrict
  have hsqW : ∀ j, IntegrableOn (fun x ↦ (f j x - flim x) ^ 2) W := fun j ↦
    ((hfW j).sub hflimW).integrable_sq
  have hconvV : Tendsto (fun j ↦ ∫ x in V, (f j x - flim x) ^ 2 ∂volume)
      atTop (nhds 0) :=
    tendsto_setIntegral_zero_of_subset hVW hVm (fun j x ↦ sq_nonneg _)
      hsqW hconv
  exact centeredNormalizedL2On_le_mul_of_tendsto hVm hVpos hVfin hWm hWpos
    hWfin hfV hflimV (tendsto_normalizedL2On_of_tendsto_integral_sq hconvV)
    hfW hflimW (tendsto_normalizedL2On_of_tendsto_integral_sq hconv) hle

/-- **The energy display passes to the limit.**  Only outer-window `L²`
convergence of the composite field is assumed. -/
theorem vectorNormalizedL2On_le_mul_of_outer_tendsto {V W : Set (Vec d)}
    {F : ℕ → Vec d → Vec d} {Flim : Vec d → Vec d} {K : ℝ}
    (hVm : MeasurableSet V) (hVW : V ⊆ W)
    (hFW : ∀ j, MemVectorL2 W (F j)) (hFlimW : MemVectorL2 W Flim)
    (hconv : Tendsto (fun j ↦ ∫ x in W, vecNormSq (F j x - Flim x) ∂volume)
      atTop (nhds 0))
    (hle : ∀ j, vectorNormalizedL2On V (F j) ≤
      K * vectorNormalizedL2On W (F j)) :
    vectorNormalizedL2On V Flim ≤ K * vectorNormalizedL2On W Flim := by
  have hrestrict : volume.restrict V ≤ volume.restrict W :=
    Measure.restrict_mono hVW le_rfl
  have hFV : ∀ j, MemVectorL2 V (F j) := fun j ↦
    (hFW j).mono_measure hrestrict
  have hFlimV : MemVectorL2 V Flim := hFlimW.mono_measure hrestrict
  have hsubW : ∀ j, MemVectorL2 W (fun x ↦ F j x - Flim x) := fun j ↦
    (hFW j).sub hFlimW
  have hsubV : ∀ j, MemVectorL2 V (fun x ↦ F j x - Flim x) := fun j ↦
    (hsubW j).mono_measure hrestrict
  have hintW : ∀ j, IntegrableOn (fun x ↦ vecNormSq (F j x - Flim x)) W :=
    fun j ↦ integrableOn_vecNormSq_of_memVectorL2 (hsubW j)
  have hconvV : Tendsto (fun j ↦ ∫ x in V, vecNormSq (F j x - Flim x) ∂volume)
      atTop (nhds 0) :=
    tendsto_setIntegral_zero_of_subset hVW hVm
      (fun j x ↦ vecNormSq_nonneg _) hintW hconv
  exact vectorNormalizedL2On_le_mul_of_tendsto_energy
    (fun j ↦ memLp_euclideanNorm_of_memVectorL2 (hFV j))
    (memLp_euclideanNorm_of_memVectorL2 hFlimV)
    (fun j ↦ memLp_euclideanNorm_of_memVectorL2 (hsubV j)) hconvV
    (fun j ↦ memLp_euclideanNorm_of_memVectorL2 (hFW j))
    (memLp_euclideanNorm_of_memVectorL2 hFlimW)
    (fun j ↦ memLp_euclideanNorm_of_memVectorL2 (hsubW j)) hconv hle

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
