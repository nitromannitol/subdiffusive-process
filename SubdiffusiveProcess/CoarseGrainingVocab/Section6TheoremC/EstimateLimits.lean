module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.SeminormLimits
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SandwichNondegeneracy

@[expose] public section

/-!
# Limit passage for the two Theorem C displays

This file closes the part of the trace-approximation and infinite-cutoff
arguments which is purely a limit passage.  In particular, raw `L²`
convergence implies convergence after subtracting the window average, and
both the scalar oscillation estimate and the weighted-gradient estimate are
closed under such convergence.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open Filter MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-- Centering by the window average is a contraction in normalized `L²`,
applied to a difference of two functions. -/
theorem normalizedL2On_centered_sub_le {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hWm : MeasurableSet W) (hW : 0 < (volume W).toReal)
    (hWfin : volume W ≠ ⊤)
    (hf : MemLp f 2 (volume.restrict W))
    (hg : MemLp g 2 (volume.restrict W)) :
    normalizedL2On W (fun x ↦
        (f x - averageOn W f) - (g x - averageOn W g)) ≤
      normalizedL2On W (fun x ↦ f x - g x) := by
  let : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hWfin
  have hfg : MemLp (fun x ↦ f x - g x) 2 (volume.restrict W) := hf.sub hg
  have hfInt : IntegrableOn f W := hf.integrable one_le_two
  have hgInt : IntegrableOn g W := hg.integrable one_le_two
  have hcenter : (fun x ↦
      (f x - averageOn W f) - (g x - averageOn W g)) =
      fun x ↦ (f x - g x) - averageOn W (fun y ↦ f y - g y) := by
    have havg : averageOn W (fun y ↦ f y - g y) =
        averageOn W f - averageOn W g :=
      volumeAverage_sub hfInt hgInt
    funext x
    rw [havg]
    ring
  rw [hcenter]
  have hmean := normalizedL2On_sub_volumeAverage_le hWm hW hWfin
    (hfg.integrable one_le_two) hfg.integrable_sq 0
  simpa only [sub_zero, averageOn] using! hmean

/-- Raw normalized-`L²` convergence implies convergence after subtracting the
window averages. -/
theorem tendsto_centeredNormalizedL2On_sub_of_tendsto_sub
    {W : Set (Vec d)} {f : ℕ → Vec d → ℝ} {flim : Vec d → ℝ}
    (hWm : MeasurableSet W) (hW : 0 < (volume W).toReal)
    (hWfin : volume W ≠ ⊤)
    (hf : ∀ j, MemLp (f j) 2 (volume.restrict W))
    (hflim : MemLp flim 2 (volume.restrict W))
    (h : Tendsto (fun j ↦ normalizedL2On W (fun x ↦ f j x - flim x))
      atTop (nhds 0)) :
    Tendsto (fun j ↦ normalizedL2On W (fun x ↦
        (f j x - averageOn W (f j)) -
          (flim x - averageOn W flim))) atTop (nhds 0) := by
  refine squeeze_zero (fun j ↦ normalizedL2On_nonneg W _) (fun j ↦ ?_) h
  exact normalizedL2On_centered_sub_le hWm hW hWfin (hf j) hflim

/-- The centered oscillation display is closed under raw `L²` convergence on
both its inner and outer windows. -/
theorem centeredNormalizedL2On_le_mul_of_tendsto
    {V W : Set (Vec d)} {f : ℕ → Vec d → ℝ} {flim : Vec d → ℝ}
    {K : ℝ}
    (hVm : MeasurableSet V) (hV : 0 < (volume V).toReal)
    (hVfin : volume V ≠ ⊤)
    (hWm : MeasurableSet W) (hW : 0 < (volume W).toReal)
    (hWfin : volume W ≠ ⊤)
    (hfV : ∀ j, MemLp (f j) 2 (volume.restrict V))
    (hflimV : MemLp flim 2 (volume.restrict V))
    (htV : Tendsto (fun j ↦ normalizedL2On V (fun x ↦ f j x - flim x))
      atTop (nhds 0))
    (hfW : ∀ j, MemLp (f j) 2 (volume.restrict W))
    (hflimW : MemLp flim 2 (volume.restrict W))
    (htW : Tendsto (fun j ↦ normalizedL2On W (fun x ↦ f j x - flim x))
      atTop (nhds 0))
    (hle : ∀ j,
      normalizedL2On V
          (fun x ↦ f j x - averageOn V (f j)) ≤
        K * normalizedL2On W
          (fun x ↦ f j x - averageOn W (f j))) :
    normalizedL2On V (fun x ↦ flim x - averageOn V flim) ≤
      K * normalizedL2On W (fun x ↦ flim x - averageOn W flim) := by
  let fV : ℕ → Vec d → ℝ := fun j x ↦ f j x - averageOn V (f j)
  let flimV : Vec d → ℝ := fun x ↦ flim x - averageOn V flim
  let fW : ℕ → Vec d → ℝ := fun j x ↦ f j x - averageOn W (f j)
  let flimW : Vec d → ℝ := fun x ↦ flim x - averageOn W flim
  have hVfinite : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hVfin
  have hWfinite : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hWfin
  have hfV' : ∀ j, MemLp (fV j) 2 (volume.restrict V) := fun j ↦
    (hfV j).sub (memLp_const _)
  have hflimV' : MemLp flimV 2 (volume.restrict V) :=
    hflimV.sub (memLp_const _)
  have hfW' : ∀ j, MemLp (fW j) 2 (volume.restrict W) := fun j ↦
    (hfW j).sub (memLp_const _)
  have hflimW' : MemLp flimW 2 (volume.restrict W) :=
    hflimW.sub (memLp_const _)
  have htV' : Tendsto
      (fun j ↦ normalizedL2On V (fun x ↦ fV j x - flimV x))
      atTop (nhds 0) := by
    exact tendsto_centeredNormalizedL2On_sub_of_tendsto_sub
      hVm hV hVfin hfV hflimV htV
  have htW' : Tendsto
      (fun j ↦ normalizedL2On W (fun x ↦ fW j x - flimW x))
      atTop (nhds 0) := by
    exact tendsto_centeredNormalizedL2On_sub_of_tendsto_sub
      hWm hW hWfin hfW hflimW htW
  exact le_mul_of_forall_le_mul_of_tendsto
    (tendsto_normalizedL2On_of_tendsto_sub hfV' hflimV' htV')
    (tendsto_normalizedL2On_of_tendsto_sub hfW' hflimW' htW') hle

/-- The vector-energy display is closed under convergence in the corresponding
vector normalized-`L²` seminorm on both windows. -/
theorem vectorNormalizedL2On_le_mul_of_tendsto
    {V W : Set (Vec d)} {F : ℕ → Vec d → Vec d}
    {Flim : Vec d → Vec d} {K : ℝ}
    (hFV : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x)) 2
      (volume.restrict V))
    (hFlimV : MemLp (fun x ↦ euclideanNorm (Flim x)) 2
      (volume.restrict V))
    (hFsubV : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x - Flim x)) 2
      (volume.restrict V))
    (htV : Tendsto
      (fun j ↦ vectorNormalizedL2On V (fun x ↦ F j x - Flim x))
      atTop (nhds 0))
    (hFW : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x)) 2
      (volume.restrict W))
    (hFlimW : MemLp (fun x ↦ euclideanNorm (Flim x)) 2
      (volume.restrict W))
    (hFsubW : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x - Flim x)) 2
      (volume.restrict W))
    (htW : Tendsto
      (fun j ↦ vectorNormalizedL2On W (fun x ↦ F j x - Flim x))
      atTop (nhds 0))
    (hle : ∀ j,
      vectorNormalizedL2On V (F j) ≤ K * vectorNormalizedL2On W (F j)) :
    vectorNormalizedL2On V Flim ≤ K * vectorNormalizedL2On W Flim := by
  exact le_mul_of_forall_le_mul_of_tendsto
    (tendsto_vectorNormalizedL2On_of_tendsto_sub hFV hFlimV hFsubV htV)
    (tendsto_vectorNormalizedL2On_of_tendsto_sub hFW hFlimW hFsubW htW) hle

/-- A bounded nonnegative scalar multiplier costs only its pointwise upper
bound in the vector normalized-`L²` seminorm. -/
theorem vectorNormalizedL2On_smul_le {W : Set (Vec d)}
    {c : Vec d → ℝ} {F : Vec d → Vec d} {A : ℝ}
    (hA : 0 ≤ A) (hc : ∀ x, 0 ≤ c x) (hcA : ∀ x, c x ≤ A)
    (hF : MemLp (fun x ↦ euclideanNorm (F x)) 2 (volume.restrict W))
    (hcF : MemLp (fun x ↦ euclideanNorm (c x • F x)) 2
      (volume.restrict W)) :
    vectorNormalizedL2On W (fun x ↦ c x • F x) ≤
      A * vectorNormalizedL2On W F := by
  have hAF : MemLp (fun x ↦ A * euclideanNorm (F x)) 2
      (volume.restrict W) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hF.const_mul A
  have hpoint : ∀ x,
      euclideanNorm (c x • F x) ≤ A * euclideanNorm (F x) := by
    intro x
    rw [euclideanNorm_smul, abs_of_nonneg (hc x)]
    exact mul_le_mul_of_nonneg_right (hcA x) (euclideanNorm_nonneg _)
  unfold vectorNormalizedL2On
  calc
    normalizedL2On W (fun x ↦ euclideanNorm (c x • F x)) ≤
        normalizedL2On W (fun x ↦ A * euclideanNorm (F x)) :=
      normalizedL2On_mono_of_nonneg hcF.integrable_sq hAF.integrable_sq
        (fun x ↦ euclideanNorm_nonneg _) hpoint
    _ = A * normalizedL2On W (fun x ↦ euclideanNorm (F x)) := by
      rw [normalizedL2On_const_mul W A, abs_of_nonneg hA]

/-- Strong vector `L²` convergence is preserved by a fixed bounded
nonnegative multiplier.  This is the weighted-gradient passage used both for
trace approximation and for the finite-cutoff limit. -/
theorem tendsto_vectorNormalizedL2On_smul_sub_of_tendsto
    {W : Set (Vec d)} {c : Vec d → ℝ}
    {F : ℕ → Vec d → Vec d} {Flim : Vec d → Vec d} {A : ℝ}
    (hA : 0 ≤ A) (hc : ∀ x, 0 ≤ c x) (hcA : ∀ x, c x ≤ A)
    (hFsub : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x - Flim x)) 2
      (volume.restrict W))
    (hcFsub : ∀ j, MemLp
      (fun x ↦ euclideanNorm (c x • (F j x - Flim x))) 2
      (volume.restrict W))
    (h : Tendsto
      (fun j ↦ vectorNormalizedL2On W (fun x ↦ F j x - Flim x))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ vectorNormalizedL2On W
        (fun x ↦ c x • (F j x - Flim x))) atTop (nhds 0) := by
  have hscaled : Tendsto
      (fun j ↦ A * vectorNormalizedL2On W (fun x ↦ F j x - Flim x))
      atTop (nhds 0) := by
    simpa only [mul_zero] using h.const_mul A
  refine squeeze_zero (fun j ↦ normalizedL2On_nonneg W _) (fun j ↦ ?_)
    hscaled
  exact vectorNormalizedL2On_smul_le hA hc hcA (hFsub j) (hcFsub j)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
