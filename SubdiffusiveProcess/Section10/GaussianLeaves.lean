import Mathlib
import MarkovProcess.Path.ExitTime
import SubdiffusiveProcess.Main.DiffusionPath
open Filter MeasureTheory ProbabilityTheory Topology Set
open MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal
noncomputable section
namespace Paper

/-- Source L:395–399. Pool order `astra10_0927_variance_positive`; independently harvested. -/
theorem aux_lim_nongaussian_variance_positive
    {d : ℕ} (P : Measure (SpatialCoordinates d)) [IsGaussian P]
    (L : StrongDual ℝ (SpatialCoordinates d))
    (hnull : P {x | L x = ∫ y, L y ∂P} = 0) :
    0 < Var[L; P] := by
  by_contra h
  push_neg at h
  have h0 : Var[⇑L; P] = 0 := le_antisymm h (variance_nonneg (⇑L) P)
  set m : ℝ := ∫ y, L y ∂P with hm
  have hmap : Measure.map (⇑L) P = Measure.dirac m := by
    rw [IsGaussian.map_eq_gaussianReal L, h0, Real.toNNReal_zero, gaussianReal_zero_var]
  have hmeas : Measurable (⇑L) := L.continuous.measurable
  have hdirac : (Measure.map (⇑L) P) {m} = 1 := by
    rw [hmap, Measure.dirac_apply_of_mem (Set.mem_singleton m)]
  have hpre : (Measure.map (⇑L) P) {m} = P {x | L x = m} := by
    rw [Measure.map_apply hmeas (measurableSet_singleton m)]
    rfl
  rw [hpre, hm] at hdirac
  rw [hdirac] at hnull
  exact one_ne_zero hnull

/-- Source L:395–398 deterministic lower-dimensional nullity. Pool order `astra10_0927_hausdorff_image_null`; independently harvested. -/
theorem aux_lim_nongaussian_hausdorff_image_null
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F]
    (s : ℝ) (hs : 0 ≤ s) (hdim : (Module.finrank ℝ E : ℝ) < s)
    (f : E → F) (C : ℝ≥0) (hf : LipschitzWith C f) :
    Measure.hausdorffMeasure s (Set.range f) = 0 := by
  have hzero : μH[s] (Set.univ : Set E) = 0 := by
    rw [Real.hausdorffMeasure_of_finrank_lt hdim]
    simp
  have hle : μH[s] (f '' (Set.univ : Set E))
      ≤ (C : ℝ≥0∞) ^ s * μH[s] (Set.univ : Set E) :=
    hf.hausdorffMeasure_image_le hs Set.univ
  rw [hzero, mul_zero] at hle
  rw [Set.image_univ] at hle
  exact le_antisymm hle (zero_le _)

/-- Source L:392–395. Pool order `astra10_0927_singular_ac_obstruction`; independently harvested. -/
theorem aux_lim_nongaussian_singular_ac_obstruction
    {X : Type*} [MeasurableSpace X] (P mu v : Measure X)
    [IsProbabilityMeasure P] (hs : mu ⟂ₘ v) (hP : P ≪ mu) :
    ¬ P ≪ v := by
  intro hPv
  have hms : P ⟂ₘ P := hs.mono_ac hP hPv
  have hzero : P = 0 := (MeasureTheory.Measure.MutuallySingular.self_iff P).mp hms
  have h1 : P univ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
  rw [hzero] at h1
  simp at h1

end Paper
